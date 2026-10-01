#!/usr/bin/env python
"""
netim_query_webui_batch.py -- pure-Python port of netim_query_webui_batch.ps1
for environments (e.g. air-gapped) where PowerShell .ps1 scripts don't run
cleanly. Same behavior: type a device name directly (fast, no waiting), or
click "Load Device List" to pull the full catalog in the background with a
progress bar, or upload a file of device names for one combined batch
report. Only Python + requests required -- no PowerShell.

Reads connection settings from config.ini (the same file netim_query.py
and the PowerShell web UIs use) one directory up from this script.

Usage: python netim_query_webui_batch.py [--port 8942]
"""
import argparse
import configparser
import csv
import html
import io
import json
import os
import sys
import threading
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, quote, urlsplit

import requests
import urllib3

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE = os.path.join(SCRIPT_DIR, 'config.ini')  # shared with the PS1 web UIs, same folder

LIMIT = 1000

# Real attribute names observed on a live NetIM instance -- used only so the
# form's attribute picker is usable right away, before the background
# catalog pull has scanned any real devices. Superseded automatically once
# that pull finishes.
FALLBACK_ATTRIBUTE_NAMES = [
    'accessAddress', 'city', 'cityDisplayName', 'configuredForPolling', 'countryCode', 'countryCodeDisplayName',
    'description', 'deviceAccessInfoId', 'deviceName', 'deviceType', 'displayName', 'hostname', 'id', 'ifNumber',
    'latitude', 'longitude', 'name', 'nodeType', 'numConnectedHosts', 'numInterfaces', 'osVersion', 'primaryAddress',
    'prompt', 'regionID', 'regionIDDisplayName', 'serialNumber', 'sitegateway', 'sysContact', 'sysDescr', 'sysDomain',
    'sysLocation', 'sysName', 'sysObjectID', 'sysServices', 'timeZone', 'timeZoneDisplayName', 'vendor',
]

DEFAULT_COLUMNS = ['deviceName', 'accessAddress', 'vendor', 'nodeType', 'sysObjectID']


def load_connection_config():
    config = configparser.ConfigParser()
    config.read(CONFIG_FILE)
    host = config.get('netim', 'host', fallback='')
    user = config.get('netim', 'username', fallback='')
    password = config.get('netim', 'password', fallback='')
    if not host or not user:
        raise SystemExit(f'{CONFIG_FILE} is missing host/username under [netim]')
    return host, user, password


def scalar_attribute_names(devices):
    """Attribute names usable as a filter/output column -- excludes nested
    object/array fields (containers, deviceAccessInfo, health, links, meta,
    userAuthorities, ...) that don't render sensibly as one table cell."""
    names = set()
    for d in devices:
        for key, value in d.items():
            if value is None or isinstance(value, (dict, list)):
                continue
            names.add(key)
    return sorted(names)


def device_name_match(device, name):
    """Case-insensitive substring match on deviceName -- blank name matches
    every device. Applied as our own precise post-filter on top of whatever
    NetIM's own ?search= returns, so behavior stays identical whether a
    device came from the fast scoped search or the full catalog."""
    if not name:
        return True
    return name.lower() in str(device.get('deviceName', '')).lower()


def fetch_paged(session, url):
    """Fetch every page of a NetIM v1 paginated GET (items/meta.total/meta.next_offset).
    No progress reporting -- used for the fast, narrowly-scoped device-name
    search path, which is normally only a page or two."""
    items = []
    offset = 0
    total = None
    sep = '&' if '?' in url else '?'
    while True:
        resp = session.get(f'{url}{sep}limit={LIMIT}&offset={offset}', timeout=60)
        resp.raise_for_status()
        payload = resp.json()
        page_items = payload.get('items', [])
        items.extend(page_items)
        if total is None:
            total = int(payload.get('meta', {}).get('total', len(items)))
        next_offset = payload.get('meta', {}).get('next_offset')
        if next_offset is None or len(items) >= total or not page_items:
            break
        offset = next_offset
    return items


class FetchProgress:
    """Thread-safe progress state for the background full-catalog pull --
    equivalent to the PS1 version's [hashtable]::Synchronized."""

    def __init__(self):
        self.lock = threading.Lock()
        self.running = False
        self.current = 0
        self.total = 0
        self.done = False
        self.error = None
        self.items = None

    def start(self):
        with self.lock:
            self.running = True
            self.current = 0
            self.total = 0
            self.done = False
            self.error = None
            self.items = None

    def snapshot(self):
        with self.lock:
            return {
                'running': self.running, 'current': self.current, 'total': self.total,
                'done': self.done, 'error': self.error,
            }


class AppState:
    """All server-wide state, equivalent to the PS1 version's $script:
    variables -- one instance, referenced by every request handler."""

    def __init__(self, host, user, password):
        self.host = host
        self.api_base = f'https://{host}/api/netim/v1'
        self.session = requests.Session()
        self.session.auth = (user, password)
        self.session.verify = False
        self.session.headers.update({'Accept': 'application/json'})

        self.devices = []
        self.attribute_names = []
        self.cache_finalized = False
        self.last_results = []
        self.last_columns = []

        self.progress = FetchProgress()
        self.fetch_thread = None
        self.state_lock = threading.Lock()

    def start_device_fetch(self):
        """Kicks off (or re-kicks-off, for /refresh) the full-catalog pull
        in a background thread so the HTTP server stays responsive the
        whole time. User-initiated only -- triggered by the form's "Load
        Device List" button or /refresh, never automatically on startup."""
        with self.state_lock:
            if self.fetch_thread and self.fetch_thread.is_alive():
                return
            self.progress.start()
            self.cache_finalized = False
            self.fetch_thread = threading.Thread(target=self._fetch_worker, daemon=True)
        print('Loading NetIM device catalog in the background...')
        self.fetch_thread.start()

    def _fetch_worker(self):
        items = []
        offset = 0
        total = None
        try:
            while True:
                resp = self.session.get(f'{self.api_base}/devices', params={'limit': LIMIT, 'offset': offset}, timeout=120)
                resp.raise_for_status()
                payload = resp.json()
                page_items = payload.get('items', [])
                items.extend(page_items)
                if total is None:
                    total = int(payload.get('meta', {}).get('total', len(items)))
                    with self.progress.lock:
                        self.progress.total = total
                with self.progress.lock:
                    self.progress.current = len(items)
                next_offset = payload.get('meta', {}).get('next_offset')
                if next_offset is None or len(items) >= total or not page_items:
                    break
                offset = next_offset
            with self.progress.lock:
                self.progress.items = items
        except Exception as exc:
            with self.progress.lock:
                self.progress.error = str(exc)
        finally:
            with self.progress.lock:
                self.progress.done = True
                self.progress.running = False

    def sync_cache_if_ready(self):
        """Called from a request-handling thread once progress.done flips
        true -- copies the finished pull's results into self.devices and
        computes the real attribute list. Cheap to call repeatedly; only
        does the copy once per completed fetch."""
        snap = self.progress.snapshot()
        if snap['done'] and not self.cache_finalized:
            if snap['error']:
                print(f"[ERROR] Device fetch failed: {snap['error']}")
            else:
                self.devices = list(snap.get('items') or self.progress.items or [])
                self.attribute_names = scalar_attribute_names(self.devices)
                print(f'Loaded {len(self.devices)} devices, {len(self.attribute_names)} usable attributes')
            self.cache_finalized = True


STATE = None  # set in main() after config is loaded

# ── Page templates ───────────────────────────────────────────────────────
PAGE_STYLE = """
  * { box-sizing: border-box; margin: 0; padding: 0; }
  body { font-family: Arial, sans-serif; background: #f0f2f5; color: #222; font-size: 14px; }
  .header { background: #003B5C; color: white; padding: 18px 28px; }
  .header h1 { font-size: 1.3em; }
  .header .sub { opacity: 0.8; font-size: 0.85em; margin-top: 4px; }
  .container { padding: 24px 28px; max-width: 1000px; margin: 0 auto; }
  .card { background: white; border-radius: 6px; box-shadow: 0 1px 4px rgba(0,0,0,0.1); padding: 20px 24px; margin-bottom: 20px; }
  h4 { color: #003B5C; font-size: 0.9em; text-transform: uppercase; letter-spacing: 0.5px; margin-bottom: 12px; }
  label { display: block; margin-bottom: 4px; font-weight: bold; }
  select, input[type=text] { width: 100%; padding: 8px; margin-bottom: 14px; border: 1px solid #ccc; border-radius: 4px; font-size: 14px; }
  .attr-select { padding: 4px; }
  .attr-select option { padding: 4px 6px; }
  button { background: #003B5C; color: white; border: none; padding: 10px 22px; border-radius: 4px; font-size: 14px; cursor: pointer; }
  button:hover { background: #00507a; }
  .meta { color: #666; font-size: 0.85em; margin-bottom: 14px; }
  .meta a { color: #003B5C; }
  .actions { display: flex; gap: 10px; margin-bottom: 16px; }
  .btn { background: #003B5C; color: white; border: none; padding: 8px 18px; border-radius: 4px; font-size: 13px; cursor: pointer; text-decoration: none; display: inline-block; }
  .btn:hover { background: #00507a; }
  .progress-wrap { margin: -6px 0 14px 0; }
  .progress-bar { background: #e6e9ec; border-radius: 4px; height: 8px; overflow: hidden; }
  .progress-bar-fill { background: #003B5C; height: 100%; width: 0%; transition: width 0.3s ease; }
  table { width: 100%; border-collapse: collapse; }
  th, td { text-align: left; padding: 8px 10px; border-bottom: 1px solid #eee; font-size: 0.9em; }
  th { background: #f7f9fb; color: #003B5C; }
  .error { background: #fdecea; border: 1px solid #f5c2c0; color: #611a15; padding: 14px 18px; border-radius: 4px; }
  .status-found { color: #1a7a3c; font-weight: bold; }
  .status-notfound { color: #b3261e; font-weight: bold; }
  .segmented { display: inline-flex; border: 1px solid #ccc; border-radius: 6px; overflow: hidden; margin-bottom: 16px; }
  .segmented button { background: white; color: #555; border: none; padding: 9px 16px; font-size: 13px; font-weight: 500; cursor: pointer; }
  .segmented button + button { border-left: 1px solid #ccc; }
  .segmented button.active { background: #003B5C; color: white; }
  #tab-file-btn { background: #145478; color: white; }
  #tab-file-btn.active { background: #003B5C; color: white; }
  .mode-panel { display: none; }
  .mode-panel.active { display: block; }
  .file-drop { border: 1.5px dashed #bbb; border-radius: 6px; padding: 18px; text-align: center; background: #f7f9fb; margin-bottom: 8px; }
  .file-drop input[type=file] { display: none; }
  .file-hint { margin-top: 8px; font-size: 0.8em; color: #666; }
  .file-summary { margin-top: 12px; background: #eaf5f2; border: 1px solid #12897A; border-radius: 4px; padding: 10px 14px; font-size: 0.85em; display: none; }
  .file-summary.active { display: block; }
  .file-summary .names { margin-top: 4px; color: #555; }
"""

# No server-side values are interpolated into this JS except the
# __START_POLLING__ boolean, substituted via .replace() -- keeping this a
# plain string (not an f-string) means none of its many { } need escaping.
FORM_JS = """
function startDevicePolling() {
  var pollTimer = setInterval(function () {
    fetch('/progress.json').then(function (r) { return r.json(); }).then(function (data) {
      var fill = document.getElementById('progress-bar-fill');
      if (fill && data.total > 0) { fill.style.width = Math.min(100, Math.round(100 * data.current / data.total)) + '%'; }
      var label = document.getElementById('loaded-text');
      if (!data.done) {
        if (label) { label.textContent = 'Loading device list: ' + data.current + ' of ' + (data.total || '?') + '...'; }
        return;
      }
      clearInterval(pollTimer);
      var wrap = document.getElementById('progress-bar-wrap');
      if (wrap) { wrap.style.display = 'none'; }
      var refreshLink = document.getElementById('refresh-link');
      if (refreshLink) { refreshLink.style.display = ''; }
      if (data.error) {
        if (label) { label.textContent = 'Device catalog load failed: ' + data.error + ' (you can still type a device name directly)'; }
        return;
      }
      if (label) { label.textContent = data.deviceCount + ' devices loaded'; }
      var nameInput = document.getElementById('device-name-input');
      if (nameInput) { nameInput.placeholder = 'Type to search ' + data.deviceCount + ' devices, or click in the box to browse the list'; }
      fetch('/device-names.json').then(function (r) { return r.json(); }).then(function (d) {
        var dl = document.getElementById('device-names-list');
        dl.innerHTML = '';
        d.names.forEach(function (n) {
          var opt = document.createElement('option');
          opt.value = n;
          dl.appendChild(opt);
        });
      });
      fetch('/attributes.json').then(function (r) { return r.json(); }).then(function (d) {
        var sel = document.getElementById('attr-select');
        var already = new Set(Array.prototype.map.call(sel.options, function (o) { return o.value; }));
        var selected = new Set(Array.prototype.map.call(sel.selectedOptions, function (o) { return o.value; }));
        d.attributes.forEach(function (a) {
          if (!already.has(a)) {
            var opt = document.createElement('option');
            opt.value = a; opt.textContent = a;
            sel.appendChild(opt);
          }
        });
        Array.prototype.forEach.call(sel.options, function (o) { o.selected = selected.has(o.value); });
      });
    }).catch(function () { /* transient poll error -- try again next tick */ });
  }, 1000);
}

var loadBtn = document.getElementById('load-devices-btn');
if (loadBtn) {
  loadBtn.addEventListener('click', function () {
    loadBtn.style.display = 'none';
    var wrap = document.getElementById('progress-bar-wrap');
    if (wrap) { wrap.style.display = ''; }
    fetch('/load-devices').then(function () { startDevicePolling(); });
  });
}

if (__START_POLLING__) { startDevicePolling(); }

var tabSingleBtn = document.getElementById('tab-single-btn');
var tabFileBtn = document.getElementById('tab-file-btn');
var panelSingle = document.getElementById('panel-single');
var panelFile = document.getElementById('panel-file');

function setDeviceMode(mode) {
  var single = mode === 'single';
  tabSingleBtn.classList.toggle('active', single);
  tabFileBtn.classList.toggle('active', !single);
  panelSingle.classList.toggle('active', single);
  panelFile.classList.toggle('active', !single);
}
tabSingleBtn.addEventListener('click', function () { setDeviceMode('single'); });
tabFileBtn.addEventListener('click', function () { setDeviceMode('file'); });

var pickFileBtn = document.getElementById('pick-file-btn');
var deviceFileInput = document.getElementById('device-file-input');
var deviceListText = document.getElementById('device-list-text');
var fileSummary = document.getElementById('file-summary');
var fileSummaryCount = document.getElementById('file-summary-count');
var fileSummaryName = document.getElementById('file-summary-name');
var fileSummaryNames = document.getElementById('file-summary-names');

pickFileBtn.addEventListener('click', function () { deviceFileInput.click(); });
deviceFileInput.addEventListener('change', function () {
  var file = deviceFileInput.files[0];
  if (!file) { return; }
  var reader = new FileReader();
  reader.onload = function (e) {
    var text = String(e.target.result || '');
    var lines = text.split(/\\r?\\n/)
      .map(function (l) { return l.split(',')[0].trim(); })
      .filter(function (l) { return l && !/^device[_ ]?name$/i.test(l); });
    deviceListText.value = lines.join('\\n');
    fileSummaryCount.textContent = lines.length + ' device name' + (lines.length === 1 ? '' : 's');
    fileSummaryName.textContent = file.name;
    fileSummaryNames.textContent = lines.slice(0, 10).join(', ') + (lines.length > 10 ? ', ...' : '');
    fileSummary.classList.add('active');
  };
  reader.readAsText(file);
});

document.getElementById('query-form').addEventListener('submit', function (e) {
  if (!tabSingleBtn.classList.contains('active') && !deviceListText.value) {
    e.preventDefault();
    alert('Choose a file first, or switch back to Single device.');
  }
});
"""

RESULTS_JS = """
document.getElementById('new-query-link').addEventListener('click', function (e) {
  e.preventDefault();
  if (window.opener && !window.opener.closed) {
    window.opener.location.href = '/';
    window.opener.focus();
  }
  window.close();
});
document.getElementById('close-window-btn').addEventListener('click', function () {
  window.close();
});
"""


def form_page_html():
    STATE.sync_cache_if_ready()
    snap = STATE.progress.snapshot()
    is_done = STATE.cache_finalized
    is_running = (not is_done) and snap['running']
    not_loaded = (not is_done) and (not is_running)

    attr_names_for_render = STATE.attribute_names if STATE.attribute_names else FALLBACK_ATTRIBUTE_NAMES
    default_cols = [c for c in DEFAULT_COLUMNS if c in attr_names_for_render]
    attr_select_options = '\n'.join(
        f'<option value="{a}"{" selected" if a in default_cols else ""}>{a}</option>'
        for a in attr_names_for_render
    )

    device_names = sorted({d.get('deviceName', '') for d in STATE.devices if d.get('deviceName')})
    device_name_options = '\n'.join(f'<option value="{n}">{n}</option>' for n in device_names)

    if is_done:
        loaded_text = f'{len(STATE.devices)} devices loaded'
    elif is_running and snap['total'] > 0:
        loaded_text = f"Loading device list: {snap['current']} of {snap['total']}..."
    elif is_running:
        loaded_text = 'Loading device list...'
    else:
        loaded_text = 'Device list not loaded'

    if is_done:
        device_name_placeholder = f'Type to search {len(STATE.devices)} devices, or click in the box to browse the list'
    else:
        device_name_placeholder = 'Type a device name directly or click the Load Device List button'

    progress_hidden_attr = '' if is_running else 'style="display:none"'
    # This button already carries style="margin-bottom:16px" -- a second
    # style="display:none" attribute would collide (browsers keep only the
    # first `style` attribute on an element and silently drop the rest),
    # so fold both into one style value instead of two attributes.
    load_button_style = 'margin-bottom:16px' + ('' if not_loaded else '; display:none')
    refresh_link_hidden_attr = '' if is_done else 'style="display:none"'
    form_js = FORM_JS.replace('__START_POLLING__', 'true' if is_running else 'false')

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<title>NetIM Device Query (Batch)</title>
<style>
{PAGE_STYLE}
</style>
</head>
<body>
<div class="header">
  <h1>NetIM Device Query (Batch)</h1>
  <div class="sub">{html.escape(STATE.host)}</div>
</div>
<div class="container">
  <div class="card">
    <div class="meta">
      <span id="loaded-text">{html.escape(loaded_text)}</span>
      <a href="/refresh" id="refresh-link" {refresh_link_hidden_attr}>&middot; refresh from NetIM</a>
    </div>
    <button type="button" id="load-devices-btn" style="{load_button_style}">Load Device List</button>
    <div id="progress-bar-wrap" class="progress-wrap" {progress_hidden_attr}>
      <div class="progress-bar"><div id="progress-bar-fill" class="progress-bar-fill"></div></div>
    </div>
    <form method="post" action="/query" target="_blank" id="query-form">
      <h4>Devices to report on</h4>
      <div class="segmented" role="tablist">
        <button type="button" class="active" id="tab-single-btn">Single device</button>
        <button type="button" id="tab-file-btn">Multiple devices, Upload File</button>
      </div>

      <div class="mode-panel active" id="panel-single">
        <input type="text" name="DEVICE_NAME" id="device-name-input" list="device-names-list" autocomplete="off"
               placeholder="{html.escape(device_name_placeholder)}">
        <datalist id="device-names-list">
{device_name_options}
        </datalist>
      </div>

      <div class="mode-panel" id="panel-file">
        <div class="file-drop">
          <input type="file" id="device-file-input" accept=".txt,.csv">
          <button type="button" class="btn" id="pick-file-btn">Choose file...</button>
          <div class="file-hint">One device name per line, or the first column of a CSV. Every device found in the file goes into one combined report.</div>
        </div>
        <div class="file-summary" id="file-summary">
          <div><strong id="file-summary-count"></strong> found in <span id="file-summary-name"></span></div>
          <div class="names" id="file-summary-names"></div>
        </div>
        <input type="hidden" name="DEVICE_LIST_TEXT" id="device-list-text">
      </div>

      <h4>Attributes to show</h4>
      <div class="meta" style="margin-bottom:6px">Ctrl-click to select more than one.</div>
      <select name="OUTPUT_ATTR" multiple size="14" class="attr-select" id="attr-select">
{attr_select_options}
      </select>
      <button type="submit" style="margin-top:14px">Generate Report</button>
    </form>
  </div>
</div>
<script>
{form_js}
</script>
</body></html>
"""


def results_page_html(rows, columns, summary):
    header_cells = ''.join(f'<th>{html.escape(c)}</th>' for c in columns)
    body_row_parts = []
    for row in rows:
        cells = []
        for c in columns:
            v = str(row.get(c, ''))
            if c == 'Status' and v == 'Found':
                cell_class = ' class="status-found"'
            elif c == 'Status' and v == 'Not found':
                cell_class = ' class="status-notfound"'
            else:
                cell_class = ''
            cells.append(f'<td{cell_class}>{html.escape(v)}</td>')
        body_row_parts.append(f'<tr>{"".join(cells)}</tr>')
    body_rows = '\n'.join(body_row_parts)

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<title>NetIM Device Query (Batch) -- Results</title>
<style>
{PAGE_STYLE}
</style>
</head>
<body>
<div class="header">
  <h1>NetIM Device Query (Batch)</h1>
  <div class="sub">{html.escape(STATE.host)}</div>
</div>
<div class="container">
  <div class="card">
    <div class="meta">{summary}</div>
    <div class="actions">
      <a class="btn" href="/" id="new-query-link">New Query</a>
      <a class="btn" href="/export.csv">Download CSV</a>
      <button class="btn" type="button" id="close-window-btn">Close Window</button>
    </div>
    <div style="overflow-x:auto">
    <table>
      <thead><tr>{header_cells}</tr></thead>
      <tbody>
{body_rows}
      </tbody>
    </table>
    </div>
  </div>
</div>
<script>
{RESULTS_JS}
</script>
</body></html>
"""


def error_page_html(message):
    return f"""<!DOCTYPE html>
<html lang="en">
<head><meta charset="UTF-8"><title>NetIM Device Query (Batch) -- Error</title>
<style>
{PAGE_STYLE}
</style>
</head>
<body>
<div class="header"><h1>NetIM Device Query (Batch)</h1></div>
<div class="container">
  <div class="card">
    <div class="error">{html.escape(message)}</div>
    <p style="margin-top:14px"><a href="/">Back to form</a></p>
  </div>
</div>
</body></html>
"""


# ── HTTP server ───────────────────────────────────────────────────────────
class Handler(BaseHTTPRequestHandler):
    server_version = 'NetimQueryBatch/1.0'

    def log_message(self, fmt, *args):
        pass  # keep console output limited to our own prints, like the PS1 version

    def _send_html(self, body_html, status=200):
        body = body_html.encode('utf-8')
        self.send_response(status)
        self.send_header('Content-Type', 'text/html; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _send_json(self, obj, status=200):
        body = json.dumps(obj).encode('utf-8')
        self.send_response(status)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _handle_error(self, exc):
        print(f'[ERROR] Request handling failed: {exc}')
        try:
            self._send_html(f'<h1>Error</h1><pre>{html.escape(str(exc))}</pre>', status=500)
        except Exception:
            pass

    def do_GET(self):
        path = urlsplit(self.path).path
        try:
            if path == '/':
                self._send_html(form_page_html())
            elif path == '/export.csv':
                self._handle_export_csv()
            elif path == '/refresh':
                STATE.start_device_fetch()
                self.send_response(302)
                self.send_header('Location', '/')
                self.end_headers()
            elif path == '/load-devices':
                # User-initiated only -- triggered by the form's "Load
                # Device List" button via fetch(), never automatically.
                STATE.start_device_fetch()
                self._send_json({'started': True})
            elif path == '/progress.json':
                STATE.sync_cache_if_ready()
                snap = STATE.progress.snapshot()
                self._send_json({
                    'done': snap['done'], 'current': snap['current'], 'total': snap['total'],
                    'error': snap['error'], 'deviceCount': len(STATE.devices),
                })
            elif path == '/device-names.json':
                STATE.sync_cache_if_ready()
                names = sorted({d.get('deviceName', '') for d in STATE.devices if d.get('deviceName')})
                self._send_json({'names': names})
            elif path == '/attributes.json':
                STATE.sync_cache_if_ready()
                self._send_json({'attributes': STATE.attribute_names})
            else:
                self._send_html('<h1>Not found</h1>', status=404)
        except Exception as exc:
            self._handle_error(exc)

    def do_POST(self):
        path = urlsplit(self.path).path
        try:
            if path == '/query':
                self._handle_query()
            else:
                self._send_html('<h1>Not found</h1>', status=404)
        except Exception as exc:
            self._handle_error(exc)

    def _handle_export_csv(self):
        if not STATE.last_results:
            self._send_html(error_page_html('No query results to export yet -- run a query first.'), status=400)
            return
        buf = io.StringIO()
        writer = csv.DictWriter(buf, fieldnames=STATE.last_columns)
        writer.writeheader()
        writer.writerows(STATE.last_results)
        body = buf.getvalue().encode('utf-8')
        self.send_response(200)
        self.send_header('Content-Type', 'text/csv')
        self.send_header('Content-Disposition', 'attachment; filename="netim_query_results.csv"')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _handle_query(self):
        length = int(self.headers.get('Content-Length', 0) or 0)
        body_text = self.rfile.read(length).decode('utf-8') if length else ''
        form = parse_qs(body_text, keep_blank_values=True)

        device_name = form.get('DEVICE_NAME', [''])[0].strip()
        file_text = form.get('DEVICE_LIST_TEXT', [''])[0]
        file_names = [line.strip() for line in file_text.split('\n') if line.strip()]
        columns = form.get('OUTPUT_ATTR', [])
        if not columns:
            columns = ['deviceName']

        STATE.sync_cache_if_ready()

        if file_names:
            self._handle_file_query(file_names, columns)
            return

        if not device_name and not STATE.cache_finalized:
            snap = STATE.progress.snapshot()
            if snap['running']:
                msg = (f"The full device catalog is still loading in the background "
                       f"({snap['current']} of {snap['total']} so far) -- wait a moment and try "
                       f"again, or type a specific device name above to search immediately "
                       f"without waiting.")
            else:
                msg = ("The device catalog hasn't been loaded yet -- go back and click "
                       "'Load Device List' to browse all devices, or type a specific device "
                       "name above to search immediately without loading anything.")
            self._send_html(error_page_html(msg), status=503)
            return

        if device_name:
            # Fast path: a live, narrowly-scoped fetch -- doesn't wait on the
            # full background catalog pull, so a known device name always
            # works immediately even against a production instance with
            # thousands of devices. NetIM's own ?search= narrows what comes
            # back server-side; our own case-insensitive contains match on
            # top keeps results identical to the "all devices" path.
            search_url = f'{STATE.api_base}/devices?search={quote(device_name)}'
            candidates = fetch_paged(STATE.session, search_url)
            matched = [d for d in candidates if device_name_match(d, device_name)]
            total_count = len(STATE.devices) if STATE.cache_finalized else None
            if total_count is not None:
                summary = f'{len(matched)} matched (direct search, not the full {total_count}-device catalog)'
            else:
                snap = STATE.progress.snapshot()
                if snap['running']:
                    summary = f'{len(matched)} matched (direct search -- full catalog still loading in the background)'
                else:
                    summary = f'{len(matched)} matched (direct search -- full catalog not loaded)'
        else:
            matched = [d for d in STATE.devices if device_name_match(d, device_name)]
            total_count = len(STATE.devices)
            summary = f'{len(matched)} of {total_count} devices matched'

        rows = [{c: str(d.get(c, '')) for c in columns} for d in matched]
        STATE.last_results = rows
        STATE.last_columns = columns

        self._send_html(results_page_html(rows, columns, summary))

    def _handle_file_query(self, file_names, columns):
        # Batch/file mode -- every requested name is checked in one
        # in-memory pass against the full catalog, so (unlike the
        # single-name fast path) this needs the catalog loaded first rather
        # than doing one live search per name. Exact match, not "contains":
        # a device-list file is expected to hold precise identifiers, not
        # partial search text.
        if not STATE.cache_finalized:
            snap = STATE.progress.snapshot()
            if snap['running']:
                msg = (f"The full device catalog is still loading in the background "
                       f"({snap['current']} of {snap['total']} so far) -- a file report needs "
                       f"the full catalog loaded first. Wait a moment and try again.")
            else:
                msg = ("A file report needs the full device catalog loaded first -- go back "
                       "and click 'Load Device List', then try again.")
            self._send_html(error_page_html(msg), status=503)
            return

        lookup = {}
        for d in STATE.devices:
            key = str(d.get('deviceName', '')).lower()
            if key and key not in lookup:
                lookup[key] = d

        other_columns = [c for c in columns if c != 'deviceName']
        report_columns = ['Status', 'deviceName'] + other_columns

        seen = set()
        rows = []
        for name in file_names:
            key = name.lower()
            if key in seen:
                continue
            seen.add(key)
            device = lookup.get(key)
            row = {
                'Status': 'Found' if device else 'Not found',
                'deviceName': device.get('deviceName', '') if device else name,
            }
            for c in other_columns:
                row[c] = str(device.get(c, '')) if device else ''
            rows.append(row)

        found_count = sum(1 for r in rows if r['Status'] == 'Found')
        not_found_count = len(rows) - found_count
        summary = f'{found_count} of {len(rows)} file devices found'
        if not_found_count:
            summary += f' ({not_found_count} not found in NetIM)'

        STATE.last_results = rows
        STATE.last_columns = report_columns

        self._send_html(results_page_html(rows, report_columns, summary))


def main():
    # Force line-buffered stdout even when it's redirected (not a real
    # console) -- otherwise "Loading device catalog..." and similar status
    # lines can sit invisible in a buffer for a long time.
    try:
        sys.stdout.reconfigure(line_buffering=True)
    except Exception:
        pass

    parser = argparse.ArgumentParser(description='NetIM device query web UI (batch/file-upload variant)')
    parser.add_argument('--port', type=int, default=8942)
    args = parser.parse_args()

    host, user, password = load_connection_config()
    global STATE
    STATE = AppState(host, user, password)

    # Bind the literal IPv4 loopback address rather than the hostname
    # "localhost" -- on Windows, "localhost" can resolve to the IPv6
    # loopback (::1) instead of 127.0.0.1, and some locked-down/security
    # software environments only allow (or only proxy-exempt) one of the
    # two, causing the browser to open to a dead address even though the
    # server itself started and is listening fine.
    server = ThreadingHTTPServer(('127.0.0.1', args.port), Handler)
    prefix = f'http://127.0.0.1:{args.port}/'
    print(f'NetIM Device Query WebUI (file-upload batch variant, Python) running at {prefix} (Ctrl+C to stop)')
    try:
        webbrowser.open(prefix)
    except Exception:
        pass
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == '__main__':
    main()
