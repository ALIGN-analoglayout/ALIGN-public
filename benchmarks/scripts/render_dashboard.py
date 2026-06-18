#!/usr/bin/env python3
"""
render_dashboard.py <history_json> <output_html>
Generates static Chart.js dashboard from benchmark history.
"""
import json, sys, pathlib

LAYOUT_METRICS = ['area_um2', 'wirelength_um', 'via_count', 'runtime_s']
SIM_METRICS = {
    'buffer':                   ['tphl_ns', 'tplh_ns'],
    'five_transistor_ota':      ['gain_db', 'ugbw_mhz', 'phase_margin_deg'],
    'current_mirror_ota':       ['gain_db', 'bandwidth_mhz'],
    'high_speed_comparator':    ['regen_time_ns', 'static_power_uw'],
    'variable_gain_amplifier':  ['gain_db', 'bandwidth_mhz'],
    'switched_capacitor_filter':['f3db_mhz', 'passband_ripple_db'],
}

HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<title>ALIGN Release Benchmarks</title>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
<style>
  * { box-sizing: border-box; }
  body { font-family: -apple-system, sans-serif; max-width: 1100px; margin: 0 auto; padding: 20px; color: #333; }
  h1 { border-bottom: 2px solid #007bff; padding-bottom: 8px; }
  .tabs { display: flex; gap: 8px; margin: 16px 0; }
  .tab-btn { padding: 8px 20px; border: 1px solid #007bff; border-radius: 4px;
             background: white; color: #007bff; cursor: pointer; font-size: 14px; }
  .tab-btn.active { background: #007bff; color: white; }
  .tab { display: none; }
  .tab.active { display: block; }
  .circuit-card { border: 1px solid #ddd; border-radius: 6px; padding: 16px; margin: 12px 0; }
  .circuit-card h3 { margin-top: 0; color: #007bff; font-size: 16px; }
  .charts-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(280px, 1fr)); gap: 12px; }
  .chart-wrap { position: relative; height: 140px; }
  .chart-label { font-size: 11px; color: #666; margin-bottom: 2px; }
  .regression-table { width: 100%; border-collapse: collapse; margin-top: 12px; font-size: 13px; }
  .regression-table th { background: #f5f5f5; padding: 6px 10px; text-align: left; border: 1px solid #ddd; }
  .regression-table td { padding: 6px 10px; border: 1px solid #ddd; }
  .warn { background: #fff3cd; }
  .fail { background: #f8d7da; }
  .ok   { background: #d4edda; }
</style>
</head>
<body>
<h1>ALIGN Release Benchmarks</h1>
<p>Post-layout metrics tracked across PyPI releases. PDK: FinFET14nm_Mock_PDK.</p>

<div class="tabs">
  <button class="tab-btn active" onclick="showTab('layout', this)">Layout Quality</button>
  <button class="tab-btn"        onclick="showTab('simulation', this)">Simulation</button>
  <button class="tab-btn"        onclick="showTab('regressions', this)">Regressions</button>
</div>

<div id="layout" class="tab active">
  <h2>Layout Quality</h2>
  <div id="layout-content"></div>
</div>

<div id="simulation" class="tab">
  <h2>Post-Layout Simulation</h2>
  <div id="sim-content"></div>
</div>

<div id="regressions" class="tab">
  <h2>Regression Summary</h2>
  <div id="reg-content"></div>
</div>

<script>
const history = __HISTORY__;
const LAYOUT_METRICS = __LAYOUT_METRICS__;
const SIM_METRICS = __SIM_METRICS__;

function showTab(name, btn) {
  document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
  document.querySelectorAll('.tab-btn').forEach(b => b.classList.remove('active'));
  document.getElementById(name).classList.add('active');
  btn.classList.add('active');
}

const versions = history.map(r => r.version);

function miniChart(canvasId, label, versions, data) {
  const ctx = document.getElementById(canvasId);
  if (!ctx) return;
  new Chart(ctx, {
    type: 'line',
    data: {
      labels: versions,
      datasets: [{ label, data,
        borderColor: '#007bff', backgroundColor: 'rgba(0,123,255,0.08)',
        tension: 0.2, pointRadius: 3, fill: true }]
    },
    options: {
      responsive: true, maintainAspectRatio: false,
      plugins: { legend: { display: false } },
      scales: {
        x: { ticks: { font: { size: 10 } } },
        y: { ticks: { font: { size: 10 } } }
      }
    }
  });
}

function getVals(circuit, metric) {
  return history.map(r => {
    const c = (r.circuits || []).find(x => x.circuit === circuit);
    return (c && c[metric] != null) ? c[metric] : null;
  });
}

function buildSection(containerId, circuits, metricsMap) {
  const container = document.getElementById(containerId);
  circuits.forEach(circuit => {
    const metrics = Array.isArray(metricsMap) ? metricsMap : (metricsMap[circuit] || []);
    const card = document.createElement('div');
    card.className = 'circuit-card';
    card.innerHTML = '<h3>' + circuit.replace(/_/g,' ') + '</h3><div class="charts-grid"></div>';
    const grid = card.querySelector('.charts-grid');
    metrics.forEach(metric => {
      const id = 'ch_' + circuit + '_' + metric;
      const wrap = document.createElement('div');
      wrap.innerHTML = '<div class="chart-label">' + metric + '</div><div class="chart-wrap"><canvas id="' + id + '"></canvas></div>';
      grid.appendChild(wrap);
      const vals = getVals(circuit, metric);
      setTimeout(() => miniChart(id, metric, versions, vals), 0);
    });
    container.appendChild(card);
  });
}

const circuits = history.length > 0
  ? [...new Set(history.flatMap(r => (r.circuits||[]).map(c => c.circuit)))]
  : [];

buildSection('layout-content', circuits, LAYOUT_METRICS);
buildSection('sim-content', circuits, SIM_METRICS);

const regContainer = document.getElementById('reg-content');
history.slice().reverse().forEach(release => {
  const regs = release.regressions || {};
  const all = [...(regs.failures||[]).map(r=>({...r,level:'fail'})),
               ...(regs.warnings||[]).map(r=>({...r,level:'warn'}))];
  const section = document.createElement('div');
  section.innerHTML = '<h3>' + release.version + '</h3>';
  if (!all.length) {
    section.innerHTML += '<p style="color:#28a745">&#10003; No regressions detected.</p>';
  } else {
    let html = '<table class="regression-table"><tr><th>Circuit</th><th>Metric</th><th>Previous</th><th>Current</th><th>Change %</th></tr>';
    all.forEach(r => {
      html += '<tr class="' + r.level + '"><td>' + r.circuit + '</td><td>' + r.metric +
              '</td><td>' + r.previous + '</td><td>' + r.current +
              '</td><td>' + (r.pct_change > 0 ? '+' : '') + r.pct_change + '%</td></tr>';
    });
    html += '</table>';
    section.innerHTML += html;
  }
  regContainer.appendChild(section);
});
</script>
</body>
</html>
"""

def main():
    if len(sys.argv) != 3:
        print("Usage: render_dashboard.py <history_json> <output_html>")
        sys.exit(1)

    history_file, output_file = sys.argv[1], sys.argv[2]

    with open(history_file) as f:
        history = json.load(f)

    html = HTML_TEMPLATE \
        .replace('__HISTORY__', json.dumps(history)) \
        .replace('__LAYOUT_METRICS__', json.dumps(LAYOUT_METRICS)) \
        .replace('__SIM_METRICS__', json.dumps(SIM_METRICS))

    out = pathlib.Path(output_file)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(html)
    print(f"Dashboard written to {output_file} ({out.stat().st_size} bytes)")

if __name__ == '__main__':
    main()
