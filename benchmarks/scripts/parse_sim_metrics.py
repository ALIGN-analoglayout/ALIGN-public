#!/usr/bin/env python3
"""Parse ngspice batch output for .measure results, merge with layout metrics."""

import re, sys, json, math, pathlib

def parse_ngspice_output(ngspice_stdout):
    """Extract .measure results from ngspice stdout. Returns dict of name→value."""
    results = {}
    for line in ngspice_stdout.splitlines():
        m = re.match(r'^\s*([\w_]+)\s*=\s*([-+]?[\d.]+(?:[eE][-+]?\d+)?)', line)
        if m:
            name = m.group(1).lower().strip()
            try:
                results[name] = float(m.group(2))
            except ValueError:
                pass
    return results

def scale_sim_metrics(raw, circuit):
    """Convert raw ngspice values to display units (ns, MHz, dB, µW)."""
    scaled = {}
    unit_map = {
        'tphl_ns':            ('tphl_ns',            1e9),
        'tplh_ns':            ('tplh_ns',             1e9),
        'gain_db':            ('gain_db',             1.0),
        'gain_lin':           ('gain_db',             lambda v: 20.0 * math.log10(abs(v)) if v != 0 else -999.0),
        'ugbw_mhz':           ('ugbw_mhz',            1e-6),
        'phase_at_ugbw':      ('phase_margin_deg',    lambda v: 180.0 + v),
        'bandwidth_mhz':      ('bandwidth_mhz',       1e-6),
        'cmrr_db':            ('cmrr_db',             1.0),
        'regen_time_ns':      ('regen_time_ns',       1e9),
        'static_power_uw':    ('static_power_uw',     1e6),
        'gain_range_db':      ('gain_range_db',       1.0),
        'f3db_mhz':           ('f3db_mhz',            1e-6),
        'passband_ripple_db': ('passband_ripple_db',  1.0),
    }
    for raw_name, (out_name, scale) in unit_map.items():
        if raw_name in raw:
            val = raw[raw_name]
            if callable(scale):
                scaled[out_name] = round(scale(val), 4)
            else:
                scaled[out_name] = round(val * scale, 4)
    return scaled

def main():
    circuit = sys.argv[1]
    work_dir = pathlib.Path(sys.argv[2])
    ngspice_output_file = sys.argv[3]

    ngspice_out = pathlib.Path(ngspice_output_file).read_text()
    raw = parse_ngspice_output(ngspice_out)
    sim_metrics = scale_sim_metrics(raw, circuit)

    layout_file = work_dir / 'layout_metrics.json'
    if layout_file.exists():
        combined = json.loads(layout_file.read_text())
    else:
        combined = {'circuit': circuit}

    combined.update(sim_metrics)

    out_path = work_dir / 'metrics.json'
    out_path.write_text(json.dumps(combined, indent=2))
    print(json.dumps(combined, indent=2))

if __name__ == '__main__':
    main()
