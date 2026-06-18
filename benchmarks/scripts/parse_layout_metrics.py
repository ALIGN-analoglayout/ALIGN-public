#!/usr/bin/env python3
"""Parse ALIGN output LEF and GDS for layout quality metrics."""

import re, sys, json, pathlib, struct

def parse_lef_area(lef_path):
    """Extract MACRO SIZE from top-level LEF. Returns (width, height, area) in µm²."""
    text = pathlib.Path(lef_path).read_text()
    m = re.search(r'SIZE\s+([\d.]+)\s+BY\s+([\d.]+)', text)
    if not m:
        return None, None, None
    w, h = float(m.group(1)), float(m.group(2))
    return w, h, round(w * h, 4)

def parse_gds_metrics(gds_path, via_layers):
    """
    Parse binary GDS II file for total wirelength and via count.
    wire_layers: set of GDS layer numbers for routing metals (M1-M5)
    via_layers: set of GDS layer numbers that represent vias
    Returns dict with wirelength_um and via_count.
    """
    wire_layers = {13, 15, 19, 21, 23}  # M1-M5
    # via_layers arg is used below

    total_wire_length = 0.0
    via_count = 0
    db_unit = 1e-9  # default, overridden by UNITS record

    with open(gds_path, 'rb') as f:
        data = f.read()

    i = 0
    current_layer = None
    in_path = False

    while i < len(data) - 4:
        length = struct.unpack_from('>H', data, i)[0]
        if length < 4:
            i += 4
            continue
        rtype = struct.unpack_from('>H', data, i + 2)[0]
        payload = data[i + 4: i + length]
        record_type = rtype >> 8

        if record_type == 0x03 and len(payload) >= 16:
            db_unit = struct.unpack_from('>d', payload, 8)[0]
        elif record_type == 0x0D and len(payload) >= 2:
            current_layer = struct.unpack_from('>H', payload)[0]
        elif record_type == 0x09:
            in_path = True
        elif record_type == 0x10 and in_path and current_layer in wire_layers:
            coords = struct.unpack_from('>' + 'i' * (len(payload) // 4), payload)
            pts = [(coords[j], coords[j+1]) for j in range(0, len(coords)-1, 2)]
            for j in range(len(pts) - 1):
                dx = abs(pts[j+1][0] - pts[j][0])
                dy = abs(pts[j+1][1] - pts[j][1])
                total_wire_length += (dx + dy) * db_unit * 1e6
        elif record_type == 0x11:
            in_path = False
        elif record_type in (0x08, 0x06) and current_layer in via_layers:
            via_count += 1

        i += length

    return {
        'wirelength_um': round(total_wire_length, 2),
        'via_count': via_count,
    }

def main():
    circuit = sys.argv[1]
    work_dir = pathlib.Path(sys.argv[2])
    runtime_ms = int(sys.argv[3])
    version = sys.argv[4]

    lef_files = list(work_dir.glob(f'{circuit}.lef'))
    if not lef_files:
        lef_files = list(work_dir.rglob('*.lef'))
    if not lef_files:
        print(f'ERROR: no LEF file found in {work_dir}', file=sys.stderr)
        sys.exit(1)
    lef_path = lef_files[0]

    gds_files = list(work_dir.rglob('*.gds'))
    gds_metrics = {'wirelength_um': None, 'via_count': None}
    if gds_files:
        try:
            gds_metrics = parse_gds_metrics(str(gds_files[0]), via_layers={12,14,16,17,22})
        except Exception as e:
            print(f'WARNING: GDS parse failed: {e}', file=sys.stderr)

    w, h, area = parse_lef_area(str(lef_path))

    metrics = {
        'circuit': circuit,
        'version': version,
        'area_um2': area,
        'cell_width_um': w,
        'cell_height_um': h,
        'wirelength_um': gds_metrics['wirelength_um'],
        'via_count': gds_metrics['via_count'],
        'runtime_s': round(runtime_ms / 1000, 2),
    }

    out_path = work_dir / 'layout_metrics.json'
    out_path.write_text(json.dumps(metrics, indent=2))
    print(json.dumps(metrics, indent=2))

if __name__ == '__main__':
    main()
