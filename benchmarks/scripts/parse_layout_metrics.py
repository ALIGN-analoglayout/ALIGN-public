#!/usr/bin/env python3
"""Parse ALIGN output LEF and GDS for layout quality metrics."""

import re, sys, json, pathlib, struct, argparse

# ---------------------------------------------------------------------------
# PDK layer definitions
# ---------------------------------------------------------------------------
# For FinFET14nm_Mock_PDK: simple layer-number sets.
# For SKY130_PDK: (layer, datatype) pairs are required because multiple
# logical layers share GDS layer numbers and are distinguished by datatype.
PDK_LAYERS = {
    'FinFET14nm_Mock_PDK': {
        'wire': {13, 15, 19, 21, 23},   # M1-M5
        'via':  {12, 14, 16, 17, 22},   # V0-V4
    },
    'SKY130_PDK': {
        # wire: M1-M5 are layers 67-71 with datatype 20
        # via:  V0-V4 are layers 66-70 with datatype 44
        # GDS parser checks (layer, datatype) pairs
        'wire_dt': {(67,20),(68,20),(69,20),(70,20),(71,20)},
        'via_dt':  {(66,44),(67,44),(68,44),(69,44),(70,44)},
    },
}

def parse_lef_area(lef_path):
    """Extract MACRO SIZE from top-level LEF. Returns (width, height, area) in µm²."""
    text = pathlib.Path(lef_path).read_text()
    m = re.search(r'SIZE\s+([\d.]+)\s+BY\s+([\d.]+)', text)
    if not m:
        return None, None, None
    w, h = float(m.group(1)), float(m.group(2))
    return w, h, round(w * h, 4)

def parse_gds_metrics(gds_path, layer_spec):
    """
    Parse binary GDS II file for total wirelength and via count.

    layer_spec is a dict from PDK_LAYERS with either:
      - 'wire' / 'via' keys (sets of layer numbers) for layer-only matching, or
      - 'wire_dt' / 'via_dt' keys (sets of (layer, datatype) tuples) for
        layer+datatype matching (e.g. SKY130_PDK).

    Returns dict with wirelength_um and via_count.
    """
    use_dt = 'wire_dt' in layer_spec  # datatype-aware matching

    if use_dt:
        wire_set = layer_spec['wire_dt']
        via_set  = layer_spec['via_dt']
    else:
        wire_set = layer_spec['wire']
        via_set  = layer_spec['via']

    total_wire_length = 0.0
    via_count = 0
    db_unit = 1e-9  # default, overridden by UNITS record

    with open(gds_path, 'rb') as f:
        data = f.read()

    i = 0
    current_layer = None
    current_datatype = None
    in_path = False

    def _in_wire():
        if use_dt:
            return (current_layer, current_datatype) in wire_set
        return current_layer in wire_set

    def _in_via():
        if use_dt:
            return (current_layer, current_datatype) in via_set
        return current_layer in via_set

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
            current_datatype = None  # reset until DATATYPE record arrives
        elif record_type == 0x0E and len(payload) >= 2:
            # DATATYPE record (0x0E xx) — follows LAYER for most element types
            current_datatype = struct.unpack_from('>H', payload)[0]
        elif record_type == 0x09:
            in_path = True
        elif record_type == 0x10 and in_path and _in_wire():
            coords = struct.unpack_from('>' + 'i' * (len(payload) // 4), payload)
            pts = [(coords[j], coords[j+1]) for j in range(0, len(coords)-1, 2)]
            for j in range(len(pts) - 1):
                dx = abs(pts[j+1][0] - pts[j][0])
                dy = abs(pts[j+1][1] - pts[j][1])
                total_wire_length += (dx + dy) * db_unit * 1e6
        elif record_type == 0x11:
            in_path = False
        elif record_type in (0x08, 0x06) and _in_via():
            via_count += 1

        i += length

    return {
        'wirelength_um': round(total_wire_length, 2),
        'via_count': via_count,
    }

def main():
    parser = argparse.ArgumentParser(
        description='Parse ALIGN output LEF/GDS and write layout_metrics.json'
    )
    parser.add_argument('circuit',    help='Circuit name')
    parser.add_argument('work_dir',   help='ALIGN output directory')
    parser.add_argument('runtime_ms', type=int, help='Runtime in milliseconds')
    parser.add_argument('version',    help='ALIGN version string')
    parser.add_argument(
        '--pdk',
        default='FinFET14nm_Mock_PDK',
        choices=list(PDK_LAYERS.keys()),
        help='PDK name to select layer definitions (default: FinFET14nm_Mock_PDK)',
    )
    args = parser.parse_args()

    circuit    = args.circuit
    work_dir   = pathlib.Path(args.work_dir)
    runtime_ms = args.runtime_ms
    version    = args.version
    layer_spec = PDK_LAYERS[args.pdk]

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
            gds_metrics = parse_gds_metrics(str(gds_files[0]), layer_spec)
        except Exception as e:
            print(f'WARNING: GDS parse failed: {e}', file=sys.stderr)

    w, h, area = parse_lef_area(str(lef_path))

    metrics = {
        'circuit': circuit,
        'version': version,
        'pdk': args.pdk,
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
