#!/usr/bin/env python3
"""Parse ALIGN output GDS for layout quality metrics."""

import sys, json, pathlib, struct, argparse

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

def parse_gds_metrics(gds_path, layer_spec):
    """
    Parse binary GDS II file for cell area, total wirelength, and via count.

    Cell area is extracted from BOUNDARY records on GDS layer 100 (Bbox layer
    used by all ALIGN PDKs). Wirelength and via count use layer_spec.

    layer_spec keys:
      'wire'/'via'       — sets of layer numbers (FinFET14nm_Mock_PDK)
      'wire_dt'/'via_dt' — sets of (layer, datatype) tuples (SKY130_PDK)

    Returns dict with area_um2, cell_width_um, cell_height_um,
    wirelength_um, via_count.
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
    # bbox extraction: collect all rectangles on GDS layer 100 (ALIGN Bbox layer)
    bbox_coords = []      # list of (x0, y0, x1, y1) in db units
    in_boundary = False

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
            current_datatype = None
        elif record_type == 0x0E and len(payload) >= 2:
            current_datatype = struct.unpack_from('>H', payload)[0]
        elif record_type == 0x08:  # BOUNDARY start
            in_boundary = True
        elif record_type == 0x09:  # PATH start
            in_path = True
        elif record_type == 0x10:  # XY data
            coords = struct.unpack_from('>' + 'i' * (len(payload) // 4), payload)
            if in_path and _in_wire():
                pts = [(coords[j], coords[j+1]) for j in range(0, len(coords)-1, 2)]
                for j in range(len(pts) - 1):
                    dx = abs(pts[j+1][0] - pts[j][0])
                    dy = abs(pts[j+1][1] - pts[j][1])
                    total_wire_length += (dx + dy) * db_unit * 1e6
            elif in_boundary and current_layer == 100:  # Bbox layer → cell outline
                xs = coords[0::2]
                ys = coords[1::2]
                if xs and ys:
                    bbox_coords.append((min(xs), min(ys), max(xs), max(ys)))
        elif record_type == 0x11:  # ENDEL
            if in_boundary and _in_via():
                via_count += 1
            in_path = False
            in_boundary = False

        i += length

    # Derive cell dimensions from the largest Bbox boundary found
    w_um = h_um = area_um2 = None
    if bbox_coords:
        # Use the bbox with the largest area (top-level cell outline)
        largest = max(bbox_coords, key=lambda b: (b[2]-b[0]) * (b[3]-b[1]))
        x0, y0, x1, y1 = largest
        w_um  = round((x1 - x0) * db_unit * 1e6, 4)
        h_um  = round((y1 - y0) * db_unit * 1e6, 4)
        area_um2 = round(w_um * h_um, 4)

    return {
        'area_um2':      area_um2,
        'cell_width_um': w_um,
        'cell_height_um': h_um,
        'wirelength_um': round(total_wire_length, 2),
        'via_count':     via_count,
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

    gds_files = list(work_dir.rglob('*.gds'))
    if not gds_files:
        print(f'ERROR: no GDS file found in {work_dir}', file=sys.stderr)
        sys.exit(1)

    gds_metrics = {
        'area_um2': None, 'cell_width_um': None,
        'cell_height_um': None, 'wirelength_um': None, 'via_count': None,
    }
    try:
        gds_metrics = parse_gds_metrics(str(gds_files[0]), layer_spec)
    except Exception as e:
        print(f'WARNING: GDS parse failed: {e}', file=sys.stderr)

    metrics = {
        'circuit':        circuit,
        'version':        version,
        'pdk':            args.pdk,
        'area_um2':       gds_metrics['area_um2'],
        'cell_width_um':  gds_metrics['cell_width_um'],
        'cell_height_um': gds_metrics['cell_height_um'],
        'wirelength_um':  gds_metrics['wirelength_um'],
        'via_count':      gds_metrics['via_count'],
        'runtime_s':      round(runtime_ms / 1000, 2),
    }

    out_path = work_dir / 'layout_metrics.json'
    out_path.write_text(json.dumps(metrics, indent=2))
    print(json.dumps(metrics, indent=2))

if __name__ == '__main__':
    main()
