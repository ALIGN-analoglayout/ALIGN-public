from align.cell_fabric import transformation
from align.schema.transistor import Transistor


def mos(canvas_gen, tx: Transistor, track_pattern=None):

    assert tx.nf % 2 == 0, f'Odd number of fingers are not allowed'

    c = canvas_gen()

    if tx.device_type == 'stack':
        c.addWire(c.m1, 'S', 'S', 1,       (1, -1), (4, 1))
        c.addWire(c.m1, 'D', 'D', 1+tx.nf, (1, -1), (4, 1))
    else:
        for x in range(1, 2+tx.nf):
            p = 'D' if x % 2 == 0 else 'S'
            c.addWire(c.m1, p, p, x, (1, -1), (4, 1))

    for x in range(2, 1+tx.nf, 2):
        c.addWire(c.m1,  'G', 'G',  x, (5, -1), (6, 1))

    if track_pattern is not None:

        if 'G' in track_pattern:
            for y in track_pattern['G']:
                if tx.nf > 2:
                    g_b_idx = (2, -1)
                    g_e_idx = (tx.nf, 1)
                else:
                    g_b_idx = (1, -1)
                    g_e_idx = (1+tx.nf, 1)
                c.addWire(c.m2, 'G', 'G',  y, g_b_idx, g_e_idx)

        if tx.device_type == 'stack':
            s_b_idx = (1, -1)
            s_e_idx = (2,  1)
            d_b_idx = (tx.nf, -1)
            d_e_idx = (1+tx.nf,  1)
        else:
            s_b_idx = (1, -1)
            s_e_idx = (1+tx.nf,  1)
            d_b_idx = (1, -1)
            d_e_idx = (1+tx.nf,  1)

        if 'S' in track_pattern:
            for y in track_pattern['S']:
                c.addWire(c.m2, 'S', 'S',  y, s_b_idx, s_e_idx)

        if 'D' in track_pattern:
            for y in track_pattern['D']:
                c.addWire(c.m2, 'D', 'D',  y, d_b_idx, d_e_idx)

        c.drop_via(c.v1)

    # Precomputed bounding box
    x1 = c.m1.clg.value(2+tx.nf)
    y1 = c.m2.clg.value(7)
    r = [0, 0, x1[0], y1[0]]
    c.bbox = transformation.Rect(*r)

    return {"bbox": c.bbox.toList(), "instance": {}, "terminals": c.terminals}


def tap(canvas_gen, tx: Transistor):

    assert tx.nf % 2 == 0, f'Odd number of fingers are not allowed'

    c = canvas_gen()

    c.addWire(c.m1, 'B', 'B', 1,          (2, -1), (5, 1))
    c.addWire(c.m1, 'B', 'B', 1+tx.nf, (2, -1), (5, 1))
    c.addWire(c.m2, 'B', 'B', 2, (1, -1), (1+tx.nf, 1))
    c.addWire(c.m2, 'B', 'B', 5, (1, -1), (1+tx.nf, 1))

    c.drop_via(c.v1)

    # Precomputed bounding box
    x1 = c.m1.clg.value(2+tx.nf)
    y1 = c.m2.clg.value(7)
    r = [0, 0, x1[0], y1[0]]
    c.bbox = transformation.Rect(*r)

    return {"bbox": c.bbox.toList(), "instance": {}, "terminals": c.terminals}
