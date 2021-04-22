from ..schema import constraint
from ..cell_fabric import transformation


def check_placement(placement_verilog_d):
    for module in placement_verilog_d['modules']:
        if len(module['constraints']) == 0:
            continue  # No constraints
        constraints = constraint.ConstraintDB(module['constraints'])
        if sum(hasattr(x, 'check') for x in constraints) == 0:
            continue  # Nothing useful to check against
        for inst in module['instances']:
            t = inst['transformation']
            r = next((x['bbox'] for x in placement_verilog_d['modules'] if x['name'] == inst['template_name']),
                     next((x['bbox'] for x in placement_verilog_d['leaves'] if x['name'] == inst['template_name']), None))
            assert r is not None, f'Could not find {inst["template_name"]} in modules or leaves!'
            bbox = transformation.Transformation(**t).hitRect(transformation.Rect(*r)).canonical()
            constraints.append(
                constraint.SetBoundingBox(
                    instance=inst['instance_name'],
                    llx=bbox.llx,
                    lly=bbox.lly,
                    urx=bbox.urx,
                    ury=bbox.ury
                )
            )
