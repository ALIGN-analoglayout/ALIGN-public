from ..schema import constraint, types
from ..cell_fabric import transformation

def check_placement(placement_verilog_d):
    for module in placement_verilog_d['modules']:
        if len(module['constraints']) == 0:
            continue  # No constraints
        constraints = module['constraints']
        for inst in module['instances']:
            t = inst['transformation']
            # Search for first match in 'modules' list
            r = next((x['bbox'] for x in placement_verilog_d['modules'] if x['name'] == inst['template_name']), None)
            # No match found in 'modules'. Search in 'leaves' instead
            if r is None:
                r = next((x['bbox'] for x in placement_verilog_d['leaves'] if x['name'] == inst['template_name']), None)
            # No match found in 'modules' or 'leaves'. Cannot proceed
            assert r is not None, f'Could not find {inst["template_name"]} in modules or leaves!'
            bbox = transformation.Transformation(**t).hitRect(transformation.Rect(*r)).canonical()
            with types.set_context(constraints):
                constraints.append(
                    constraint.SetBoundingBox(
                        instance=inst['instance_name'],
                        llx=bbox.llx,
                        lly=bbox.lly,
                        urx=bbox.urx,
                        ury=bbox.ury
                    )
                )
