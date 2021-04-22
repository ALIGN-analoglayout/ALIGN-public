from ..schema import constraint

def check_placement(placement_verilog_d):
    for module in placement_verilog_d['modules']:
        if len(module['constraints']) == 0:
            continue  # No constraints
        constraints = constraint.ConstraintDB(module['constraints'])
        if sum(hasattr(x, 'check') for x in constraints) == 0:
            continue  # Nothing useful to check against
        for inst in module['instances']:
            bbox = next((x['bbox'] for x in placement_verilog_d['modules'] if x['name'] == inst['template_name']), 
                        next((x['bbox'] for x in placement_verilog_d['leaves'] if x['name'] == inst['template_name']), None))
            assert bbox is not None and bbox[0] < bbox[2] and bbox[1] < bbox[3], f'Undefined bbox {bbox}'
            constraints.append(
                constraint.SetBoundingBox(
                    instance = inst['instance_name'],
                    llx = inst['transformation']['oX'] + bbox[0],
                    lly = inst['transformation']['oY'] + bbox[1],
                    urx = inst['transformation']['oX'] + bbox[0] + inst['transformation']['sX'] * (bbox[2] - bbox[0]),
                    ury = inst['transformation']['oY'] + bbox[1] + inst['transformation']['sY'] * (bbox[3] - bbox[1])
                )
            )
