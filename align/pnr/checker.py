from ..schema import constraint, types
from ..cell_fabric import transformation

def check_placement(placement_verilog_d):
    leaf_bboxes = { x['name'] : x['bbox'] for x in placement_verilog_d['leaves']}
    internal_bboxes = { x['name'] : x['bbox'] for x in placement_verilog_d['modules']}

    for module in placement_verilog_d['modules']:
        if len(module['constraints']) == 0:
            continue  # No constraints
        constraints = module['constraints']
        # Set module (i.e. subcircuit) bounding box parameters
        bbox = transformation.Rect(*module['bbox'])
        with types.set_context(constraints):
            constraints.append(
                constraint.SetBoundingBox(
                    instance=module['name'],
                    llx=bbox.llx,
                    lly=bbox.lly,
                    urx=bbox.urx,
                    ury=bbox.ury,
                    is_subcircuit=True
                )
            )
        for inst in module['instances']:
            t = inst['transformation']

            if 'template_name' in inst:
                r = internal_bboxes[inst['template_name']]
            elif 'abstract_template_name' in inst:
                r = leaf_bboxes[inst['abstract_template_name']]
            else:
                assert False, f'Neither \'template_name\' or \'abstract_template_name\' in inst {inst}.'

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
