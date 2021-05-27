from ..schema import constraint, types
from ..cell_fabric import transformation

def check_placement(placement_verilog_d, scale_factor):
    leaf_bboxes = { x['concrete_name'] : x['bbox'] for x in placement_verilog_d['leaves']}

    internal_bboxes = { x['concrete_name'] : x['bbox'] for x in placement_verilog_d['modules']}

    non_leaves = { module['concrete_name'] for module in placement_verilog_d['modules']}

    for module in placement_verilog_d['modules']:
        if len(module['constraints']) == 0:
            continue  # No constraints
        constraints = module['constraints']
        # Set module (i.e. subcircuit) bounding box parameters
        bbox = transformation.Rect(*module['bbox'])
        with types.set_context(constraints):
            constraints.append(
                constraint.SetBoundingBox(
                    instance=module['abstract_name'],
                    llx=bbox.llx//scale_factor,
                    lly=bbox.lly//scale_factor,
                    urx=bbox.urx//scale_factor,
                    ury=bbox.ury//scale_factor,
                    is_subcircuit=True
                )
            )
        for inst in module['instances']:
            t = inst['transformation']
            ctn = inst['concrete_template_name']
            if ctn in non_leaves:
                r = internal_bboxes[ctn]
            else:
                r = leaf_bboxes[ctn]

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
