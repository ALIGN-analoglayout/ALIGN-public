from ..schema import constraint, types
from ..cell_fabric import transformation


def check_placement(placement_verilog_d, scale_factor):
    leaf_bboxes = {x['concrete_name']: x['bbox'] for x in placement_verilog_d['leaves']}

    internal_bboxes = {x['concrete_name']: x['bbox'] for x in placement_verilog_d['modules']}

    non_leaves = {module['concrete_name'] for module in placement_verilog_d['modules']}

    for module in placement_verilog_d['modules']:
        if len(module['constraints']) == 0:
            continue  # No constraints
        constraints = module['constraints']

        # The check below is at the mercy of constraint translation
        do_not_identify = []
        for const in constraints:
            if isinstance(const, constraint.DoNotIdentify):
                do_not_identify.extend(const.instances)
        do_not_identify = list(set(do_not_identify))
        all_inst = [inst['instance_name'] for inst in module['instances']]
        for inst in do_not_identify:
            assert inst in all_inst, f'Instance not found {inst}'

        # Set module (i.e. subcircuit) bounding box parameters
        bbox = transformation.Rect(*module['bbox'])
        with types.set_context(constraints):
            constraints.append(
                constraint.SetBoundingBox(
                    instance=module['concrete_name'],
                    llx=bbox.llx/scale_factor,
                    lly=bbox.lly/scale_factor,
                    urx=bbox.urx/scale_factor,
                    ury=bbox.ury/scale_factor,
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
                        llx=bbox.llx/scale_factor,
                        lly=bbox.lly/scale_factor,
                        urx=bbox.urx/scale_factor,
                        ury=bbox.ury/scale_factor,
                        sx=1,  # TODO: change back to sX
                        sy=1  # TODO: change back to sY
                    )
                )
