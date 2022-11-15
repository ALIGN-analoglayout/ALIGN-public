import logging
from ..schema import constraint, types
from ..cell_fabric import transformation
import json
import pathlib
logger = logging.getLogger(__name__)


def check_placement(placement_verilog_d, scale_factor):
    leaf_bboxes = {x['concrete_name']: x['bbox'] for x in placement_verilog_d['leaves']}

    internal_bboxes = {x['concrete_name']: x['bbox'] for x in placement_verilog_d['modules']}

    non_leaves = {module['concrete_name'] for module in placement_verilog_d['modules']}

    for module in placement_verilog_d['modules']:
        constraints = module['constraints']
        constraints.checkpoint()

        # logger.info(f'{constraints}')

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
                constraint.AssignBboxVariables(
                    bbox_name='subcircuit',
                    llx=bbox.llx/scale_factor,
                    lly=bbox.lly/scale_factor,
                    urx=bbox.urx/scale_factor,
                    ury=bbox.ury/scale_factor
                )
            )

        # logger.info(f"{bbox=}")

        for inst in module['instances']:
            t = inst['transformation']
            ctn = inst['concrete_template_name']
            if ctn in non_leaves:
                r = internal_bboxes[ctn]
            else:
                r = leaf_bboxes[ctn]

            bbox = transformation.Transformation(**t).hitRect(transformation.Rect(*r)).canonical()

            # logger.info(f"{inst['instance_name']}: {bbox=}")

            with types.set_context(constraints):
                constraints.append(
                    constraint.AssignBboxVariables(
                        bbox_name=inst['instance_name'],
                        llx=bbox.llx/scale_factor,
                        lly=bbox.lly/scale_factor,
                        urx=bbox.urx/scale_factor,
                        ury=bbox.ury/scale_factor
                    )
                )

        # # TODO: Check SameTemplate In a future PR. Below fails when abstract_template_name's differ
        # # Validate SameTemplate: Instances of the same template should match in concrete_template_name
        # instance_to_concrete = {inst["instance_name"]: inst["concrete_template_name"] for inst in module["instances"]}
        # for const in constraints:
        #     if isinstance(const, constraint.SameTemplate):
        #         for i0, i1 in more_itertools.pairwise(const.instances):
        #             assert instance_to_concrete[i0] == instance_to_concrete[i1],\
        #                 f"Templates do not match for {i0} and {i1} {instance_to_concrete[i0]} vs {instance_to_concrete[i1]}"

        constraints.revert()


def _transform_leaf(instance, leaf):
    name_new = instance['instance_name']
    if 'transformation' in leaf:
        tr_leaf = transformation.Transformation(**leaf['transformation'])
        assert 'name' in leaf
        name_new += '/' + leaf['name']
    else:
        tr_leaf = transformation.Transformation()
    tr_inst = transformation.Transformation(**instance['transformation'])
    tr_new = transformation.Transformation.mult(tr_inst, tr_leaf)

    return {'concrete_name': leaf['concrete_name'], 'name': name_new, 'transformation': tr_new.toDict()}


def _flatten_leaves(placement, concrete_name):
    """ transform leaf coordinates to top level """
    flat_leaves = []
    for instance in placement['modules'][concrete_name]['instances']:
        leaf = placement['leaves'].get(instance['concrete_template_name'], None)
        if leaf is not None:
            flat_leaves.append(_transform_leaf(instance, leaf))
        else:
            for leaf in _flatten_leaves(placement, instance['concrete_template_name']):
                flat_leaves.append(_transform_leaf(instance, leaf))
    return flat_leaves


def _check_place_on_grid(flat_leaf, constraints):
    for const in constraints:
        if const['direction'] == 'H':
            o, s = flat_leaf['transformation']['oY'], flat_leaf['transformation']['sY']
        else:
            o, s = flat_leaf['transformation']['oX'], flat_leaf['transformation']['sX']

        is_satisfied = False
        for term in const['ored_terms']:
            for offset in term['offsets']:
                if (o - offset) % const['pitch'] == 0 and s in term['scalings']:
                    is_satisfied = True
                    logger.debug(f'{flat_leaf["name"]}@{flat_leaf["concrete_name"]} satisfied {term} in {const}')
                    break
            if is_satisfied:
                break
        assert is_satisfied, f'{flat_leaf} does not satisfy {const}'


def check_place_on_grid(placement_verilog_d, concrete_name, opath):
    placement = {
        'leaves': {x['concrete_name']: x for x in placement_verilog_d['leaves']},
        'modules': {x['concrete_name']: x for x in placement_verilog_d['modules']}
    }

    flat_leaves = _flatten_leaves(placement, concrete_name)

    constrained_cns = dict()
    all_cns = {x['concrete_name'] for x in flat_leaves}
    for cn in all_cns:
        filename = pathlib.Path(opath) / '../inputs' / f'{cn}.json'
        if filename.exists() and filename.is_file():
            with filename.open("r") as fp:
                data = json.load(fp)
                if 'metadata' in data and 'constraints' in data['metadata']:
                    place_on_grids = [c for c in data['metadata']['constraints'] if c['constraint'] == 'PlaceOnGrid']
                    if place_on_grids:
                        constrained_cns[cn] = place_on_grids

    for flat_leaf in flat_leaves:
        if flat_leaf['concrete_name'] in constrained_cns:
            _check_place_on_grid(flat_leaf, constrained_cns[flat_leaf['concrete_name']])
