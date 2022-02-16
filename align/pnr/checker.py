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
            newconstraint = \
                constraint.AssignBboxVariables(
                    bbox_name='subcircuit',
                    llx=bbox.llx/scale_factor,
                    lly=bbox.lly/scale_factor,
                    urx=bbox.urx/scale_factor,
                    ury=bbox.ury/scale_factor
                )
            print(newconstraint)
            #constraints.append(newconstraint)

        for inst in module['instances']:
            t = inst['transformation']
            ctn = inst['concrete_template_name']
            if ctn in non_leaves:
                r = internal_bboxes[ctn]
            else:
                r = leaf_bboxes[ctn]

            bbox = transformation.Transformation(**t).hitRect(transformation.Rect(*r)).canonical()
            with types.set_context(constraints):
                newconstraint = \
                    constraint.AssignBboxVariables(
                        bbox_name=inst['instance_name'],
                        llx=bbox.llx/scale_factor,
                        lly=bbox.lly/scale_factor,
                        urx=bbox.urx/scale_factor,
                        ury=bbox.ury/scale_factor
                    )
                print(newconstraint)
                #constraints.append(newconstraint)



def _transform_leaf(module, instance, leaf):
    if 'transformation' in leaf:
        tr_leaf = transformation.Transformation(**leaf['transformation'])
    else:
        tr_leaf = transformation.Transformation(**{'oX': leaf['bbox'][0], 'oY': leaf['bbox'][1], 'sX': 1, 'sY': 1})
    tr_inst = transformation.Transformation(**instance['transformation'])
    if 'name' in leaf:
        name = leaf['name']
    else:
        name = leaf['concrete_name']
    flat_leaf = dict()
    flat_leaf['concrete_name'] = leaf['concrete_name']
    flat_leaf['name'] = instance['instance_name'] + '/' + name
    flat_leaf['transformation'] = transformation.Transformation.mult(tr_inst, tr_leaf).toDict()
    module['leaves'].append(flat_leaf)


def _flatten_leaves(placement, concrete_name):
    """ transform leaf coordinates to top level """
    module = placement['modules'][concrete_name]
    module['leaves'] = []
    for instance in module['instances']:
        leaf = placement['leaves'].get(instance['concrete_template_name'], False)
        if leaf:
            _transform_leaf(module, instance, leaf)
        else:
            leaves = _flatten_leaves(placement, instance['concrete_template_name'])
            for leaf in leaves:
                _transform_leaf(module, instance, leaf)
    return module['leaves']


def _check_place_on_grid(leaf, constraints):
    for const in constraints:
        if const['direction'] == 'H':
            o, s = leaf['transformation']['oY'], leaf['transformation']['sY']
        else:
            o, s = leaf['transformation']['oX'], leaf['transformation']['sX']

        is_satisfied = False
        for term in const['ored_terms']:
            for offset in term['offsets']:
                if (o - offset) % const['pitch'] == 0 and s in term['scalings']:
                    is_satisfied = True
                    logger.debug(f'{leaf["name"]} satisfied {term} in {const}')
                    break
            if is_satisfied:
                break
        assert is_satisfied, f'{leaf} does not satisfy {const}'


def check_place_on_grid(placement_verilog_d, concrete_name, opath):

    if False:
        # Load JSON file for easier debug
        filename = (pathlib.Path(opath) / f'{concrete_name}.scaled_placement_verilog.json')
        with (filename).open('rt') as fp:
            placement_dict = json.load(fp)
    else:
        placement_dict = placement_verilog_d

    placement = dict()
    placement['leaves'] = {x['concrete_name']: x for x in placement_dict['leaves']}
    placement['modules'] = {x['concrete_name']: x for x in placement_dict['modules']}
    leaves = _flatten_leaves(placement, concrete_name)

    constrained_cns = dict()
    all_cns = {x['concrete_name'] for x in leaves}
    for cn in all_cns:
        filename = pathlib.Path(opath) / '../inputs' / f'{cn}.json'
        if filename.exists() and filename.is_file():
            with filename.open("r") as fp:
                data = json.load(fp)
                if 'metadata' in data and 'constraints' in data['metadata']:
                    place_on_grids = [c for c in data['metadata']['constraints'] if c['constraint'] == 'place_on_grid']
                    if place_on_grids:
                        constrained_cns[cn] = place_on_grids

    if constrained_cns:
        for leaf in leaves:
            if leaf['concrete_name'] in constrained_cns:
                _check_place_on_grid(leaf, constrained_cns[leaf['concrete_name']])
