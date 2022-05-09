import logging
from copy import deepcopy
from math import sqrt, floor, log10
from align.compiler.util import get_generator

logger = logging.getLogger(__name__)


def generate_generic(pdkdir, parameters, netlistdir=None):
    primitive1 = get_generator(parameters["real_inst_type"], pdkdir)
    uc = primitive1()
    uc.generate(
        ports=parameters["ports"],
        netlist_parameters=parameters["values"],
        netlistdir=netlistdir
    )
    return uc, parameters["ports"]


def limit_pairs(pairs):
    # Hack to limit aspect ratios when there are a lot of choices
    if len(pairs) > 12:
        new_pairs = []
        log10_aspect_ratios = [-0.3, 0, 0.3]
        for val in log10_aspect_ratios:
            best_pair = min((abs(log10(newy) - log10(newx) - val), (newx, newy))
                            for newx, newy in pairs)[1]
            new_pairs.append(best_pair)
        return new_pairs
    else:
        return pairs


def add_primitive(primitives, block_name, block_args):
    if block_name in primitives:
        block_args['abstract_template_name'] = block_name
        block_args['concrete_template_name'] = block_name
        if not primitives[block_name] == block_args:
            assert False, f"Distinct devices mapped to the same primitive {block_name}:\
                            existing: {primitives[block_name]} new: {block_args}"
    else:
        logger.debug(f"Found primitive {block_name} with {block_args}")
        if 'x_cells' in block_args and 'y_cells' in block_args:
            x, y = block_args['x_cells'], block_args['y_cells']
            pairs = set()
            m = x*y
            y_sqrt = floor(sqrt(x*y))
            for y in range(y_sqrt, 0, -1):
                if m % y == 0:
                    pairs.add((y, m//y))
                    pairs.add((m//y, y))
                if y == 1:
                    break
            pairs = limit_pairs((pairs))
            for newx, newy in pairs:
                concrete_name = f'{block_name}_X{newx}_Y{newy}'
                if concrete_name not in primitives:
                    primitives[concrete_name] = deepcopy(block_args)
                    primitives[concrete_name]['x_cells'] = newx
                    primitives[concrete_name]['y_cells'] = newy
                    primitives[concrete_name]['abstract_template_name'] = block_name
                    primitives[concrete_name]['concrete_template_name'] = concrete_name
        else:
            primitives[block_name] = block_args
            primitives[block_name]['abstract_template_name'] = block_name
            primitives[block_name]['concrete_template_name'] = block_name


def gen_param(subckt, primitives, pdk_dir):
    block_name = subckt.name
    generator_name = subckt.generator["name"]
    logger.debug(f"Checking if PDK offers a generator for: {block_name}")
    if get_generator(generator_name.lower(), pdk_dir):
        # ThinFilmResistor, StandardCell
        values = dict()
        if len(subckt.elements) > 0:
            values = subckt.elements[0].parameters
        attr = {'ports': list(subckt.pins),
                'values': values,
                'real_inst_type': block_name.lower()
                }
        block_args = {"parameters": deepcopy(attr), "primitive": 'generic'}
        logger.debug(f"Black-box primitive: {block_name} {block_args} {attr}")
        add_primitive(primitives, block_name, block_args)
    else:  # Transistor
        vt = subckt.elements[0].model
        values = deepcopy(subckt.elements[0].parameters)
        for e in subckt.elements:
            assert vt == e.model, f'Primitive with different models not supported {vt} vs {e.model}'
            assert values == e.parameters, f'Primitive with different parameters not supported {values} vs {e.parameters}'
        assert 'M' in values,  f'm: Number of instances not specified {values}'
        assert 'NF' in values, f'nf: Number of fingers not specified {values}'

        m = int(values['M'])
        nf = int(values['NF'])

        def x_by_y(m):
            y_sqrt = floor(sqrt(m))
            for y in range(y_sqrt, 0, -1):
                if y == 1:
                    return m, y
                elif m % y == 0:
                    return m//y, y

        x, y = x_by_y(m)

        values['real_inst_type'] = vt

        # TODO: Stacking parallel transistors is illegal. To be addressed in compiler
        st = int(values.get('STACK', '1'))
        pl = int(values.get('PARALLEL', '1'))
        if st > 1 and (nf > 1 or pl > 1):
            assert False, 'Stacking multi-leg transistors not supported. Turn off MergeSeriesDevices'
        elif pl > 1 and nf != pl:
            assert False, 'Number of legs do not match'

        exclude_keys = ['M', 'real_inst_type']
        if 'W' in values:
            exclude_keys.append('NFIN')
        if 'PARALLEL' in values:
            exclude_keys.append('PARALLEL')
        if st > 1:
            exclude_keys.append('NF')
        elif 'STACK' in values:
            exclude_keys.append('STACK')

        block_args = {
            'primitive': block_name,
            'x_cells': x,
            'y_cells': y,
            'parameters': values
        }
        add_primitive(primitives, block_name, block_args)
    return True
