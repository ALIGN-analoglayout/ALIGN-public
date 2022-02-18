import sys
import pathlib
import logging
import importlib.util
from copy import deepcopy
from math import sqrt, floor

from align import primitive

logger = logging.getLogger(__name__)


def get_generator(name, pdkdir):
    if pdkdir is None:
        return False
    pdk_dir_path = pdkdir
    if isinstance(pdkdir, str):
        pdk_dir_path = pathlib.Path(pdkdir)
    pdk_dir_stem = pdk_dir_path.stem

    try:  # is pdk an installed module
        module = importlib.import_module(pdk_dir_stem)
    except ImportError:
        init_file = pdk_dir_path / '__init__.py'
        if init_file.is_file():  # is pdk a package
            spec = importlib.util.spec_from_file_location(pdk_dir_stem, pdk_dir_path / '__init__.py')
            module = importlib.util.module_from_spec(spec)
            sys.modules[pdk_dir_stem] = module
            spec.loader.exec_module(module)
        else:  # is pdk old school (backward compatibility)
            print(f"check {pdkdir/'primitive.py'}")
            spec = importlib.util.spec_from_file_location("primitive", pdkdir / 'primitive.py')
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
    return getattr(module, name, False) or getattr(module, name.lower(), False)

def generate_generic(pdkdir, parameters, netlistdir=None):
    primitive1 = get_generator(parameters["real_inst_type"], pdkdir)
    uc = primitive1()
    uc.generate(
        ports=parameters["ports"],
        netlist_parameters=parameters["values"],
        netlistdir=netlistdir
    )
    return uc, parameters["ports"]


def gen_param(subckt, primitives, pdk_dir):
    block_name = subckt.name
    vt = subckt.elements[0].model
    values = subckt.elements[0].parameters
    generator_name = subckt.elements[0].generator
    logger.info(f"generating primitive structure {subckt}")
    if generator_name == 'generic':
        #generic/tfr_prim
        attr = {'ports': list(subckt.pins),
                'values': values if values else None,
                'real_inst_type': subckt.elements[0].model.lower()
                }
        block_args = {"parameters": deepcopy(attr), "primitive": 'generic'}
        logger.debug(f"creating generic primitive {block_name} {block_args}")
        primitives[block_name] = block_args
    elif get_generator(block_name.lower(), pdk_dir):
        #DIG22INV  primitive
        attr = {'ports': list(subckt.pins),
                'values': values if values else None,
                'real_inst_type': block_name.lower()
                }
        block_args = {"parameters": deepcopy(attr), "primitive": 'generic'}
        logger.debug(f"creating generic primitive {block_name} {block_args}")
        primitives[block_name] = block_args
    elif get_generator(generator_name.lower(), pdk_dir):
        #TFR primitive
        attr = {'ports': list(subckt.pins),
                'values': values if values else None,
                'real_inst_type': subckt.elements[0].model.lower()
                }
        block_args = {"parameters": deepcopy(attr), "primitive": 'generic'}
        logger.debug(f"creating generic primitive {block_name} {block_args}")
        primitives[block_name] = block_args
    else:
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
        primitives[block_name] = block_args
    return True
