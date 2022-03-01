import logging
import pathlib
import re

from .. import PnR
from .build_pnr_model import gen_DB_verilog_d

logger = logging.getLogger(__name__)

def cap_placer_driver(*, toplevel_args, results_dir):

    logger.info(f'Running cap_placer_driver...')
    DB, verilog_d, fpath, opath, numLayout, effort = gen_DB_verilog_d(toplevel_args, results_dir)

    for idx in DB.TraverseHierTree():
        logger.info(f'Starting bottom-up cap placement on {DB.hierTree[idx].name} {idx}')
        current_node = DB.CheckoutHierNode(idx,-1)
        DB.AddingPowerPins(current_node)
        PRC = PnR.Placer_Router_Cap_Ifc(opath,fpath,current_node,DB.getDrc_info(),DB.checkoutSingleLEF(),1,6)


    # can we determine the capacitor names from the verilog_d
    required_caps = set()
    for module in verilog_d['modules']:
        tbl = { instance['instance_name'] : instance['abstract_template_name'] for instance in module['instances'] }
        for constraint in module['constraints']:
            if constraint.constraint == 'group_caps':
                required_caps.add(tbl[constraint.name.upper()])

    logger.info(f'Required capacitors: {required_caps}')


    odir = pathlib.Path(opath)

    p = re.compile(r'^(.*)_AspectRatio_(.*)$')

    cap_map = []
    cap_lef_s = ''

    for fn in odir.glob('*.lef'):
        if fn.is_file():
            if fn.suffixes == ['.lef']:
                ctn = fn.stem
                m = p.match(ctn)
                if m:
                    atn = m.groups()[0]
                    logger.info(f'Found lef file for CC capacitor {atn} {ctn}')
                    cap_map.append((atn,str(odir/f'{ctn}.gds')))
                    with (odir/f'{ctn}.lef').open("rt") as fp:
                        cap_lef_s += fp.read()

    generated_caps = {atn for atn, _ in cap_map}
    assert required_caps == generated_caps, "Required capacitors {required_caps} different from generated_caps {generated_caps}."


    return fpath, cap_map, cap_lef_s
