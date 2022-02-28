import logging

from .. import PnR
from .build_pnr_model import gen_DB_verilog_d

logger = logging.getLogger(__name__)

def cap_placer_driver(*,
                  gui, lambda_coeff, scale_factor,
                  reference_placement_verilog_json, concrete_top_name, select_in_ILP, seed,
                  use_analytical_placer, ilp_solver, primitives, nroutings, toplevel_args, results_dir):

    logger.info(f'Running cap_placer_driver...')
                
    DB, verilog_d, fpath, opath, numLayout, effort = gen_DB_verilog_d(toplevel_args, results_dir)

    for idx in DB.TraverseHierTree():
        logger.info(f'Starting bottom-up cap placement on {DB.hierTree[idx].name} {idx}')
        current_node = DB.CheckoutHierNode(idx,-1)
        DB.AddingPowerPins(current_node)
        PRC = PnR.Placer_Router_Cap_Ifc(opath,fpath,current_node,DB.getDrc_info(),DB.checkoutSingleLEF(),1,6)

    return fpath, opath
