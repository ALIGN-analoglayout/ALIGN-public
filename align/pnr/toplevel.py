import logging

from .placer import placer_driver
from .router import router_driver
from .cap_placer import cap_placer_driver

logger = logging.getLogger(__name__)

def toplevel(args, *, PDN_mode=False, adr_mode=False, results_dir=None, router_mode='top_down',
             gui=False, skipGDS=False,
             lambda_coeff=1.0, scale_factor=2,
             reference_placement_verilog_json=None,
             concrete_top_name=None,
             nroutings=1, select_in_ILP=False,
             seed=0, use_analytical_placer=False, ilp_solver='symphony', primitives=None):

    fpath, cap_map, cap_lef_s = cap_placer_driver(gui=gui, lambda_coeff=lambda_coeff, scale_factor=scale_factor,
                                                  reference_placement_verilog_json=reference_placement_verilog_json, concrete_top_name=concrete_top_name,
                                                  select_in_ILP=select_in_ILP, seed=seed,
                                                  use_analytical_placer=use_analytical_placer, ilp_solver=ilp_solver, primitives=primitives, nroutings=nroutings,
                                                  toplevel_args=args, results_dir=results_dir)

    verilog_ds_to_run, new_fpath, opath, numLayout, effort = \
        placer_driver(fpath=fpath, cap_map=cap_map, cap_lef_s=cap_lef_s,
                      gui=gui, lambda_coeff=lambda_coeff, scale_factor=scale_factor,
                      reference_placement_verilog_json=reference_placement_verilog_json, concrete_top_name=concrete_top_name, select_in_ILP=select_in_ILP, seed=seed,
                      use_analytical_placer=use_analytical_placer, ilp_solver=ilp_solver, primitives=primitives, nroutings=nroutings,
                      toplevel_args=args, results_dir=results_dir)
    assert fpath == new_fpath

    res_dict = router_driver(opath=opath, fpath=fpath, cap_map=cap_map, cap_lef_s=cap_lef_s,
                             numLayout=numLayout, effort=effort, adr_mode=adr_mode, PDN_mode=PDN_mode,
                             router_mode=router_mode, skipGDS=skipGDS, scale_factor=scale_factor,
                             nroutings=nroutings, primitives=primitives, toplevel_args=args, results_dir=results_dir,
                             verilog_ds_to_run=verilog_ds_to_run)


    return res_dict
