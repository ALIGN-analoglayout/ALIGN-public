import textwrap
import json
import shutil
from align.pnr.hpwl import gen_netlist, calculate_HPWL_from_placement_verilog_d
from align.pnr.render_placement import standalone_overlap_checker


try:
    from .utils import get_test_id, build_example, run_example
    from . import circuits
except BaseException:
    from utils import get_test_id, build_example, run_example
    import circuits

cleanup = False


def test_place_cmp_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        DONT_CONST = {name}
        """)
    constraints = [
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"},
        {"constraint": "GroupBlocks", "instances": ["mn11", "mp13"], "name": "invp"},
        {"constraint": "GroupBlocks", "instances": ["mn12", "mp14"], "name": "invn"},
        {"constraint": "SameTemplate", "instances": ["mp7", "mp8"]},
        {"constraint": "SameTemplate", "instances": ["mp9", "mp10"]},
        {"constraint": "SameTemplate", "instances": ["invn", "invp"]},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["mn0"], ["dp"]]},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["ccp"], ["ccn"], ["invn", "invp"], ["mp9", "mp10"], ["mp7", "mp8"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["mn0", "dp"]},
        {"constraint": "AlignInOrder", "line": "bottom", "instances": ["dp", "ccn"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 1, "ratio_high": 2}
    ]
    example = build_example(name, netlist, setup, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=cleanup, area=4e10)

    cn = f'{name.upper()}_0'

    with (run_dir / '3_pnr' / 'Results' / f'{cn}.placement_verilog.json').open('rt') as fp:
        placement = json.load(fp)

        assert standalone_overlap_checker(placement, cn)
        nets = gen_netlist(placement, cn)
        hpwl_align = calculate_HPWL_from_placement_verilog_d(placement, cn, nets)
        print('HPWL_align=', hpwl_align)

    with (run_dir / '..' / f'_{cn}.placement_verilog.json').open('rt') as fp:
        placement = json.load(fp)

        assert standalone_overlap_checker(placement, cn)
        nets = gen_netlist(placement, cn)
        hpwl_human = calculate_HPWL_from_placement_verilog_d(placement, cn, nets)
        print('HPWL_human=', hpwl_human)

        assert hpwl_align <= hpwl_human, f'Suboptimal placement. hpwl_align={hpwl_align} vs hpwl_human={hpwl_human} ratio={hpwl_align/hpwl_human}'

    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)
