import pytest
import align
import os
import pathlib

examples = ['inverter_v1',
            'buffer',
            'five_transistor_ota',
            'adder']

ALIGN_HOME = pathlib.Path(__file__).resolve().parent.parent

if 'ALIGN_HOME' in os.environ:
    assert pathlib.Path(os.environ['ALIGN_HOME']).resolve() == ALIGN_HOME
else:
    os.environ['ALIGN_HOME'] = str(ALIGN_HOME)

if 'LD_LIBRARY_PATH' not in os.environ:
    os.environ['LD_LIBRARY_PATH'] = '/usr/local/lib/lpsolve/lp_solve_5.5.2.5_dev_ux64'

@pytest.mark.parametrize( "design", examples)
def test_cmdline(design):
    run_dir = ALIGN_HOME / 'tests' / 'tmp'
    run_dir.mkdir(parents=True, exist_ok=True)
    os.chdir(run_dir)

    design_dir = ALIGN_HOME / 'examples' / design
    pdk_dir = ALIGN_HOME / 'pdks' / 'FinFET14nm_Mock_PDK'
    args = [str(design_dir), '-f', str(design_dir / f"{design}.sp"), '-s', design, '-p', str(pdk_dir), '-flat',  str(0), '--check']

    results = align.CmdlineParser().parse_args(args)

    for result in results:
        _, variants = result
        for (k,v) in variants.items():
            print(k,v)
            assert 'errors' in v
            assert v['errors'] == 0
