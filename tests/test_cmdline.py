import pytest
import align
import os
import pathlib
import shutil

examples = ['inverter_v1',
            'buffer',
            'five_transistor_ota',
            'adder']

ALIGN_HOME = pathlib.Path(__file__).resolve().parent.parent

if 'ALIGN_HOME' in os.environ:
    assert pathlib.Path(os.environ['ALIGN_HOME']).resolve() == ALIGN_HOME
else:
    os.environ['ALIGN_HOME'] = str(ALIGN_HOME)

if 'ALIGN_WORK_DIR' in os.environ:
    ALIGN_WORK_DIR = pathlib.Path( os.environ['ALIGN_WORK_DIR']).resolve() 
else:
    ALIGN_WORK_DIR = ALIGN_HOME / 'tests' / 'tmp'

@pytest.mark.parametrize( "design", examples)
def test_cmdline(design):
    run_dir = ALIGN_WORK_DIR / design

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)
    os.chdir(run_dir)

    design_dir = ALIGN_HOME / 'examples' / design
    pdk_dir = ALIGN_HOME / 'pdks' / 'FinFET14nm_Mock_PDK'
    args = [str(design_dir), '-f', str(design_dir / f"{design}.sp"), '-s', design, '-p', str(pdk_dir), '-flat',  str(0), '--check', '-v', 'INFO', '-l', 'INFO']

    results = align.CmdlineParser().parse_args(args)

    for result in results:
        _, variants = result
        for (k,v) in variants.items():
            print(k,v)
            assert 'errors' in v
            assert v['errors'] == 0
