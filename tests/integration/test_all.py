import pytest
import align
import os
import pathlib

ALIGN_HOME = pathlib.Path(__file__).parent.parent.parent

pdks= [pdk for pdk in (ALIGN_HOME / 'pdks').iterdir() \
           if pdk.is_dir() and (pdk / 'layers.json').exists() and 'Bulk' not in pdk.name]

run_flat=['linear_equalizer']

examples_dir =  ALIGN_HOME / 'examples'

examples = [p for p in examples_dir.iterdir() if p.is_dir() and p.name != 'modified_USC_UW_UT_testcases']
# examples += [p for p in (examples_dir / 'modified_USC_UW_UT_testcases').iterdir() if p.is_dir()]

@pytest.mark.nightly
@pytest.mark.parametrize( "design_dir", examples, ids=lambda x: x.name)
@pytest.mark.parametrize( "pdk_dir", pdks, ids=lambda x: x.name)
def test_A( pdk_dir, design_dir):
    nm = design_dir.name
    run_dir = pathlib.Path( os.environ['ALIGN_WORK_DIR']).resolve() / pdk_dir.name / nm
    run_dir.mkdir(parents=True, exist_ok=True)
    os.chdir(run_dir)

    args = [str(design_dir), '-f', str(design_dir / f"{nm}.sp"), '-s', nm, '-p', str(pdk_dir), '-flat',  str(1 if nm in run_flat else 0), '--check']
    results = align.CmdlineParser().parse_args(args)

    for result in results:
        sp_file, variants = result
        for (k,v) in variants.items():
            print(k,v)
            assert 'errors' in v
            assert v['errors'] == 0

