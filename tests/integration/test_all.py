import pytest
import align
import os
import pathlib

pdks= []
for pdk in (pathlib.Path(__file__).parent.parent.parent / 'pdks').iterdir():
    if pdk.is_dir() and (pdk / 'layers.json').exists():
        pdks.append(pdk)

run_flat=['linear_equalizer']

examples = []
for p in (pathlib.Path(__file__).parent.parent.parent / 'examples').iterdir():
    if p.is_dir():
        if p.parts[-1] == 'modified_USC_UW_UT_testcases': continue
        print(p)
        examples.append( p)

for p in (pathlib.Path(__file__).parent.parent.parent / 'examples' / 'modified_USC_UW_UT_testcases').iterdir():
    if p.is_dir():
        print(p)
        examples.append( p)

@pytest.mark.nightly
@pytest.mark.parametrize( "design_dir", examples, ids=lambda x: x.name)
@pytest.mark.parametrize( "pdk_dir", pdks, ids=lambda x: x.name)
def test_A( pdk_dir, design_dir):
    nm = design_dir.name
    run_dir = pathlib.Path( os.environ['ALIGN_WORK_DIR']).resolve() / nm

    run_dir.mkdir( exist_ok=True)
    os.chdir(run_dir)

    args = [str(design_dir), '-f', str(design_dir / f"{nm}.sp"), '-s', nm, '-p', str(pdk_dir), '-flat',  str(1 if nm in run_flat else 0),'--check']

    results = align.CmdlineParser().parse_args(args)

    for result in results:
        sp_file, variants = result
        for (k,v) in variants.items():
            print(k,v)
            assert 'errors' in v
            assert v['errors'] == 0

