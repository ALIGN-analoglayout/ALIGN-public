
import pytest
import align
import os
import pathlib

run_flat=set(['linear_equalizer'])
skip_dirs = set(['modified_USC_UW_UT_testcases','.hypothesis'])

examples = []
for p in pathlib.Path( 'examples').iterdir():
    if p.is_dir():
        if p.parts[-1] in skip_dirs: continue
        print(p)
        examples.append( ('/'.join(p.parts[:-1]), p.parts[-1]))

for p in (pathlib.Path( 'examples') / 'modified_USC_UW_UT_testcases').iterdir():
    if p.is_dir():
        print(p)
        examples.append( ('/'.join(p.parts[:-1]), p.parts[-1]))

@pytest.mark.nightly
@pytest.mark.parametrize( "d,nm", examples)
def test_A( d, nm):
    home = pathlib.Path( os.environ['ALIGN_HOME'])
    design_dir = home / d / nm
    run_dir = pathlib.Path( os.environ['ALIGN_WORK_DIR']) / nm

    run_dir.mkdir( exist_ok=True)
    os.chdir(run_dir)

    flat = 1 if nm in run_flat

    args = [str(design_dir), '-f', str(design_dir / f"{nm}.sp"), '-s', nm, '-p', str(home / "pdks" / "FinFET14nm_Mock_PDK"), '-flat',  str(flat),'--check']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None, f"No results generated."
    for result in results:
        sp_file, variants = result
        for (k,v) in variants.items():
            print(k,v)
            assert 'errors' in v
            assert v['errors'] == 0

