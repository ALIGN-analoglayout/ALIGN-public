import pytest
import align
import os
import pathlib

run_flat = ['linear_equalizer', 'adder', 'variable_gain_amplifier', 'single_to_differential_converter']
skip_dirs = []
skip_pdks = []

ALIGN_HOME = pathlib.Path(__file__).parent.parent.parent

examples_dir =  ALIGN_HOME / 'examples'
examples =  [p.parents[0] for p in examples_dir.rglob('*.sp') \
                if all(x not in skip_dirs for x in p.relative_to(examples_dir).parts)]

pdks= [pdk for pdk in (ALIGN_HOME / 'pdks').iterdir() \
           if pdk.is_dir() and pdk.name not in skip_pdks]

@pytest.mark.nightly
@pytest.mark.parametrize( "design_dir", examples, ids=lambda x: x.name)
@pytest.mark.parametrize( "pdk_dir", pdks, ids=lambda x: x.name)
def test_A( pdk_dir, design_dir):
    nm = design_dir.name
    run_dir = pathlib.Path( os.environ['ALIGN_WORK_DIR']).resolve() / pdk_dir.name / nm
    run_dir.mkdir(parents=True, exist_ok=True)
    os.chdir(run_dir)

    args = [str(design_dir), '-f', str(design_dir / f"{nm}.sp"), '-s', nm, '-p', str(pdk_dir), '-flat',  str(1 if nm in run_flat else 0), '--check', '--generate']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None, f"{nm} :No results generated"
    for result in results:
        _, variants = result
        for (k,v) in variants.items():
            assert 'errors' in v, f"No Layouts were generated for {nm} ({k})"
            assert v['errors'] == 0, f"{nm} ({k}):Number of DRC errorrs: {str(v['errors'])}"

