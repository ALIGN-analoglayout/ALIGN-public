import pytest
import align
import os
import pathlib
import shutil
import align.pdk.finfet

my_dir = pathlib.Path(__file__).resolve().parent

pdk_dir = pathlib.Path(align.pdk.finfet.__file__).parent

examples_dir = pdk_dir / 'examples'

skip_dirs = ['ring_oscillator']

examples = [p.parents[0] for p in examples_dir.rglob('*.sp') \
                if all(x not in skip_dirs for x in p.relative_to(examples_dir).parts)]

@pytest.mark.parametrize( "example", examples, ids=lambda x: x.name)
def test_examples(example):

    maxerrors = 0

    run_dir = my_dir / f'run_{example.name}'
    if run_dir.exists() and run_dir.is_dir():
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=True)
    os.chdir(run_dir)

    args = [str(example), '-p', str(pdk_dir), '-l','INFO']
   
    results = align.CmdlineParser().parse_args(args)

    assert results is not None, f"{example.name}: No results generated"
    for result in results:
        _, variants = result
        for (k,v) in variants.items():
            assert 'errors' in v, f"No Layouts were generated for {example.name} ({k})"
            assert v['errors'] <= maxerrors, f"{example.name} ({k}):Number of DRC errorrs: {str(v['errors'])}"
    
    shutil.rmtree(run_dir)
