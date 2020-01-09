
import pytest
import align
import os
import pathlib

examples = [('examples', 'buffer'),
            ('examples', 'adder'),
            ('examples', 'telescopic_ota'),
            ('examples', 'high_speed_comparator'),
            ('examples', 'inverter_v1'),
            ('examples', 'inverter_v2'),
            ('examples', 'inverter_v3'),
            ('examples', 'single_to_differential_converter'), 
            ('examples', 'telescopic_ota_with_bias'),
            ('examples', 'current_mirror_ota'),
            ('examples', 'five_transistor_ota'),
            ('examples', 'cascode_current_mirror_ota'),
            ('examples', 'switched_capacitor_filter'),
            ('examples', 'sc_dc_dc_converter')
            ]

examples = []
for p in pathlib.Path( 'examples').iterdir():
    if p.is_dir():
        if p.parts[-1] == 'modified_USC_UW_UT_testcases': continue
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

    args = [str(design_dir), '-f', str(design_dir / f"{nm}.sp"), '-s', nm, '-p', str(home / "pdks" / "FinFET14nm_Mock_PDK"), '-flat',  str(0), '--check']

    results = align.CmdlineParser().parse_args(args)

    for result in results:
        sp_file, variants = result
        for (k,v) in variants.items():
            print(k,v)
            assert 'errors' in v
            assert v['errors'] == 0

