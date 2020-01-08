
import pytest
import align
import os
import pathlib

examples = ['buffer',
            'adder',
            'telescopic_ota',
            'high_speed_comparator',
            'inverter_v1',
            'inverter_v2',
            'inverter_v3',
            'single_to_differential_converter', 
            'telescopic_ota_with_bias',
            'current_mirror_ota',
            'five_transistor_ota',
            'cascode_current_mirror_ota',
            'switched_capacitor_filter',
            'sc_dc_dc_converter']

@pytest.mark.nightly
@pytest.mark.parametrize( "nm", examples)
def test_A( nm):
    home = pathlib.Path( os.environ['ALIGN_HOME'])
    design_dir = home / "examples" / nm
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

