
import pytest
import align
import os
import pathlib

@pytest.mark.nightly
@pytest.mark.parametrize( "nm", ['telescopic_ota', 'cascode_current_mirror_ota', 'current_mirror_ota',  'five_transistor_ota', 'switched_capacitor_filter'])
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

