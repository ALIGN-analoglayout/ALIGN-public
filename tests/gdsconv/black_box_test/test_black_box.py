import pathlib
import align
import os
import shutil
import align
import pytest


from align.gdsconv.gds2primitive import GEN_PRIMITIVE_FROM_GDS

mydir  = pathlib.Path(__file__).resolve().parent
spdir  = mydir / "hsc_black_box_test"
gdsdir = spdir
ALIGN_HOME = pathlib.Path(__file__).resolve().parent.parent.parent.parent
if 'ALIGN_HOME' in os.environ:
    assert pathlib.Path(os.environ['ALIGN_HOME']).resolve() == ALIGN_HOME
pdkdir = ALIGN_HOME / "pdks" / "FinFET14nm_Mock_PDK"
ALIGN_WORK_DIR = ALIGN_HOME / 'tests' / 'tmp'
if 'ALIGN_WORK_DIR' in os.environ:
    ALIGN_WORK_DIR = pathlib.Path(os.environ['ALIGN_WORK_DIR']).resolve()

def test_black_box_dp_in_hsc ():
    nm = 'black_box_test'
    run_dir = ALIGN_WORK_DIR / f'{nm}'
    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)
    primdir = run_dir / '2_primitives'
    topodir = run_dir / '1_topology'
    os.chdir(run_dir)
    args = ['-f', spdir.as_posix() + '/high_speed_comparator.sp', '-p', pdkdir.as_posix(), '--flow_stop', '2_primitives', spdir.as_posix()]
    results = align.CmdlineParser().parse_args(args)
    assert results is not None
    genprim = GEN_PRIMITIVE_FROM_GDS(gdsdir.as_posix(), (pdkdir / 'layers.json').as_posix(), primdir.as_posix(), topodir.as_posix(), 1e9)
    args = ['-f', spdir.as_posix() + '/high_speed_comparator.sp', '-p', pdkdir.as_posix(), '--flow_start', '3_pnr', '--place_using_ILP', '--skipGDS', spdir.as_posix()]
    results = align.CmdlineParser().parse_args(args)
    assert results is not None

def test_black_box_dp_in_hsc_auto ():
    nm = 'black_box_test_auto'
    run_dir = ALIGN_WORK_DIR / f'{nm}'
    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)
    os.chdir(run_dir)
    args = ['-s', 'high_speed_comparator', '-f', spdir.as_posix() + '/high_speed_comparator_auto.sp', '-p', pdkdir.as_posix(), '--place_using_ILP', '-b', gdsdir.as_posix(), '--scale', '1e9', '--skipGDS', spdir.as_posix()]
    results = align.CmdlineParser().parse_args(args)
    assert results is not None
