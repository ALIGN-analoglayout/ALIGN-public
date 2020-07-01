import pytest
import pathlib
import align.pnr.main
import logging
import os

logger = logging.getLogger(__name__)

@pytest.mark.skipif('ALIGN_WORK_DIR' not in os.environ,
                    reason='Necessary test collateral has not been built')
def test_a():
    logging.getLogger().setLevel("DEBUG")

    ALIGN_HOME = os.environ['ALIGN_HOME']
    ALIGN_WORK_DIR = os.environ['ALIGN_WORK_DIR']

    dbfile = ALIGN_WORK_DIR + "/FinFET14nm_Mock_PDK/adder/3_pnr/Results/adder_0.db.json"
    variant = "adder_0"
    primitive_dir = ALIGN_WORK_DIR + "/FinFET14nm_Mock_PDK/adder/2_primitives"
    pdk_dir = pathlib.Path(ALIGN_HOME) / "pdks/FinFET14nm_Mock_PDK"
    output_dir = pathlib.Path(ALIGN_WORK_DIR) / "FinFET14nm_Mock_PDK/adder/3_pnr"
    check = True
    extract = False
    input_dir = pathlib.Path(ALIGN_WORK_DIR) / "FinFET14nm_Mock_PDK/adder/3_pnr"
    toplevel = True
    gds_json = True

    align.pnr.main._generate_json( dbfile=dbfile, variant=variant, primitive_dir=primitive_dir, pdk_dir=pdk_dir, output_dir=output_dir, check=check, extract=extract, input_dir=input_dir, toplevel=toplevel, gds_json=gds_json)
