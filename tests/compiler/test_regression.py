import pytest
import align
import os
import pathlib
from align.compiler import generate_hierarchy
import filecmp
import logging

run_flat = ['linear_equalizer',
            'adder',
            'variable_gain_amplifier',
            'single_to_differential_converter']

skip_dirs = set(['Sanitized_CDAC_SW_Coarse',
                 'Sanitized_model3x_MDLL_TOP',
                 'Santized_12b_ADC_TOP',
                 'CTDTDSM_V3',
                 'TI_SAR',
                 'Sanitized_TX_8l12b',
                 'Sanitized_DLPF_RCFilter', # 24sec
                 'Sanitized_TempSensor',    # 30sec
                 'Sanitized_5b_ADC',
                 'Sanitized_civiR_DLDO_TOP'
                ])

ALIGN_HOME = pathlib.Path(__file__).parent.parent.parent

examples_dir =  ALIGN_HOME / 'examples'
examples =  [p.parents[0] for p in examples_dir.rglob('*.sp') \
                if all(x not in skip_dirs for x in p.relative_to(examples_dir).parts)]

@pytest.mark.regression
@pytest.mark.parametrize( "design_dir", examples, ids=lambda x: x.name)
def test_A( design_dir):
    logging.getLogger().setLevel(logging.getLevelName("ERROR"))

    nm = design_dir.name
    run_dir = pathlib.Path( os.environ['ALIGN_WORK_DIR']).resolve() / nm
    run_dir.mkdir(parents=True, exist_ok=True)
    os.chdir(run_dir)

    gold_dir =  pathlib.Path( os.environ['ALIGN_HOME']).resolve() / "tests" / "compiler" / "gold" / nm / "1_topology"

    run_dir.mkdir(parents=True, exist_ok=True)

    netlist = design_dir / f"{nm}.sp"
    subckt = nm
    topology_dir = run_dir / "1_topology"
    flatten = 1 if nm in run_flat else 0
    unit_size_mos = 12
    unit_size_cap = 12

    primitives = generate_hierarchy( netlist, subckt, topology_dir, flatten, unit_size_mos, unit_size_cap)

    for suffix in ['v','const']:
        for p in gold_dir.rglob(f'*.{suffix}'):
            assert filecmp.cmp( topology_dir / p.name,
                                gold_dir / p.name,
                                False)
