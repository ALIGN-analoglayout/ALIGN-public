import pytest
import align
import os
import pathlib
import filecmp
import logging

run_flat = ['linear_equalizer',
            'adder',
            'variable_gain_amplifier',
            'single_to_differential_converter']

skip_pdks = ['Bulk65nm_Mock_PDK']
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
pdks= [pdk for pdk in (ALIGN_HOME / 'pdks').iterdir() \
           if pdk.is_dir() and pdk.name not in skip_pdks]

@pytest.mark.regression
@pytest.mark.parametrize( "design_dir", examples, ids=lambda x: x.name)
@pytest.mark.parametrize( "pdk_dir", pdks, ids=lambda x: x.name)
def test_A( pdk_dir, design_dir):
    logging.getLogger().setLevel(logging.getLevelName("CRITICAL"))

    nm = design_dir.name
    run_dir = pathlib.Path( os.environ['ALIGN_WORK_DIR']).resolve() / pdk_dir.name / nm
    run_dir.mkdir(parents=True, exist_ok=True)
    os.chdir(run_dir)

    args = [str(design_dir), '-f', str(design_dir / f"{nm}.sp"), '-s', nm, '-p', str(pdk_dir), '-flat',  str(1 if nm in run_flat else 0), '--generate', '--regression']
    results = align.CmdlineParser().parse_args(args)
    assert results is not None, f"{nm} :No results generated"

    gold_dir =  pathlib.Path( os.environ['ALIGN_HOME']).resolve() / "tests" / "gold" / "FinFET14nm_Mock_PDK" / nm / "regression"
    result_dir = run_dir / "regression"

    for suffix in ['v','const','lef']:
        for p in gold_dir.rglob(f'*.{suffix}'):
            assert filecmp.cmp( result_dir / p.name, gold_dir / p.name, False)
