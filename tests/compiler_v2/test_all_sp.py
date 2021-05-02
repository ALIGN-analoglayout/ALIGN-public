import pytest
from align.schema.parser import SpiceParser
import pathlib

ALIGN_HOME = pathlib.Path(__file__).parent.parent.parent

skip_dirs = ['tb_single_SAR','TI_SAR','Sanitized_TX_8l12b','Sanitized_DLPF_RCFilter','Sanitized_TempSensor',\
    'SW_Cres_v3_5','Sanitized_5b_ADC','Sanitized_CDAC_SW_Coarse','Santized_12b_ADC_TOP',\
    'single_to_differential_converter','vco_dtype_12_hierarchical', 'vco_dtype_12_hierarchical_res', \
    'vco_dtype_12_hierarchical_res_constrained', 'ldo_error_amp_v2']

examples_dir =  ALIGN_HOME / 'examples'
examples =  [p for p in examples_dir.rglob('*.sp') \
                if all(x not in skip_dirs for x in p.relative_to(examples_dir).parts)]

@pytest.fixture
def get_parser():
    parser = SpiceParser()
    model_statemenets = ALIGN_HOME/ 'align' / 'config' / 'model.txt'
    with open(model_statemenets) as f:
        lines = f.read()
    parser.parse(lines)
    return parser

@pytest.mark.parametrize( "design", examples)
def test_all_examples(get_parser,design):
    print(design.name)
    with open(design) as f:
        lines = f.read()
    get_parser.parse(lines)

