from align.schema import model
import pytest
from align.schema.parser import SpiceParser
import pathlib
import os

ALIGN_HOME = pathlib.Path(__file__).resolve().parent.parent.parent

if 'ALIGN_HOME' in os.environ:
    assert pathlib.Path(os.environ['ALIGN_HOME']).resolve() == ALIGN_HOME
else:
    os.environ['ALIGN_HOME'] = str(ALIGN_HOME)

skip_dirs = ['tb_single_SAR','TI_SAR','Sanitized_TX_8l12b','Sanitized_DLPF_RCFilter','Sanitized_TempSensor',\
    'SW_Cres_v3_5','Sanitized_5b_ADC','Sanitized_CDAC_SW_Coarse','Santized_12b_ADC_TOP',\
    'single_to_differential_converter','vco_dtype_12_hierarchical', 'vco_dtype_12_hierarchical_res', \
    'vco_dtype_12_hierarchical_res_constrained', 'ldo_error_amp_v2','VCO_type2_65']

examples_dir =  ALIGN_HOME / 'examples'
assert examples_dir.is_dir()
examples =  [p for p in examples_dir.rglob('*.sp') \
                if all(x not in skip_dirs for x in p.relative_to(examples_dir).parts)]

for root, dirs, files in os.walk(os.environ['ALIGN_HOME']):
    for file in files:
        if file.endswith("model.txt"):
             model_path = os.path.join(root, file)

@pytest.fixture
def get_parser():
    parser = SpiceParser()
    assert ALIGN_HOME.is_dir()
    ah = ALIGN_HOME / 'align' # There is no align dir in ALIGN HOME in CI

    model_statemenets = ALIGN_HOME/ 'align' / 'config' / 'model.txt'
    assert model_statemenets == model_path
    assert model_statemenets.is_file()
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

