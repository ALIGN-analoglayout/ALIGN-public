import pytest
from align.schema.parser import SpiceParser
import pathlib

ALIGN_HOME = pathlib.Path(__file__).parent.parent.parent
failing_dirs = ['adder']
skip_dirs = ['vco_dtype_12_hierarchical_res_constrained']

examples_dir =  ALIGN_HOME / 'examples_v2'
examples =  [p for p in examples_dir.rglob('*.sp') \
                if all(x not in skip_dirs for x in p.relative_to(examples_dir).parts)]
examples =  [p for p in examples \
                 if all(x in failing_dirs for x in p.relative_to(examples_dir).parts[:1])]

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

# TBF: fix spacings at end of line in the parser; Uncomment this testcase to check if it is working
def test_spacing_at_EOL(get_parser):
    get_parser.parse(f'''
    .subckt check d g s b 
    .param p1=2 
        MN0 d g n1 b    nfet l=0.014u nfin=p1 
        MN1 n1 g s b    nfet l=0.014u nfin=p1 
        R0 d n1 resistor res=rb 
    .ends check 
    ''')