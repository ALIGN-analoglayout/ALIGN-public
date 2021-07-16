import pytest
from align.schema.parser import SpiceParser
import pathlib

ALIGN_HOME = pathlib.Path(__file__).parent.parent.parent

@pytest.fixture
def get_parser():
    parser = SpiceParser()
    model_statemenets = ALIGN_HOME/ 'align' / 'config' / 'model.txt'
    with open(model_statemenets) as f:
        lines = f.read()
    parser.parse(lines)
    return parser

#parameters without default values
# def test_top_param(get_parser):
#     get_parser.parse(f'''
#     .subckt nfet2x d g s b
#     .param p1
#         MN0 d g n1 b    nmos l=0.014u nfin=p1
#         MN1 n1 g s b    nmos l=0.014u nfin=p1
#     .ends nfet2x
#     ''')
# def test_m_value(get_parser):
#     get_parser.parse(f'''
#         MN0 d g n1 b    nmos l=0.014u nfin=p1 m=1
#     ''')
#TBF: new line character in parameter is traslated to args [single_to_differential_converter]
#This ecample does not reroduce the testcase plese use  [single_to_differential_converter]
# def test_top_param(get_parser):
#     get_parser.parse(f'''
#     .param p1=1 b=1 \
#         c=1

#     .subckt nfet2x d g s b
#     .param p1=30
#         MN0 d g n1 b    nmos l=0.014u nfin=p1
#         MN1 n1 g s b    nmos l=0.014u nfin=p1
#     .ends nfet2x
#     ''')

# TBF: parameter for instance of subckt is not defined inside subckt
# def test_subckt_param(get_parser):
#     get_parser.parse(f'''
#     .subckt check d g s b
#     MN0 d g n1 b    nfet l=0.014u nfin=p1
#     .ends check
#     .subckt top d g s b
#     x1 d g n1 b  m=1
#     .ends top
#     ''')
#
# TBF: fix spacings at end of line in the parser; Uncomment this testcase to check if it is working
# def test_spacing_at_EOL(get_parser):
#     get_parser.parse(f'''
#     .subckt check d g s b
#     .param p1=2
#         MN0 d g n1 b    nfet l=0.014u nfin=p1
#         MN1 n1 g s b    nfet l=0.014u nfin=p1
#         R0 d n1 resistor res=rb
#     .ends check
#     ''')

# def test_top_level():
#     test_path = (pathlib.Path(__file__).parent / 'test_circuits' / 'test1.sp').resolve()
#     pdk_dir = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
#     config_path =  pathlib.Path(__file__).resolve().parent.parent.parent / 'align' / 'config'
#     circuit = compiler(test_path, "test1", pdk_dir, config_path) # Not able to parse spice files with no top level names
#     assert len(circuit.elements) == 9

#Non supported lines
# .param _par0 _par1
# parameters _par=1 #spectre format
# e0 clksb gnd VCVS vdd clks 1
# d2 gnd vcc_gm diode #COMP_GM_STAGE_0415
# simulator lang = spectre
# global 0
# .include <path>
# #spectre lines #GF65_DLL_sanitized
# subckt trial a
# M1 ( a b c d) p=1
# ends trial
# I9 a trial
# T1 net104 CK_DLL net114 VSS lvtnfet l=60n w=800n nf=1
# V26 VDD 0 vsource dc=VDD type=dc
# xI8 net07 0 isource dc=20u type=dc
# XI11 CK VRCTL net010 DVDD DVSS / ND2D1LVT
# XCres8<7> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
# XR7 RTUNE<7> RTUNE<6> rppolys l=LD w=WQ m=1
# XR23 outa ntx rppolyl l=LC w=WG
# DDI3 VSS I ndio_hvt area=6.6e-14 pj=1.18e-06 m=1