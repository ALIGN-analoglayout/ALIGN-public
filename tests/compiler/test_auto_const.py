import pathlib
import pytest
import pathlib
import shutil
import json
from align.schema import Model, Instance, SubCircuit, Library
from align.schema.graph import Graph
from align.schema.types import set_context, List, Dict
from align.compiler.compiler import compiler_input
from align.compiler.find_constraint import symmnet_device_pairs
from utils import clean_data, build_example, ota_six
import textwrap

pdk_path = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
config_path =  pathlib.Path(__file__).resolve().parent.parent / 'files'
out_path = pathlib.Path(__file__).resolve().parent / 'Results'


def test_ota_six():
    name = 'CKT_OTA'
    netlist = ota_six(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find('CKT_OTA')
    G = Graph(ckt)
    pairs, pinsA, pinsB = symmnet_device_pairs(G,'VIN','VIP', None,None)
    print(pairs, pinsA, pinsB)
    assert pairs == 1
    clean_data(name)

# def test_scf():
#     mydir = pathlib.Path(__file__).resolve()
#     test_path = mydir.parent.parent / 'files' / 'test_circuits' / 'switched_capacitor_filter' / 'switched_capacitor_filter.sp'
#     gen_const_path = mydir.parent / 'Results' / 'SWITCHED_CAPACITOR_FILTER.verilog.json'
#     gold_const_path = mydir.parent.parent / 'files' / 'test_results' / 'switched_capacitor_filter.const.json'

#     updated_cktlib = compiler_input(test_path, "SWITCHED_CAPACITOR_FILTER", pdk_dir, config_path)
#     assert updated_cktlib.find('SWITCHED_CAPACITOR_FILTER')
#     result_path = out_path / 'switched_capacitor_filter'
#     compiler_output(test_path, updated_cktlib, 'SWITCHED_CAPACITOR_FILTER', result_path, pdk_dir)
#     gen_const_path = result_path / 'SWITCHED_CAPACITOR_FILTER.verilog.json'
#     gold_const_path = pathlib.Path(__file__).resolve().parent.parent / 'files' / 'test_results' / 'switched_capacitor_filter.const.json'
#     with open(gen_const_path, "r") as const_fp:
#         gen_const = next(x for x in json.load(const_fp)['modules'] if x['name'] == 'SWITCHED_CAPACITOR_FILTER')["constraints"]
#         gen_const.sort(key=lambda item: item.get("constraint"))
#     with open(gold_const_path, "r") as const_fp:
#         gold_const = json.load(const_fp)
#         gold_const.sort(key=lambda item: item.get("constraint"))
#     assert gold_const == gen_const