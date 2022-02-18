import argparse
import pathlib

from align.primitive import generate_primitive
from align.schema.parser import SpiceParser
from align.schema import Model, SubCircuit, Instance
from align.schema.types import set_context


def gen_parser():
    parser = argparse.ArgumentParser(description="Inputs for Cell Generation")
    parser.add_argument("-b", "--block_name", type=str, required=True)
    parser.add_argument("-n", "--unit_cap", type=float, default=None)
    parser.add_argument("-q", "--pinSwitch", type=int, required=False, default=0)
    parser.add_argument("-d", "--pdkdir", type=pathlib.Path, required=False, default=pathlib.Path(__file__).resolve().parent)
    parser.add_argument("-o", "--outputdir", type=pathlib.Path, required=False, default=pathlib.Path(__file__).resolve().parent)
    return parser


def read_primitive_spice(args):
    model_statements = args.pdkdir / "models.sp"
    assert model_statements.exists(), f"No model file found for this PDK {model_statements}"
    primitive_spice_parser = SpiceParser()
    with open(model_statements, 'r') as f:
        lines = f.read()

    primitive_spice_parser.parse(lines)
    primitive_def = primitive_spice_parser.library.find('CAP')
    assert primitive_def, f"No such primitive definition found {args.primitive}"
    if isinstance(primitive_def, Model):
        with set_context(primitive_spice_parser.library):
            cap_subckt = SubCircuit(name=args.block_name, pins=list(primitive_def.pins))
            with set_context(cap_subckt.elements):
                new_ele = Instance(name='C0',
                                   model='CAP',
                                   pins={x: x for x in primitive_def.pins},
                                   generator='CAP'
                                   )
            cap_subckt.elements.append(new_ele)
    return cap_subckt


def main(args):
    cap_subckt = read_primitive_spice(args)
    return generate_primitive(args.block_name, cap_subckt, value=args.unit_cap, pdkdir=args.pdkdir, outputdir=args.outputdir)


if __name__ == "__main__":
    main(gen_parser().parse_args())
