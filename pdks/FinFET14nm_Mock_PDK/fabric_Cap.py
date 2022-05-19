import argparse
import pathlib

from align.primitive import generate_primitive
from align.schema.parser import SpiceParser
from align.compiler.util import get_primitive_spice



def gen_parser():
    parser = argparse.ArgumentParser(description="Inputs for Cell Generation")
    parser.add_argument("-i", "--input_spice", type=str, required=False, default=None)
    parser.add_argument("-b", "--block_name", type=str, required=True)
    parser.add_argument("-n", "--unit_cap", type=float, default=None)
    parser.add_argument("-q", "--pinSwitch", type=int, required=False, default=0)
    parser.add_argument("-d", "--pdkdir", type=pathlib.Path, required=False, default=pathlib.Path(__file__).resolve().parent)
    parser.add_argument("-o", "--outputdir", type=pathlib.Path, required=False, default=pathlib.Path(__file__).resolve().parent)
    return parser


def read_primitive_spice(args):
    model_statements = args.pdkdir / "models.sp"
    assert model_statements.exists(), f"No model file found for this PDK {model_statements}"
    parser = SpiceParser()
    with open(model_statements, 'r') as f:
        lines = f.read()
    parser.parse(lines)

    if not args.input_spice:
        primitive_spice = get_primitive_spice()
    else:
        primitive_spice = args.pdkdir / args.input_spice
    assert primitive_spice.exists(), f"No spice file found {primitive_spice}"
    with open(primitive_spice) as f:
        lines = f.read()
    parser.parse(lines)
    primitive_def = parser.library.find('CAP_2T')
    assert primitive_def, f"CAP_2T not found in library {primitive_spice}"
    primitive_def.add_generator('CAP')
    assert primitive_def, f"No such primitive definition found {args.primitive}"
    return primitive_def


def main(args):
    cap_subckt = read_primitive_spice(args)
    return generate_primitive(args.block_name, cap_subckt, value=args.unit_cap, pdkdir=args.pdkdir, outputdir=args.outputdir)


if __name__ == "__main__":
    main(gen_parser().parse_args())
