from align.schema.parser import SpiceParser
import argparse
import pathlib

from align.primitive import generate_primitive


def gen_parser():
    parser = argparse.ArgumentParser(description="Inputs for Cell Generation")
    parser.add_argument("-b", "--block_name", type=str, required=True)
    parser.add_argument("-X", "--Xcells", type=int, required=True)
    parser.add_argument("-Y", "--Ycells", type=int, required=True)
    parser.add_argument("-n", "--height", type=int, required=True)
    parser.add_argument("-r", "--res", type=float, required=True)
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
    primitive_def = primitive_spice_parser.library.find('RES')
    assert primitive_def, f"No such primitive definition found {args.primitive}"
    return primitive_def


def main(args):
    primitive_def = read_primitive_spice(args)
    return generate_primitive(args.block_name, primitive_def, value=(args.height, args.res), pdkdir=args.pdkdir, outputdir=args.outputdir)


if __name__ == "__main__":
    main(gen_parser().parse_args())
