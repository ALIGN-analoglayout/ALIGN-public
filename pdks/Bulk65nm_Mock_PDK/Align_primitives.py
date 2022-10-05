import argparse
import pathlib
import logging
import json

from align.primitive import generate_primitive
from align.schema.parser import SpiceParser
from align.compiler.util import get_primitive_spice
from align.compiler.user_const import ConstraintParser


def main(args):
    logging.basicConfig(level=logging.getLevelName(args.logLevel))
    primitive_def = read_primitive_spice(args)

    return generate_primitive(
        args.block_name,
        primitive_def,
        args.height,
        args.Xcells,
        args.Ycells,
        args.pattern,
        args.value,
        args.vt_type,
        args.stack,
        args.params,
        args.pinSwitch,
        args.bodySwitch,
        args.pdkdir,
        args.outputdir
    )


def gen_parser():
    parser = argparse.ArgumentParser(description="Inputs for Cell Generation")
    parser.add_argument("-i", "--input_spice", type=str, required=False, default=None)
    parser.add_argument("-c", "--constraint_dir", type=str, required=False, default=None)
    parser.add_argument("-p", "--primitive", type=str, required=True)
    parser.add_argument("-b", "--block_name", type=str, required=True)
    parser.add_argument("-u", "--height", type=int, required=False, default=28)
    parser.add_argument("-X", "--Xcells", type=int, required=True)
    parser.add_argument("-Y", "--Ycells", type=int, required=True)
    parser.add_argument("-s", "--pattern", type=int, required=False, default=1)
    parser.add_argument("-q", "--pinSwitch", type=int, required=False, default=0)
    parser.add_argument("-bs", "--bodySwitch", type=int, required=False, default=1)
    parser.add_argument("-v", "--vt_type", type=str, required=False, default='RVT')
    parser.add_argument("-st", "--stack", type=int, required=False, default=1)
    parser.add_argument("-n", "--value", type=str, required=False, default=None)
    parser.add_argument("--params", type=json.loads, required=False, default='{}')
    parser.add_argument("-d", "--pdkdir", type=pathlib.Path, required=False, default=pathlib.Path(__file__).resolve().parent)
    parser.add_argument("-o", "--outputdir", type=pathlib.Path, required=False, default=pathlib.Path(__file__).resolve().parent)
    parser.add_argument("-l", "--log", dest="logLevel", choices=['DEBUG', 'INFO', 'WARNING',
                        'ERROR', 'CRITICAL'], default='ERROR', help="Set the logging level (default: %(default)s)")
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
    primitive_def = parser.library.find(args.primitive.upper())
    primitive_def.add_generator('MOS')
    if args.constraint_dir:
        assert pathlib.Path(args.constraint_dir).exists(), f"constraint dir {args.constraint_dir} does not exist"
        const_parse = ConstraintParser(args.pdkdir, pathlib.Path(args.constraint_dir))
        const_parse.annotate_user_constraints(primitive_def)
    assert primitive_def, f"No such primitive definition found {args.primitive}"
    return primitive_def


if __name__ == "__main__":
    main(gen_parser().parse_args())
