import argparse
import pathlib

from align.primitive import generate_primitive
from align.schema import SpiceParser, Model, SubCircuit, Instance
from align.schema.types import set_context


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
    res_model = primitive_spice_parser.library.find('RES')
    assert res_model, f"No such primitive definition found {args.primitive}"
    if isinstance(res_model, Model):
        with set_context(primitive_spice_parser.library):
            res_subckt = SubCircuit(name=args.block_name, pins=list(res_model.pins))
            with set_context(res_subckt.elements):
                new_ele = Instance(name='R0',
                                   model='RES',
                                   pins={x: x for x in res_model.pins},
                                   generator='RES'
                                   )
            res_subckt.elements.append(new_ele)
    return res_subckt


def main(args):
    res_subckt = read_primitive_spice(args)
    return generate_primitive(args.block_name, res_subckt, value=(args.height, args.res), pdkdir=args.pdkdir, outputdir=args.outputdir)


if __name__ == "__main__":
    main(gen_parser().parse_args())
