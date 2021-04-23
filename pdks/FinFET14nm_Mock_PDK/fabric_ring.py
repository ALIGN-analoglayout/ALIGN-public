import argparse
import pathlib

from align.primitive import generate_primitive

def gen_parser():
    parser = argparse.ArgumentParser( description="Inputs for Cell Generation")
    parser.add_argument( "-b", "--block_name", type=str, required=True)
    parser.add_argument( "-X", "--Xcells", type=int, required=False, default=1)
    parser.add_argument( "-Y", "--Ycells", type=int, required=False, default=1)
    parser.add_argument( "-q", "--pinSwitch", type=int, required=False, default=0)
    parser.add_argument( "-d", "--pdkdir", type=pathlib.Path, required=False, default=pathlib.Path(__file__).resolve().parent)
    parser.add_argument( "-o", "--outputdir", type=pathlib.Path, required=False, default=pathlib.Path(__file__).resolve().parent)
    return parser

def main( args):
    return generate_primitive(args.block_name, 'ring', pdkdir=args.pdkdir, outputdir=args.outputdir)

if __name__ == "__main__":
    main( gen_parser().parse_args())


