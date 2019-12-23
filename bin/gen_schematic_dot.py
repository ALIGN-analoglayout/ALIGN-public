import sys
import pathlib
import argparse

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from align import circuit

if __name__ == "__main__":
    parser = argparse.ArgumentParser( description="Visualize Netlist using Graphviz")

    parser.add_argument( "-o", "--output_file", type=str, default=None)
    parser.add_argument( "-n", "--block_name", type=str, default="BUFFER_VCM_FINAL1")
    parser.add_argument( "-i", "--input_file", type=str, default=None)

    args = parser.parse_args()

    assert args.block_name is not None
    nm = args.block_name
    ofn = f"./{nm}.dot" if args.output_file is None else args.output_file
    ifn = f"./{nm}.sp" if args.input_file is None else args.input_file

    circuit.gen_dot_file(nm, ifn, ofn)
