import pathlib
import json
import argparse


def create_test_case(args):
    nets = args.nets.upper().split(',')
    layers = args.layers.upper().split(',')
    with pathlib.Path(args.input_path).open('rt') as fp:
        data = json.load(fp)

    bbox = data["bbox"]
    terminals = list()
    for term in data["terminals"]:
        # if term["netName"] != "CLK":
        #     continue
        if term["netName"]:
            term["netName"] = term["netName"].upper()
        term["layer"] = term["layer"].upper()
        if term["layer"] in layers:
            if term["netName"] in nets and term["netType"] == "pin":
                terminals.append(term)
            elif term["layer"].startswith("M"):
                term["netName"] = None
                term["netType"] = "blockage"
                terminals.append(term)

    with pathlib.Path(args.output_path).open('w') as fp:
        json.dump({"bbox": bbox, "terminals": terminals}, fp=fp, indent=2)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Utility to create test case for router")
    parser.add_argument("--input_path", type=pathlib.Path, help="Path to the input json file")
    parser.add_argument("--output_path", type=pathlib.Path, help="Path to the output json file")
    parser.add_argument("--nets", type=str, help="comma separated list of net names to keep")
    parser.add_argument("--layers", type=str, help="comma separated list of layers to keep")
    args = parser.parse_args()
    create_test_case(args)
