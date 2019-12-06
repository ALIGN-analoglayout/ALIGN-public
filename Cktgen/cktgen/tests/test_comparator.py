from cktgen import cktgen, cktgen_physical_from_json

def test_A():
    args,tech = cktgen.parse_args(["-n", "comparator",
                                   "-tf", "../../DetailedRouter/DR_COLLATERAL_Generator/hack84/Process.json",
                                   "--placer_json", "../Intel/__json",
                                   "-s", "comparator"])

     
    cktgen_physical_from_json.main(args,tech)
