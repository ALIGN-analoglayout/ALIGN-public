from cktgen import cktgen, cktgen_physical_from_json

import pytest

@pytest.mark.intel_22nm
def test_A():
    args,tech = cktgen.parse_args(["-n", "comparator",
                                   "-tf", "../Intel/DR_COLLATERAL_Generator/22nm/Process.json",
                                   "--placer_json", "../Intel/__json",
                                   "--gr_json", "../Intel/__json_grs",
                                   "-s", "comparator"])

     
    cktgen_physical_from_json.main(args,tech)
