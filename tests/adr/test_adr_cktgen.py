import json
import os
import pathlib

from align.adr.cktgen_physical_from_json import main
from align.adr.cktgen import parse_args

ALIGN_HOME = pathlib.Path(__file__).resolve().parent.parent.parent

if 'ALIGN_HOME' in os.environ:
    assert pathlib.Path(os.environ['ALIGN_HOME']).resolve() == ALIGN_HOME
else:
    os.environ['ALIGN_HOME'] = str(ALIGN_HOME)

def test_adr_cktgen():
    
    collateral_dir = ALIGN_HOME / "DetailedRouter" / "DR_COLLATERAL_Generator" / "hack84" 

    command_line_args = [
        '-n', 'foo',
        '-tf', str(collateral_dir / "Process.json"),
        '-s', 'foo',
        '--placer_json', 'foo.json'
    ]

    #command_line_args.append( '--help')

    args, tech = parse_args( command_line_args)



    main( args, tech)
