import pathlib
import json

from pnrdb import *
from cell_fabric import DefaultCanvas, Pdk, transformation
from pprint import pformat
import json
import pytest
import os

import re

dir = pathlib.Path( os.environ["ALIGN_WORK_DIR"]) / "switched_capacitor_filter/pnr_output/Results"
assert dir.is_dir()

p = re.compile( r'^.*AspectRatio.*_\d+x\d+\.json$')
res = [ nm for child in dir.iterdir() for nm in (child.name,) if p.match( nm)]

@pytest.mark.parametrize("fn",res)
def test_remove_duplicates(fn):

    filepath = dir / fn

    with filepath.open( "rt") as fp:
        d = json.load( fp)
        
    pdk = "../PDK_Abstraction/FinFET14nm_Mock_PDK"
    sys.path.append(str(pathlib.Path(pdk).parent.resolve()))
    pdkpkg = pathlib.Path(pdk).name
    canvas = importlib.import_module(f'{pdkpkg}.canvas')
    # TODO: Remove these hardcoded widths & heights from __init__()
    #       (Height may be okay since it defines UnitCellHeight)
    cnv = getattr(canvas, f'{pdkpkg}_Canvas')(12, 4, 2, 3)

    cnv.bbox = transformation.Rect( *d["bbox"])
    cnv.terminals = d["terminals"]
    
    cnv.gen_data(run_pex=False)

    assert len(cnv.rd.different_widths) == 0, pformat(cnv.rd.different_widths)
    assert len(cnv.rd.shorts) == 0, pformat(cnv.rd.shorts)
#    assert len(cnv.rd.opens) == 0, pformat(cnv.rd.opens)
    assert len(cnv.drc.errors) == 0, pformat(cnv.drc.errors)
