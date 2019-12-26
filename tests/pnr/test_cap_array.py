import pathlib
import json

from align.pnr import *
from align.cell_fabric import DefaultCanvas, transformation
from pprint import pformat

import pytest
import os

import re

def get_files():
    if "ALIGN_WORK_DIR" in os.environ:
        rdir = pathlib.Path( os.environ["ALIGN_WORK_DIR"]) / "switched_capacitor_filter/pnr_output/Results"
        if rdir.is_dir():
            p = re.compile( r'^.*AspectRatio.*_\d+x\d+\.json$')
            return [ nm for child in rdir.iterdir() for nm in (child.name,) if p.match( nm)]
    return []

@pytest.mark.parametrize("fn",get_files())
def test_remove_duplicates(fn):
    with (rdir / fn).open( "rt") as fp:
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
