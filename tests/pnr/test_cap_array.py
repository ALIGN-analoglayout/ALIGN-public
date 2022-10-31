import pathlib
import json

from align.pnr import *
from align.cell_fabric import transformation, pdk
from align.compiler.util import get_generator
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

    pdkdir = pathlib.Path(__file__).parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"
    generator = get_generator('MOSGenerator', pdkdir)

    # TODO: Remove these hardcoded widths & heights from __init__()
    #       (Height may be okay since it defines UnitCellHeight)
    cnv = generator(pdk.Pdk().load(pdkdir / 'layers.json'),12, 4, 2, 3)
    cnv.bbox = transformation.Rect( *d["bbox"])
    cnv.terminals = d["terminals"]
    
    cnv.gen_data(run_pex=False)

    assert len(cnv.rd.different_widths) == 0, pformat(cnv.rd.different_widths)
    assert len(cnv.rd.shorts) == 0, pformat(cnv.rd.shorts)
#    assert len(cnv.rd.opens) == 0, pformat(cnv.rd.opens)
    assert len(cnv.drc.errors) == 0, pformat(cnv.drc.errors)
