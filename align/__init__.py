__version__ = '0.9.8'

import pathlib
import os
import logging

logdir = pathlib.Path.cwd() / "LOG"
if not os.path.exists(logdir):
    os.mkdir(logdir)
elif os.path.exists(logdir / "compiler.log"):
    os.rename(logdir / "compiler.log", logdir / "compiler.log1")
logging.basicConfig(filename=logdir / "compiler.log", level=logging.ERROR)

from .main import schematic2layout
from .cmdline import CmdlineParser
