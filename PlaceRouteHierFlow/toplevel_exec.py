#!/usr/bin/env python

import sys
import logging
import colorlog

#level = logging.DEBUG
level = logging.INFO

root = logging.getLogger()
root.setLevel(level)

handler = logging.StreamHandler(sys.stdout)
handler.setLevel(level)

fmt = '[%(asctime)s] %(levelname)s [%(filename)s.%(funcName)s:%(lineno)d] %(message)s'
datefmt = '%a, %d %b %Y %H:%M:%S' 
if False:
    formatter = logging.Formatter(fmt, datefmt=datefmt)
else:
    formatter = colorlog.ColoredFormatter('%(log_color)s ' + fmt, datefmt=datefmt)
handler.setFormatter(formatter)
root.addHandler(handler)

#from align.pnr.toplevel import toplevel
from toplevel import toplevel

DB = toplevel( sys.argv)
