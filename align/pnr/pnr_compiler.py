#!/usr/bin/env python

import logging
import colorlog
import sys

from align.pnr import toplevel

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
#root.addHandler(handler)

logger = logging.getLogger(__name__)

def cmdline( argv):
    logger.info('Running C++ toplevel(args)')
    toplevel.toplevel( argv)

if __name__ == "__main__":
    cmdline( sys.argv)
