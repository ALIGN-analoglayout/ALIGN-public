#!/usr/bin/env python

import logging
import sys

from align.pnr import toplevel

level = logging.INFO
root = logging.getLogger()
root.setLevel(level)

logger = logging.getLogger(__name__)

def cmdline( argv):
    logger.info('Running C++ toplevel(args)')
    toplevel.toplevel( argv)

if __name__ == "__main__":
    cmdline( sys.argv)
