#!/usr/bin/env python

import sys

from align.pnr import toplevel
from align.utils.logging import reconfigure_loglevels

import logging
logger = logging.getLogger(__name__)

def cmdline( argv):
    reconfigure_loglevels( file_level='INFO', console_level='INFO')
    logger.info('Running pnr_compiler using the Python-interface...')
    toplevel.toplevel( argv)

if __name__ == "__main__":
    cmdline( sys.argv)
