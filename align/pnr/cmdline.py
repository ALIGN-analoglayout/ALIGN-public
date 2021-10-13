#!/usr/bin/env python

import sys
import gc

from align.pnr import toplevel
from align.utils import logmanager

import logging
logger = logging.getLogger(__name__)

def cmdline( argv, results_dir=None):
    logmanager.reconfigure_loglevels( file_level='INFO', console_level='INFO')
    logger.info('Running pnr_compiler using the Python-interface...')
    DB, results_name_map = toplevel.toplevel( argv, results_dir=results_dir)
    del DB
    gc.collect(1)
