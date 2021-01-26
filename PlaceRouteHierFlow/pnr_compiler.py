#!/usr/bin/env python

import sys, os
sys.setdlopenflags(os.RTLD_GLOBAL|os.RTLD_LAZY)

import logging
import colorlog

root = logging.getLogger()
root.setLevel(logging.INFO)

logger = logging.getLogger(__name__)
handler = logging.StreamHandler(sys.stdout)
handler.setLevel(logging.INFO)
#formatter = logging.Formatter('[%(asctime)s] %(levelname)s [%(filename)s.%(funcName)s:%(lineno)d] %(message)s', datefmt='%a, %d %b %Y %H:%M:%S')
#handler.setFormatter(formatter)
handler.setFormatter(colorlog.ColoredFormatter('%(log_color)s [%(asctime)s] %(levelname)s [%(filename)s.%(funcName)s:%(lineno)d] %(message)s', datefmt='%a, %d %b %Y %H:%M:%S'))
root.addHandler(handler)

import PnR

PnR.toplevel( sys.argv)
