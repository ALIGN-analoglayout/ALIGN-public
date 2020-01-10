#!/usr/bin/env python
import align
import sys

if __name__ == '__main__':
    ret = align.CmdlineParser().parse_args()
    sys.exit(0 if ret is not None else 1)
