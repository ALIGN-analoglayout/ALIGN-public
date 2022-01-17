import align
import sys

def console_entry():
    ret = align.CmdlineParser().parse_args()
    sys.exit(0 if ret is not None else 1)

if __name__ == '__main__':
    console_entry()