import pathlib
import subprocess
import sys
import os

import logging
logger = logging.getLogger(__name__)

def generate_lef_with_obs(working_dir, gdsfile, layersfile, leffile):
    cmd = [
        os.path.dirname(sys.executable) + "/gen_lef_with_obs.py",
        "-l", str(working_dir / f'{layersfile}'),
        "-g", str(working_dir / f'{gdsfile}'),
        "-f", str(working_dir / f'{leffile}')
    ]
    try:
        ret = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding='utf-8', cwd=working_dir, check=True)
        logger.debug(ret.stdout)
    except subprocess.CalledProcessError as e:
        logger.error(f"Call to '{' '.join(cmd)}' failed:\n{e.stdout}")
        return {}
