import pathlib
import subprocess
import sys

import logging
logger = logging.getLogger(__name__)

def generate_png(working_dir, variant):
    cmd = [
        os.path.dirname(sys.executable) + "/gds2png.sh",
        str(working_dir / f'{variant}.gds'),
        str(working_dir / f'{variant}.png'),
        str(pathlib.Path(__file__).parent.parent / 'config' / 'image_png.rb')
    ]
    try:
        ret = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding='utf-8', cwd=working_dir, check=True)
        logger.debug(ret.stdout)
    except subprocess.CalledProcessError as e:
        logger.error(f"Call to '{' '.join(cmd)}' failed:\n{e.stdout}")
        return {}
