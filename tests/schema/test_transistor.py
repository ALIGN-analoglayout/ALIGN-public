import pathlib
import json
from align.schema.transistor import Transistor, TransistorArray

my_dir = pathlib.Path(__file__).resolve().parent


def test_one():
    tx = Transistor(device_type='parallel', nf=4, nfin=4, model_name='n')
    tx_array = TransistorArray(unit_transistor=tx,
                               m={1: 1},
                               ports={1: {k: k for k in ['D', 'G', 'S']}},
                               n_rows=1
                               )
