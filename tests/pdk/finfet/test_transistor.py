from align.pdk.finfet import CanvasPDK, mos, tap
from align.schema.transistor import Transistor
from .helper import *


def test_one():
    tx = Transistor(model_name='n', nf=2, nfin=4, device_type='stack')
    data = mos(CanvasPDK, tx, track_pattern={'G':[6], 'D':[4], 'S':[2]})
    fn = "test_transistor_1"
    compare_with_golden(fn, data)


def test_two():
    tx = Transistor(model_name='n', nf=4, nfin=4, device_type='stack')
    data = mos(CanvasPDK, tx, track_pattern={'G':[6], 'D':[4], 'S':[2]})
    fn = "test_transistor_2"
    compare_with_golden(fn, data)


def test_three():
    tx = Transistor(model_name='n', nf=2, nfin=4, device_type='parallel')
    data = mos(CanvasPDK, tx, track_pattern={'G':[6], 'D':[4], 'S':[2]})
    fn = "test_transistor_3"
    compare_with_golden(fn, data)


def test_four():
    tx = Transistor(model_name='n', nf=4, nfin=4, device_type='parallel')
    data = mos(CanvasPDK, tx, track_pattern={'G':[6], 'D':[4], 'S':[2]})
    fn = "test_transistor_4"
    compare_with_golden(fn, data)


def test_five():
    tx = Transistor(model_name='n', nf=2, nfin=4, device_type='stack')
    data = tap(CanvasPDK, tx)
    fn = "test_transistor_5"
    compare_with_golden(fn, data)


def test_six():
    tx = Transistor(model_name='n', nf=4, nfin=4, device_type='stack')
    data = tap(CanvasPDK, tx)
    fn = "test_transistor_6"
    compare_with_golden(fn, data)
