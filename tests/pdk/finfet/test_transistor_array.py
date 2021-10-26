import pytest
from align.pdk.finfet import MOSGenerator
try:
    from .utils import get_test_id, export_to_viewer
except BaseException:
    from utils import get_test_id, export_to_viewer
import logging
logger = logging.getLogger(__name__)


ports_uno = [
    # 3 terminal source body shorted
    {'S': [('M1', 'S'), ('M1', 'B')], 'D': [('M1', 'D')], 'G': [('M1', 'G')]},
    # 3 terminal
    {'S': [('M1', 'S')], 'D': [('M1', 'D')], 'G': [('M1', 'G')]},
    # diode connected
    {'S': [('M1', 'S')], 'D': [('M1', 'D'), ('M1', 'G')]},
    # decap
    {'D': [('M1', 'S'), ('M1', 'D')], 'G': [('M1', 'G')]},
    # bonus
    {'D': [('M1', 'D')], 'S': [('M1', 'G'), ('M1', 'S')]},
    # full dummy
    {'B': [('M1', 'D'), ('M1', 'G'), ('M1', 'S'), ('M1', 'B')]}
    ]


ports_duo = [
    # diffpair
    {'S': [('M1', 'S'), ('M2', 'S')], 'DA': [('M1', 'D')], 'DB': [('M2', 'D')], 'GA': [('M1', 'G')], 'GB': [('M2', 'G')]},
    # current mirror
    {'S': [('M1', 'S'), ('M2', 'S')], 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')], 'DB': [('M2', 'D')]},
    # level shifter
    {'G': [('M1', 'G'), ('M2', 'G')], 'SA': [('M1', 'S')], 'SB': [('M2', 'S')], 'DA': [('M1', 'D')], 'DB': [('M2', 'D')]},
    # cross coupled
    {'SA': [('M1', 'S')], 'SB': [('M2', 'S')], 'DA': [('M1', 'D'), ('M2', 'G')], 'DB': [('M2', 'D'), ('M1', 'G')]},
    # cross coupled shared source
    {'S': [('M1', 'S'), ('M2', 'S')], 'DA': [('M1', 'D'), ('M2', 'G')], 'DB': [('M2', 'D'), ('M1', 'G')]}
    ]


@pytest.mark.nightly
@pytest.mark.parametrize('n_row', range(1, 4))
@pytest.mark.parametrize('n_col', range(1, 6))
@pytest.mark.parametrize('nf', [2, 4, 6, 8])
@pytest.mark.parametrize('device_type', ['parallel', 'stack'])
@pytest.mark.parametrize('ports', ports_uno)
def test_uno_drc(n_row, n_col, nf, device_type, ports):
    logger.info(f'running {get_test_id()}')
    c = MOSGenerator()
    parameters = {'M': n_row*n_col, 'NFIN': 4, 'real_inst_type': 'n'}
    if device_type == 'parallel':
        parameters['NF'] = nf
    else:
        parameters['STACK'] = nf
    c.addNMOSArray(n_col, n_row, 0, None, ports, **parameters)
    c.gen_data(run_drc=True)
    if c.drc.num_errors > 0 or len(c.rd.opens) > 0 or len(c.rd.shorts) > 0:
        export_to_viewer(get_test_id(), c)
        assert False, f'{get_test_id()} DRC ports:{ports} type:{device_type} nf:{nf}, n_col:{n_col} n_row:{n_row}'


@pytest.mark.nightly
@pytest.mark.parametrize('n_row', range(1, 4))
@pytest.mark.parametrize('n_col', range(1, 6))
@pytest.mark.parametrize('nf', [2, 4, 6, 8])
@pytest.mark.parametrize('device_type', ['parallel', 'stack'])
@pytest.mark.parametrize('ports', ports_duo)
def test_duo_drc(n_row, n_col, nf, device_type, ports):
    logger.info(f'running {get_test_id()}')
    if n_row * n_col % 2 == 0 and n_col >= 2:
        c = MOSGenerator()
        parameters = {'M': n_row*n_col, 'NFIN': 4, 'real_inst_type': 'n'}
        if device_type == 'PARALLEL':
            parameters['NF'] = nf
        else:
            parameters['STACK'] = nf
        c.addNMOSArray(n_col, n_row, 1, None, ports, **parameters)
        c.gen_data(run_drc=True)
        if c.drc.num_errors > 0 or len(c.rd.opens) > 0 or len(c.rd.shorts) > 0:
            export_to_viewer(get_test_id(), c)
            assert False, f'{get_test_id()} DRC ports:{ports} type:{device_type} nf:{nf}, n_col:{n_col} n_row:{n_row}'


def test_uno_one():
    c = MOSGenerator()
    parameters = {'M': 1, 'NFIN': 4, 'real_inst_type': 'p'}
    parameters['NF'] = 2
    c.addNMOSArray(1, 1, 0, None, ports_uno[1], **parameters)
    c.gen_data(run_drc=True)
    export_to_viewer(get_test_id(), c)
    if c.drc.num_errors > 0 or len(c.rd.opens) > 0 or len(c.rd.shorts) > 0:
        assert False, f'{get_test_id()}'


def test_duo_one():
    c = MOSGenerator()
    parameters = {'M': 1, 'NFIN': 4, 'real_inst_type': 'p'}
    parameters['NF'] = 2
    c.addNMOSArray(2, 1, 1, None, ports_duo[0], **parameters)
    c.gen_data(run_drc=True)
    export_to_viewer(get_test_id(), c)
    if c.drc.num_errors > 0 or len(c.rd.opens) > 0 or len(c.rd.shorts) > 0:
        assert False, f'{get_test_id()}'


# Unit tests ###

def test_unit_interleave_pattern():
    mg = MOSGenerator()
    assert [1, 2] == mg.interleave_pattern(1, 2)
    assert [1, 2, 2, 1] == mg.interleave_pattern(2, 2)
    assert [1, 2, 1, 2, 1, 2] == mg.interleave_pattern(2, 3)


def test_unit_validate_array():
    mg = MOSGenerator()
    assert (1, 1) == mg.validate_array(1, 1, 1)
    assert (1, 2) == mg.validate_array(2, 1, 2)
    assert (1, 2) == mg.validate_array(2, 2, 2)
