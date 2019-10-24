import sys, inspect

from .core import NTerminalDevice

class _MosFET(NTerminalDevice):
	_prefix = 'M'
	_pins = ('D', 'G', 'S', 'B')
	_parameters = {'w' : (float, 0), 'l' : (float, 0), 'nfin' : (int, 1)}

class NMOS(_MosFET):
	pass

class PMOS(_MosFET):
	pass

class _TwoTerminalDevice(NTerminalDevice):
	_pins = ('plus', 'minus')
	_parameters = {'value': (float, 0)}

class CAP(_TwoTerminalDevice):
	_prefix = 'C'

class RES(_TwoTerminalDevice):
	_prefix = 'R'

class IND(_TwoTerminalDevice):
	_prefix = 'L'

class Library(dict):

	def __init__(self):
		self.update({ x[0]: x[1] for x in
			inspect.getmembers(sys.modules[__name__], lambda x: inspect.isclass(x) and
																issubclass(x, NTerminalDevice) and
																not x.__name__.startswith('_')) })

