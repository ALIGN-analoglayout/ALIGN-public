import sys, inspect

from .core import NTerminalDevice

'''WARNING: All pin & parameter names must be capitalized
			to support case-insensitive parsing'''

class _MosFET(NTerminalDevice):
	_prefix = 'M'
	_pins = ('D', 'G', 'S', 'B')
	_parameters = {'W' : (float, 0), 'L' : (float, 0), 'NFIN' : (int, 1)}

class NMOS(_MosFET):
	pass

class PMOS(_MosFET):
	pass

class _TwoTerminalDevice(NTerminalDevice):
	_pins = ('+', '-')
	_parameters = {'VALUE': (float, 0)}

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

