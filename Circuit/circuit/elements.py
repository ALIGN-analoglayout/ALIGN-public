import sys, inspect

from .core import _SubCircuit, NTerminalDevice, Circuit

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
library = Library()

def SubCircuit(name, *pins, library=library, **parameters):
	assert len(pins) >= 1, "Subcircuit must have at least 1 pin"
	# Automatically register subcircuit into library for later reuse
	library[name] = type(name, (_SubCircuit,), {'_pins': pins})
	library[name].add_parameters(parameters)
	# return new class containing subcircuit
	return library[name]
