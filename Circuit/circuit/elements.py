import sys, inspect

from .core import _SubCircuit, NTerminalDevice

def SubCircuit(name, *pins, **parameters):
	assert len(pins) >= 1, "Subcircuit must have at least 1 pin"
	# Automatically register subcircuit into design library for later reuse
	library[name] = type(name, (_SubCircuit,), {'_pins': pins,
		'_kwargs': {x: (str if issubclass(NTerminalDevice.get_param_type(y), str) else float, y)  for x, y in parameters.items()}})
	# return new class containing subcircuit
	return library[name]

class _MosFET(NTerminalDevice):
	_prefix = 'M'
	_pins = ('D', 'G', 'S', 'B')
	_args = {'model': str}
	_kwargs = {'w' : (float, 0), 'l' : (float, 0), 'nfin' : (int, 1)}

class NMOS(_MosFET):
	pass

class PMOS(_MosFET):
	pass

class CAP(NTerminalDevice):
	_prefix = 'C'
	_pins = ('plus', 'minus')
	_args = {'value': float}
	_kwargs = {}

class RES(NTerminalDevice):
	_prefix = 'R'
	_pins = ('plus', 'minus')
	_args = {'value': float}
	_kwargs = {}

library = { x[0]: x[1] for x in
			inspect.getmembers(sys.modules[__name__], lambda x: inspect.isclass(x) and
																issubclass(x, NTerminalDevice) and
																not x.__name__.startswith('_')) }
