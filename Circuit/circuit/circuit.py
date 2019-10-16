class Circuit():

	_prefix = 'X'
	_pins = ()
	_args = {} # name : type
	_kwargs = {} # name : type

	name = ''
	pins = {} # name: net
	parameters = {} # name : val

	def __init__(self, name, *args, **kwargs):
		self.name = name
		assert self.name.startswith(self._prefix)
		assert len(args) == len(self._pins) + len(self._args), f"One or more positional arguments has not been specified. Need pins {self._pins} and arguments {tuple(self._args.keys())}"
		self.pins = {pin: net for pin, net in zip(self._pins, args[:len(self._pins)])}
		self.parameters = {param: self._cast(val, ty) for (param, ty), val in zip(self._args.items(), args[len(self._pins):])}
		assert all(x in self._kwargs for x in kwargs.keys())
		self.parameters.update({param: self._cast(val, ty) for param, (ty, val) in self._kwargs.items()})
		self.parameters.update({param: self._cast(val, self._kwargs[param][0]) for param, val in kwargs.items()})

	unit_multipliers = {
		'T': 1e12,
		'G': 1e9,
		'X': 1e6,
		'MEG': 1e6,
		'K': 1e3,
		'M': 1e-3,
		'U': 1e-6,
		'N': 1e-9,
		'P': 1e-12,
		'F': 1e-15
	}

	@staticmethod
	def _cast(val, ty):
		# Check for valid types
		assert isinstance(val, (str, int, float))
		assert issubclass(ty, (str, int, float))
		# Nothing to do. Return early
		if isinstance(val, ty):
			return val
		# Pretty print SPICE compatible numbers
		if issubclass(ty, str):
			if isinstance(val, int):
				return str(val)
			else:
				# TODO: Make this nicer by using units
				return str(val)
		# ty is numeric from this point on
		# Attempt to cast string to float
		if isinstance(val, str):
			try:
				val = Circuit.str2float(val)
			except ValueError:
				raise AssertionError("Attempting to cast invalid string to float")
		# Check if it is safe to cast to int
		if issubclass(ty, int):
			assert isinstance(val, int) or val.is_integer(), "Attempting to cast non-integral number to int"
		# Final casting
		return ty(val)

	@staticmethod
	def str2float(val):
		unit = next((x for x in Circuit.unit_multipliers if val.endswith(x.upper()) or val.endswith(x.lower())), None)
		numstr = val if unit is None else val[:-1*len(unit)]
		return float(numstr) * Circuit.unit_multipliers[unit]

	@staticmethod
	def get_param_type(val):
		# Check for valid types
		assert isinstance(val, (str, int, float))
		# Attempt to cast string to float
		if isinstance(val, str):
			try:
				val = Circuit.str2float(val)
			except ValueError:
				return str
		return int if isinstance(val, int) or val.is_integer() else float

def SubCircuit(name, *pins, **parameters):
	assert len(pins) >= 1, "Subcircuit must have at least 1 pin"
	return type(name, (Circuit,), {'_pins': pins, '_args': {'subckt': str}, '_kwargs': {x: (str if issubclass(Circuit.get_param_type(y), str) else float, y)  for x, y in parameters.items()}})

class MosFET(Circuit):
	_prefix = 'M'
	_pins = ('D', 'G', 'S', 'B')
	_args = {'model': str}
	_kwargs = {'w' : (float, 0), 'l' : (float, 0), 'nfin' : (int, 1)}

class Capacitor(Circuit):
	_prefix = 'C'
	_pins = ('plus', 'minus')
	_args = {'value': float}
	_kwargs = {}

class Resistor(Circuit):
	_prefix = 'R'
	_pins = ('plus', 'minus')
	_args = {'value': float}
	_kwargs = {}
