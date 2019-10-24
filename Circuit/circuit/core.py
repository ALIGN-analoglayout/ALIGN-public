from networkx import Graph

class NTerminalDevice():

	_prefix = ''
	_pins = ()
	_parameters = {} # name : (type, defaultval)

	name = ''
	pins = {} # name: net
	parameters = {} # name : val

	@classmethod
	def add_parameters(self, parameters):
		self._parameters.update({x: (str if issubclass(NTerminalDevice.get_param_type(y), str) else float, y)  for x, y in parameters.items()})

	def __init__(self, name, *pins, **parameters):
		self.name = name
		assert self.name.startswith(self._prefix)
		assert len(pins) == len(self._pins), f"One or more positional arguments has not been specified. Need name and pins {self._pins}"
		self.pins = {pin: net for pin, net in zip(self._pins, pins)}
		self.parameters = {param: self._cast(val, ty) for param, (ty, val) in self._parameters.items()}
		assert all(x in self._parameters for x in parameters.keys())
		self.parameters.update({param: self._cast(val, self._parameters[param][0]) for param, val in parameters.items()})

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
				val = NTerminalDevice.str2float(val)
			except ValueError:
				raise AssertionError("Attempting to cast invalid string to float")
		# Check if it is safe to cast to int
		if issubclass(ty, int):
			assert isinstance(val, int) or val.is_integer(), "Attempting to cast non-integral number to int"
		# Final casting
		return ty(val)

	@staticmethod
	def str2float(val):
		unit = next((x for x in NTerminalDevice.unit_multipliers if val.endswith(x.upper()) or val.endswith(x.lower())), None)
		numstr = val if unit is None else val[:-1*len(unit)]
		return float(numstr) * NTerminalDevice.unit_multipliers[unit] if unit is not None else float(numstr)

	@staticmethod
	def get_param_type(val):
		# Check for valid types
		assert isinstance(val, (str, int, float))
		# Attempt to cast string to float
		if isinstance(val, str):
			try:
				val = NTerminalDevice.str2float(val)
			except ValueError:
				return str
		return int if isinstance(val, int) or val.is_integer() else float

class Circuit(Graph):

	@property
	def elements(self):
		return [x for x in self.nodes if isinstance(x, NTerminalDevice)]

	@property
	def nets(self):
		return [x for x in self.nodes if isinstance(x, str)]

	def add_element(self, element):
		assert isinstance(element, NTerminalDevice)
		for pin, net in element.pins.items():
			self.add_edge(element, net, pin=pin)
		return element

# WARNING: Do not add attributes/methods which may exist
#          in Circuit to _SubCircuitMetaClass/_SubCircuit

class _SubCircuitMetaClass(type):

	def __new__(cls, clsname, bases, attributedict):
		if 'circuit' not in attributedict: attributedict.update({'_circuit': Circuit()})
		if '_parameters' not in attributedict: attributedict.update({'_parameters': {}})
		return super(_SubCircuitMetaClass, cls).__new__(cls, clsname, bases, attributedict)

	def __getattr__(self, name):
		return getattr(self._circuit, name)

class _SubCircuit(NTerminalDevice, metaclass=_SubCircuitMetaClass):
	_prefix = 'X'

	def __getattr__(self, name):
		if name == 'add_element':
			raise AssertionError("Add elements directly to subcircuit definition (not to instance)")
		return getattr(self._circuit, name)

def SubCircuit(name, *pins, library=None, **parameters):
	assert len(pins) >= 1, "Subcircuit must have at least 1 pin"
	subckt = type(name.upper(), (_SubCircuit,), {'_pins': pins})
	subckt.add_parameters(parameters)
	# Automatically register subcircuit into library for later reuse
	if library is not None:
		library[name] = subckt
	# return new class containing subcircuit
	return subckt

