import networkx
from collections.abc import Iterable

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
        assert self.name.startswith(self._prefix), f'Prefix is {self._prefix}' + \
            '. Did you try overwriting an inbuilt element with subckt?' if self._prefix == 'X' else ''
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
                return val # probably a parameter reference
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

class Circuit(networkx.Graph):

    @staticmethod
    def _is_element(v):
        return 'instance' in v

    @property
    def elements(self):
        return [v['instance'] for v in self.nodes.values() if self._is_element(v)]

    def element(self, name):
        assert name in self.nodes and self._is_element(self.nodes[name])
        return self.nodes[name]['instance']

    @property
    def nets(self):
        return [x for x, v in self.nodes.items() if not self._is_element(v)]

    def add_element(self, element):
        assert isinstance(element, NTerminalDevice)
        for pin, net in element.pins.items():
            if self.has_edge(element.name, net):
                self[element.name][net]['pin'].add(pin)
            else:
                self.add_edge(element.name, net, pin={pin})
                self.nodes[element.name]['instance'] = element
        return element

    @staticmethod
    def default_node_match(x, y):
        return issubclass(type(x.get('instance')), type(y.get('instance')))

    @staticmethod
    def default_edge_match(x, y):
        return x.get('pin') == y.get('pin')

    def find_matching_subgraphs(self, subckt, node_match=None, edge_match=None):
        if node_match is None:
            node_match = self.default_node_match
        if edge_match is None:
            edge_match = self.default_edge_match
        assert hasattr(subckt, '_circuit') and isinstance(subckt._circuit, Circuit)
        matcher = networkx.algorithms.isomorphism.GraphMatcher(
            self, subckt._circuit, node_match=node_match, edge_match=edge_match)
        return list(matcher.subgraph_isomorphisms_iter())

    def replace_matching_subgraphs(self, primitives, node_match=None, edge_match=None):
        if not isinstance(primitives, Iterable):
            primitives = [primitives]
        for subckt in primitives:
            matches = self.find_matching_subgraphs(subckt, node_match, edge_match)
            self._replace_matches_with_subckt(matches, subckt)

    def _replace_matches_with_subckt(self, matches, subckt):
        assert hasattr(subckt, '_circuit') and isinstance(subckt._circuit, Circuit)
        counter = 0
        for match in matches:
            # Cannot replace as some prior transformation has made the current one invalid
            if any(x not in self.nodes for x in match):
                continue
            # Cannot replace as internal node is used elsewhere in circuit
            internal_nodes = [x for x, y in match.items() if y not in subckt._pins]
            if not all(x in match for node in internal_nodes for x in self.neighbors(node)):
                continue
            # Remove nodes not on subckt boundary
            self.remove_nodes_from(internal_nodes)
            # Create new instance of subckt
            name, counter = f'X_{subckt.__name__}_{counter}', counter + 1
            assert name not in self.elements
            pinmap = {pin: net for net, pin in match.items() if pin in subckt._pins}
            assert all(x in pinmap for x in subckt._pins), (match, subckt)
            inst = subckt(name, *[pinmap[x] for x in subckt._pins])
            # attach instance to current graph
            self.add_element(inst)

# WARNING: Do not add attributes/methods which may exist
#          in Circuit to _SubCircuitMetaClass/_SubCircuit

class _SubCircuitMetaClass(type):

    def __new__(cls, clsname, bases, attributedict):
        if '_circuit' not in attributedict: attributedict.update({'_circuit': Circuit()})
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
    subckt = type(name, (_SubCircuit,), {'_pins': pins})
    subckt.add_parameters(parameters)
    # Automatically register subcircuit into library for later reuse
    if library is not None:
        library[name] = subckt
    # return new class containing subcircuit
    return subckt

def Model(name, base, library=None, **parameters):
    assert issubclass(base, NTerminalDevice), base
    model = type(name, (base, ), {'_parameters': base._parameters.copy()})
    model.add_parameters(parameters)
    # Automatically register model into library for later reuse
    if library is not None:
        library[name] = model
    # return new class containing model
    return model
