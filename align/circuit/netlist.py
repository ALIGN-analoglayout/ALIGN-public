import networkx
from pydantic import PrivateAttr
from typing import Optional, List

from .instance import Instance
from .subcircuit import SubCircuit, Circuit

class Netlist(networkx.Graph):

    @property
    def elements(self):
        return [v['instance'] for v in self.nodes.values() if self._is_element(v)]

    def element(self, name):
        assert name in self.nodes and self._is_element(self.nodes[name]), name
        return self.nodes[name]['instance']

    @property
    def nets(self):
        return [x for x, v in self.nodes.items() if not self._is_element(v)]

    def __init__(self, subckt, instances = []):
        super().__init__()
        self.subckt = subckt
        for inst in instances:
            self.add_element(inst)

    def add_element(self, element):
        assert isinstance(element, Instance)
        for pin, net in element.pins.items():
            if self.has_edge(element.name, net):
                self[element.name][net]['pin'].add(pin)
            else:
                self.add_edge(element.name, net, pin={pin})
                self.nodes[element.name]['instance'] = element
        return element

    def remove_element(self, element):
        self.remove_nodes_from([x for x in self.neighbors(element.name) if self.degree(x) == 1])
        self.remove_node(element.name)

    def xyce(self):
        return '\n'.join(x.xyce() for x in self.elements)

    #
    # Helpers
    #
    @staticmethod
    def _is_element(v):
        return 'instance' in v

    # Algorithms to find & replace subgraph / subckt matches

    @staticmethod
    def default_node_match(x, y):
        if isinstance(x.get('instance'), Instance) and isinstance(y.get('instance'), Instance):
            return y.get('instance').model.name in x.get('instance').model.bases + [x.get('instance').model.name]
        else:
            return type(x.get('instance')) == type(y.get('instance'))

    @staticmethod
    def default_edge_match(x, y):
        return x.get('pin') == y.get('pin')

    def find_subgraph_matches(self, graph, node_match=None, edge_match=None):
        if node_match is None:
            node_match = self.default_node_match
        if edge_match is None:
            edge_match = self.default_edge_match
        matcher = networkx.algorithms.isomorphism.GraphMatcher(
            self, graph, node_match=node_match, edge_match=edge_match)
        ret = []
        for match in matcher.subgraph_isomorphisms_iter():
            if not any(self._is_element(self.nodes[node]) and any(node in x for x in ret) for node in match):
                ret.append(match)
        return ret

    def replace_matching_subckts(self, subckts, node_match=None, edge_match=None):
        if isinstance(subckts, SubCircuit):
            subckts = [subckts]
        for subckt in subckts:
            matches = self.find_subgraph_matches(subckt.circuit, node_match, edge_match)
            self._replace_matches_with_subckt(matches, subckt)

    def _replace_matches_with_subckt(self, matches, subckt):
        assert isinstance(subckt, SubCircuit)
        counter = 0
        for match in matches:
            # Cannot replace as some prior transformation has made the current one invalid
            assert all(x in self.nodes for x in match)
            # Cannot replace as internal node is used elsewhere in circuit
            internal_nodes = [x for x, y in match.items() if y not in subckt.pins]
            if not all(x in match for node in internal_nodes for x in self.neighbors(node)):
                continue
            # Remove nodes not on subckt boundary
            self.remove_nodes_from(internal_nodes)
            # Create new instance of subckt
            name, counter = f'X_{subckt.name}_{counter}', counter + 1
            assert name not in self.elements
            pinmap = {pin: net for net, pin in match.items() if pin in subckt.pins}
            assert all(x in pinmap for x in subckt.pins), (match, subckt)
            inst = subckt(name, *[pinmap[x] for x in subckt.pins])
            # attach instance to current graph
            self.add_element(inst)

    # Algorithms to find & replace repeated subgraphs

    def find_repeated_subckts(self, replace=False):
        index = 0
        subckts = []
        worklist = list(self.elements)
        while len(worklist) > 0:
            # Create new graph with a single element
            ckt = Circuit().netlist
            ckt.add_element(worklist.pop(0))
            # Grow graph iteratively & look for subgraph matches
            matchlist = self._get_match_candidates(worklist, ckt)
            while len(matchlist) > 0:
                element = matchlist.pop(0)
                ckt.add_element(element)
                if len(self.find_subgraph_matches(ckt)) <= 1:
                    ckt.remove_element(element)
                else:
                    matchlist = self._get_match_candidates(worklist, ckt)
            # Create subcircuit & update worklist if needed
            if len(ckt.elements) > 1:
                pinmap = {y: f'pin{x}' for x, y in enumerate(
                    (net for net in ckt.nets \
                        if not all(neighbor in ckt.nodes for neighbor in self.neighbors(net))))}
                subckt, index = SubCircuit(name=f'XREP{index}', pins=list(pinmap.values())), index + 1
                for element in ckt.elements:
                    subckt.add_element(element.model(element.name,
                        *[pinmap[x] if x in pinmap else x for x in element.pins.values()]))
                subckts.append(subckt)
                matches = self.find_subgraph_matches(subckt.circuit)
                worklist = [element for element in worklist if not any(element.name in match for match in matches)]
                if replace:
                    self._replace_matches_with_subckt(matches, subckt)
        return subckts

    def replace_repeated_subckts(self):
        return self.find_repeated_subckts(True)

    def _get_match_candidates(self, worklist, ckt):
        # Pick circuit elements that have some net-name based overlap with ckt subgraph
        matchlist = [element for element in worklist if element.name not in ckt and any(x in ckt for x in self.neighbors(element.name))]
        # Sort circuit elements to minimize the number of (net) nodes added to ckt subgraph
        matchlist.sort(key=lambda element: sum([x not in ckt for x in self.neighbors(element.name)]))
        return matchlist

    # Algorithms to flatten netlist

    def flatten(self, depth=999):
        ''' depth = 999 helps protect against recursive subckt definitions '''
        depth = depth - 1
        for subcktinst in (x for x in self.elements if isinstance(x.model, SubCircuit)):
            self._replace_subckt_with_components(subcktinst)
        if any((isinstance(x.model, SubCircuit) for x in self.elements)) and depth > 0:
            self.flatten(depth)
        for element in self.elements:
            if element.model.prefix and not element.name.startswith(element.model.prefix):
                    element.name = f'{element.model.prefix}_{element.name}'

    def _replace_subckt_with_components(self, subcktinst):
        # Remove element from graph
        self.remove_node(subcktinst.name)
        # Add new elements
        for element in subcktinst.model.circuit.elements:
            newelement = element.model(f'{subcktinst.name}_{element.name}',
                *[subcktinst.pins[x] if x in subcktinst.pins else f'{subcktinst. name}_{x}' for x in element.pins.values()],
                **{key: eval(val, {}, subcktinst.parameters) if isinstance(val, str) else val for key, val in element.parameters.items()})
            self.add_element(newelement)

