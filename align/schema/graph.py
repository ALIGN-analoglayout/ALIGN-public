from align.schema import constraint
from .types import set_context
from .subcircuit import SubCircuit, Circuit
from .instance import Instance
from .translator import ConstraintTranslator
import networkx
from collections import Counter
import logging
from flatdict import FlatDict
import hashlib

logger = logging.getLogger(__name__)


class Graph(networkx.Graph):

    '''
    Helper class to traverse & modify graph-like netlists

    This class is meant to wrap around a SubCircuit (or Circuit) definition
    and modifies the wrapped object IN PLACE (does not create a copy).
    '''

    @property
    def elements(self):
        return [v['instance'] for v in self.nodes.values() if self._is_element(v)]

    def element(self, name):
        assert name in self.nodes and self._is_element(self.nodes[name]), name
        return self.nodes[name]['instance']

    @property
    def nets(self):
        return [x for x, v in self.nodes.items() if not self._is_element(v)]

    def __init__(self, subckt):
        super().__init__()
        self.subckt = subckt
        for element in subckt.elements:
            self._add_to_graph(element)

    def _add_to_graph(self, element):
        assert isinstance(element, Instance)
        for pin, net in element.pins.items():
            if self.has_edge(element.name, net):
                # Multiple device ports connected to same net
                self[element.name][net]['pin'].add(pin)
            else:
                # New net / element
                self.add_edge(element.name, net, pin={pin})
                self.nodes[element.name]['instance'] = element

    def add_instance(self, **kwargs):
        with set_context(self.subckt.elements):
            element = Instance(**kwargs)
        self.subckt.elements.append(element)
        self._add_to_graph(element)
        return element

    def remove(self, element):
        self.subckt.elements.remove(element)
        self.remove_nodes_from(
            [x for x in self.neighbors(element.name)
             if self.degree(x) == 1])
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
        # Assumes all library (y) definitions are in base class
        if isinstance(x.get('instance'), Instance) and isinstance(y.get('instance'), Instance):
            return y.get('instance').model in x.get('instance').mclass.bases + [x.get('instance').model]
        else:
            return isinstance(x.get('instance'), type(y.get('instance')))

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
        _temp = len(self.subckt.constraints)
        # Three possible scenarios of non determinism (M1, M2, M3, M4, M5) (Ma, Mb, Mc)
        # 1. Different keys [{M1:Ma, M2:Mb, M3:Mc}, {M4:Ma, M2:Mb, M3:Mc}]
        # 2. keys in diff order: [{M1:Ma, M2:Mb, M3:Mc}, {M2:Mb, M1:Ma, M3:Mb}]
        # 3. Different values: [{M1:Ma, M2:Mb, M3:Mc}, {M1:Ma, M2:Mc, M3:Mb}]
        # Thus sorting based on key,value pair
        matches = sorted(matcher.subgraph_isomorphisms_iter(), key=lambda k: [(x, y)for x, y in k.items()])
        for match in matches:
            # for match in sorted(matcher.subgraph_isomorphisms_iter(), key=lambda i: tuple(i.keys())):
            if not any(self._is_element(self.nodes[node]) and any(node in x for x in ret) for node in match):
                try:
                    self.check_constraint_satisfiability(graph, match)
                    ret.append(match)
                except BaseException:  # Make this more specific
                    # primitives with unsatisfied constraints will not be created
                    logger.debug(f"skipping match {graph.subckt.name} {match.keys()} due to unsatisfied constraints")
                    pass
        # revert any added const TODO: add checker here
        while len(self.subckt.constraints) > _temp:
            self.subckt.constraints.pop()
        return ret

    def check_constraint_satisfiability(self, subgraph, match):
        # Check if the constraints defined at primitive stage are valid for subckt
        subckt_const = subgraph.subckt.constraints
        with set_context(self.subckt.constraints):
            for const in subckt_const:
                if const.constraint == 'symmetric_blocks':
                    t = [[self._get_key(ele, match) for ele in pair] for pair in const.pairs]
                    d = const.direction
                    x = constraint.SymmetricBlocks(direction=d, pairs=t)
                    self.subckt.constraints.append(x)
                    assert x in self.subckt.constraints, f"constraint: {x} not found in {self.subckt.constraints}"
                    self.subckt.constraints.remove(x)
                elif const.constraint == 'symmetric_nets':
                    pair = [self._get_key(const.net1, match), self._get_key(const.net2, match)]
                    nbrs1, nbrs2 = self.all_neighbors(pair)
                    assert nbrs1 == nbrs2, f"neighbors mismatch {nbrs1} {nbrs2}"

    def all_neighbors(self, pair):
        nbrs1 = networkx.shortest_path_length(self, source=pair[0])
        nbrs2 = networkx.shortest_path_length(self, source=pair[1])
        # TODO: Can be modified to flat-distances? gropblock1 != groupblock2
        nbrs1_type = Counter([(self.element(nbr).model, dist) for nbr, dist in nbrs1.items() if self._is_element(self.nodes[nbr])])
        nbrs2_type = Counter([(self.element(nbr).model, dist) for nbr, dist in nbrs2.items() if self._is_element(self.nodes[nbr])])
        logger.debug(f"All neighbors of {pair[0]}: {nbrs1_type} , {pair[1]}: {nbrs2_type}")
        return nbrs1_type, nbrs2_type

    def _get_key(self, val, dicta):
        for key, value in dicta.items():
            if val == value:
                return key
        return "key doesn't exist"

    def replace_matching_subgraph(self, subgraph, skip=None, node_match=None, edge_match=None):
        matches = self.find_subgraph_matches(subgraph, node_match, edge_match)
        return self._replace_matches_with_subckt(matches, subgraph.subckt, skip)

    def _replace_matches_with_subckt(self, matches, subckt, skip=None):
        assert isinstance(subckt, SubCircuit)
        new_subckt_names = []
        for match in matches:

            # Cannot replace as some prior transformation has made the current one invalid
            assert all(x in self.nodes for x in match)
            assert len(subckt.pins) == len(set(subckt.pins)), f"duplicate pins found in module {subckt.name}, {subckt.pins}"
            removal_candidates = [
                x for x, y in match.items()
                if y not in subckt.pins]

            # Cannot replace if internal node is used elsewhere in subckt (Boundary elements / nets)
            if not all(x in match for node in removal_candidates for x in self.neighbors(node)):
                continue
            # Remove nodes not on subckt boundary
            if skip and set(removal_candidates) & set(skip) and len(removal_candidates) > 1:
                continue

            # subcircuit_name = subckt.name
            new_subckt = self.create_subckt_instance(subckt, match)
            new_subckt_names.append(new_subckt.name)

            nodes = list()
            for node in sorted(removal_candidates):
                # Elements only
                if node in self.nodes and self._is_element(self.nodes[node]):
                    # Takes care of nets attached to element too
                    nodes.append(node)
                    self.remove(self.element(node))
            nodes_str = '_'.join(nodes)
            instance_name = f'X_{nodes_str}'
            assert instance_name not in self.elements

            pin2net_map = {pin: net for net, pin in match.items() if pin in subckt.pins}
            assert all(x in pin2net_map for x in subckt.pins), (match, subckt)

            logger.debug(f"adding instance {instance_name} of type {new_subckt.name} in subckt {self.name}")
            self.add_instance(
                name=instance_name,
                model=new_subckt.name,
                pins=pin2net_map
            )
            if self.subckt.name:
                tr = ConstraintTranslator(self.subckt.parent)
                tr._update_const(self.subckt.name, removal_candidates, instance_name)

        return new_subckt_names
    # TODO: in future use paramaters from generator
    # HACK can also be moved to end of flow

    def create_subckt_instance(self, subckt, match):
        with set_context(self.subckt.parent):
            subckt_instance = SubCircuit(name=subckt.name,
                                         pins=subckt.pins,
                                         parameters=subckt.parameters,
                                         generator=subckt.generator)
        with set_context(subckt_instance.elements):
            for x, y in match.items():
                element = subckt.get_element(y)
                if not element:
                    continue  # copying only elements
                subckt_instance.elements.append(Instance(
                    name=element.name,
                    model=self.nodes[x].get('instance').model,
                    pins=element.pins,
                    parameters=self.nodes[x].get('instance').parameters))
        with set_context(subckt_instance.constraints):
            for const in subckt.constraints:
                subckt_instance.constraints.append(const)
        param = FlatDict(subckt_instance.dict(exclude_unset=True))
        arg_str = '_'.join([k+':'+str(param[k]) for k in sorted(param.keys())])
        key = f"_{str(int(hashlib.sha256(arg_str.encode('utf-8')).hexdigest(), 16) % 10**8)}"
        new_subckt_dict = subckt_instance.dict(exclude_unset=True)
        new_subckt_dict["name"] = new_subckt_dict["name"]+key
        with set_context(self.subckt.parent):
            new_subckt = SubCircuit(**new_subckt_dict)
            if not self.subckt.parent.find(new_subckt.name):
                self.subckt.parent.append(new_subckt)
        return new_subckt

    def find_repeated_subckts(self, replace=False):
        index = 0
        subckts = []
        worklist = list(self.elements)
        while len(worklist) > 0:
            # Create new graph with a single element
            with set_context(self.subckt.parent):
                netlist = Graph(Circuit())
            netlist.add_instance(**worklist.pop(0).dict())
            # Grow graph iteratively & look for subgraph matches
            matchlist = self._get_match_candidates(worklist, netlist)
            while len(matchlist) > 0:
                element = matchlist.pop(0)
                netlist.add_instance(**element.dict())
                if len(self.find_subgraph_matches(netlist)) <= 1:
                    netlist.remove(element)
                else:
                    matchlist = self._get_match_candidates(worklist, netlist)
            # Create subcircuit & update worklist if needed
            if len(netlist.elements) > 1:
                net2pin_map = {y: f'pin{x}' for x, y in enumerate(
                    (net
                     for net in netlist.nets
                     if not all(neighbor in netlist.nodes for neighbor in self.neighbors(net))))}
                with set_context(self.subckt.parent):
                    subckt, index = SubCircuit(
                        name=f'XREP{index}', pins=list(net2pin_map.values())), index + 1
                for element in netlist.elements:
                    with set_context(subckt.elements):
                        subckt.elements.append(
                            Instance(
                                name=element.name,
                                model=element.model,
                                pins={
                                    pin: net2pin_map[net]
                                    if net in net2pin_map else net
                                    for pin, net in element.pins.items()}
                            )
                        )
                subckts.append(subckt)
                matches = self.find_subgraph_matches(Graph(subckt))
                worklist = [element for element in worklist if not any(
                    element.name in match for match in matches)]
                if replace:
                    self._replace_matches_with_subckt(matches, subckt)
        return subckts

    def replace_repeated_subckts(self):
        return self.find_repeated_subckts(True)

    def _get_match_candidates(self, worklist, netlist):
        # Pick subckt elements that have some net-name based overlap with netlist subgraph
        matchlist = [element for element in worklist if element.name not in netlist and any(
            x in netlist for x in self.neighbors(element.name))]
        # Sort subckt elements to minimize the number of (net) nodes added to netlist subgraph
        matchlist.sort(key=lambda element: sum(
            [x not in netlist for x in self.neighbors(element.name)]))
        return matchlist

    # Algorithms to flatten netlist

    def flatten(self, depth=999):
        ''' depth = 999 helps protect against recursive subckt definitions '''
        depth = depth - 1
        for subcktinst in (x for x in self.elements if isinstance(x.mclass, SubCircuit)):
            self._replace_subckt_with_components(subcktinst)
        if any((isinstance(x.mclass, SubCircuit) for x in self.elements)) and depth > 0:
            self.flatten(depth)
        for element in self.elements:
            model = element.mclass
            if model.prefix and not element.name.startswith(model.prefix):
                element.name = f'{model.prefix}_{element.name}'

    def _replace_subckt_with_components(self, subcktinst):
        # Remove element from graph
        self.remove(subcktinst)
        # Add new elements
        for element in subcktinst.mclass.elements:
            self.add_instance(
                name=f'{subcktinst.name}_{element.name}',
                model=element.model,
                pins={
                    pin: subcktinst.pins[net] if net in subcktinst.pins else f'{subcktinst.name}_{net}' for pin, net in element.pins.items()},
                parameters={key: eval(val, {}, subcktinst.parameters)
                            for key, val in element.parameters.items()}
            )
