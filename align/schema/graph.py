from re import sub
import networkx
# from networkx.algorithms.structuralholes import constraint
from networkx.classes.function import subgraph
import logging
logger = logging.getLogger(__name__)

from .instance import Instance
from .subcircuit import SubCircuit, Circuit
from .types import set_context
from align.schema import instance, constraint, model


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
                try:
                    self.check_constraint_satisfiability(graph,match)
                    ret.append(match)
                except:
                    #primitives with unsatisfied constraints will not be created
                    logger.info(f"skipping match {graph.subckt.name} {match} due to unsatisfied constraints")
                    pass
        return ret
    def check_constraint_satisfiability(self,subgraph,match):
        #Check if the constraints defined at primitive stage are valid for subckt
        subckt_const = subgraph.subckt.constraints
        with set_context(self.subckt.constraints):
            for const in subckt_const:
                if const.constraint == 'symmetric_blocks':
                    t = [[self._get_key(ele,match) for ele in pair] for pair in const.pairs]
                    d = const.direction
                    x = constraint.SymmetricBlocks(direction=d, pairs=t)
                    self.subckt.constraints.append(x)
                    self.subckt.constraints.remove(x)
                    for pair in const.pairs:
                        if len(pair)==2:
                            self.match_pin_distance(pair,self.subckt.pins[0])
    def match_pin_distance(self,pair,pin):
        # Symmetric nets should have same position w.r.t gnd and power
        return True
        logger.debug(f"checking port distance")
        #TODO: focus on power pins
        pin_dist2 = []
        pin_dist1 = []
        if networkx.has_path(self, source=pin, target=pair[0]):
            pin_dist1.append(networkx.shortest_path_length(self, source=pin, target=pair[0]))
            logger.debug(f"path exist: {pin} {pair[0]} {pin_dist1}")
        if networkx.has_path(self, source=pin, target=pair[1]):
            pin_dist2.append(networkx.shortest_path_length(self, source=pin, target=pair[1]))
            logger.debug(f"path exist: {pin} {pair[1]} {pin_dist2}")
        logger.debug(f"pin distance: {pin_dist1} {pin_dist2}")
        assert sorted(pin_dist1) == sorted(pin_dist2), f"pin distance mismatch"

    def _get_key(self,val,dicta):
        for key, value in dicta.items():
            if val == value:
                return key
        return "key doesn't exist"

    def replace_matching_subgraph(self, subgraph, skip=None, node_match=None, edge_match=None):
        matches = self.find_subgraph_matches(subgraph, node_match, edge_match)
        return self._replace_matches_with_subckt(matches, subgraph.subckt, skip)

    def _replace_matches_with_subckt(self, matches, subckt, skip=None):
        assert isinstance(subckt, SubCircuit)
        new_subckt = []
        for match in matches:
            # Cannot replace as some prior transformation has made the current one invalid
            assert all(x in self.nodes for x in match)
            removal_candidates = [
                x for x, y in match.items()
                if y not in subckt.pins]
            # Cannot replace if internal node is used elsewhere in subckt (Boundary elements / nets)
            if not all(x in match for node in removal_candidates for x in self.neighbors(node)):
                continue
            # Remove nodes not on subckt boundary
            # pp = self.resolve_subckt_param(removal_candidates)
            if set(removal_candidates) & set(skip):
                continue
            # Create a dummy instance of instance of subckt
            subckt_instance = self.create_subckt_instance(subckt, match, subckt.name)
            # check dummy is existing in library
            inst_name = self.instance_counter(subckt_instance)
            # Create correct instance
            new_subckt.append(inst_name)
            logger.info(f"Creating new instance {inst_name} of subckt: {subckt.name}")
            subckt_instance = self.create_subckt_instance(subckt, match, inst_name)

            for node in removal_candidates:
                # Elements only
                if node in self.nodes and self._is_element(self.nodes[node]):
                    # Takes care of nets attached to element too
                    self.remove(self.element(node))
            assert subckt_instance not in self.elements
            pin2net_map = {pin: net for net,
                           pin in match.items() if pin in subckt.pins}
            assert all(x in pin2net_map for x in subckt.pins), (match, subckt)
            # Model may need to be copied to current library
            if subckt_instance not in self.subckt.parent:
                # self.subckt.parent.append(subckt_instance)
                with set_context(self.subckt.parent):
                    self.subckt.parent.append(SubCircuit(**subckt_instance.dict(exclude_unset=True)))
            # attach instance to current graph
            self.add_instance(
                name='X_'+inst_name,
                model=inst_name,
                pins=pin2net_map
            )
        return new_subckt
    #TODO: in future use paramaters from generator
    # HACK can also be moved to end of flow
    def create_subckt_instance(self, subckt, match, instance_name):
        with set_context(self.subckt.parent):
            subckt_instance = SubCircuit(name=instance_name,
                                pins=subckt.pins,
                                parameters=subckt.parameters)
        with set_context(subckt_instance.elements):
            for x, y in match.items():
                element = subckt.get_element(y)
                if not element:
                    continue #copying only elements
                subckt_instance.elements.append(Instance(
                    name=element.name,
                    model=self.nodes[x].get('instance').model,
                    pins=element.pins,
                    parameters=self.nodes[x].get('instance').parameters))
        return subckt_instance
    # def resolve_subckt_param(self,removal_candidates):
    #     assert len(removal_candidates) >= 1
    #     for x in removal_candidates:
    #         # Elements only
    #         if x in self.nodes and self._is_element(self.nodes[x]):
    #             if 'parameters' in locals():
    #                 parameters.update(self.nodes[x].get('instance').parameters)
    #             else:
    #                 parameters = self.nodes[x].get('instance').parameters
    #     return parameters
    # Algorithms to find & replace repeated subgraphs
    def instance_counter(self, subckt ,counter=0):
        if counter == 0:
            name = subckt.name
        else:
            name = f'{subckt.name}_{counter}'
        existing_ckt = self.subckt.parent.find(name)
        if existing_ckt:
            if subckt.pins == existing_ckt.pins and \
                subckt.parameters == existing_ckt.parameters and \
                subckt.constraints == existing_ckt.constraints:
                # logger.debug(f"Existing ckt defnition found, checking all elements")
                for x in subckt.elements:
                    if (not existing_ckt.get_element(x.name).model == x.model) or \
                        (not existing_ckt.get_element(x.name).parameters == x.parameters) or \
                            (not existing_ckt.get_element(x.name).pins == x.pins):
                        logger.info(f"multiple instance of same subcircuit found {subckt.name} {counter+1}")
                        name = self.instance_counter(subckt,counter+1)
                        break #Break after first mismatch
        return name

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
