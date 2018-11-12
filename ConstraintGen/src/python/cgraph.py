"""
read .sp netlist and generate its annotated circuit topology graph in undirected graph representation
"""

####################################################################################################
import os, sys, argparse
import matplotlib.pyplot as plt
import networkx as nx
import pickle
import PySpice
####################################################################################################


class CGraph(nx.Graph):
    """
        Circuit Graph
            graph attributes:
                name: NAME(_CIRCUITCLASS)?
                class: CIRCUITCLASS
            node attributes
                element_type:
                    Mosfet::p, Mosfet::n, Resistor, Capacitor, Inductor, Subcircuit::subcircuit_name
                element_type-dependent sub-attributes (variable length):
                    ...

    """
    def __init__(self, **attr):
        super(CGraph, self).__init__(attr)
    
    def set_pins(self, pin_dict):
        pass

    def flatten(self):
        pass

    def __repr__(self):
        pass


class CGraphNodeAttr(object):
    def __init__(self):
        pass
    
    #def __repr__(self):
    #    return str(attr)


class CElementAttr(CGraphNodeAttr):
    """
    Transistor: nmos, pmos, diode
        (n|p, W, L)
    Resistor/Capacitance/Inductor/Mutual inductor (R, C, L, K)
        (R|L|C, value) | (K, L1_value, L2_value, K_value)
    Subcircuit: name of sub-ckt, circuit class/type
        (name|unknown)
    """
    def __init__(self, **attr):
        #super(CElementAttr, self).__init__()
        if(not 'element_type' in attr):
            self._element_type = None
        else:
            self._element_type = attr['element_type']
        self._attr = attr

    #def __repr__(self):
    #    return str(self._attr)


class CNetAttr(CGraphNodeAttr):
    """

    two/three terminal bridge (between terminals of circuit elemets)
        attibutes = [in|out|inout|internal|other|unknown, 
                    vdd|gnd|clk|analog|bias|logic|other|unknown,
                    g|d|s|b|[0-9]+|unknown]

            PIN: [in|out|inout|internal|other|unknown], default=internal

            SIGNAL_TYPE: [vdd|gnd|clk|analog|bias|logic|other|unknown]
                Power net
                    VDD/GND
                Clock net
                    clk/clkb
                Signal net
                    Analog signal (default)
                        Voltage, current
                        differential
                    Logic/digital
                        Voltage, current
                Biasing net 

            Terminal: instance_name-terminal_position
                plus/minus for two terminal elements
                g/d/s/b for mosfet
                Subckt_class_pin[i]

            Parastics
                pi-model (| t-model) 
                    (C,R,C) | (R,C,R)

    """
    pin_type = set(['in','out', 'inout', 'internal', 'unknown'])
    signal_type = set(['vdd','gnd', 'vss', 'clk', 'analog', 'bias', 'logic', 'unknown'])

    def __init__(self, **attr):
        super(CNetAttr, self).__init__()
        # ground
        if(not 'gnd' in attr):
            self._gnd = None
        else:
            self._gnd = attr['gnd']
        # pi-model or t-model RC parastic
        if(not 'parastic' in attr):
            self._parastic = None
        else:
            self._parastic = attr['parastic']
        self._attr = attr # net attributes: {'pin_type':X, 'signal_type':X, }

    def is_x(self, x, k):
        return (x==self._attr[k])

    def is_in(self):
        return self.is_x('in', 'pin_type')
    
    def is_out(self):
        return self.is_x('out', 'pin_type')
    
    def is_inout(self):
        return self.is_x('inout', 'pin_type')

    def is_pin(self):
        return self.is_in() or self.is_out() or self.is_inout()
    
    def is_unknown(self):
        return self.is_x('unknown', 'net_pin_type')

    def is_internal(self):
        return not (self.is_pin() or self.is_unknown())


class CGraphwAttr(CGraph):
    def __init__(self, cgraph_obj):
        self = cgraph_obj
        for n, d in self.nodes(data=True):
            if(d['element_type'].upper()=='NET'):
                self.nodes[n]['attr'] = CNetAttr(**d)
            else:
                self.nodes[n]['attr'] = CElementAttr(**d)
            #print(self.nodes[n])


def build_cgraph(c, name, remove_dummy=False, guess_by_name=True, add_edge_annotation=False):
    """
        c: `Circuit` instance from PySpice, can be acquired by SpiceParser.build_circuit() function
        name: name of the circuit to build a topology graph for
        remove_dummy: when True, remove dummy mos
        guess_by_name: when True, some attributes such as signal type is inferred/guessed from net/instance name
        add_edge_annotation: when True, add matching/group edge constraints to the graph

        return networkx.Graph
    """
    G = nx.Graph()
    G.graph['name'] = name
    # parse out circuit class
    #   [a-zA-Z]+[a-zA-Z0-9]*_ CIRCUITCLASS.sp
    if(name.find('_')>-1):
        G.graph['class'] = name.split('_')[-1]
    else:
        G.graph['class'] = 'UNKNOWN'
    # iterate over elements
    for e in (c.elements):
        # subcircuit or not
        if(isinstance(e, PySpice.Spice.BasicElement.SubCircuitElement)):
            #e_type = e.subcircuit_name
            e_type = 'Subcircuit::%s' % e.subcircuit_name
        else:
            e_type = type(e).__name__
        # mosfet or not
        if(e_type=='Mosfet'):
            e_type += '::' + str(e.model)[0] # e.g. Mosfet:p, for mosfet device, only take the first char to tell p/n mos
            if(remove_dummy and len(set([n.name for n in e.nodes]))==1): #remove dummy mosfets
                continue
        
        # add circuit element as node
        #print('\t' + str(type(e)) + ':' + e.name + ':', end=':')
        e_name = e.name[1:] # the first character is for SPICE 
        G.add_node(e_name, element_type=e_type)
        
        # parse out circuit element label/attribute/constraint
        #   [a-zA-Z]+[a-zA-Z0-9]*(@minvar)?(-MATCHING ELEMENTNAME)*(-GROUP NAME)?
        if(e_name.find('-')>-1):
             G.nodes[e_name]['group'] = e_name.split('-')[1:]
        else:
             G.nodes[e_name]['group'] = None
        flags = e_name.split('-')[0].split('@')[1:]
        G.nodes[e_name]['minvar'] = ('minvar' in flags)
            
        # connect elements with circuit nets
        for ii, n in enumerate(e.nodes):
            terminal_type = str("%s-%d" % (e_type, e.pins[ii].position) if e.pins[ii].name is None else e.pins[ii].name)
            if(n.name in G.nodes()):
                G.nodes[n.name]['terminal'][e_name] = terminal_type
            else:
                # add Net as node
                G.add_node(n.name, element_type='NET', terminal={e_name:terminal_type})
                # parse out net label/attribute/constraint
                #   NETNAME (_PIN TYPE)? (@SIGNAL TYPE)? (@SHIELDING FLAG)? (@LOW PARASTIC FLAG)? (-MATCHING NETNAME)?(-GROUP NAME)?
                if(n.name.find('_')>-1):
                     G.nodes[n.name]['pin'] = n.name.split('-')[0].split('@')[0].split('_')[1]
                else:
                     G.nodes[n.name]['pin'] = 'internal'
                if(n.name.find('-')>-1):
                     G.nodes[n.name]['group'] = n.name.split('-')[1:]
                else:
                     G.nodes[n.name]['group'] = None
                flags = n.name.split('-')[0].split('@')[1:]
                G.nodes[n.name]['shield'] = ('shield' in flags)
                G.nodes[n.name]['lowp'] = ('lowp' in flags)
                G.nodes[n.name]['signal'] = 'analog'
                for stype in CNetAttr.signal_type:
                    if(stype in flags):
                        G.nodes[n.name]['signal'] = stype
                if(guess_by_name and n.name in CNetAttr.signal_type):
                    G.nodes[n.name]['signal'] = n.name
            
            # add connection between edge and circuit element
            G.add_edge(e_name, n.name, edge_type=str("%s-%d" % (e_type,e.pins[ii].position) if e.pins[ii].name is None else e.pins[ii].name))

    # decouple matching from grouping
    for node in G.nodes:
        n = G.nodes[node]
        n['matching'] = None
        if('group' in n and n['group'] is not None):
            rm_idx = []
            node_names = [name.split('-')[0].split('@')[0].split('_')[0] for name in G.nodes]
            for j, gn in enumerate(n['group']):
                name = gn.split('-')[0].split('@')[0].split('_')[0]
                if(name in node_names):
                    n['matching'] = gn
                    rm_idx.append(j)
            for j in rm_idx:
                n['group'].pop(j)
            if(len(n['group'])==0):
                n['group'] = None
    
    # remove annotations (except pin info) from the name
    mapping = {n:n.split('-')[0].split('@')[0] for n in G.nodes}
    nx.relabel.relabel_nodes(G, mapping, copy=False)

    # check bipartite property
    if(not nx.algorithms.bipartite.basic.is_bipartite(G)):
        raise ValueError("the given netlist is not bipartite when transformed!")

    # add annotating edge
    if(add_edge_annotation):
        new_edges=[]
        for node in G.nodes:
            n = G.nodes[node]
            if('matching' in n and n['matching'] is not None):
                new_edges.append((node, n['matching'], "matching"))
        for e in new_edges:
            if(not e[1] in G.nodes):
                raise ValueError("%s not in G!" % e[1])
            G.add_edge(e[0], e[1], edge_type=e[2])
    
    return G


def build_cgraph_lib(ffn_netlist, dir_graph_out=None, ground=0, remove_dummy=False, dir_node_edge_list=None, dir_lib_out=None, 
                    guess_by_name=True, add_edge_annotation=False):
    """
        ffn_netlist: full file path of netlist to parse
        dir_graph_out: directory path to save the resulting circuit topology graph in yaml format
        dir_lib_out: directory path to save circuit topology graph lib in pickle format
        remove_dummy: when True, remove dummy mos
        guess_by_name: when True, some attributes such as signal type is inferred/guessed from net/instance name
        add_edge_annotation: when True, add matching/group edge constraints to the graph

        return dict (i.e. {circuit_name:networkx.Graph})
    """
    from PySpice.Spice.Parser import SpiceParser
    parser = SpiceParser(path=ffn_netlist)
    circuit = parser.build_circuit(ground=ground)
    
    cgraph_dict = {}
    top_name, ext = os.path.splitext(os.path.basename(ffn_netlist))
    G = build_cgraph(circuit, top_name, guess_by_name=guess_by_name, add_edge_annotation=add_edge_annotation)
    cgraph_dict[top_name] = G

    for c in (circuit.subcircuits):
        for e in (c.elements):
            G = build_cgraph(c, c.name, guess_by_name=guess_by_name, add_edge_annotation=add_edge_annotation)
        cgraph_dict[c.name] = G

    for name, G in cgraph_dict.items():
        if(dir_graph_out is not None):
            nx.write_yaml(G, os.path.join(dir_graph_out, "%s.yaml" % name))
        
        if(dir_node_edge_list is not None):
            node_number = {}
            with open(os.path.join(dir_node_edge_list, "%s.nodelist" % name), 'w') as f:
                for ii, n in enumerate(G.nodes()):
                    f.write("%s %d\n" % (n, ii))
                    node_number[n]=ii
            with open(os.path.join(dir_node_edge_list, "%s.edgelist" % name), 'w') as f:
                for e in G.edges():
                    f.write('%s %s\n' % (node_number[e[0]], node_number[e[1]]))

    if(dir_lib_out is not None):
        with open(os.path.join(dir_lib_out, "%s.cgraph.pkl" % top_name), 'wb') as f:
            pickle.dump(cgraph_dict, f, -1)
    return cgraph_dict


if __name__ == '__main__':
    description = "parse spice netlist and build annotated circuit topology graph"
    parser = argparse.ArgumentParser(description=description)

    parser.add_argument(
        "netlist",
        help="full path to spice netlist to parse"
    )
    parser.add_argument(
        "--add_edge_annotation",
        action='store_true',
        help="if given, add matching/group edge annotations"
    )
    parser.add_argument(
        "--dir_graph_out",
        default='./',
        help="output directory path"
    )
    parser.add_argument(
        "--plot",
        action='store_true',
        help="if given, plot the top cgraph"
    )
    parser.add_argument(
        "--with_label",
        action='store_true',
        help="if given, plot node label"
    )
    parser.add_argument(
        "--with_edge_type",
        action='store_true',
        help="if given, plot edge label"
    )
    args = parser.parse_args(sys.argv[1:])
    
    cgraph_lib = build_cgraph_lib(args.netlist, dir_graph_out=args.dir_graph_out, add_edge_annotation=args.add_edge_annotation)
    top_name, ext = os.path.splitext(os.path.basename(args.netlist))
    if(args.plot):
        G = cgraph_lib[top_name]
        X = [node for node in G.nodes if G.nodes[node]['element_type']!='NET']
        Y = [node for node in G.nodes if G.nodes[node]['element_type']=='NET']
        pos = dict()
        pos.update( (n, (1, i)) for i, n in enumerate(X) ) # put nodes from X at x=1
        pos.update( (n, (2, i)) for i, n in enumerate(Y) ) # put nodes from Y at x=2
        #nx.draw(G, pos=pos, with_labels=(args.with_label))
        nx.draw(G, pos, with_labels=(args.with_label))
        if(args.with_edge_type):
            edge_labels = nx.get_edge_attributes(G,'edge_type')
            nx.draw_networkx_edge_labels(G, pos, edge_labels)
        plt.show()
        plt.close()
        
