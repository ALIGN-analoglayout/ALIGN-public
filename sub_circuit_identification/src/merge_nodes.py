# -*- coding: utf-8 -*-
"""
Created on Thu Nov 29 22:19:39 2018

@author: kunal
"""
import networkx as nx
from networkx.algorithms import isomorphism

def merge_nodes(G, hier_type, argv, matched_ports):
    """ Merges the  given nodes in argv and returns a
     reduced graph. It also returns a subgraph(not used anymore)"""

    g_copy = G.copy()
    for node in argv:
        if not G.nodes[node]:
            print("node not in graph anymore")
            return G, nx.Graph
    #print("Is input bipartite",nx.is_bipartite(G))
    assert len(argv) > 1
    #  print("Merging nodes",argv)
    new_node = ""
    ports = {}
    subgraph = nx.Graph()
    max_value = {}
    for node in argv:
        new_node += '_' + node
        subgraph.add_node(node,
                          inst_type=G.nodes[node]["inst_type"],
                          real_inst_type=G.nodes[node]["real_inst_type"],
                          ports=G.nodes[node]['ports'],
                          edge_weight=G.nodes[node]['edge_weight'],
                          values=merged_value({},G.nodes[node]['values']))

        #max_value.extend(G.nodes[node]['values'])
        max_value = merged_value(max_value, G.nodes[node]['values'])
        #if max_value.values()
        #print(G.nodes[node])
        nbr = G.neighbors(node)
        for ele in nbr:
            if ele not in subgraph.nodes():
                subgraph.add_node(ele,
                                  inst_type=G.nodes[ele]["inst_type"],
                                  net_type=G.nodes[ele]["net_type"])

            #print("adding edge b/w:",node,ele,G[node][ele]["weight"])
            subgraph.add_edge(node, ele, weight=G[node][ele]["weight"])

            if ele in ports:
                ports[ele] += G[node][ele]["weight"]
            else:
                ports[ele] = G[node][ele]["weight"]

        #G.add_edge(new_node,ele,weight=wt)
    new_node = new_node[1:]
    G.add_node(new_node,
               inst_type=hier_type,
               ports_match=matched_ports,
               values=max_value)
    #print("max_value",max_value)
    #if [val for val in max_value.values() if isinstance(val, str)]
    #    print("wrong value type",new_node)
    for pins in list(ports):
        if set(G.neighbors(pins)) <= set(argv) and G.nodes[pins]["net_type"]=='internal':
            del ports[pins]
            #print("deleting node",pins)
            G.remove_node(pins)
    for node in argv:
        G.remove_node(node)
    for pins in ports:
        G.add_edge(new_node, pins, weight=ports[pins])
        #print("new ports",pins,ports[pins])

    #nx.write_yaml(subgraph,"subgraph.yaml")
    #nx.write_yaml(g_copy,"graph.yaml")

    #print("Is output bipartite",nx.is_bipartite(G))
    #print("Is subgraph bipartite",nx.is_bipartite(G))


#    for node in g_copy:
#        print(g_copy[node])
#    for node in subgraph:
#        print(node,"subg node",subgraph.nodes[node])
#        print(node,"main node",g_copy.nodes[node])

    graph_match = isomorphism.GraphMatcher(
        g_copy,
        subgraph,
        node_match=isomorphism.categorical_node_match(['inst_type'],
                                                      ['metal', 1]))
    #    GM = isomorphism.GraphMatcher(g_copy,subgraph)

    if not graph_match.subgraph_is_isomorphic():
        print("isomorphism check fail")
    #print("checking sub graph")
    check_nodes(subgraph)

    return G, subgraph

#%%
#def merged_value(values1, values2):
#    if [param for param in values1.keys() if 'fin' in param.lower()]:
#        value = {'nfin': find_max_transistor_size(values1, values2)}
#    elif [param for param in values2.keys() if 'r' == param.lower()]:
#        value = {'res': calc_res(values2)}
#    elif [param for param in values2.keys() if 'c' == param.lower()]:
#        value = {'cap': calc_cap(values2)}
#    elif [param for param in values2.keys() if 'fin' in param.lower()]:
#        value = {'nfin': calc_total_fin(values2)}
#    else: 
#        value = calc_value(values2)
#    #print(value)
#    return value
#
#
#def find_max_transistor_size(values1, values2):
#    val_1 = calc_total_fin(values1)
#    val_2 = calc_total_fin(values1)
#    return max(val_1, val_2)
#
#
#def calc_total_fin(values):
#    total_fin = 1
#    #print(values)
#    for param, value in values.items():
#        if 'fin' in param:
#            total_fin = total_fin * int(value)
#        elif 'nf' in param:
#            total_fin = total_fin * int(value)
#        elif 'M' in param:
#            total_fin = total_fin * int(value)
#    #print("total fin", total_fin)
#    return total_fin
#
#
#def calc_res(values):
#    for param, value in values.items():
#        if 'r' in param:
#            float_value = convert_unit(value)
#    total_res = float_value
#
#    return total_res
#
#
#def calc_cap(values):
#    for param, value in values.items():
#        if 'c' in param:
#            float_value = convert_unit(value)
#    value = float_value * 1e15
#
#    return value
#
#def calc_value(values):
#    #print(values)
#    total_val =1
#    for param, value in values.items():
#        if value == '0' or  'flag' in param:
#            continue
#        elif 'l' in param:
#            length = convert_unit(value)
#            total_val = total_val *length
#        elif 'w' in param:
#            width = convert_unit(value)
#            total_val = total_val *width
#        elif 'm' == param:
#            multiplier = convert_unit(value)
#            total_val = total_val *multiplier
#        else:
#            convert_unit(value)
#       # print (param, total_val)
#    #return {'len': length , 'width':width, 'multiplier':multiplier, 'total_val': total_val } 
#    #print(length*1E9)
#    return {'total_val': int(length*1E9) } 
        
#%%
def convert_unit(value):
    #print("checking value",value)
    mult =1
    if type(value)==float or type(value)== int:
        value = value
    elif '*' in value:
        value_function = value.split('*')
        #total =1
        value = 1
        for val in value_function:
            try:
                mult = mult*int(val)
            except:
                value = val
    if isinstance(value, float) or isinstance(value, int):
        value = value
    elif 'k' in value:
        value = float(value.replace('k', ""))
        value = value * 1000
    elif 'K' in value:
        value = float(value.replace('K', ""))
        value = value * 1000
    elif 'm' in value.lower():
        value = float(value.replace('m', ""))
        value = value * 1E6
    elif 'p' in value.lower():
        value = float(value.replace('p', ""))
        value = value * 1E-12
    elif 'n' in value.lower():
        value = float(value.replace('n', ""))
        value = value * 1E-9
    elif 'u' in value.lower():
        value = float(value.replace('u', ""))
        value = value * 1E-6
    elif 'f' in value.lower():
        #value='{:.2e}'.format(float(re.sub("[^0-9]", "", value)))
        value = float(value.replace('f', ""))
        value = value * 1e-15
    else:
        try:
            value = float(value)
        except ValueError:
            print("ERROR: Parameter",value, "not defined. \
                  using value=10n. Please fix netlist")
            value = 1e-8
    #print()
    return mult*value

def check_values(values):
    for param,value in values.items():
        #print("param,value:%s,%s", param,value)
        assert(type(value)==int or type(value)==float)

def check_nodes(graph):
    """ Checking all values"""
    for node, attr in graph.nodes(data=True):
        if  not attr["inst_type"] == "net":
            check_values(attr["values"])
            
def merged_value(values1, values2):
    merged_vals={}
    if values1:
        for param,value in values1.items():
            merged_vals[param] = convert_unit(value)
    for param,value in values2.items():
        if param in merged_vals.keys():
            merged_vals[param] = max(convert_unit(value), merged_vals[param])
        else:
            merged_vals[param] = convert_unit(value)
    check_values(merged_vals)
    return merged_vals
#val1={'res': '13.6962k', 'l': '8u', 'w': '500n', 'm': '1'}
#val2 = {'res': '13.6962k', 'l': '8u', 'w': '500n', 'm': '1'}
#merged_value(val1,val2)
