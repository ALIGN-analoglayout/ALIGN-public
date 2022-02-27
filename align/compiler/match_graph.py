# -*- coding: utf-8 -*-
"""
Created on Fri Nov  2 21:33:22 2018

@author: kunal
"""

from align.schema import Model, SubCircuit, Instance
from ..schema.types import set_context
import logging
from ..schema import constraint
from align.schema.graph import Graph
from align.schema import ConstraintTranslator
logger = logging.getLogger(__name__)


class Annotate:
    """
    Creates hierarchies in the graph based on a library or user defined groupblock constraint
    Boundries (clk,digital, etc) are defined from constraints
    """

    def __init__(self, ckt_data, primitive_library):
        """
        Args:
            ckt_data (dict): all subckt information
            library (list): template library to match
        """
        self.ckt_data = ckt_data
        self.lib = primitive_library
        self.lib_names = [lib_ele.name for lib_ele in primitive_library]

    def _is_skip(self, ckt):
        di_const = [
            const.instances
            for const in ckt.constraints
            if isinstance(const, constraint.DoNotIdentify)
        ]
        # Changing 2D list to 1D list
        if len(di_const) > 0:
            di_const = [x for y in di_const for x in y]
        return di_const

    def _is_digital(self, ckt):
        IsDigital = False
        for const in ckt.constraints:
            if isinstance(const, constraint.IsDigital):
                IsDigital = const.isTrue
        return IsDigital

    def annotate(self):
        """
        Main function to creates hierarchies in the block
        iterativily goes through all subckts in the netlist
        Reduce graph to a list of nodes
        Returns:
            list: all updated circuit list
        """
        logger.debug(
            f"ALl  subckt:{[ckt.name for ckt in self.ckt_data if isinstance(ckt, SubCircuit)]}"
        )

        # names = list(self.ckt_data)
        for ckt in self.ckt_data:
            if isinstance(ckt, SubCircuit):
                circuit_name = ckt.name
                self._group_block_const(circuit_name)
                self._group_cap_const(circuit_name)

        logger.debug(
            f"All subckt after grouping:{[ckt.name for ckt in self.ckt_data if isinstance(ckt, SubCircuit)]}"
        )

        traversed = []  # libray gets appended, so only traverse subckt once
        temp_match_dict = {}  # To avoid iterative calls (search subckt in subckt)
        for ckt in self.ckt_data:
            if not isinstance(ckt, SubCircuit):
                logger.debug(f"skip annotation for model {ckt.name}")
                continue
            elif self._is_digital(ckt):
                logger.debug(f"skip annotation for digital circuit {ckt.name}")
                continue
            elif [True for const in ckt.constraints if isinstance(const, constraint.Generator)]:
                logger.debug(f"skip annotation for circuit {ckt.name} with available generators {ckt.constraints}")
                continue
            elif ckt.name in traversed:
                logger.debug(f"Finished annotation for circuit circuit {ckt.name}")
                continue
            else:
                netlist_graph = Graph(ckt)
                skip_nodes = self._is_skip(ckt)
                logger.debug(f"all subckt defnition {[x.name for x in self.ckt_data if isinstance(x, SubCircuit)]}")
                logger.debug(
                    f"Start matching in circuit: {ckt.name} count: {len(ckt.elements)} \
                    ele: {[e.name for e in ckt.elements]} traversed: {traversed} skip: {skip_nodes}"
                )
                do_not_use_lib = set()
                for const in ckt.constraints:
                    if isinstance(const, constraint.DoNotUseLib):
                        do_not_use_lib.update(const.libraries)
                traversed.append(ckt.name)
                for subckt in self.lib:
                    logger.debug(f"matching circuit {subckt.name}")

                    if subckt.name == ckt.name or \
                       subckt.name in do_not_use_lib or \
                       (subckt.name in temp_match_dict and ckt.name in temp_match_dict[subckt.name]):  # to stop searching INVB in INVB_1
                        continue
                    new_subckts = netlist_graph.replace_matching_subgraph(
                        Graph(subckt), skip_nodes
                    )
                    if subckt.name in temp_match_dict:
                        temp_match_dict[subckt.name].extend(new_subckts)
                    else:
                        temp_match_dict[subckt.name] = new_subckts
                logger.debug(f"Circuit after annotation: {ckt.name} {[e.name for e in ckt.elements]}")
        all_subckt = [ckt.name for ckt in self.ckt_data if isinstance(ckt, SubCircuit)]
        logger.debug(f"Subcircuits after creating primitive hiearchy {all_subckt}")
        return self.lib_names

    def _remove_group_const(self, subckt, rm_const):
        with set_context(subckt.constraints):
            start_count = len(subckt.constraints)
            for const in rm_const:
                subckt.constraints.remove(const)
            assert len(subckt.constraints) == start_count - len(rm_const)

    def _group_block_const(self, name):
        subckt = self.ckt_data.find(name)
        const_list = subckt.constraints
        pwr = list()
        gnd = list()
        clk = list()
        for const in subckt.constraints:
            if isinstance(const, constraint.PowerPorts):
                pwr.extend(const.ports)
            elif isinstance(const, constraint.GroundPorts):
                gnd.extend(const.ports)
            elif isinstance(const, constraint.ClockPorts):
                clk.extend(const.ports)
        if not const_list:
            return
        gb_const = [
            const
            for const in subckt.constraints
            if isinstance(const, constraint.GroupBlocks)
        ]
        self._remove_group_const(subckt, gb_const)
        tr = ConstraintTranslator(self.ckt_data)
        for const in gb_const:
            assert self.ckt_data.find(const.name.upper()) is None, "Already existing subckt with this name, please provide different name to const"
            const_inst = [i.upper() for i in const.instances]
            ckt_ele = set([ele.name for ele in subckt.elements])
            assert set(const_inst).issubset(
                ckt_ele
            ), f"Constraint instances: {const_inst} not in subcircuit {subckt.name}"
            # ac_nets : all nets connected to group block instances
            ac_nets = [
                ele.pins.values() for ele in subckt.elements if ele.name in const_inst
            ]
            ac_nets = set([x for y in ac_nets for x in y])
            # Filter internal nets but skip internal net connected to port
            ac_nets = [
                net
                for net in ac_nets
                if any(
                    net in ele.pins.values()
                    for ele in subckt.elements
                    if ele.name not in const_inst
                )
            ] + list(ac_nets & set(subckt.pins))
            ac_nets = list(set(ac_nets))
            pwr = list(set(pwr) & set(ac_nets))
            gnd = list(set(gnd) & set(ac_nets))
            clk = list(set(clk) & set(ac_nets))

            logger.debug(
                f"Grouping instances {const_inst} in subckt {const.name.upper()} pins: {ac_nets}"
            )
            # Create a subckt and add to library
            with set_context(self.ckt_data):
                new_subckt = SubCircuit(name=const.name.upper(), pins=ac_nets)
                self.ckt_data.append(new_subckt)
            # Add all instances of groupblock to new subckt
            with set_context(new_subckt.elements):
                for e in const_inst:
                    new_subckt.elements.append(subckt.get_element(e))
            # Remove elements from subckt then Add new_subckt instance
            inst_name = "X_" + const.name.upper() + "_" + "_".join(const_inst)
            with set_context(subckt.elements):
                for e in const_inst:
                    subckt.elements.remove(subckt.get_element(e))
                X1 = Instance(
                    name=inst_name,
                    model=const.name.upper(),
                    pins={x: x for x in ac_nets},
                )
                subckt.elements.append(X1)
            # Translate any constraints defined on the groupblock elements to subckt
            tr._top_to_bottom_translation(
                name, {inst: inst for inst in const_inst}, const.name
            )
            # Modify instance names in constraints after modifying groupblock
            tr._update_const(name, [const.name.upper(), *const_inst], inst_name)
        # Removing const with single instances.
        for c in list(self.ckt_data.find(name).constraints):
            tr._check_const_length(self.ckt_data.find(name).constraints, c)
        logger.debug(f"reduced constraints of design {name} {self.ckt_data.find(name).constraints}")

    def _group_cap_const(self, name):
        # TODO: merge group cap and group block
        subckt = self.ckt_data.find(name)
        gc_const = [
            const
            for const in subckt.constraints
            if isinstance(const, constraint.GroupCaps) and len(const.instances) > 1
        ]
        if len(gc_const) > 0:
            logger.info(f"Existing GroupCaps constraint {gc_const} for subckt {name}")
        else:
            return
        tr = ConstraintTranslator(self.ckt_data)
        for const in gc_const:
            for i in range(len(const.instances)):
                const.instances[i] = const.instances[i].upper()
            const_inst = [i for i in const.instances]

            assert set(const_inst).issubset(
                set([e.name for e in subckt.elements])
            ), f"const instances{const_inst} are not in subckt {name}"
            # all nets connected to common centroid cap constraints
            new_pins = {}
            for i, e in enumerate(const_inst):
                sc_pins = subckt.get_element(e).pins  # single cap pins
                new_pins.update({k + str(i): v for k, v in sc_pins.items()})
            cc_name = "CAP_CC_" + "_".join([str(x) for x in const.num_units])
            if not self.ckt_data.find(const.name.upper()):
                # Create a group cap model and add to library
                # Ideally create a subckt initially but did not work at PnR needs Cap names startwith C
                if self.ckt_data.find(cc_name):
                    with set_context(self.ckt_data):
                        new_subckt = Model(
                            name=cc_name, pins=list(new_pins.keys())
                        )
                        self.ckt_data.append(new_subckt)

            with set_context(subckt.elements):
                for e in const_inst:
                    subckt.elements.remove(subckt.get_element(e))
                logger.debug(f"pins {new_pins} {new_subckt.pins}")
                X1 = Instance(
                    name=const.name.upper(),
                    model=cc_name,
                    pins=new_pins
                )
                subckt.elements.append(X1)
            # Modify instance names in constraints after modifying groupblock
            tr._update_const(
                name, [const.name.upper(), *const_inst], const.name.upper()
            )

