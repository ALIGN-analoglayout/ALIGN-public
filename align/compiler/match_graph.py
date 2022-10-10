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
from flatdict import FlatDict
import hashlib
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
        self.matched_dict = {} # To avoid iterative calls (search subckt in subckt)

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
            if isinstance(const, constraint.ConfigureCompiler):
                IsDigital = const.is_digital
        return IsDigital

    def annotate(self):
        """
        Main function to creates hierarchies in the block.
        Iteratively goes through all subckts in the netlist.
        Reduce graph to a list of nodes.
        Returns:
            list: all updated circuit list
        """
        logger.debug(
            f"All  subckts: {[ckt.name for ckt in self.ckt_data if isinstance(ckt, SubCircuit)]}"
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
            else:
                self.create_hierarchy(ckt)
                logger.debug(f"Circuit after annotation: {ckt.name} {[e.name for e in ckt.elements]}")
        all_subckt = [ckt.name for ckt in self.ckt_data if isinstance(ckt, SubCircuit)]
        logger.debug(f"Subcircuits after creating primitive hiearchy {all_subckt}")
        return self.lib_names

    def create_hierarchy(self,ckt, skip_nodes=None):
        netlist_graph = Graph(ckt)
        skip_constrained = (self._is_skip(ckt) + skip_nodes) if skip_nodes else self._is_skip(ckt)
        logger.debug(f"all subckt defnition {[x.name for x in self.ckt_data if isinstance(x, SubCircuit)]}")
        logger.debug(
            f"Start matching in circuit: {ckt.name} count: {len(ckt.elements)} \
            ele: {[e.name for e in ckt.elements]} skip: {skip_nodes}"
            )
        do_not_use_lib = set()
        for const in ckt.constraints:
            if isinstance(const, constraint.DoNotUseLib):
                do_not_use_lib.update(const.libraries)
        all_matched_subckts = []
        for subckt in self.lib:
            logger.debug(f"matching circuit {subckt.name}")
            if subckt.name == ckt.name or \
                subckt.name in do_not_use_lib or \
                (subckt.name in self.matched_dict and ckt.name in self.matched_dict[subckt.name]):  # to stop searching INVB in INVB_1
                continue
            if len(subckt.elements) > 1:
                new_subckts = netlist_graph.replace_matching_subgraph(
                    Graph(subckt), skip_constrained
                )
            else:
                new_subckts = netlist_graph.replace_matching_subgraph(
                    Graph(subckt), skip_nodes
                )
            if subckt.name in self.matched_dict:
                self.matched_dict[subckt.name].extend(new_subckts)
            else:
                self.matched_dict[subckt.name] = new_subckts
            all_matched_subckts.extend(new_subckts)
        return all_matched_subckts

    def create_canonical_primitive(self, parent_subckt, const):
        parent_graph = Graph(parent_subckt)
        insts = [e for e in parent_subckt.elements if e.name in const.instances]
        def pin_id(pins):
            id = []
            repeat = {}
            for pin in sorted(pins.keys()):
                if pins[pin] not in repeat:
                    id.append(pin)
                    repeat[pins[pin]] = pin
                else:
                    id.append(repeat[pins[pin]])
            return "".join(id)
        #create unique order of instances, making it independent of unstance name
        insts = sorted(insts, key=lambda inst: pin_id(inst.pins)+'_'.join([k+':'+str(inst.parameters[k]) for k in sorted(inst.parameters.keys())]))
        inst_names = {"M"+str(i):inst for i,inst in enumerate(insts)}
        # Filter internal nets but skip internal net connected to port

        new_nets = []
        for inst in insts:
            for pin in sorted(inst.pins.keys()):
                net = inst.pins[pin]
                if net not in new_nets:
                    new_nets.append(net)

        all_pins = {pin: "P"+str(i) for i, pin in enumerate(new_nets)}
        subckt_pins = [net for net in new_nets if (not set(parent_graph.neighbors(net)).issubset(
            set(inst.name for inst in inst_names.values()))) or net in parent_subckt.pins]
        new_insts = []
        for new_inst_name, old_inst in inst_names.items():
            new_insts.append({"name": new_inst_name,
                              "model":old_inst.model,
                              "pins":{formal: all_pins[actual] for formal,actual in old_inst.pins.items()},
                              "parameters": old_inst.parameters
                              })
        all_properties = new_insts + [const.generator]
        param = FlatDict({"_":all_properties})
        arg_str = '_'.join([k+':'+str(param[k]) for k in sorted(param.keys())])
        key = f"_{str(int(hashlib.sha256(arg_str.encode('utf-8')).hexdigest(), 16) % 10**8)}"
        new_subckt_name = (const.template_name if const.template_name else 'primitive')+key
        if self.ckt_data.find(new_subckt_name):
            # Matching hash based names ensures the new subckt name is identical or different
            new_subckt = self.ckt_data.find(new_subckt_name)
            logger.info(f"identical group found {new_subckt_name} {self.ckt_data.find(new_subckt_name)}")
        else:
            # Create a subckt and add to library
            with set_context(self.ckt_data):
                new_subckt = SubCircuit(name=new_subckt_name, pins=[all_pins[pin] for pin in subckt_pins])
                if getattr(const, 'generator', None):
                    new_subckt.generator["name"] = const.generator["name"]
                    gen_const = constraint.Generator(**const.generator)
                    with set_context(parent_subckt.constraints):
                        new_subckt.constraints.append(gen_const)

                self.ckt_data.append(new_subckt)
            # Add all instances of groupblock to new subckt
            with set_context(new_subckt.elements):
                for e in new_insts:
                    new_subckt.elements.append(Instance(**e))

            # Handle any cnstraints provided to this grouped block
            if getattr(const, 'constraints', None):
                constraints_for_group = getattr(const, 'constraints')
                instance_map = {parent_inst.name: child_inst_name for child_inst_name, parent_inst in inst_names.items()}
                for child_constraint in constraints_for_group:
                    recursive_replace(getattr(child_constraint, child_constraint._instance_attribute), instance_map)
                    child_constraint._parent = new_subckt.constraints
                    with set_context(new_subckt.constraints):
                        logger.debug(f"Appended {child_constraint} to {new_subckt_name}")
                        new_subckt.constraints.append(child_constraint)

            logger.debug(f"added new hiearchy {new_subckt} based on group_block_constraint")
        # Remove elements from subckt then Add new_subckt instance
        with set_context(parent_subckt.elements):
            for e in insts:
                parent_subckt.elements.remove(e)
            X1 = Instance(
                name=const.instance_name,
                model=new_subckt_name,
                pins={all_pins[x]: x for x in subckt_pins},
            )
            parent_subckt.elements.append(X1)
        tr = ConstraintTranslator(self.ckt_data, parent_subckt.name, new_subckt)
        # Translate any constraints defined on the groupblock elements to subckt
        tr._top_to_bottom_translation(
            {parent_inst.name: child_inst_name for child_inst_name, parent_inst in inst_names.items()}
        )
        # Modify instance names in constraints after modifying groupblock
        tr._update_const(const.instance_name, {parent_inst.name: child_inst_name for child_inst_name, parent_inst in inst_names.items()})
        # Add const after removing const with single instances.
        for c in list(parent_subckt.constraints):
            tr._add_const(parent_subckt.constraints, c)

        # TODO: parent_subckt.verify()  # This call is to reset the formulae to exclude the bbox variables for removed elements

    def _group_block_const(self, parent_subckt_name):
        parent_subckt = self.ckt_data.find(parent_subckt_name)
        const_list = parent_subckt.constraints
        if not const_list:
            return
        gb_const = [
            const
            for const in parent_subckt.constraints
            if isinstance(const, constraint.GroupBlocks)
        ]

        def rename_inst(old_name, new_name):
            with set_context(parent_subckt.elements):
                inst = parent_subckt.get_element(old_name)
                assert inst, f" No instance found to rename {old_name} {[x.name for x in parent_subckt.elements]}"
                inst_new = Instance(**{k: (v if k!='name' else new_name) for k, v in inst.dict().items()})
                parent_subckt.elements.remove(inst)
                parent_subckt.elements.append(inst_new)
            tr = ConstraintTranslator(self.ckt_data, parent_subckt_name, None)
            # Modify instance names in constraints after modifying groupblock
            tr._update_const(new_name, {old_name: new_name})

        for const in gb_const:
            const_insts = [i.upper() for i in const.instances]
            ckt_ele = set([ele.name for ele in parent_subckt.elements])
            assert set(const_insts).issubset(
                ckt_ele
            ), f"Constraint instances: {const_insts} not in subcircuit {parent_subckt.name} with elements {ckt_ele}"
            if const.template_name and const.template_name.upper() in self.lib_names:
                # Create virtual hierarchies with user defined template name
                # Reusing primitives defined in ALIGN library
                child_subckt_graph = Graph([l for l in self.lib if l.name==const.template_name.upper()][0])
                skip_insts = [e.name for e in parent_subckt.elements if e.name not in const_insts]
                group_block_name = Graph(parent_subckt).replace_matching_subgraph(
                        child_subckt_graph, skip_insts)[0]
                assert group_block_name, f"a primitive name same as {group_block_name} does not match group features"
                if const.template_name.upper() in self.matched_dict.keys():
                    self.matched_dict[const.template_name.upper()].append(group_block_name)
                else:
                     self.matched_dict[const.template_name.upper()]=[group_block_name]
                auto_generated_name = [inst.name for inst in parent_subckt.elements if inst.model == group_block_name and all( i in inst.name for i in const_insts)][0]
                rename_inst(auto_generated_name, const.instance_name.upper())
                continue
            else:
                # For any new virtual hierarchy definition
                self.create_canonical_primitive(parent_subckt, const)
        logger.debug(f"reduced constraints of design {parent_subckt_name} {parent_subckt.constraints}")

        # TODO: parent_subckt.verify()  # This call is to reset the formulae to exclude the bbox variables for removed elements


    def _group_cap_const(self, parent_subckt_name):
        # TODO: merge group cap and group block
        parent_subckt = self.ckt_data.find(parent_subckt_name)
        gc_const = [
            const
            for const in parent_subckt.constraints
            if isinstance(const, constraint.GroupCaps) and len(const.instances) > 1
        ]
        if len(gc_const) > 0:
            logger.info(f"Existing GroupCaps constraint {gc_const} for subckt {parent_subckt_name}")
        else:
            return
        for const in gc_const:
            for i in range(len(const.instances)):
                const.instances[i] = const.instances[i].upper()
            const_inst = [i for i in const.instances]

            assert set(const_inst).issubset(
                set([e.name for e in parent_subckt.elements])
            ), f"const instances{const_inst} are not in subckt {parent_subckt_name}"
            # all nets connected to common centroid cap constraints
            new_pins = {}
            for i, e in enumerate(const_inst):
                sc_pins = parent_subckt.get_element(e).pins  # single cap pins
                new_pins.update({k + str(i): v for k, v in sc_pins.items()})
            cc_name = "CAP_CC_" + "_".join([str(x) for x in const.num_units])
            if not self.ckt_data.find(const.name.upper()):
                # Create a group cap model and add to library
                # Ideally create a subckt initially but did not work at PnR needs Cap names startwith C
                with set_context(self.ckt_data):
                    new_subckt = Model(
                        name=cc_name, pins=list(new_pins.keys())
                    )
                if not self.ckt_data.find(cc_name):
                    self.ckt_data.append(new_subckt)

            with set_context(parent_subckt.elements):
                for e in const_inst:
                    parent_subckt.elements.remove(parent_subckt.get_element(e))
                logger.debug(f"pins {new_pins} {new_subckt.pins}")
                X1 = Instance(
                    name=const.name.upper(),
                    model=cc_name,
                    pins=new_pins
                )
                parent_subckt.elements.append(X1)
            # Modify instance names in constraints after modifying groupblock
            tr = ConstraintTranslator(self.ckt_data, parent_subckt_name)
            tr._update_const(
                const.name.upper(), {inst: inst for inst in [const.name.upper(), *const_inst]}
            )


def recursive_replace(items, update_map):
    for idx, item in enumerate(items):
        if isinstance(item, str):
            item_upper = item.upper()
            assert item_upper in update_map
            items[idx] = update_map[item_upper]
        elif isinstance(item, list):
            recursive_replace(item, update_map)
