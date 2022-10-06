"""
Created on Fri Nov  2 21:33:22 2018

@author: kunal
"""

from .types import set_context
import logging
from align.schema import constraint


logger = logging.getLogger(__name__)


class ConstraintTranslator():
    def __init__(self, ckt_data, parent_name: str, child: str = None):
        """
        Translate input constraints to hierarchial netlist
        Args:
            ckt_data (dict): all subckt graph, names and port
            parent_name (str): name of parent hierarchy
            child_name (str): name of child hierarchy
        """
        self.ckt_data = ckt_data
        self.parent_name = parent_name
        self.parent = self.ckt_data.find(parent_name)
        assert self.parent, f"Hierarchy not found, {parent_name}"
        self.parent_const = self.parent.constraints
        if child:
            self.child = child
            self.child_name = child.name
            self.child_const = self.child.constraints
        else:
            self.child = None

    def _top_to_bottom_translation(self, node_map):
        """
        Inherit constraints from parent
        Args:
            node_map (dict): dict of mapping from parent instance names to child instance names
        """

        logger.debug(f"Propagate constraints from parent: {self.parent_name} to child: {self.child_name}")

        constraints_to_propagate = [
                "HorizontalDistance",
                "VerticalDistance",
                "BlockDistance",
                "CompactPlacement",
                "ConfigureCompiler"
            ]
        constraint_exists = {c: False for c in constraints_to_propagate}
        for const in self.child_const:
            if const.constraint in constraint_exists:
                constraint_exists[const.constraint] = True

        for const in list(self.parent_const):
            if const.constraint in constraint_exists and not constraint_exists[const.constraint]:
                if isinstance(const, constraint.ConfigureCompiler) and not const.propagate:
                    continue
                else:
                    logger.debug(f"Propagating parent constraint to child: {const}")
                    self.child_const.append(const)

            if hasattr(const, "pin_current"):
                logger.debug(f"transferring charge flow constraints {const.pin_current.keys()}")
                pin_map = {}
                for pin in const.pin_current.keys():
                    parent_inst_name = pin.split('/')[0].upper()
                    parent_pin = pin.split('/')[1].upper()
                    if parent_inst_name in node_map.keys():
                        child_inst_name = node_map[parent_inst_name]
                        assert parent_pin in self.child.get_element(child_inst_name).pins
                        pin_map[pin] = child_inst_name+'/'+parent_pin
                _child_const = {x: {pin_map[pin]: current for pin, current in getattr(const, x).items() if pin in pin_map}
                                if x == "pin_current" else getattr(const, x) for x in const.__fields_set__}
                self._add_const(self.child_const, _child_const)

    def _update_const(self, new_inst_name, node_map):
        """
        Update instance names in the parent constraint

        Args:
            new_inst_name (str): name of instance of child hierarchy
        """

        def _list_replace(lst, old_value, new_value):
            for i, value in enumerate(lst):
                if value == old_value:
                    lst[i] = new_value

        logger.debug(f"update constraints of {self.parent_name} with {new_inst_name} map {node_map}")
        for const in self.parent_const:
            if hasattr(const, "instances") and not isinstance(const,constraint.GroupBlocks):
                # checking instances in the constraint and update names
                if set(const.instances) & set(node_map.keys()):
                    replace = True
                    for old_inst in node_map.keys():
                        if replace and not new_inst_name in const.instances:
                            _list_replace(const.instances, old_inst, new_inst_name)
                            replace = False
                        elif old_inst in const.instances:
                            const.instances.remove(old_inst)
                    if len(const.instances) == 0:
                        logger.debug(f"remove const belonging to new hierarchy {const}")
                    logger.debug(f"updated instances in the constraint:{const}")
            elif hasattr(const, "pairs"):
                for pair in const.pairs:
                    if len(pair) == 2:
                        if pair[0] in node_map.keys() and pair[1] in node_map.keys():
                            pair[0] = new_inst_name
                            pair.pop()
                        elif pair[0] in node_map.keys() and pair[1] not in node_map.keys():
                            pair[0] = new_inst_name
                        elif pair[1] in node_map.keys() and pair[0] not in node_map.keys():
                            pair[1] = new_inst_name
                    elif len(pair) == 1:
                        if pair[0] in node_map.keys():
                            pair[0] = new_inst_name
            elif hasattr(const, "pin_current"):
                logger.debug(f"updating charge flow constraints {const.pin_current.keys()}")
                updated_pc = {}
                remove_pins = []
                for pin, current in const.pin_current.items():
                    parent_inst_name = pin.split('/')[0].upper()
                    if parent_inst_name in node_map.keys():
                        remove_pins.append(pin)
                        child_inst_name = node_map[parent_inst_name]
                        if self.child_name:
                            new_parent_pin = self.child.get_element(child_inst_name).pins[pin.split('/')[1]]
                        else:
                            raise NotImplementedError("Groupcap does not have child hieararchy")
                        if new_inst_name+'/'+new_parent_pin in updated_pc:
                            for id, cur in enumerate(updated_pc[new_inst_name+'/'+new_parent_pin]):
                                updated_pc[new_inst_name+'/'+new_parent_pin][id] = cur + current[id]
                        else:
                            updated_pc[new_inst_name+'/'+new_parent_pin] = current

                for pin in remove_pins:
                    const.pin_current.pop(pin)
                for pin, current in updated_pc.items():
                    const.pin_current[pin] = current
            elif hasattr(const, "pins1") and const.pins1:
                replace_pins = {}
                for pin in const.pins1 + const.pins2:
                    if '/' in pin:
                        if self.child:
                            new_pin = self._get_pin_map(pin, node_map, new_inst_name)
                            if new_pin:
                                replace_pins[pin]=new_pin
                        else:
                            parent_inst_name= pin.split('/')[0]
                            if parent_inst_name in node_map.keys():
                                replace_pins[pin] = pin.replace(parent_inst_name, new_inst_name)
                for k, v in replace_pins.items():
                    for i in range(len(const.pins1)):
                        if k==const.pins1[i]:
                            const.pins1[i]=v
                        if k == const.pins2[i]:
                            const.pins2[i] = v

            elif hasattr(const, "regions"):
                for i, row in enumerate(const.regions):
                    if set(row) & set(node_map.keys()):
                        replace = True
                        for old_inst in node_map.keys():
                            if replace:
                                _list_replace(const.regions[i], old_inst, new_inst_name)
                                replace = False
                            elif old_inst in row:
                                const.regions[i].remove(old_inst)

        logger.debug(f"updated constraints of {self.parent_name} {self.parent_const}")

    def _get_pin_map(self, pin, node_map, new_inst_name):
        parent_inst_name, port = pin.split('/')
        if parent_inst_name in node_map.keys():
            child_inst_name = node_map[parent_inst_name]
            if self.child_name: #no child during renaming
                assert self.child.get_element(child_inst_name), f"child does not have instance {child_inst_name}"
                new_parent_pin = self.child.get_element(child_inst_name).pins[port]
            else:
                raise NotImplementedError("Groupcap does not have child hieararchy")
            new_pin = new_inst_name+'/'+new_parent_pin
        else:
            new_pin = None
        return new_pin

    def _add_const(self, const_list, const):
        is_append = False
        with set_context(const_list):
            if hasattr(const, "instances") and len(const.instances) > 0:
                is_append = True
            elif (
                isinstance(const, dict)
                and "instances" in const
                and len(const["instances"]) == 0
            ):
                # Modified constraint are initially of dict type
                pass
                # skipping const of zero length
            elif not hasattr(const, "instances"):
                is_append = True
            else:
                logger.debug(f"invalid constraint {const}")
            if not is_append and const in const_list:
                const_list.remove(const)
            if is_append and const not in const_list:
                logger.debug(f"constraint appended: {const}")
                const_list.append(const)
