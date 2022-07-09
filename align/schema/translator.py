"""
Created on Fri Nov  2 21:33:22 2018

@author: kunal
"""

from operator import sub
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

    def _top_to_bottom_translation(self, node_map):
        """
        Update instance names in the child constraints

        Args:
            node_map (dict): dict of mapping from parent instance names to child instance names

        """

        logger.debug(
            f"transferring constraints from top subckt: {self.parent_name} to bottom subckt: {self.child_name} "
        )

        if not self.child_const:
            with set_context(self.child_const):
                for const in list(self.parent_const):
                    if any(
                        isinstance(const, x)
                        for x in [
                            constraint.HorizontalDistance,
                            constraint.VerticalDistance,
                            constraint.BlockDistance,
                            constraint.CompactPlacement,
                        ]
                    ):
                        self.child_const.append(const)
                    elif hasattr(const, "instances") and const.constraint != "group_blocks":
                        # checking if sub hierarchy instances in const are defined
                        _child_const = {
                            x: [
                                node_map[block]
                                for block in const.instances
                                if block in node_map.keys()
                            ]
                            if x == "instances"
                            else getattr(const, x)
                            for x in const.__fields_set__
                        }
                        assert "constraint" in _child_const, f"format check failed"
                        logger.debug(f"transferred constraint instances {node_map} from {const} to {_child_const}")
                        self._add_const(self.child_const, _child_const)

        for const in list(self.parent_const):
            if hasattr(const, "pin_current"):
                logger.debug(f"transferring charge flow constraints {const.pin_current.keys()}")
                pin_map = {}
                for pin in const.pin_current.keys():
                    parent_inst_name = pin.split('/')[0].upper()
                    parent_pin = pin.split('/')[1].upper()
                    if parent_inst_name in node_map.keys():
                        child_inst_name = node_map[parent_inst_name]
                        assert parent_pin in self.child.get_element(child_inst_name).pins
                        pin_map[pin] = child_inst_name+'/'+ parent_pin
                _child_const = {x: {pin_map[pin]:current for pin, current in getattr(const,x).items() if pin in pin_map}
                                if x== "pin_current" else getattr(const, x) for x in const.__fields_set__}
                self._add_const(self.child_const, _child_const)

        if self.child_const:
            logger.debug(f"transferred constraints to {self.child_name} {self.child_const}")

    def _update_const(self, new_inst, node_map):
        """
        Update instance names in the parent constraint

        Args:
            new_inst (str): name of instance of child hierarchy
        """

        def _list_replace(lst, old_value, new_value):
            for i, value in enumerate(lst):
                if value == old_value:
                    lst[i] = new_value

        logger.debug(f"update constraints of {self.parent_name} with {new_inst}")
        for const in self.parent_const:
            if hasattr(const, "instances") and const.constraint != 'group_blocks':
                # checking instances in the constraint and update names
                if set(const.instances) & set(node_map.keys()):
                    replace = True
                    for old_inst in node_map.keys():
                        if replace:
                            _list_replace(const.instances, old_inst, new_inst)
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
                            pair[0] = new_inst
                            pair.pop()
                        elif pair[0] in node_map.keys() and pair[1] not in node_map.keys():
                            pair[0] = new_inst
                        elif pair[1] in node_map.keys() and pair[0] not in node_map.keys():
                            pair[1] = new_inst
                    elif len(pair) == 1:
                        if pair[0] in node_map.keys():
                            pair[0] = new_inst
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
                        if new_inst+'/'+new_parent_pin in updated_pc:
                            for id, cur in enumerate(updated_pc[new_inst+'/'+new_parent_pin]):
                                updated_pc[new_inst+'/'+new_parent_pin][id] = cur + current[id]
                        else:
                            updated_pc[new_inst+'/'+new_parent_pin] = current

                for pin in remove_pins:
                    const.pin_current.pop(pin)
                for pin, current in updated_pc.items():
                    const.pin_current[pin] = current
            elif hasattr(const, "regions"):
                for i, row in enumerate(const.regions):
                    if set(row) & set(node_map.keys()):
                        replace = True
                        for old_inst in node_map.keys():
                            if replace:
                                _list_replace(const.regions[i], old_inst, new_inst)
                                replace = False
                            elif old_inst in row:
                                const.regions[i].remove(old_inst)

        logger.debug(f"updated constraints of {self.parent_name} {self.parent_const}")

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
