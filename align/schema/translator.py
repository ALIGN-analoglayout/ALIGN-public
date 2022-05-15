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
    def __init__(self, ckt_data):
        """
        Args:
            ckt_data (dict): all subckt graph, names and port
            design_setup (dict): information from setup file
            library (list): list of library elements in dict format
            existing_generator (list): list of names of existing generators
        """
        self.ckt_data = ckt_data

    def _top_to_bottom_translation(self, top, match_dict, bottom):
        """
        Update instance names in the constraint in case they are reduced

        Args:
            top (str): name of subckt
            match_dict (dict): node mapping
        """

        logger.debug(
            f"transfering constraints from top subckt: {top} to bottom subckt: {bottom} "
        )
        assert self.ckt_data.find(bottom), f"Hierarchy not found, {bottom}"
        assert self.ckt_data.find(top), f"Hierarchy not found, {top}"
        const_list = self.ckt_data.find(top).constraints
        sub_const = self.ckt_data.find(bottom).constraints
        if not sub_const:
            with set_context(sub_const):
                for const in list(const_list):
                    if any(
                        isinstance(const, x)
                        for x in [
                            constraint.HorizontalDistance,
                            constraint.VerticalDistance,
                            constraint.BlockDistance,
                            constraint.CompactPlacement,
                        ]
                    ):
                        sub_const.append(const)
                    elif hasattr(const, "instances"):
                        # checking if sub hierarchy instances are in const defined
                        sconst = {
                            x: [
                                match_dict[block]
                                for block in const.instances
                                if block in match_dict.keys()
                            ]
                            if x == "instances"
                            else getattr(const, x)
                            for x in const.__fields_set__
                        }
                        assert "constraint" in sconst
                        # logger.debug(f"transferred constraint instances {match_dict} from {const} to {sconst}")
                        self._check_const_length(
                            self.ckt_data.find(bottom).constraints, sconst
                        )
                if sub_const:
                    logger.debug(f"transferred constraints to {bottom} {sub_const}")

    def _update_const(self, name, remove_nodes, new_inst):
        """
        Update instance names in the constraint in case they are reduced by groupblock

        Args:
            name (str): name of subckt
            G1 (graph): subckt graph
            remove_nodes (list): nodes which are being removed
        """

        def _list_replace(lst, old_value, new_value):
            for i, value in enumerate(lst):
                if value == old_value:
                    lst[i] = new_value

        logger.debug(f"update constraints of {name} :{remove_nodes} with {new_inst}")
        assert self.ckt_data.find(name), f"subckt {name} not found in graph"
        const_list = self.ckt_data.find(name).constraints
        for const in const_list:
            if hasattr(const, "instances"):
                # checking instances in the constraint and update names
                if set(const.instances) & set(remove_nodes):
                    replace = True
                    for old_inst in remove_nodes:
                        if replace:
                            _list_replace(const.instances, old_inst, new_inst)
                            replace = False
                        elif old_inst in const.instances:
                            const.instances.remove(old_inst)
                    if len(const.instances) == 0:
                        logger.debug(f"remove const belonging to new hierarchy {const}")
                    # logger.debug(f"updated instances in the constraint:{const}")
            elif hasattr(const, "pairs"):
                for pair in const.pairs:
                    if len(pair) == 2:
                        if pair[0] in remove_nodes and pair[1] in remove_nodes:
                            pair[0] = new_inst
                            pair.pop()
                        elif pair[0] in remove_nodes and pair[1] not in remove_nodes:
                            pair[0] = new_inst
                        elif pair[1] in remove_nodes and pair[0] not in remove_nodes:
                            pair[1] = new_inst
                    elif len(pair) == 1:
                        if pair[0] in remove_nodes:
                            pair[0] = new_inst
            elif hasattr(const, "pin_current"):
                updated_pc={}
                for pin,current in const.pin_current.popitems():
                    inst_name = pin.split('/')[0]
                    if inst_name in remove_nodes:
                        updated_pc[new_inst/pin.split('/')] = current
                    else:
                        updated_pc[pin] = current
            elif hasattr(const, "regions"):
                for i, row in enumerate(const.regions):
                    if set(row) & set(remove_nodes):
                        replace = True
                        for old_inst in remove_nodes:
                            if replace:
                                _list_replace(const.regions[i], old_inst, new_inst)
                                replace = False
                            elif old_inst in row:
                                const.regions[i].remove(old_inst)

        logger.debug(f"updated constraints of {name} {const_list}")

    def _check_const_length(self, const_list, const):
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
