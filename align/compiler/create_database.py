#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan 15 10:38:14 2021

@author: kunal001
"""
from ..schema.hacks import HierDictNode
from align.schema.graph import Graph

import logging
logger = logging.getLogger(__name__)


class CreateDatabase:
    def __init__(self, ckt_parser, const_parse):
        self.ckt_data = {}
        self.const_parse = const_parse
        self.ckt_parser = ckt_parser

    def read_inputs(self, name: str):
        """
        read circuit graphs
        """

        logger.debug("Merging nested graph hierarchies to dictionary: ")
        self.const_parse.annotate_user_constraints(self.ckt_parser.library.find(name))
        logger.debug(f"read graph {self.ckt_data}")
        #TODO remove redundant library model
        return self.ckt_parser.library

