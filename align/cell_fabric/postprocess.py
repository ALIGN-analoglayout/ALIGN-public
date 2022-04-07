import types

import logging
logger = logging.getLogger(__name__)

from copy import deepcopy

class PostProcessor():
    def __init__(self):
        self.postprocessors = {}
        self.errors = []

    def register(self, layer, func):
        assert layer not in self.postprocessors, "Please specify only one postprocessor per layer"
        self.postprocessors[layer] = func

    @staticmethod
    def _check_valid_rect(rect):
        assert len(rect) == 4 and all(isinstance(x, int) for x in rect), f'Invalid generator output {rect}'

    def run(self, terminals):
        logger.debug("Running PostProcessor...")
        old_terminals = deepcopy(terminals)
        terminals = []
        for term in old_terminals:
            if term['layer'] in self.postprocessors:
                postprocessor_output = self.postprocessors[term['layer']](term)
                if isinstance(postprocessor_output, types.GeneratorType) or \
                   isinstance(postprocessor_output, list):
                    # Generator output is a list of terminals
                    postprocessor_output = list(postprocessor_output)
                else:
                    # Generator output is a single terminal
                    postprocessor_output = [postprocessor_output]
                logger.debug(f"postprocessor_output: {postprocessor_output}")
                
                for new_term in postprocessor_output:
                    self._check_valid_rect(new_term['rect'])
                    terminals.append(new_term)
            else:
                terminals.append(term)
        logger.debug(f"Terminals before {len(old_terminals)} after {len(terminals)}")

        if self.errors:
            logger.error( f'Found errors: POSTPROCESSING: {len(self.errors)}')

        return terminals
