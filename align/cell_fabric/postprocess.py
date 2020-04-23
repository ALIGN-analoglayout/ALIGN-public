import types

class PostProcessor():

    def __init__(self):
        self.postprocessors = {}

    def register(self, layer, func):
        assert layer not in self.postprocessors, "Please specify only one postprocessor per layer"
        self.postprocessors[layer] = func

    @staticmethod
    def _check_valid_rect(rect):
        assert len(rect) == 4 and all(isinstance(x, int) for x in rect), f'Invalid generator output {rect}'

    def run(self, terminals):
        worklist = [term for term in terminals if term['layer'] in self.postprocessors]
        for term in worklist:
            postprocessor_output = self.postprocessors[term['layer']](term['rect'])
            if isinstance(postprocessor_output, types.GeneratorType) or \
                isinstance(postprocessor_output[0], list):
                # Generator output is a list of rectangles
                terminals.remove(term)
                for rect in postprocessor_output:
                    self._check_valid_rect(rect)
                    terminals.append({k:v if k != 'rect' else rect for k, v in term.items()})
            else:
                # Generator output is a single rectangle
                self._check_valid_rect(postprocessor_output)
                term.update({'rect': postprocessor_output})

