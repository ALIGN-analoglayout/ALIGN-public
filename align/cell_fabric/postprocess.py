class PostProcessor():

    def __init__(self):
        self.postprocessors = {}

    def register(self, layer, func):
        assert layer not in self.postprocessors, "Please specify only one postprocessor per layer"
        self.postprocessors[layer] = func

    def run(self, terminals):
        for term in terminals:
            if term['layer'] in self.postprocessors:
                term.update({'rect': self.postprocessors[term['layer']](term['rect'])})
        return terminals

