import json

class Pdk():
    def __init__(self):
        self.pdk = {}

    def load(self, filename):
        with open(filename, "rt") as fp:
            j = json.load(fp)
        assert 'Abstraction' in j
        for layer in j['Abstraction']:
            assert layer['Layer'] not in self.pdk, f"Cannot have multiple {layer['Layer']} layers with same name"
            self.pdk[layer['Layer']] = layer
        return self.pdk
