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
            if layer['Layer'].lower().startswith('m'):
                self.addMetal(**layer)
            elif layer['Layer'].lower().startswith('v'):
                self.addVia(**layer)
            else:
                self.add(**layer)
        return self.pdk

    def _check(self, parameters, **kwargs):
        assert all( x in kwargs for x in parameters), f"Entry {kwargs} missing one or more of {parameters}"
        assert all( x in parameters for x in kwargs.keys()), f"Entry {kwargs} has one or more spurious entries (Needs only {parameters})"

    def _add(self, parameters, **kwargs):
        # Guarantee one is to one mapping between parameters & kwargs
        layername = kwargs.pop('Layer')
        self.pdk[layername] = {key: None if value == 'NA' else value for key, value in kwargs.items()}

    def addMetal(self, **kwargs):
        params = ['Layer',
                  'LayerNo',
                  'Type',
                  'Direction',
                  'Pitch',
                  'Width',
                  'MinL',
                  'MaxL',
                  'End-to-End']
        assert 'Type' in kwargs
        if kwargs['Type'] == 'Power':
            params.extend(['MinW', 'MaxW'])
        self._check(params, **kwargs)
        self._add(params, **kwargs)

    def addVia(self, **kwargs):
        params = ['Layer',
                  'LayerNo',
                  'Type',
                  'Stack',
                  'SpaceX',
                  'SpaceY',
                  'WidthX',
                  'WidthY',
                  'VencA_L',
                  'VencA_H',
                  'VencP_L',
                  'VencP_H']
        self._check(params, **kwargs)
        if isinstance(kwargs['Stack'], str):
            kwargs['Stack'] = kwargs['Stack'].split('-')
        assert len(kwargs['Stack']) == 2
        self._add(params, **kwargs)

    def add(self, **kwargs):
        assert 'Layer' in kwargs, '"Layer" is required parameter for all layers in PDK abstraction'
        self._add(None, **kwargs)