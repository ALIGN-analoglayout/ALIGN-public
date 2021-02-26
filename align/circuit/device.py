import pydantic

class Device():

    _prefix = ''
    _pins = ()
    _parameters = {} # name : defaultval

    name = ''
    pins = {} # name: net
    parameters = {} # name : val

    @classmethod
    def add_parameters(self, parameters):
        self._parameters.update(parameters)

    def __init__(self, name, *pins, **parameters):
        self.name = name
        if self._prefix:
            assert self.name.startswith(self._prefix), f'Prefix is {self._prefix}' + \
                '. Did you try overwriting an inbuilt element with subckt?' if self._prefix == 'X' else ''
        assert len(pins) == len(self._pins), f"One or more positional arguments has not been specified. Need name and pins {self._pins}"
        self.pins = {pin: net for pin, net in zip(self._pins, pins)}
        self.parameters = self._parameters.copy()
        assert all(x in self._parameters for x in parameters.keys())
        self.parameters.update(parameters)

    def __str__(self):
        return f'{self.name} ' + \
            ' '.join(self.pins.values()) + \
            f' {self.__class__.__name__} ' + \
            ' '.join(f'{x}='+ (f'{{{y}}}' if isinstance(y, str) else f'{y}') for x, y in self.parameters.items())

