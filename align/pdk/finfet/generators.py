from .digital import StandardCell
from .resistor import ThinFilmResistor


def generator_class(name):
    if name.lower().startswith("dig22"):
        return StandardCell
    elif name.lower().startswith("tfr"):
        return ThinFilmResistor
    else:
        return False
