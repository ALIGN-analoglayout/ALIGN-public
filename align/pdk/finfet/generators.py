from .digital import StandardCells


def generator_class(name):
    if name.lower().startswith("dig22"):
        return StandardCells
    else:
        return False
