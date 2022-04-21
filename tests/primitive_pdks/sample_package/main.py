
class abc():
    pass


def generator_class(name):
    if name.startswith("abc"):
        return abc
    else:
        return False
