
class a_class():
    pass


def a_method():
    pass


def generator_class(name):
    if name.startswith("a_"):
        return a_class
    else:
        return False
