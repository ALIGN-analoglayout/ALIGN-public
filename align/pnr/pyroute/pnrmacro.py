import pyparsing as pp
from geom import Point, Rect, LayerRects
from logger import logger


class Port:
    def __init__(self, tokens = []):
        self._lr = dict()
        if (tokens):
            for lr in tokens:
                for l in lr:
                    if l._layer:
                        if l._layer in self._lr:
                            for r in l._rects:
                                self._lr[l._layer].append(r)
                        else:
                            self._lr[l._layer] = l._rects[:]

    def __str__(self):
        s = ''
        for l in self._lr:
            s += ("layer : " + l)
            for r in self._lr[l]:
                s += ', '    + str(r)
        return s

class Obstacles:
    def __init__(self, tokens = []):
        self._lr = dict()
        if (tokens):
            for lr in tokens:
                for l in lr:
                    if l._layer:
                        if l._layer in self._lr:
                            for r in l._rects:
                                self._lr[l._layer].append(r)
                        else:
                            self._lr[l._layer] = l._rects[:]

    def __str__(self):
        s = ''
        for l in self._lr:
            s += ("layer : " + l)
            for r in self._lr[l]:
                s += ', '    + str(r)
        return s



class Pin:
    def __init__(self, tokens):
        self._name      = ''
        self._direction = ''
        self._ports     = []
        self._bbox      = Rect()
        if (tokens and len(tokens) >= 1):
            self._name = tokens[0].name
            self._direction = tokens[0].direction
            for p in tokens[0].ports:
                self._ports.append(p)
                for l in p._lr:
                    for r in p._lr[l]:
                        self._bbox.bloat(r)

    def __str__(self):
        s = ("name : " + str(self._name))
        s += (", dir : " + str(self._direction))
        for p in self._ports:
            s += ', ' + str(p)
        s += (", bbox : " + str(self._bbox))
        return s



class Macro:
    def __init__(self, tokens = []):
        self._name   = ''
        self._units  = 1.
        self._origin = Point()
        self._width  = 0.
        self._height = 0.
        self._pins   = dict()
        self._obs    = None

        if tokens and len(tokens) > 0:
            token = tokens[0]
            self._name = token.name
            if type(token.units[0]) == str:
                if ';' in token.units[0]:
                    self._units = int(token.units[0][0:-1])
                else:
                    self._units = int(token.units[0])
            elif token.unites: self._units = int(token.units[0])
            self._origin = token.origin[0] if token.origin else Point()
            self._width = token.width
            self._height = token.height
            for pin in token.pins:
                if pin._name and pin._name not in self._pins:
                    self._pins[pin._name] = pin
            self._obs = token.obs[0]._lr

    def __repr__(self):
        return self._name

    def __str__(self):
        s    = ("name : "   + str(self._name))
        s += (", units : "  + str(self._units))
        s += (", origin : " + str(self._origin))
        s += (", width : "  + str(self._width))
        s += (", height : " + str(self._height))
        for p in self._pins:
            s += (',\n\t' + str(p) + ':' + str(self._pins[p]))
        for l in self._obs:
            s += ("\nobs : layer : " + l)
            for r in self._obs[l]:
                s += (", " + str(r))
        return s

    def print(self):
        print(str(self))


def parseLef(lefFile = ""):
    macros = dict()
    if lefFile:
        print(f"parsing lef file : {lefFile}")
        sc_      = pp.Suppress(pp.Keyword(';'))
        macro_   = pp.Suppress(pp.Keyword("MACRO"))
        pin_     = pp.Suppress(pp.Keyword("PIN"))
        port_    = pp.Suppress(pp.Keyword("PORT"))
        obs_     = pp.Suppress(pp.Keyword("OBS"))
        units_   = pp.Suppress(pp.Keyword("UNITS"))
        origin_  = pp.Suppress(pp.Keyword("ORIGIN"))
        foreign_ = pp.Suppress(pp.Keyword("FOREIGN"))
        end_     = pp.Suppress(pp.Keyword("END"))
        dir_     = pp.Suppress(pp.Keyword("DIRECTION"))
        use_     = pp.Suppress(pp.Keyword("USE"))
        layer_   = pp.Suppress(pp.Keyword("LAYER"))
        rect_    = pp.Suppress(pp.Keyword("RECT"))
        db_      = pp.Suppress(pp.Keyword("DATABASE"))
        microns_ = pp.Suppress(pp.Keyword("MICRONS"))
        size_    = pp.Suppress(pp.Keyword("SIZE"))
        by_      = pp.Suppress(pp.Keyword("BY"))
        
        name            = pp.Word(pp.alphanums + "_")
        num             = pp.pyparsing_common.fnumber
        pointparser     = pp.Group(num("x") + num("y")).setParseAction(lambda t: Point(t[0].x, t[0].y))
        rectparser      = pp.Group(rect_ + num("llx") + num("lly") + num("urx") + num("ury") + sc_).setParseAction(lambda t: Rect(Point(t[0].llx, t[0].lly), Point(t[0].urx, t[0].ury)))
        layerrectparser = pp.Group(layer_ + name("layer") + sc_ + pp.ZeroOrMore(rectparser)("rects")).setParseAction(LayerRects)
        portparser      = pp.Group(port_ + pp.ZeroOrMore(layerrectparser) + end_).setParseAction(Port)
        pinparser       = pp.Group(pin_ + name("name") + pp.ZeroOrMore((dir_ + name + sc_)("direction") | (use_ + name + sc_)("use"))
                + pp.ZeroOrMore(portparser)("ports") + end_ + pp.Suppress(name)).setParseAction(Pin)
        foreignparser   = pp.Suppress(foreign_ + name + num + num + sc_)
        originparser    = pp.Group(origin_ + pointparser + sc_)
        obsparser       = pp.Group(obs_ + pp.ZeroOrMore(layerrectparser) + end_).setParseAction(Obstacles)
        numwithsc       = pp.Word(pp.nums + ";")
        unitparser      = pp.Group(units_ + db_ + microns_ + units_ + numwithsc("units") + end_ + units_).setParseAction(lambda t: int(t[0][0:-1]) if ';' in t[0] else t[0][:])
        macroparser     = pp.Group(macro_ + name("name") + pp.Optional(unitparser)("units")
                + pp.ZeroOrMore(originparser("origin") | foreignparser | (size_ + num("width") + by_ + num("height") + sc_))
                + pp.ZeroOrMore(pinparser)("pins") + pp.ZeroOrMore(obsparser)("obs") + end_ + name).setParseAction(Macro)
        macrosparser    = pp.ZeroOrMore(macroparser)

        try:
            tmpmacros = macrosparser.parseFile(lefFile)
        except pp.ParseException as pe:
            print(pe.markInputline())
        for m in tmpmacros:
            macros[m._name] = m
    return macros
