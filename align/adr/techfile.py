import json


class MetalTemplate:
    def __init__(self, *, layer, name, widths, spaces, colors, stops, stop_offset):
        self.layer = layer
        self.name = name
        self.widths = widths
        self.spaces = spaces
        self.colors = colors
        self.stops = stops
        self.stop_offset = stop_offset

    def __eq__(self, that):
        return \
            self.layer == that.layer and \
            self.name == that.name and \
            self.widths == that.widths and \
            self.spaces == that.spaces and \
            self.colors == that.colors and \
            self.stops == that.stops and \
            self.stop_offset == that.stop_offset

    def __str__(self):
        result = "MetalTemplate layer=%s name=%s widths=%s spaces=%s" % (
            self.layer, self.name, (",".join(str(i) for i in self.widths)), (",".join(str(i) for i in self.spaces)))
        if self.colors:
            result += " colors=%s" % (",".join(self.colors))
        if self.stops:
            result += " stops=%s" % (",".join(str(i) for i in self.stops))
        return result


class TechFile:
    def __init__(self, fp):
        self.json = json.load(fp)
        self._metalTemplates = [MetalTemplate(**d) for d in self.json['metalTemplates']]

    def __getattr__(self, nm):
        return self.json[nm]

    @property
    def metalTemplates(self):
        return self._metalTemplates

    def write_files(self, dir, nm, bbox):
        self.write_options_file(dir + "/" + nm + "_dr_mti.txt", bbox)
        self.write_metal_template_file(dir + "/" + nm + "_dr_metal_templates.txt")

    def write_options_file(self, fn, bbox):
        with open(fn, "w") as fp:
            for mt in self.metalTemplates:
                ogd = "" if mt.stop_offset is None else f" ogdoffset_abs={mt.stop_offset}"
                fp.write(
                    f"MetalTemplateInstance template={mt.name} pgdoffset_abs=0{ogd} region={':'.join( str(i) for i in bbox)}\n")

    def write_metal_template_file(self, fn):
        with open(fn, "w") as fp:
            for mt in self.metalTemplates:
                fp.write("%s\n" % str(mt))
