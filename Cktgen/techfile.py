#!/usr/bin/env python

import json

class MetalTemplate:
  def __init__( self, *, layer, name, widths, spaces, colors, stops, stop_offset):
    self.layer = layer
    self.name = name
    self.widths = widths
    self.spaces = spaces
    self.colors = colors
    self.stops  = stops
    self.stop_offset = stop_offset

  def __eq__( self, that):
    return self.layer == that.layer and self.name == that.name and self.widths == that.widths and self.spaces == that.spaces and self.colors == that.colors

  def __str__( self):
    result = "MetalTemplate layer=%s name=%s widths=%s spaces=%s" % ( self.layer, self.name, (",".join( str(i) for i in self.widths)), (",".join( str(i) for i in self.spaces)))
    if self.colors:
      result += " colors=%s" % (",".join( self.colors))
    result += " stops=%s" % (",".join( str(i) for i in self.stops))
    return result


class TechFile:
  def __init__( self, fp):
    self.json = json.load( fp)
    self._metalTemplates = [ MetalTemplate( layer=d['layer'], name=d['name'], widths=d['widths'], spaces=d['spaces'], colors=d['colors'], stops=d['stops'], stop_offset=d['stop_offset']) for d in self.json['metalTemplates']]

  def __getattr__( self, nm):
    return self.json[nm]

  @property
  def metalTemplates( self):
    return self._metalTemplates

  def write_files( self, dir, nm, bbox):
    self.write_options_file( dir + "/" + nm + "_dr_mti.txt", bbox)
    self.write_metal_template_file( dir + "/" + nm + "_dr_metal_templates.txt")

  def write_options_file( self, fn, bbox):
    with open( fn, "w") as fp:
      for mt in self.metalTemplates:
        fp.write( "MetalTemplateInstance template=%s pgdoffset_abs=0 ogdoffset_abs=%d region=%s\n" % (mt.name, mt.stop_offset, (':'.join( str(i) for i in bbox))))

  def write_metal_template_file( self, fn):
    with open( fn, "w") as fp:
      for mt in self.metalTemplates:
        fp.write( "%s\n" % str(mt) )
