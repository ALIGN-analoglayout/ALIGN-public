#!/usr/bin/env python

import json

class MetalTemplate:
  def __init__( self, *, layer, name, widths, spaces, colors):
    self.layer = layer
    self.name = name
    self.widths = widths
    self.spaces = spaces
    self.colors = colors

  def __eq__( self, that):
    return self.layer == that.layer and self.name == that.name and self.widths == that.widths and self.spaces == that.spaces and self.colors == that.colors

  def __str__( self):
    result = "MetalTemplate layer=%s name=%s widths=%s spaces=%s" % ( self.layer, self.name, (",".join( str(i) for i in self.widths)), (",".join( str(i) for i in self.spaces)))
    if self.colors:
      result += " colors=%s" % (",".join( c for c in self.colors))
    return result


class TechFile:
  def __init__( self, fn):
    with open( fn, 'rt') as fp:
      self.json = json.load( fp)

  def __getattr__( self, nm):
    return self.json[nm]

  # @property
  # def pitchDG( self):
  #   return self.json['pitchDG']

  # @property
  # def dgPerRow( self):
  #   return self.json['dgPerRow']

  # @property
  # def pitchPoly( self):
  #   return self.json['pitchPoly']

  # @property
  # def pitchM1( self):
  #   return self.json['pitchM1']

  # @property
  # def halfWidthM1( self):
  #   return self.json['halfWidthM1']

  # @property
  # def halfMinETESpaceM1( self):
  #   return self.json['halfMinETESpaceM1']

  # @property
  # def halfWidthM3( self):
  #   return self.json['halfWidthM3']

  # @property
  # def halfWidthM4( self):
  #   return self.json['halfWidthM4']

  # @property
  # def halfXGRGrid( self):
  #   return self.json['halfXGRGrid']

  # @property
  # def halfYGRGrid( self):
  #   return self.json['halfYGRGrid']

  @property
  def metalTemplates( self):
    return [ MetalTemplate( layer=d['layer'], name=d['name'], widths=d['widths'], spaces=d['spaces'], colors=d['colors']) for d in self.json['metalTemplates']]

  def write_files( self, dir, nm):
    self.write_options_file( dir + "/" + nm + "_dr_mti.txt")
    self.write_metal_template_file( dir + "/" + nm + "_dr_metal_templates.txt")

  def write_options_file( self, fn):
    with open( fn, "w") as fp:
#      fp.write( "MetalTemplateInstance template=adt_m2 pgoffset_abs=0 region=%s\n" % self.bbox)
      pass

  def write_metal_template_file( self, fn):
    with open( fn, "w") as fp:
      for mt in self.metalTemplates:
        fp.write( "%s\n" % str(mt) )
