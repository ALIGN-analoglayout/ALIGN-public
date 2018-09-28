import json
import argparse

hMetals = {"metal%d" % i for i in range(2,6,2)}
vMetals = {"metal%d" % i for i in range(1,6,2)}

metals  = ["metal%d" % i for i in range(1,6)]
vias    = ["via%d"   % i for i in range(1,5)]

def generateVia( v, l, u):
    
    halfSpace = "%.3f" % (160/10000)
    zero      = "%.3f" % (  0/10000)
    width     = "%.3f" % (400/10000)

    if   l in hMetals and u in vMetals:
        x1 = halfSpace
        y1 = zero
        x2 = zero
        y2 = halfSpace
    elif l in vMetals and u in hMetals:
        x1 = zero
        y1 = halfSpace
        x2 = halfSpace
        y2 = zero
    else:
        assert False

    return ("""Generator name={0}_simple {{
  Layer1 value={1} {{
    x_coverage value={3}
    y_coverage value={4}
    widths value={7}
  }}
  Layer2 value={2} {{
    x_coverage value={5}
    y_coverage value={6}
    widths value={7}
  }}
  CutWidth value={7}
  CutHeight value={7}
  cutlayer value={0}
}}
""").format( v, l, u, x1, y1, x2, y2, width)

if __name__ == "__main__":
    triples = zip( vias,metals[:-1],metals[1:])

    with open( "Process.json", "rt") as fp:
        tech = json.load( fp)

    with open( "car_generators.txt", "wt") as fp:
        for (v,l,u) in triples:
            fp.write( generateVia( v, l, u))

    with open( "arch.txt", "wt") as fp:
        fp.write( """Option name=gr_region_width_in_poly_pitches value={0}
Option name=gr_region_height_in_diff_pitches value={0}
""".format( tech['halfXGRGrid']*2, tech['halfYGRGrid']*2))

    def emitLayer( fp, layer, level, types=None, pgd=None, pitch=None, cLayers=None):
        fp.write( "Layer name=%s" % layer)
        if pgd is not None:
            fp.write( " pgd=%s" % pgd)
        fp.write( " level=%d {\n" % level)
        if types is not None:
            for ty in types:
                fp.write( "   Type value=%s\n" % ty)
        if pitch is not None:
            fp.write( "   Technology pitch=%d\n" % pitch)
        if cLayers is not None:
            for ly in cLayers:
                fp.write( "   ElectricallyConnected layer=%s\n" % ly)
        fp.write( "}\n")

    with open( "layers.txt", "wt") as fp:
        emitLayer( fp, "diffusion", 0, types=["diffusion"],    pgd="hor", pitch=tech['pitchDG'])
        emitLayer( fp, "wirepoly",  1, types=["wire","poly"],  pgd="ver", pitch=tech['pitchPoly'])

        def dir( m):
            if m in vMetals:
                return "ver"
            elif m in hMetals:
                return "hor"
            else:
                assert False, m

        lCount = 2
        for i in range(len(metals)):
            m = metals[i]
            if i == 0:
                emitLayer( fp, m, lCount, types=["wire","metal"], pgd=dir(m), cLayers=vias[i:i+1])
            elif i < len(vias):
                emitLayer( fp, m, lCount, types=["wire","metal"], pgd=dir(m), cLayers=vias[i-1:i+1])
            else:
                emitLayer( fp, m, lCount, types=["wire","metal"], pgd=dir(m), cLayers=vias[i-1:i])
            lCount += 1
            if i < len(vias):
                 emitLayer( fp, vias[i], lCount, types=["via"], cLayers=metals[i:i+2])
                 lCount += 1


    with open( "design_rules.txt", "wt") as fp:
        minete = str(720)
        for m in metals:
            fp.write( "Rule name={0}_{1} type={1} value={2} layer={0}\n".format( m, "minete", minete))
        fp.write( "\n")
        minlength = str(3*720)
        for m in metals:
            fp.write( "Rule name={0}_{1} type={1} value={2} layer={0}\n".format( m, "minlength", minlength))

    with open( "v2_patterns.txt", "wt") as fp:
        pass
