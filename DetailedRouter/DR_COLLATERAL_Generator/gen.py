import json
import argparse

hMetals = {"metal%d" % i for i in range(2,6,2)}
vMetals = {"metal%d" % i for i in range(1,6,2)}

metals  = ["metal%d" % i for i in range(1,6)]
vias    = ["via%d"   % i for i in range(1,5)]

def generateVia( tech, v, l, u):
    
    halfSpace = "%.3f" % (160/10000)
    zero      = "%.3f" % (  0/10000)
    width1    = "%.3f" % (tech['halfWidthM'+l[-1]][0]/5000)
    width2    = "%.3f" % (tech['halfWidthM'+u[-1]][0]/5000)

    if   l in hMetals and u in vMetals:
        cutHeight = width1
        cutWidth = width2

        x1 = halfSpace
        y1 = zero
        x2 = zero
        y2 = halfSpace
    elif l in vMetals and u in hMetals:
        cutWidth = width1
        cutHeight = width2


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
    widths value={8}
  }}
  CutWidth value={9}
  CutHeight value={10}
  cutlayer value={0}
}}
""").format( v, l, u, x1, y1, x2, y2, width1, width2, cutWidth, cutHeight)

def write_collateral( tech):

    triples = zip( vias,metals[:-1],metals[1:])


    with open( "car_generators.txt", "wt") as fp:
        for (v,l,u) in triples:
            fp.write( generateVia( tech, v, l, u))

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

        for m in metals:
            minete = str(tech['halfMinETESpaceM'+m[-1]]*2)
            fp.write( "Rule name={0}_{1} type={1} value={2} layer={0}\n".format( m, "minete", minete))
        fp.write( "\n")
        for m in metals:
            minlength = str(tech['halfMinETESpaceM'+m[-1]]*2*3)
            fp.write( "Rule name={0}_{1} type={1} value={2} layer={0}\n".format( m, "minlength", minlength))

    with open( "v2_patterns.txt", "wt") as fp:
        pass

import argparse

if __name__ == "__main__":
    parser = argparse.ArgumentParser( description="Generates detailed router collateral")
    parser.add_argument( "-tf", "--technology_file", type=str, default="Process.json")

    args = parser.parse_args()

    with open( args.technology_file, "rt") as fp:
        tech = json.load( fp)
        write_collateral( tech)

