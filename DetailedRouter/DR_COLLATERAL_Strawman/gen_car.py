
hMetals = ["metal%d" % i for i in range(2,6,2)]
vMetals = ["metal%d" % i for i in range(1,6,2)]

metals = ["metal%d" % i for i in range(1,6)]
vias = ["via%d" % i for i in range(1,5)]


def generateVia( v, l, u):
    
    if   l in hMetals and u in vMetals:
        x1 = "0.016"
        y1 = "0.000"
        x2 = "0.000"
        y2 = "0.016"
    elif l in vMetals and u in hMetals:
        x1 = "0.000"
        y1 = "0.016"
        x2 = "0.016"
        y2 = "0.000"
    else:
        assert False

    return ("""Generator name={0}_simple {{
  Layer1 value={1} {{
    x_coverage value={3}
    y_coverage value={4}
    widths value=0.040
  }}
  Layer2 value={2} {{
    x_coverage value={5}
    y_coverage value={6}
    widths value=0.040
  }}
  CutWidth value=0.040
  CutHeight value=0.040
  cutlayer value={0}
}}
""").format( v, l, u, x1, y1, x2, y2)

if __name__ == "__main__":


    triples = zip( vias,metals[:-1],metals[1:])

    with open( "car_generators.txt", "wt") as fp:
        for (v,l,u) in triples:
            fp.write( generateVia( v, l, u))
