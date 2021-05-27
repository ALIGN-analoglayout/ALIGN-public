import sys
import json
import collections

def lef_from_layout_d(layout_d, fp, out_lef, cell_pin, bodyswitch, blockM, *, exclude_layers, Scale_factor, m1pitch, m2pitch):

    bbox = layout_d['bbox']

    assert (bbox[3]-bbox[1]) % m2pitch == 0, f"Cell height not a multiple of the grid {bbox}"
    assert (bbox[2]-bbox[0]) % m1pitch == 0, f"Cell width not a multiple of the grid {bbox}"

    fp.write("MACRO %s\n" % out_lef)
    fp.write("  UNITS \n")
    fp.write("    DATABASE MICRONS UNITS %s ;\n" % (1000*Scale_factor))
    fp.write("  END UNITS \n")
    fp.write("  ORIGIN 0 0 ;\n")
    fp.write("  FOREIGN %s 0 0 ;\n" % out_lef)

    fp.write("  SIZE %s BY %s ;\n" % (bbox[2], bbox[3]))
    cell_pin = list(cell_pin)

    for i in cell_pin:
        if i == 'B' and bodyswitch==0:continue
        fp.write("  PIN %s\n" % i)
        #fp.write( "    DIRECTION %s ;\n" % obj[ported'])
        fp.write("    DIRECTION INOUT ;\n")
        fp.write("    USE SIGNAL ;\n")
        fp.write("    PORT\n")
        for obj in layout_d['terminals']:
            if 'pin' in obj and obj['pin'] == i:
                fp.write("      LAYER %s ;\n" % obj['layer'])
                fp.write("        RECT %s %s %s %s ;\n" % tuple(obj['rect']))
                # Check Pins are on grid or not
                if obj['layer'] == 'M2':
                    cy = (obj['rect'][1]+obj['rect'][3])//2
                    assert cy % m2pitch == 0, f"M2 pin is not on grid {cy} {cy%m2pitch}"
                if obj['layer'] == 'M1' or obj['layer'] == 'M3':
                    cx = (obj['rect'][0]+obj['rect'][2])//2
                    assert cx % m1pitch == 0, "M1 pin is not on grid {cx} {cx%m1pitch}"

        fp.write("    END\n")
        fp.write("  END %s\n" % i)
    fp.write("  OBS\n")
    cap_layers = ['M1', 'M2', 'M3']
    for obj in layout_d['terminals']:
        if ('pin' not in obj or obj['pin'] not in cell_pin) and blockM == 0 and obj['layer'] not in exclude_layers:
            fp.write("    LAYER %s ;\n" % obj['layer'])
            fp.write("      RECT %s %s %s %s ;\n" % tuple(obj['rect']))
        elif (blockM == 1) and obj['layer'] == 'Boundary':
            for capL in cap_layers: 
                fp.write("    LAYER %s ;\n" % capL)
                fp.write("      RECT %s %s %s %s ;\n" % tuple(obj['rect']))
        else:
            pass

    fp.write("  END\n")

    fp.write("END %s\n" % out_lef)

def json_lef(input_json, out_lef, cell_pin, bodyswitch, blockM, p):

    exclude_layers = p.get_lef_exclude()

    with open(p.layerfile, "rt") as fp1:
        j1 = json.load(fp1)
    Scale_factor = j1["ScaleFactor"]

    m1pitch = p['M1']['Pitch']
    m2pitch = p['M2']['Pitch']

    with open(input_json, "rt") as fp:
        layout_d = json.load(fp)

    macro_name = out_lef + '.lef'

    with (input_json.parents[0] / macro_name).open("wt") as fp:
        lef_from_layout_d(layout_d, fp, out_lef, cell_pin, bodyswitch, blockM, exclude_layers=exclude_layers, Scale_factor=Scale_factor, m1pitch=m1pitch, m2pitch=m2pitch)
