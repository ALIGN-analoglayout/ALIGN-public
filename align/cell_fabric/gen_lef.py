import sys
import json
import collections


def gen_lef_data(data, fp, macro_name, cell_pin, bodyswitch):
    def s(x):
        return "%.4f" % (x/10000.0)

    fp.write("MACRO %s\n" % macro_name)
    fp.write("  ORIGIN 0 0 ;\n")
    fp.write("  FOREIGN %s 0 0 ;\n" % macro_name)

    fp.write("  SIZE %s BY %s ;\n" % (s(data['bbox'][2]), s(data['bbox'][3])))

    exclude_layers = {"via0", "via1", "via2", "poly", "LISD", "SDT", "RVT",
                      "M0", "fin", "polycon", "GCUT", "active", "nselect", "pselect", "nwell"}

# O(npins * nsegments) algorithm. Could be O(npins + nsegments) FIX!

    for i in cell_pin:
        if i == 'B' and bodyswitch==0:continue
        fp.write("  PIN %s\n" % i)
        #fp.write( "    DIRECTION %s ;\n" % obj['ported'])
        fp.write("    DIRECTION INOUT ;\n")
        fp.write("    USE SIGNAL ;\n")
        fp.write("  PORT\n")
        for obj in data['terminals']:
            if 'pin' in obj:
                if obj['pin'] == i:
                    fp.write("      LAYER %s ;\n" % obj['layer'])
                    fp.write("        RECT %s %s %s %s ;\n" %
                             tuple([s(x) for x in obj['rect']]))
        fp.write("    END\n")
        fp.write("  END %s\n" % i)

    fp.write("  OBS\n")
    for obj in data['terminals']:
        if ('pin' not in obj or obj['pin'] not in cell_pin) and obj['layer'] not in exclude_layers:
            fp.write("    LAYER %s ;\n" % obj['layer'])
            fp.write("      RECT %s %s %s %s ;\n" %
                     tuple([s(x) for x in obj['rect']]))
    fp.write("  END\n")

    fp.write("END %s\n" % macro_name)


def gen_lef_json_fp(json_fp, lef_fp, macro_name, cell_pin, bodyswitch):
    gen_lef_data(json.load(json_fp), lef_fp, macro_name, cell_pin, bodyswitch)


def gen_lef_json(json_fn, lef_fn, macro_name, cell_pin, bodyswitch):
    with open(json_fn, "rt") as json_fp, open(lef_fn, "wt") as lef_fp:
        gen_lef_json_fp(json_fp, lef_fp, macro_name, cell_pin)


def json_lef(input_json, out_lef, cell_pin, bodyswitch, blockM, p):

    exclude_layers = p.get_lef_exclude()

    macro_name = out_lef + '.lef'

    def s(x):
        return "%.4f" % (x/10000.0)
    # Start: This part converting all negative coordinates into positive
    with open(input_json, "rt") as fp:
        j = json.load(fp, object_pairs_hook=collections.OrderedDict)

        for i in range(4):
            j['bbox'][i] *= 10

        assert (j['bbox'][3]-j['bbox'][1]
                ) % p['M2']['Pitch'] == 0, f"Cell height not a multiple of the grid {j['bbox']}"
        assert (j['bbox'][2]-j['bbox'][0]
                ) % p['M1']['Pitch'] == 0, f"Cell width not a multiple of the grid {j['bbox']}"

        for obj in j['terminals']:
            for i in range(4):
                obj['rect'][i] *= 10

    with open(input_json, "wt") as fp:
        fp.write(json.dumps(j, indent=2) + '\n')

    # End:

    with open(input_json, "rt") as fp:
        j = json.load(fp)

    with open(input_json.parents[0] / macro_name, "wt") as fp:

        fp.write("MACRO %s\n" % out_lef)
        fp.write("  ORIGIN 0 0 ;\n")
        fp.write("  FOREIGN %s 0 0 ;\n" % out_lef)

        fp.write("  SIZE %s BY %s ;\n" % (s(j['bbox'][2]), s(j['bbox'][3])))
        cell_pin = list(cell_pin)

        for i in cell_pin:
            if i == 'B' and bodyswitch==0:continue
            fp.write("  PIN %s\n" % i)
            #fp.write( "    DIRECTION %s ;\n" % obj['ported'])
            fp.write("    DIRECTION INOUT ;\n")
            fp.write("    USE SIGNAL ;\n")
            fp.write("    PORT\n")
            for obj in j['terminals']:
                if 'pin' in obj and obj['pin'] == i:
                    fp.write("      LAYER %s ;\n" % obj['layer'])
                    fp.write("        RECT %s %s %s %s ;\n" %
                             tuple([s(x) for x in obj['rect']]))
                    # Check Pins are on grid or not
                    if obj['layer'] == 'M2':
                        cy = (obj['rect'][1]+obj['rect'][3])//2
                        assert cy % p['M2']['Pitch'] == 0, (
                            f"M2 pin is not on grid {cy} {cy%84}")
                    if obj['layer'] == 'M1' or obj['layer'] == 'M3':
                        cx = (obj['rect'][0]+obj['rect'][2])//2
                        assert cx % p['M1']['Pitch'] == 0, (
                            f"M1 pin is not on grid {cx} {cx%80}")

            fp.write("    END\n")
            fp.write("  END %s\n" % i)
        fp.write("  OBS\n")
        cap_layers = ['M1', 'M2', 'M3']
        for obj in j['terminals']:
            if ('layer' in obj and obj['layer'] == "Nwell") :
                fp.write("    LAYER %s ;\n" % obj['layer'])
                fp.write("      RECT %s %s %s %s ;\n" %
                         tuple([s(x) for x in obj['rect']]))
            if ('terminal' in obj and ("B" in obj['terminal'] or "G" in obj['terminal'])) and obj['layer'] == "V0":
                if ("B" in obj['terminal']):
                    fp.write("    LAYER %s ;\n" % "V0_tap")
                if ("G" in obj['terminal']):
                    fp.write("    LAYER %s ;\n" % "V0_active")
                fp.write("      RECT %s %s %s %s ;\n" %
                         tuple([s(x) for x in obj['rect']]))
            if ('pin' not in obj or obj['pin'] not in cell_pin) and blockM == 0 and obj['layer'] not in exclude_layers:
                fp.write("    LAYER %s ;\n" % obj['layer'])
                fp.write("      RECT %s %s %s %s ;\n" %
                         tuple([s(x) for x in obj['rect']]))
            elif (blockM == 1) and obj['layer'] == 'Boundary':
                for capL in cap_layers: 
                    fp.write("    LAYER %s ;\n" % capL)
                    fp.write("      RECT %s %s %s %s ;\n" %
                             tuple([s(x) for x in obj['rect']]))
            else:
                pass

        fp.write("  END\n")

        fp.write("END %s\n" % out_lef)
