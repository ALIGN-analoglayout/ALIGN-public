import sys
import json
from collections import defaultdict

def lef_from_layout_d(layout_d, fp, out_lef, bodyswitch, blockM, *, exclude_layers, Scale_factor, m1pitch, m2pitch, mode='routing'):

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

    pins = [term['netName'] for term in layout_d['terminals'] if term['netType'] == 'pin']

    print('lef_from_layout_d', pins)
    pin_map = {}

    if mode == 'placement':
        if 'metadata' in layout_d and 'partially_routed_pins' in layout_d['metadata']:
            pin_map = layout_d['metadata']['partially_routed_pins']
        pins = list(set(pin_map.get(p, p) for p in pins))

    print('mode', mode, 'pin_map', pin_map, 'pins', pins)

    terminals_on_net = defaultdict(list)
    for obj in layout_d['terminals']:
        if obj['netType'] == 'pin':
            pin_name = obj['netName']
            pin_name = pin_map.get(pin_name, pin_name)
            terminals_on_net[pin_name].append(obj)

    for pin in pins:
        if pin == 'B' and bodyswitch==0:continue
        fp.write("  PIN %s\n" % pin)
        fp.write("    DIRECTION INOUT ;\n")
        fp.write("    USE SIGNAL ;\n")
        fp.write("    PORT\n")
        for obj in terminals_on_net[pin]:
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
        fp.write("  END %s\n" % pin)
    fp.write("  OBS\n")

    pins = set(pins)

    cap_layers = ['M1', 'M2', 'M3']
    for obj in layout_d['terminals']:
        cond = pin_map.get(obj['netName'], obj['netName']) not in pins
        if (obj['netType'] != 'pin' or cond) and blockM == 0 and obj['layer'] not in exclude_layers:
            fp.write("    LAYER %s ;\n" % obj['layer'])
            fp.write("      RECT %s %s %s %s ;\n" % tuple(obj['rect']))
        elif (blockM == 1) and obj['layer'] == 'Cboundary':
            for capL in cap_layers: 
                fp.write("    LAYER %s ;\n" % capL)
                fp.write("      RECT %s %s %s %s ;\n" % tuple(obj['rect']))
        else:
            pass

    fp.write("  END\n")

    fp.write("END %s\n" % out_lef)

def json_lef(input_json, out_lef, bodyswitch, blockM, p, *, mode='routing'):

    exclude_layers = p.get_lef_exclude()

    with open(p.layerfile, "rt") as fp1:
        j1 = json.load(fp1)
    Scale_factor = j1["ScaleFactor"]

    m1pitch = p['M1']['Pitch']
    m2pitch = p['M2']['Pitch']

    with open(input_json, "rt") as fp:
        layout_d = json.load(fp)

    if mode == 'placement':
        output_file_name = out_lef + '.placement_lef'
    else:
        output_file_name = out_lef + '.lef'
        
    with (input_json.parents[0] / output_file_name).open("wt") as fp:
        lef_from_layout_d(layout_d, fp, out_lef, bodyswitch, blockM, exclude_layers=exclude_layers, Scale_factor=Scale_factor, m1pitch=m1pitch, m2pitch=m2pitch, mode=mode)
