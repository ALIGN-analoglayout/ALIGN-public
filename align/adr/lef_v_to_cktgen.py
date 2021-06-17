
from .lef_parser import LEFParser
from .verilog_parser import VerilogParser
from .pl_parser import PLParser

from .import_gds import import_gds
import pathlib


def get_placement_from_gds( top_module):
    with pathlib.Path( "tests/vga.gds.json").open("rt") as fp:
        bboxes,gds_json = import_gds(fp)


    bbox_map = { nm : bbox for (nm,bbox) in bboxes}

    print(bbox_map)

    die = bbox_map[top_module.nm]

    scale = 4
    assert all( map( lambda x: x%scale == 0, die))
    bbox = list(map( lambda x: x//scale, die))

    # TODO: placement
    
    vga = { x['strname'] : x for x in gds_json}['vga']

    srefs = [ x for x in vga['elements'] if x['type'] == 'sref']

    print( srefs)
    for sref in srefs:
        print( sref['sname'], sref['xy'], sref['strans'], sref['angle'])

    hand_placements = [
        ("C1", "Cap_10f",  [128400, 588640], 0, 0), #N
        ("C2", "Cap_10f", [631920, 588640], 32768, 180), #FN
        ("Nsw0", "Switch_NMOS_n10_X4_Y4", [24160, 588640], 0, 0), #N
        ("Nsw1", "Switch_NMOS_n10_X4_Y4", [1840, 275840], 0, 0),
        ("Nsw2", "Switch_NMOS_n10_X4_Y4", [24160, 415440], 0, 0),
        ("R0", "Res_400", [22320, 701360], 0, 180), #S
        ("R1", "Res_400", [738000, 701360], 32768, 0), #FS
        ("xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0", "CMB_4_n10_A1_B1_C2_D4", [252160, 1840], 0, 0),
        ("xM20|MN0_xM21|MN0", "DP_NMOS_n10_X5_Y4", [508160, 275840], 32768, 180), #FN
        ("xM30|MN0_xM31|MN0", "DP_NMOS_n10_X8_Y5", [584960, 415440], 32768, 180), #FN
        ("xM10|MN0_xM11|MN0", "DP_NMOS_n10_X5_Y2", [508160, 659200], 0, 180), #S
        ("xM00|MN0_xM01|MN0", "DP_NMOS_n10_X5_Y2", [508160, 731600], 0, 180) #S
        ]

    lst = []
    for (i,t,xy,trans,angle) in hand_placements:
        assert trans == 32768 or trans == 0
        assert angle == 0 or angle == 180
        tr = 'N'
        if angle == 180 and trans == 32768: #FN
            tr = 'FN'
        elif angle == 0 and trans == 32768: #FS
            tr = 'FS'
        elif angle == 180 and trans == 0: #S
            tr = 'S'

        assert xy[0] % scale == 0
        assert xy[1] % scale == 0

        lst.append( (i,t,[xy[0]//scale,xy[1]//scale],tr))

    hand_placements = lst

    return hand_placements, bbox


def convert( lef_str, verilog_str, pl_str):

    lp = LEFParser()
    lp.parse(lef_str)
    
    vp = VerilogParser()
    vp.parse(verilog_str)

    pp = PLParser()
    pp.parse(pl_str)

    assert len(vp.modules) == 1
    top_module = vp.modules[0]

    d = { 'nm' : top_module.nm, 'bbox' : [0,0,0,0]}

    lef_map = {}

    leaves = []
    for m in lp.macros:
        assert m.macroName not in lef_map
        lef_map[m.macroName] = m

        leaf = { 'template_name' : m.macroName, 'bbox' : m.bbox }
        terminals = []
        
        for pin in m.pins:
            for port in pin.ports:
                terminal = { 'net_name' : pin.nm, 'layer' : port[0], 'rect' : list(port[1]) }
                terminals.append(terminal)

        for port in m.obs.ports:
            terminal = { 'net_name' : '!kor', 'layer' : port[0], 'rect' : list(port[1]) }
            terminals.append(terminal)

        leaf['terminals'] = terminals
        leaves.append(leaf)

    d['leaves'] = leaves

    instances = []
    d['instances'] = instances

    for inst in top_module.instances:
        
        assert inst.template_name in lef_map, (inst.template_name, lef_map)
        lef_formals = { pin.nm for pin in lef_map[inst.template_name].pins }
        assert all( formal in lef_formals for (formal,actual) in inst.fa_list), (inst.fa_list, lef_formals)

        instance = { 'template_name' : inst.template_name,
                     'instance_name' : inst.instance_name}

        instance['transformation'] = { 'oX': 0, 'oY': 0, 'sX': 1, 'sY': 1}

        instance['formal_actual_map'] = \
            { formal : actual for (formal, actual) in inst.fa_list}

        instances.append( instance)

    inst_map = { x['instance_name'] : x for x in d['instances']}

    pl_placements = []
    for (nm,x,y,transform) in pp.lst:
        if transform is not None:
            assert nm in inst_map
            template_name = inst_map[nm]['template_name']
            pl_placements.append( (nm, template_name, [x, y], transform))



    if False:
        placements, die = get_placement_from_gds(top_module)        
    else:
        placements, die = pl_placements, pp.die

    print(placements)

    d['bbox'] = die

    plc_map = {}
    for tup in placements:
        (instance_name, template_name, xy, tr) = tup
        assert instance_name not in plc_map
        plc_map[instance_name] = tup
        
    
    for instance in d['instances']:
        assert instance['instance_name'] in plc_map
        (instance_name, template_name, xy, tr) = plc_map[instance['instance_name']]
        assert template_name == instance['template_name']


        new_y = int(round(xy[1]/840,0))*840
        if xy[1] != new_y:
            print('Adjusting y to be on grid', template_name, xy[1], "=>", new_y, 'delta', new_y-xy[1])
            xy[1] = new_y

        instance['transformation'] = { 'oX': xy[0], 'oY': xy[1],
                                       'sX': 1, 'sY': 1} #N

        if   tr == 'FN':
            instance['transformation']['sX'] = -1
        elif tr == 'FS':
            instance['transformation']['sY'] = -1
        elif tr == 'S':
            instance['transformation']['sX'] = -1
            instance['transformation']['sY'] = -1

    return d
