import json
import sys

def modify_gds(name, oname):
    red_data={}
    with open (name, 'rt') as ifile:
        data = json.load (ifile)
        red_data['header']=data['header']
        red_data['bgnlib']=[]
        for i,lib in enumerate(data['bgnlib']):
            red_data['bgnlib'].append({})
            red_data['bgnlib'][i]['time'] = lib['time']
            red_data['bgnlib'][i]['libname'] = lib['libname']
            red_data['bgnlib'][i]['units'] = lib['units']
            red_data['bgnlib'][i]['bgnstr'] = []
            #for ic, cell in enumerate(lib['bgnstr']):
            #    if 'elements' in cell and cell['strname'] in name:
            for cell in lib['bgnstr']:
                if 'elements' in cell and cell['strname'] in name:
                    block={}
                    block['time'] = cell['time']
                    block['strname'] = cell['strname']
                    block['elements'] = []
                    for element in cell['elements']:
                        if 'type' in element and element['type']=='sref':
                            pass
                        else:
                            block['elements'].append(element)
                    red_data['bgnlib'][i]['bgnstr'].append(block)

    with open (oname, 'w') as ofile:
        json.dump (red_data, ofile, indent=4)

             
def usage(prog):
    print('Usage: %s <file.gds.json> <file.gds.json>' % prog)

if __name__ == '__main__':
    if (len(sys.argv) == 3):
        modify_gds (sys.argv[1], sys.argv[2])
    else:
        usage(sys.argv[0])
        sys.exit(1)
    sys.exit(0)	
