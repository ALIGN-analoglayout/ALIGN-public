import json
import sys

def create_lef_boundry(x,y):
    x=int(x)
    y=int(y)
    bound_element={"type" : "boundary",
                    "layer": 150,
                    "datatype": 2,
                    "xy" : [0,0,0,y,x,y,x,0,0,0]
                    }
    return bound_element

def modify_gds(name, lef_name,extra):
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
            block={}
            for cell in lib['bgnstr']:
                if cell['strname'] in name:
                    block=cell
                    block['strname'] = lef_name 
                    block['elements'].append(extra)
                else:
                    red_data['bgnlib'][i]['bgnstr'].append(cell)
            red_data['bgnlib'][i]['bgnstr'].append(block)


    with open (lef_name+'.gds.json', 'w') as ofile:
        json.dump (red_data, ofile, indent=4)

             
def usage(prog):
    print('Usage: %s <file.gds.json> <new_name> x y' % prog)

if __name__ == '__main__':
    if (len(sys.argv) == 5):
        extra=create_lef_boundry(sys.argv[3],sys.argv[4])
        modify_gds (sys.argv[1], sys.argv[2],extra)
    else:
        usage(sys.argv[0])
        sys.exit(1)
    sys.exit(0)	
