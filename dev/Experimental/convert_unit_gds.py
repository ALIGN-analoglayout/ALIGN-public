import json
import sys

def modify_gds(name, mult):
    red_data={}
    with open (name, 'rt') as ifile:
        data = json.load (ifile)
        red_data['header']=data['header']
        red_data['bgnlib']=[]
        for i,lib in enumerate(data['bgnlib']):
            data['bgnlib'][i]['units'] =[unit/40 for unit in  lib['units']]
            for cell in lib['bgnstr']:
                for tt,vv in cell.items():
                    if 'elements' in tt:
                        for ele in cell['elements']:
                            for k,v in ele.items():
                                if k == "xy":
                                    xy =[]
                                    for val in v:
                                        xy.append(val*40)
                                    ele["xy"]=xy

    with open (mult+'.gds.json', 'w') as ofile:
        json.dump (data, ofile, indent=4)

             
def usage(prog):
    print('Usage: %s <file.gds.json> mult' % prog)

if __name__ == '__main__':
    if (len(sys.argv) == 3):
        modify_gds (sys.argv[1], sys.argv[2])
    else:
        usage(sys.argv[0])
        sys.exit(1)
    sys.exit(0)	
