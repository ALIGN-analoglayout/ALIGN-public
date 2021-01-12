import json
import matplotlib.pyplot as plt

def read_data():
    read_file = "global_router_plt.json"
    data = json.load(open(read_file,'r'))
    global_route = data["Glbaol_Routes"]
    Gcell = data["Gcell"]
    blocks = data["Blocks"]
    node_box = data["Cell box"]
    return global_route,Gcell,blocks,node_box

def plot_global_routing(global_routr,Gcell,blocks,node_box,name):
    
    plt.figure()
    
    plot_box(node_box['LLx'], node_box['LLy'],node_box['URx'],node_box['URy'],'r')
    
    for tile in Gcell:
        plot_dot(tile['x'],tile['y'],'k')
    
    for net in global_routr:
    
        if net['name']!=name:
            continue
    
        for path in net['global_path']:
            plot_line(path['llx'],path['lly'],path['urx'],path['ury'],'r')
        
        for terminal in net['terminals']:
            plot_dot(terminal['x'],terminal['y'],'r')
            
        #for stiner_node in net['steiner_node']:
            #plot_dot(stiner_node['x'],stiner_node['y'],'g')
    
    plt.show()
    
def plot_box(llx,lly,urx,ury,c):
    plt.plot([llx,urx], [lly,lly], lw=2, color=c)
    plt.plot([urx,urx], [lly,ury], lw=2, color=c)
    plt.plot([urx,llx], [ury,ury], lw=2, color=c)
    plt.plot([llx,llx], [lly,ury], lw=2, color=c)
    
def plot_line(llx,lly,urx,ury,c):
    plt.plot([llx,urx], [lly,ury], lw=2, color=c)
    
def plot_dot(x,y,c):
    plt.plot(x,y, 'o', color=c)


global_routr,Gcell,blocks,node_box=read_data()

plot_global_routing(global_routr,Gcell,blocks,node_box,global_routr[1]['name'])
print(global_routr[1])
