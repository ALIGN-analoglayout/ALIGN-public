
# import all functions from the tkinter
from tkinter import filedialog

from tkinter import *

# importing required libraries 
import json, os 

# Create a GUI window 
root = Tk() 
root.title("Constraint writer GUI") 

	
# Function for clearing the Entry field 
def generate_const_json(): 
    constraints ={}
    constraints["critical_nets"] = []
    for net in CritNet_field.get().strip().split():
        crit ={"net":net,"value":def_criticality.get()}
        constraints["critical_nets"].append(crit)
    for net in CritNet_field1.get().strip().split():
        crit ={"net":net,"value":def_criticality1.get()}
        constraints["critical_nets"].append(crit)
    for net in CritNet_field2.get().strip().split():
        crit ={"net":net,"value":def_criticality2.get()}
        constraints["critical_nets"].append(crit)

    constraints["shielded_nets"] = []
    for net in ShieldNet_field.get().strip().split():
        snet ={"net":net,"value":s_net.get()}
        constraints["shielded_nets"].append(snet)
    for net in ShieldNet_field1.get().strip().split():
        snet ={"net":net,"value":s_net1.get()}
        constraints["shielded_nets"].append(snet)

    constraints["matching_blocks"]  =[]
    for blocks in MatchBlock_field.get().strip().split(';'):
        if blocks.strip():
            [block1,block2] = blocks.strip().split()
            match= {"block1":block1, "block2":block2}
            constraints["matching_blocks"].append(match)
    constraints["Symmetrical_nets"] = []
    for nets in SymmNet_field.get().strip().split(';'):
        if nets.strip():
            [net1, net2] = nets.strip().split(',')
            net1=net1.strip().split()
            net2=net2.strip().split()
            match= {"net1":net1[0], "net2":net2[0], "pins1":net1[1:] , "pins2":net2[1:]}
            constraints["Symmetrical_nets"].append(match)

    for unit_cap in Unit_cap_field.get().strip().split(';'):
        if unit_cap.strip():
            [unit_cap_inst,unit_value] = unit_cap.strip().split();

    constraints["cap"]=[]
    for cap_blocks in Cap_field.get().strip().split(';'):
        if cap_blocks.strip():
            cap_inst = cap_blocks.strip().split()[0];
            cap_value =cap_blocks.strip().split()[1:];
            cap_const={"inst":cap_inst, "value":','.join(cap_value) ,"unit_cap":unit_cap_inst,"unit_value":unit_value}
            constraints["cap"].append(cap_const)
            #print("CC ({"+cap_inst+'},{'+','.join(cap_value)+'},{'+unit_cap+'})')

    constraints["current"]  =[]
    for blocks in Current_field.get().strip().split(';'):
        if blocks.strip():
            [pin,value] = blocks.strip().split()
            match= {"pin":pin, "value":value}
            constraints["current"].append(match)    
    
    with open('constraint.json', 'w') as outfile:
        json.dump(constraints, outfile,indent =4)

def read_cap():
    file_name = input_netlist.get().strip()
    cap_constraint ={}
    if os.path.exists(file_name):
        with open(file_name) as fp:
            for line in fp:
                if line.startswith("Cap"):
                    #print(line)
                    [value,name] = line.strip().split()[0:2]
                    #print("KK", value,name)
                    #value = int(list(filter(str.isdigit, value))[0])
                    value = int(value.replace('Cap_','').replace('f',''))
                    #print("cap value",value)
                    cap_constraint[name]=value
    unit_cap = int(Unit_cap_field.get().strip().split()[1])
    all_cap=[] 
    for name,value in cap_constraint.items():
        all_cap.append(name+' '+ str(int(value/unit_cap))+';')
    #print(all_cap)
    Cap_field.insert(0,str(' '.join(all_cap)))

def clear_all():
    Cap_field.delete(0,'end') 
    CritNet_field.delete(0,'end') 
    CritNet_field1.delete(0,'end') 
    CritNet_field2.delete(0,'end') 
    Current_field.delete(0,'end') 
    MatchBlock_field.delete(0,'end') 
    ShieldNet_field.delete(0,'end') 
    ShieldNet_field1.delete(0,'end') 
    SymmNet_field.delete(0,'end') 

   

def read_const_text():
    file_name = input_file.get().strip()
    constraints={}
    constraints["critical_nets"]=[]
    constraints["Symmetrical_nets"] = []
    constraints["shielded_nets"] = []
    constraints["matching_blocks"]  =[]
    constraints["current"]  =[]
    constraints["cap"]  =[]
    if os.path.exists(file_name):
        with open(file_name) as fp:
            for line in fp:
                line= line.strip().replace(')','')
                if line:
                    if line.startswith("CritNet"):
                        [net,value] = line.strip().split('(')[1].split(',')
                        crit_const = {"net":net,
                                      "value":value}
                        constraints["critical_nets"].append(crit_const)
                    elif line.startswith("ShieldNet"):
                        net = line.strip().split('(')[1].replace(')','')
                        shield_const = {"net":net}
                        constraints["shielded_nets"].append(shield_const)
                    elif line.startswith("SymmNet"):
                        line = line.strip().split('(')[1]
                        [net1,net2] = line.split('}')[0:2]
                        net1=net1.strip().replace('{','').split(',')
                        net2=net2.strip().replace('{','').split(',')[1:]
                        match= {"net1":net1[0], 
                                "net2":net2[0], 
                                "pins1":net1[1:] ,
                                "pins2":net2[1:]}
                        constraints["Symmetrical_nets"].append(match)
                    elif line.startswith("MatchBlock"):
                        [block1,block2] = line.strip().split('(')[1].split(',')
                        match= {"block1":block1, 
                                "block2":block2}
                        constraints["matching_blocks"].append(match)
                    elif line.startswith("Current"):
                        [pin,value] = line.strip().split('(')[1].split(',')
                        current_const = {"pin":pin,"value":value}
                        constraints["current"].append(current_const)
                    elif line.startswith("CC"):
                        line = line.strip().split('(')[1]
                        #print(line.split('}'))
                        [cap1,value,unit_cap] = line.split('}')[0:3]
                        cap1=cap1.strip().replace('{','')
                        value=value.strip().replace(',{','').split(',')
                        [unit_cap,unit_val]=unit_cap.strip().replace(',{','').split()
                        match= {"cap":cap1, 
                                "value":value, 
                                "unit_cap":unit_cap ,
                                "unit_val":unit_val}
                        constraints["cap"].append(match)
                    else:
                        print("wrong input:%s",line)
    crit_net_min =[]
    crit_net_mid =[]
    crit_net_max =[]
    for nets in constraints["critical_nets"]:
        if 'min' in nets["value"]:
            crit_net_min.append(nets["net"])
        elif 'mid' in nets["value"]:
            crit_net_mid.append(nets["net"])
        elif 'max' in nets["value"]:
            crit_net_max.append(nets["net"])
    CritNet_field.insert(0,str(' '.join(crit_net_min)))
    CritNet_field1.insert(0,str(' '.join(crit_net_mid)))
    CritNet_field2.insert(0,str(' '.join(crit_net_max)))
    shield_net =[]
    for nets in constraints["shielded_nets"]:
        shield_net.append(nets["net"])
    symm_net =[]
    for match in constraints["Symmetrical_nets"]:
        symm_net.append(match["net1"]+' '+' '.join(match["pins1"])+','+
                        match["net2"]+' '+' '.join(match["pins2"])+';')
    match_block =[]
    for match in constraints["matching_blocks"]:
        match_block.append(match["block1"]+' '+match["block2"]+';')
    current_value=[]
    for match in constraints["current"]:
        current_value.append(match["pin"]+' '+match["value"]+';')
    cap_value=[]
    for match in constraints["cap"]:
        cap_value.append(match["cap"]+' '+' '.join(match["value"])+';')
    ShieldNet_field.insert(0,str(' '.join(shield_net)))
    SymmNet_field.insert(0,str(' '.join(symm_net)))
    MatchBlock_field.insert(0,str(' '.join(match_block)))
    Current_field.insert(0,str(' '.join(current_value)))
    Cap_field.insert(0,str(' '.join(cap_value)))
    if(constraints["cap"]):
        Unit_cap_field.insert(0,str(constraints["cap"][0]["unit_cap"]+' '+
                                    constraints["cap"][0]["unit_val"]))
        
def openfile():
   filename = filedialog.askopenfilename(parent=root)
   input_file.delete(0,'end') 
   input_file.insert(0,filename) 
   #f = open(filename)
   #f.read()

# Driver code 
if __name__ == "__main__" : 
    """ 
    example inputs:
    Critical Nets: n1 n2
    Shield Nets: n1 n2 n3
    Match blocks: b1 b2; b3 b4
    Symmetrical nets: n1 p1 p2, n2 p22 p21; n2 p1,n3 p3
    """
    menu = Menu(root) 
    root.config(menu=menu) 
    filemenu = Menu(menu) 
    menu.add_cascade(label='File', menu=filemenu) 
    filemenu.add_command(label='New') 
    filemenu.add_command(label='Open...', command = openfile) 
    filemenu.add_separator() 
    filemenu.add_command(label='Exit', command=root.quit)
    helpmenu = Menu(menu) 
    menu.add_cascade(label='Help', menu=helpmenu) 
    helpmenu.add_command(label='About')


    # Set the background colour of GUI window 
    root.configure(background = 'white') 
    
    # Set the configuration of GUI window (WidthxHeight) 
    root.geometry("800x400") 
    
    # Create welcome to Real Time Currency Convertor label 
    headlabel = Label(root, text = ' Welcome to constraint writer package', 
    				fg = 'black',
                    bg = "cyan",
                    pady=10) 
    
    label1 = Label(root, text = "Critical Nets :",
                   fg = 'black',
                   bg = 'slategray') 
    label2 = Label(root, text = "Shielded Nets(GND) :",
                   fg = 'black',
                   bg = 'slategray') 
    label3 = Label(root, text = "Match Blocks \n(; seperated pairs):",
                   fg = 'black',
                   bg = 'slategray') 
    label4 = Label(root, text = "Symmetrical Nets(pin list) :",
                   fg = 'black',
                   bg = 'slategray') 
    label5_1 = Label(root, text = "Cap and values :",
                     fg = 'black',
                     bg = 'slategray') 
    label5_2 = Label(root, text = "Unit cap :",
                     fg = 'black',
                     bg = 'slategray') 
    label6 = Label(root, text = "Avg Current :",
                   fg = 'black',
                   bg = 'slategray') 
    
    # grid method is used for placing the widgets at respective positions in table like structure . 
    headlabel.grid(row = 0, column = 1, sticky =W) 
    label1.grid(row = 1, column = 0 , columnspan=3, sticky =W, ipady=10) 
    label2.grid(row = 4, column = 0, columnspan=2, sticky =W, ipady=10) 
    label3.grid(row = 6, column = 0, sticky =W,ipady=4) 
    label4.grid(row = 8, column = 0, sticky =W,ipady =4) 
    label5_1.grid(row = 9, column = 0, sticky =W,ipady =4) 
    label5_2.grid(row = 9, column = 2, sticky =W,ipady =4) 
    label6.grid(row = 10, column = 0, sticky =W,ipady =4) 
    #label5.grid(row = 10, column = 0) 
    
    # Create a text entry box 
    # for filling or typing the information. 
    CritNet_field = Entry(root) 
    CritNet_field1 = Entry(root) 
    CritNet_field2 = Entry(root) 
    CritNet_field.insert(0,"net1 net2") 
    ShieldNet_field = Entry(root)
    ShieldNet_field1 = Entry(root)
    ShieldNet_field.insert(0,"net1 net2") 
    MatchBlock_field = Entry(root)
    MatchBlock_field.insert(0,"block1 block2; block3 block4") 
    SymmNet_field = Entry(root)
    SymmNet_field.insert(0,"net1 pin1 pin2, net2 pina pinb; net3 pin1 pin2,net4 pina pinb") 
    Cap_field = Entry(root)
    Cap_field.insert(0,"cc1 50; cc2 30 40") 
    Unit_cap_field = Entry(root)
    Unit_cap_field.insert(0,"cc1 10") 
    Current_field = Entry(root)
    Current_field.insert(0,"pin1 120uA; pinb 160uA") 
    input_file = Entry(root)
    input_file.insert(0,"<filename>") 
    input_netlist = Entry(root)
    input_netlist.insert(0,"<filename>") 
    
    # ipadx keyword argument set width of entry space. 
    CritNet_field.grid(row = 1, column = 1, ipadx ="40",ipady=5, sticky=N) 
    CritNet_field1.grid(row = 2, column = 1, ipadx ="40",ipady=5, sticky=N) 
    CritNet_field2.grid(row = 3, column = 1, ipadx ="40",ipady=5, sticky=N) 
    ShieldNet_field.grid(row = 4, column = 1, ipadx ="40",ipady=5) 
    ShieldNet_field1.grid(row = 5, column = 1, ipadx ="40",ipady=5) 
    MatchBlock_field.grid(row = 6, column = 1, ipadx ="40",ipady=5) 
    SymmNet_field.grid(row = 8, column = 1, ipadx ="40",ipady=5) 
    Cap_field.grid(row = 9, column = 1, ipadx ="40",ipady=5) 
    Unit_cap_field.grid(row = 9, column = 3, ipadx ="10",ipady=5) 
    Current_field.grid(row = 10, column = 1, ipadx ="40",ipady=5) 
    input_file.grid(row = 11, column = 1, ipadx ="40",ipady=5) 
    input_netlist.grid(row = 12, column = 1, ipadx ="40",ipady=5) 
    def_criticality = StringVar(root)
    def_criticality.set("min")
    def_criticality1 = StringVar(root)
    def_criticality1.set("mid")
    def_criticality2 = StringVar(root)
    def_criticality2.set("max")
    criticality = ["min","mid","max"] 
    criticality_option = OptionMenu(root, def_criticality, *criticality) 
    criticality_option.grid(row=1,column=2,ipadx=10)
    criticality_option1 = OptionMenu(root, def_criticality1, *criticality) 
    criticality_option1.grid(row=2,column=2,ipadx=10)
    criticality_option2 = OptionMenu(root, def_criticality2, *criticality) 
    criticality_option2.grid(row=3,column=2,ipadx=10)
    s_net = StringVar(root)
    s_net.set("GND")
    s_net1 = StringVar(root)
    s_net1.set("VDD")
    shield_nets = ["VDD","GND"] 
    criticality_option = OptionMenu(root, s_net, *shield_nets) 
    criticality_option.grid(row=4,column=2,ipadx=10)
    criticality_option1 = OptionMenu(root, s_net1, *shield_nets) 
    criticality_option1.grid(row=5,column=2,ipadx=10)
    

    # Create a Clear Button and attached 
    # with delete function 
    button1 = Button(root, text = "Read constraint from text file", bg = "cyan", 
    				fg = "black", command = read_const_text) 
    button1.grid(row = 11, column = 0) 
    button2 = Button(root, text = "Read cap from verilog file", bg = "cyan", 
    				fg = "black", command = read_cap) 
    button2.grid(row = 12, column = 0) 
    button3 = Button(root, text = "Generate constraint json", bg = "green", 
    				fg = "black", command = generate_const_json) 
    button3.grid(row = 13, column = 1) 
    
    button4 = Button(root, text = "clear all", bg = "green", 
    				fg = "black", command = clear_all) 
    button4.grid(row = 13, column = 0)     
    # Start the GUI 
    root.mainloop() 
