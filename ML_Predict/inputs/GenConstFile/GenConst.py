import os

slist = ['module','endmodule','input','`celldefine','`endcelldefine', 'supply0', 'supply1']
device_list = []
net_list = []
parasitic_list = []
constraint_list = []

with open("param_name.txt","r") as fparam:
    for line in fparam:
        line = line.strip()
        params = line.split(',')
        print(params)
        for item in params:
            temp = item.split('_')
            parasitic_list.append(temp[0])
            net_list.append(temp[2])
            device_list.append(temp[1])
            pass

print(device_list)
print(net_list)
print(parasitic_list)

with open("telescopic_ota.v","r") as fverilog:
    for line_verilog in fverilog:
        if not line_verilog.startswith("//"):
            temp = line_verilog.strip().split()
            if temp:
                if temp[0] not in slist and temp[1] in device_list:
                    for i, node in enumerate(temp):
                        if i > 2 and i < len(temp)-1:
                            net = node.strip('.),').split('(')
                            # print("{} {}".format(net[0],net[1]))
                            for j, item in enumerate(net_list):
                                if net[1]==item and net[0]!="B" and temp[1] == device_list[j]:
                                    print("Device: {}, Net: {}, Node: {}, Type: {}".format(temp[1], net[1], net[0], parasitic_list[j]))
                                    constraint_list.append(net[1] + "/" + temp[1] + "/" + net[0] + "/" + parasitic_list[j][0])

print(' , '.join(constraint_list))
