

class device:
	def __init__(self,line,nodes_under_test,node_list,device_type_set):		#line contains [dev name] [nodelist] [dev type]
		device_details = [s.strip('()') for s in line.split()]
		#device_details.remove('')
		for item in (item for item in device_details if item in device_type_set):
			j = device_details.index(item)
			break

		self.name = device_details[0]
		self.kind = device_details[j]
		self.nodelist = list()
		#self.nodelist = device_details[1:j]
		for item in set(device_details[1:j]):
			is_in_nodelist = False
			for n in node_list:
				if item == n.name:
					self.nodelist.append(n)
					n.devlist.add(self)
					is_in_nodelist = True
					break
			if is_in_nodelist == False:
				node_list.append(node(item,"local",nodes_under_test))
				node_list[-1].devlist.add(self)
				self.nodelist.append(node_list[-1])

		# logging.info("{} added in device list.".format(self.name))

class node:
	def __init__(self,name,kind,nodes_under_test):
		# print("Constructor called for - {}".format(name))
		self.name = name
		self.kind = kind
		if self.name.isnumeric():
			self.alias = kind+"_"+name
		else:
			self.alias = None
		self.devlist = set()

		for item in nodes_under_test:
			if item == self.name:
				self.isundertest = True
				break
			else:
				self.isundertest = False

		def add_devlist(self,device):
			self.devlist.add(device)

class specs:
	def __init__(self,name,maxval,minval,unit):
		self.name = name
		self.minval = minval
		self.maxval = maxval
		self.unit = unit

class param:
	def __init__(self, name, pin):
		self.name = name
		self.pin = pin
		self.critval = None

class simulation:
	def __init__(self,name):
		self.name = name
		self.start = list()
		self.stop = list()
		self.step = list()
		self.count = list()

	def __str__(self):
		str_to_print = "Simulation name: " + self.name \
					 + " Start: " + str(self.start[0]) \
					 + " Stop: " + str(self.stop[0]) \
					 + " Step: " + str(self.step[0]) \
					 + " Step: " + str(self.count[0])
		return str_to_print

class net:
    def __init__(self, name, isundertest, netid):
        self.name = name
        self.isundertest = isundertest
        self.connections = list()
        self.branchcurrents = list()
        self.id = netid
    def __str__(self):
        return "name: {}\nisundertest: {}\nnet id: {}\nconnections: {}\nbranches: {}\n" \
                .format(self.name, self.isundertest, self.id, self.connections, self.branchcurrents)

class subcircuit:
    def __init__(self, name, portlist, netlist, id):
        self.name = name
        self.portlist = portlist
        self.netlist = netlist
        self.id = id
    def __str__(self):
        str_to_print = "Subcircuit name: " + self.name + "\nsubcircuit id: " + str(self.id) + "\nportlist: " + str(self.portlist) + "\n"
        for item in self.netlist:
            str_to_print = str_to_print + str(item)
        # str_to_print = str_to_print + str(self.netset) + "\n"
        return str_to_print
