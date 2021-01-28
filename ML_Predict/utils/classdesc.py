

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
	def __init__(self,name):
		self.name = name
		self.critval = None

class simulation:
	def __init__(self,name):
		self.name = name
		self.start = list()
		self.stop = list()
		self.step = list()
		self.count = list()
