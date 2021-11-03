
class subcircuit:
	def __init__(self, name, portlist, netlist):
		self.name = name
		self.portlist = portlist
		self.netlist = netlist  # Holds list of 'net' type objects
		# self.id = id
	def __str__(self):
		str_to_print = "Subcircuit name: " + self.name + "\nportlist: " + str(self.portlist) + "\n"
		for item in self.netlist:
			str_to_print = str_to_print + str(item)
		str_to_print = str_to_print + "\n"
		return str_to_print

class net:
	def __init__(self, name, isundertest):
		self.name = name
		self.isundertest = isundertest
		self.connections = list() # Holds list of 'connection' type objects
		self.branches = list() # Holds list of 'branch' type objects
		# self.id = netid
	def __str__(self):
		str_to_print =  "name: {}\nisundertest: {}\n" \
				.format(self.name, self.isundertest)

		str_to_print = str_to_print + "connections:\n"
		for conn in self.connections:
			str_to_print = str_to_print + str(conn)

		for branch in self.branches:
			str_to_print = str_to_print + str(branch)			
		return str_to_print

class connection:
	def __init__(self, devicename, nodename):
		self.devicename = devicename
		self.nodename = nodename

	def __str__(self):
		return f"{self.devicename}/{self.nodename}\n"

class branch:
	def __init__(self, conn1, conn2):
		self.conn1 = conn1  # conn1, conn2 are 'connection' type objects
		self.conn2 = conn2	

	def __str__(self):
		return f"First pin: {self.conn1}, Second pin: {self.conn2}\n"		


