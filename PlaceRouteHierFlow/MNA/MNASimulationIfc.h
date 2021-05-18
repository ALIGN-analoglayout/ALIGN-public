#ifndef MNASIMULATIONIFC_H_
#define MNASIMULATIONIFC_H_

#include <string>
#include "../PnRDB/datatype.h"

class MNASimulation;

class MNASimulationIfc {

  MNASimulation *MNA;

  public:
	MNASimulationIfc(PnRDB::hierNode &current_node, PnRDB::Drc_info &drc_info, std::string inputfile, std::string outputfile, std::string outputem);
	~MNASimulationIfc();
	double Return_Worst_Voltage();
	void Clear_Power_Grid(PnRDB::PowerGrid &temp_grid);
};

#endif
