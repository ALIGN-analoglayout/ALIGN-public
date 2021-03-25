#include "MNASimulationIfc.h"

#include "MNASimulation.h"

MNASimulationIfc::MNASimulationIfc(PnRDB::hierNode &current_node, PnRDB::Drc_info &drc_info, std::string inputfile, std::string outputfile, std::string outputem){
  MNA = new MNASimulation( current_node, drc_info, inputfile, outputfile, outputem);
}

MNASimulationIfc::~MNASimulationIfc() {
  delete MNA;
}

double MNASimulationIfc::Return_Worst_Voltage() {
  return MNA->Return_Worst_Voltage();
}

void MNASimulationIfc::Clear_Power_Grid(PnRDB::PowerGrid &temp_grid) {
  MNA->Clear_Power_Grid( temp_grid);
}
