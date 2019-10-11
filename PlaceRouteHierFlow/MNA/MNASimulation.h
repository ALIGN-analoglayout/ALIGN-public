#ifndef MNASIMULATION_H_
#define MNASIMULATION_H_

#include <boost/numeric/ublas/matrix.hpp>
#include <boost/numeric/ublas/io.hpp>
#include <sstream>
#include <iostream>
#include <stdlib.h>
#include <vector>
#include "Mdatatype.h"
#include "../PnRDB/datatype.h"
#include "../router/Rdatatype.h"


typedef boost::numeric::ublas::matrix<double> boost_matrix;


class MNASimulation {

  private:
      //std::vector<std::vector<double>> R;
      //std::vector<double> I;
      //std::vector<double> V;
	boost_matrix R;
	boost_matrix I;
	boost_matrix V;



  public:
      //MNASimulation(std::vector<std::vector<double>> &out_R, std::vector<double>& out_I);
      MNASimulation(boost_matrix &out_R, boost_matrix &out_I);
      void ExtractPowerGrid();
      boost_matrix ConstructR(std::vector<std::vector<double>> Rstore, std::vector<std::vector<double>> Istore);
      //void ConstructI();
      int SolveIR_drop();

      //added by yg
      void ExtractPowerGridPoint(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set);
      void ExtractPowerGridWireR(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices);
      void ExtractPowerGridViaR(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices);
      void ExtractPowerGrid(PnRDB::PowerGrid &vdd, PnRDB::PowerGrid &gnd, PnRDB::Drc_info &drc_info);

};

#endif
