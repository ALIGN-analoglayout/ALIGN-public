#ifndef MNASIMULATION_H_
#define MNASIMULATION_H_

#include <boost/numeric/ublas/matrix.hpp>
#include <boost/numeric/ublas/matrix_proxy.hpp>
#include <boost/numeric/ublas/io.hpp>
#include <boost/numeric/ublas/matrix_expression.hpp>
#include <boost/numeric/ublas/vector.hpp>
#include <boost/numeric/ublas/vector_proxy.hpp>
#include <boost/numeric/ublas/triangular.hpp>
#include <boost/numeric/ublas/lu.hpp>
#include "MatrixInverse.hpp"
#include <sstream>
#include <iostream>
#include <stdlib.h>
#include <vector>
#include <set>
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

	std::vector<MDB::device> Power_Grid_devices_Vdd;
	std::vector<MDB::device> Power_Grid_devices_Gnd;



  public:
      //MNASimulation(std::vector<std::vector<double>> &out_R, std::vector<double>& out_I);
      MNASimulation(PnRDB::hierNode &current_node, PnRDB::Drc_info &drc_info);
      void ExtractPowerGrid();
      void ConstructI(std::vector<std::vector<double>> Istore, std::vector<std::vector<double>> Vstore, std::vector<std::vector<double>> Rstore);
      void ConstructR(std::vector<std::vector<double>> Rstore, std::vector<std::vector<double>> Vstore);
      //void ConstructI();
      int SolveIR_drop();

      //added by yg
      void ExtractPowerGridPoint(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set);
      void ExtractPowerGridWireR(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices);
      void ExtractPowerGridViaR(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices);
      void ExtractPowerGrid(PnRDB::PowerGrid &vdd, PnRDB::PowerGrid &gnd, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices_Vdd, std::vector<MDB::device> &Power_Grid_devices_Gnd);
      void Print_Devices(std::vector<MDB::device> &temp_devices);

};

#endif
