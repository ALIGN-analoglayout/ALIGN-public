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
//#include "MatrixInverse.hpp"
#include <sstream>
#include <fstream>
#include <string>
#include <iostream>
#include <stdlib.h>
#include <vector>
#include <set>
#include "Mdatatype.h"
#include "slu_ddefs.h"
#include "../PnRDB/datatype.h"
#include "../router/Rdatatype.h"
#include "spdlog/spdlog.h"


typedef boost::numeric::ublas::matrix<double> boost_matrix;


class MNASimulation {

  private:
      //std::vector<std::vector<double>> R;
      //std::vector<double> I;
      //std::vector<double> V;
	boost_matrix R;
	boost_matrix I;
	boost_matrix V;
	double result;
	std::vector<MDB::device> Power_Grid_devices_Vdd;
	std::vector<MDB::device> Power_Grid_devices_Gnd;
	std::vector<MDB::device> Power_Grid_devices;
	SuperMatrix A;
        PnRDB::Drc_info Drc_info;


  public:
      //MNASimulation(std::vector<std::vector<double>> &out_R, std::vector<double>& out_I);
      //MNASimulation(boost_matrix &out_R, boost_matrix &out_I);
	MNASimulation(PnRDB::hierNode &current_node, PnRDB::Drc_info &drc_info, std::string inputfile, std::string outputfile, std::string outputem);
      void Transfer(std::vector<MDB::device> &temp_devices, std::vector<MDB::device> &temp2_devices, std::vector<std::vector<double> > &Rstore, std::vector<std::vector<double> > &Istore, std::vector<std::vector<double> > &Vstore);
      int nodenum(std::vector<MDB::device> &temp_devices);
      void ExtractPowerGrid();
      void ConstructI(std::vector<std::vector<double>> Istore, std::vector<std::vector<double>> Vstore, std::vector<std::vector<double>> Rstore);
      void ConstructR(std::vector<std::vector<double>> Rstore, std::vector<std::vector<double>> Vstore);
      //void ConstructI();
      double SolveIR_drop(int Rsize);
      boost_matrix Return_Voltage(){return V;};
	int MapPoint(std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set1, int x, int y, int layer);
	int MaxY(std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, int layer);
	int MaxX(std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, int layer);
	int MapY(std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, int layer);
	int MapX(std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, int layer);
	void Print_Result(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, double* dp, std::string outputfile);
      void Print_Grid(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, std::vector<MDB::device> &temp_devices);
	void Print_EM(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, std::vector<MDB::device> &temp_devices, int size, double* dp, std::string outputfile);
      void Map(std::vector<std::vector<double>> &currentstore, std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, std::vector<MDB::device> &Power_Grid_devices, int metal_layer);
      void Map_new(std::vector<std::vector<double>> &currentstore, std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, std::vector<MDB::device> &Power_Grid_devices, int metal_layer);
      void Map_old(std::vector<std::vector<double>> &currentstore, std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, std::vector<MDB::device> &Power_Grid_devices, int metal_layer);
	void ReadCurrent(std::vector<std::vector<double>> &currentstore, std::string inputfile);
      //added by yg
      void Clear_Power_Grid(PnRDB::PowerGrid &temp_grid);
      void ExtractPowerGridPoint(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, int &highest_metal, int &lowest_metal, double power);
      //void ExtractPowerGridPoint(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set);
      void ExtractPowerGridWireR(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices,double power);
      void ExtractPowerGridViaR(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices,double power, std::vector<int> vianumber);
      void ExtractPowerGrid(PnRDB::PowerGrid &vdd, PnRDB::PowerGrid &gnd, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices, std::vector<int> &mark_point, std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, std::string inputfile);
      void Print_Devices(std::vector<MDB::device> &temp_devices);
      double Return_Worst_Voltage(){return result;};
      void Test_superlu();
      void AddingI(std::vector<MDB::metal_point> &I_point_v, std::vector<MDB::metal_point> &I_point_g, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, std::vector<MDB::device> &Power_Grid_devices, double current);
      void AddingPower(std::vector<MDB::metal_point> &power_points, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, std::vector<MDB::device> &Power_Grid_devices, double power);
      void FindPowerPoints(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, double power, int metal_layer, int power_number, std::vector<MDB::metal_point> &power_points);
      void FindPowerPoints_New(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, double power, int metal_layer, int power_number, std::vector<MDB::metal_point> &power_points);
      int find_nearest(double x, vector<int> &x_v);
      std::string Index_Postion(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, int index);
      std::string Index_Postion_New(int index, bool start_end);
      void WriteOut_Spice(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set);
};

#endif
