#ifndef MNASIMULATION_H_
#define MNASIMULATION_H_

#include <boost/numeric/ublas/matrix.hpp>
#include <boost/numeric/ublas/io.hpp>
#include <sstream>
#include <iostream>
#include <stdlib.h>
#include <vector>

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
	void read();
      boost_matrix ConstructR(std::vector<std::vector<double>> Rstore, std::vector<std::vector<double>> Istore);
      //void ConstructI();
      int SolveIR_drop();

};

#endif
