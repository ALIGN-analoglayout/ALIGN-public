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

typedef boost::numeric::ublas::matrix<double> boost_matrix;


class MNASimulation {

  private:
      //std::vector<std::vector<double>> R;
      //std::vector<double> I;
      //std::vector<double> V;
	boost_matrix R;
	boost_matrix I;
	boost_matrix V;
	std::vector<std::vector<double>> Rstore;
	std::vector<std::vector<double>> Istore;
	std::vector<std::vector<double>> Vstore;



  public:
      //MNASimulation(std::vector<std::vector<double>> &out_R, std::vector<double>& out_I);
	MNASimulation(boost_matrix &out_R, boost_matrix &out_I);
	void read();
	
	void ConstructI(std::vector<std::vector<double>> Istore, std::vector<std::vector<double>> Vstore, std::vector<std::vector<double>> Rstore);
        void ConstructR(std::vector<std::vector<double>> Rstore, std::vector<std::vector<double>> Vstore);
      //void ConstructI();
      int SolveIR_drop();

};

#endif
