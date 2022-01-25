#ifndef APLACE_h_
#define APLACE_h_

#include <stdlib.h>

#include <algorithm>
#include <climits>
#include <cmath>
#include <iostream>
#include <queue>
#include <set>
#include <sstream>
#include <string>
#include <utility>  // pair, make_pair
#include <vector>

#include "../PnRDB/datatype.h"
#include "../PnRDB/readfile.h"
#include "Pdatatype.h"
#include "design.h"
#if BOOST_VERSION >= 106300  // or 64, need to check
#include <bboost/serialization/array_wrapper.hpp>
#else
#include <boost/serialization/array.hpp>
#endif
#include <boost/numeric/ublas/io.hpp>
#include <boost/numeric/ublas/vector.hpp>
// using std::vector;
// using std::string;
// using std::iostream;
// using std::pair;
// using std::make_pair;
// using std::ofstream;
// using std::endl;
// using std::cout;
// using std::cerr;

typedef boost::numeric::ublas::vector<double> boost_vector;

class Aplace {
  private:
  struct Ablock {
    placerDB::point center;
    placerDB::Omark orient;
  };
  struct Sgroup {
    placerDB::Smark axis_dir;
    int axis_coor;
  };
  std::vector<Ablock> ABlocks;
  std::vector<Sgroup> SGroups;
  std::vector<int> VSG, HSG;
  std::vector<int> selected;
  int B_len, VSG_len, HSG_len;
  int width, height;
  string name;
  void AddWireLengthGradient(boost_vector& G_k, boost_vector& x_k, design& caseNL, double alpha, double beta);
  void AddSymmetryGradient(boost_vector& G_k, boost_vector& x_k, design& caseNL, double beta);
  void AddBoundaryGradient(boost_vector& G_k, boost_vector& x_k, design& caseNL, double alpha, double beta);
  void AddOverlapGradient(boost_vector& G_k, boost_vector& x_k, design& caseNL, double alphaA, double alphaB, double beta);
  void ConjugateGrident(design& caseNL, string opath);
  void PlotPlacement(design& caseNL, boost_vector& x_k, string outfile);
  double CalculateWireLength(design& caseNL, boost_vector& x_k);
  double CalculateWireLengthSmooth(design& caseNL, boost_vector& x_k, double alpha);
  double CalculateSymmetryViolation(design& caseNL, boost_vector& x_k);
  double CalculateOverlap(design& caseNL, boost_vector& x_k);
  double CalculateOverlapSmooth(design& caseNL, boost_vector& x_k, double alphaA, double alphaB);
  double CalculateBoundaryViolation(design& caseNL, boost_vector& x_k);
  double CalculateBoundaryViolationSmooth(design& caseNL, boost_vector& x_k, double alpha);
  double CalculateObjective(design& caseNL, boost_vector& x_k, double lamda_wl, double lamda_sym, double lamda_bnd, double lamda_ovl);
  double CalculateObjectiveSmooth(design& caseNL, boost_vector& x_k, double lamda_wl, double lamda_sym, double lamda_bnd, double lamda_ovl, double alpha_wl,
                                  double alpha_ola, double alpha_olb, double alpha_bnd);

  public:
  Aplace(){};
  Aplace(PnRDB::hierNode& node, design& caseNL, string opath);
  void PrintABlocks();
  void PrintSGroups();
  void PrintAplace();
  placerDB::Omark GetBlockOrient(int i);
  placerDB::point GetBlockCenter(int i);
  inline int GetWidth() { return this->width; }
  inline int GetHeight() { return this->height; }
  inline std::vector<int> GetSelectedInstanceList() { return this->selected; }
  inline int GetSelectedInstance(int idx) { return this->selected.at(idx); }
  placerDB::Smark GetSBlockDir(int i);
  int GetSBlockCorr(int i);
};

#endif
