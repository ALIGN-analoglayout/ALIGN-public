#ifndef ILP_solver_h_
#define ILP_solver_h_

#include <stdio.h>
#include <stdlib.h> /* srand, rand */
#include <time.h>   /* time */

#include <algorithm>
#include <climits>
#include <cmath>
#include <fstream>
#include <iostream>
#include <stack>
#include <string>
#include <utility>
#include <vector>

#include "../PnRDB/datatype.h"
#include "Aplace.h"
#include "ConstGraph.h"
#include "Pdatatype.h"
#include "SeqPair.h"
#include "design.h"
#include "lp_lib.h"

using std::cerr;
using std::cin;
using std::cout;
using std::make_pair;
using std::min;
using std::pair;
using std::stack;
using std::string;
using std::vector;

class ILP_solver {
  private:
  struct Block {
    int x = 0, y = 0;            // LL of each block
    int H_flip = 0, V_flip = 0;  // flip along V axis and H axis
  };
  vector<Block> Blocks;
  placerDB::point LL, UR;
  int area = 0, HPWL = 0;

  public:
  ILP_solver();
  ILP_solver(design& mydesign);
  ILP_solver(const ILP_solver& solver);
  ILP_solver& operator=(const ILP_solver& solver);
  double GenerateValidSolution(design& mydesign, SeqPair& curr_sp);
  double CalculateCost(design& mydesign, SeqPair& curr_sp);
  void WritePlacement(design& caseNL, SeqPair& curr_sp, string outfile);
  void PlotPlacement(design& caseNL, SeqPair& curr_sp, string outfile);
};

#endif