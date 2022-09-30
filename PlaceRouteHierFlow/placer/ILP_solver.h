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
#include "Pdatatype.h"
#include "PlacerHyperparameters.h"
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

class ILP_solver;

using SolutionMap=std::map<double, std::pair<SeqPair, ILP_solver>>;

class ILP_solver {
  friend class Placer;

  private:
  struct Block {
    int x = 0, y = 0;            // LL of each block
    int H_flip = 0, V_flip = 0;  // flip along V axis and H axis
  };
  vector<Block> Blocks;
  placerDB::point LL, UR;
  double area = 0, area_ilp = 0., HPWL = 0, HPWL_ILP = 0., HPWL_extend = 0, HPWL_extend_terminal = 0, ratio = 0, linear_const = 0, multi_linear_const = 0;
  double HPWL_extend_net_priority = 0, cfcost = 0;
  double area_norm = 0, HPWL_norm = 0;
  double Aspect_Ratio_weight = 1000;
  double Aspect_Ratio[2] = {0, 100};
  double placement_box[2] = {-1.0, -1.0};
  typedef void(lphandlestr_func)(lprec* lp, void* userhandle, char* buf);
  static void lpsolve_logger(lprec* lp, void* userhandle, char* buf);
  vector<vector<int>> block_order;
  int x_pitch, y_pitch;
  enum SOLVERTOUSE {SYMPHONY = 0, LPSOLVE, CBC};
  int use_ilp_solver = SYMPHONY;

  int roundupint (const double& x) const {
    int ix = int(x);
    return ((fabs(x-ix) > 0.5) ? ((ix < 0) ? ix - 1 : ix + 1) : ix);
  };
  inline void roundup(int& v, const int pitch) { v = pitch * ((v + pitch - 1) / pitch); }
  inline void rounddown(int& v, const int pitch) { v = pitch * (v / pitch); }
  bool MoveBlocksUsingSlack(const std::vector<Block>& blockslocal, const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo, const int num_threads = 1, const bool genvalid = true);
  bool FrameSolveILPCore(const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo, bool flushbl, const SOLVERTOUSE solvertouse, const bool snapGridILP, const vector<placerDB::point>* prev);
  bool PlaceILPCbc_select(SolutionMap& sol, const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo, const int num_threads, bool flushlb, const int numsol, const vector<placerDB::point>* prev = nullptr);
  bool FrameSolveILP(const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo, const int num_threads, const bool flushlb, const bool snapGridILP, const vector<placerDB::point>* prev = nullptr)
  {
    bool offsetpresent{false};
    for(unsigned int i = 0; i < mydesign.Blocks.size(); ++i){
      if (!mydesign.Blocks[i][curr_sp.selected[i]].xoffset.empty() ||
          !mydesign.Blocks[i][curr_sp.selected[i]].yoffset.empty()) {
        offsetpresent = true;
        break;
      }
    }
    if (!offsetpresent) return FrameSolveILPCore(mydesign, curr_sp, drcInfo, flushlb, SYMPHONY, snapGridILP, prev);
    return FrameSolveILPCore(mydesign, curr_sp, drcInfo, flushlb, CBC, snapGridILP, prev);
  }
  std::vector<std::set<int>> GetCC(const design& mydesign) const;
  public:
  double cost = 0;
  double constraint_penalty = 0;
  ILP_solver();
  ILP_solver(design& mydesign, PnRDB::hierNode& node);
  ILP_solver(design& mydesign, int ilps = SYMPHONY);
  ILP_solver(const ILP_solver& solver);
  ILP_solver& operator=(const ILP_solver& solver);
  int xdim() const { return UR.x - LL.x; }
  int ydim() const { return UR.y - LL.y; }
  double GenerateValidSolutionAnalytical(design& mydesign, PnRDB::Drc_info& drcInfo, PnRDB::hierNode& node);
  bool GenerateValidSolutionCore(const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo, const int num_threads, const bool snapGridILP);
  double GenerateValidSolution(const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo, const int num_threads = 1);
  SolutionMap PlaceUsingILP(const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo, const int num_threads, const int numsol = 1);
  double GenerateValidSolution_select(design& mydesign, SeqPair& curr_sp, PnRDB::Drc_info& drcInfo);
  double UpdateAreaHPWLCost(const design& mydesign, const SeqPair& curr_sp);
  double CalculateCost(const design& mydesign) const;
  double CalculateCost(const design& mydesign, const SeqPair& curr_sp) ;
  double CalculateCFCost(const design& mydesign, const SeqPair& curr_sp) ;
  void WritePlacement(design& caseNL, SeqPair& curr_sp, string outfile);
  void PlotPlacement(design& mydesign, SeqPair& curr_sp, string outfile);
  //void PlotPlacementAnalytical(design& caseNL, string outfile, bool plot_pin, bool plot_terminal, bool plot_net);
  std::vector<double> Calculate_Center_Point_feature(std::vector<std::vector<placerDB::point>>& temp_contact);
  void updateTerminalCenter(design& mydesign, SeqPair& curr_sp);
  void updateTerminalCenterAnalytical(design& mydesign);
  void UpdateHierNode(design& mydesign, SeqPair& curr_sp, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo);
  void UpdateHierNodeAnalytical(design& mydesign, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo);
  void UpdateBlockinHierNode(design& mydesign, placerDB::Omark ort, PnRDB::hierNode& node, int i, int sel, PnRDB::Drc_info& drcInfo);
  void UpdateTerminalinHierNode(design& mydesign, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo);
  void UpdateSymmetryNetInfoAnalytical(design& mydesign, PnRDB::hierNode& node, int i, int SBidx, placerDB::Smark axis_dir);
  void UpdateSymmetryNetInfo(design& mydesign, PnRDB::hierNode& node, int i, int SBidx, placerDB::Smark axis_dir, SeqPair& curr_sp);
  PnRDB::bbox ConvertBoundaryData(vector<placerDB::point> Bdata);
  PnRDB::point ConvertPointData(placerDB::point Pdata);
};

class ExtremeBlocksOfNet {
  private:
    std::map<int, int> _posPosition, _negPosition;
    std::vector<std::set<int>> _ltExtreme, _rtExtreme, _botExtreme, _topExtreme;
  public:
    ExtremeBlocksOfNet(const SeqPair& sp, const int N);
    void FindExtremes(const placerDB::net& n, const int neti);
    bool InLeftExtreme(const int neti, const int i) const { return _ltExtreme.size() > neti && _ltExtreme[neti].find(i) != _ltExtreme[neti].end(); }
    bool InRightExtreme(const int neti, const int i) const { return _rtExtreme.size() > neti && _rtExtreme[neti].find(i) != _rtExtreme[neti].end(); }
    bool InTopExtreme(const int neti, const int i) const { return _topExtreme.size() > neti && _topExtreme[neti].find(i) != _topExtreme[neti].end(); }
    bool InBottomExtreme(const int neti, const int i) const { return _botExtreme.size() > neti && _botExtreme[neti].find(i) != _botExtreme[neti].end(); }

};

class TimeMeasure {
  private:
    std::chrono::nanoseconds& _rt;
    std::chrono::high_resolution_clock::time_point _begin;
  public:
    TimeMeasure(std::chrono::nanoseconds& rt) : _rt(rt)
    {
      _begin = std::chrono::high_resolution_clock::now();
    }
    ~TimeMeasure()
    {
      auto _end = std::chrono::high_resolution_clock::now();
      _rt += std::chrono::duration_cast<std::chrono::nanoseconds>(_end - _begin);
    }
};

#endif
