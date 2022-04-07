#ifndef PLACER_H_
#define PLACER_H_

#include <stdlib.h> /* srand, rand */
#include <time.h>   /* time */

#include <cmath>
#include <nlohmann/json.hpp>
#include <thread>

#include "../PnRDB/datatype.h"
#include "ILP_solver.h"
#include "PlacerHyperparameters.h"
#include "SeqPair.h"
#include "design.h"
#ifdef PERFORMANCE_DRIVEN
#include <Python.h>
#endif
using std::cout;
using std::endl;
using namespace nlohmann;

//#define MAX_TIMEOUT 4300000 //4.3 seconds = 4300000 us

//#define MTMODE 1 // flag to turn on multi-threading

class Placer {
  private:
  // design designData;
  // PnRDB::hierNode node;
  // std::map<double, std::pair<SeqPair, ILP_solver>> PlacementCoreAspectRatio_ILP(design& designData, SeqPair& curr_sp, ILP_solver& curr_sol, int mode, int
  // nodeSize, int effort, PnRDB::Drc_info& drcInfo, PnRDB::hierNode& node);
  std::map<double, std::pair<SeqPair, ILP_solver>> PlacementCoreAspectRatio_ILP(design& designData, SeqPair& curr_sp, ILP_solver& curr_sol, int mode,
                                                                                int nodeSize, int effort, PnRDB::Drc_info& drcInfo);
  int scale_coord(int x, int mul, int div);

  void ReshapeSeqPairMap(std::map<double, SeqPair>& spMap, int nodeSize);
  void ReshapeSeqPairMap(std::map<double, std::pair<SeqPair, ILP_solver>>& spMap, int nodeSize);
  void PlacementRegularAspectRatio_ILP(std::vector<PnRDB::hierNode>& nodeVec, string opath, int effort, PnRDB::Drc_info& drcInfo);
  void PlacementRegularAspectRatio_ILP_Analytical(std::vector<PnRDB::hierNode>& nodeVec, string opath, int effort, PnRDB::Drc_info& drcInfo);
  void ReadPrimitiveOffsetPitch(std::vector<PnRDB::hierNode>& nodeVec, PnRDB::Drc_info& drcInfo, const string& jsonStr);
  void setPlacementInfoFromJson(std::vector<PnRDB::hierNode>& nodeVec, string opath, PnRDB::Drc_info& drcInfo);
  PlacerHyperparameters hyper;
  std::uniform_real_distribution<double> _rnd{0., 1.};
  static std::mt19937_64 _rng;

  public:
  Placer(std::vector<PnRDB::hierNode>& nodeVec, string opath, int effort, PnRDB::Drc_info& drcInfo, const PlacerHyperparameters& hyper_in);
  // Placer(PnRDB::hierNode& input_node); // Constructor
  // PnRDB::hierNode CheckoutHierNode(); // Output hier Node after placement
};

#endif
