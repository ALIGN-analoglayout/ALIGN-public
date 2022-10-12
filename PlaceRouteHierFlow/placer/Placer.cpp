
#include "Placer.h"

#include "spdlog/spdlog.h"

std::mt19937_64 Placer::_rng{0};

Placer::Placer(std::vector<PnRDB::hierNode>& nodeVec, string opath, int effort, PnRDB::Drc_info& drcInfo, const PlacerHyperparameters& hyper_in)
    : hyper(hyper_in) {
  auto logger = spdlog::default_logger()->clone("placer.Placer");
  ReadPrimitiveOffsetPitch(nodeVec, drcInfo, hyper_in.place_on_grid_constraints_json);
  if (hyper.use_external_placement_info) {
    logger->debug("Requesting placement from JSON");
    // logger->info(hyper.placement_info_json);
    setPlacementInfoFromJson(nodeVec, opath, drcInfo);
  }else{
    if (hyper.use_analytical_placer)
      //#define analytical_placer
      PlacementRegularAspectRatio_ILP_Analytical(nodeVec, opath, effort, drcInfo);
    else
      PlacementRegularAspectRatio_ILP(nodeVec, opath, effort, drcInfo);
  }
}

void Placer::ReadPrimitiveOffsetPitch(std::vector<PnRDB::hierNode>& nodeVec, PnRDB::Drc_info& drcInfo, const string& jsonStr) {
  auto logger = spdlog::default_logger()->clone("placer.Placer.ReadPrimitiveOffsetPitch");
  // auto &b = lefData[primitive.front().name].front();
  json jedb = json::parse(jsonStr);
  for (auto concrete : jedb) {
    string s = concrete["concrete_name"];
    for (const auto& constraint : concrete["constraints"]) {
      if (constraint["constraint"] != "PlaceOnGrid") continue;
      unsigned int start = 0;
      unsigned int slash = s.find_last_of('_');
      if (slash != string::npos) {
        start = slash + 1;
      }
      string concrete_name = s.substr(0, slash);
      int instance_id = atoi(s.substr(start, s.size() - start).c_str());
      for (auto& block : nodeVec.back().Blocks) {
        if (block.instance.front().master == concrete_name) {
          auto& b = block.instance[instance_id];
          if (constraint["direction"] == "H") {  // horizontal metal
            for (auto offset : constraint["ored_terms"][0]["offsets"]) {
              b.yoffset.push_back(offset);
              b.yoffset.back() = b.yoffset.back() * 2 / drcInfo.ScaleFactor;
            }
            b.ypitch = constraint["pitch"];
            b.ypitch = b.ypitch * 2 / drcInfo.ScaleFactor;
            if (constraint["ored_terms"][0]["scalings"].size() < 2) {
              b.yflip = constraint["ored_terms"][0]["scalings"][0];
            }
          } else if (constraint["direction"] == "V") {  // vertical metal
            for (auto offset : constraint["ored_terms"][0]["offsets"]) {
              b.xoffset.push_back(offset);
              b.xoffset.back() = b.xoffset.back() * 2 / drcInfo.ScaleFactor;
            }
            b.xpitch = constraint["pitch"];
            b.xpitch = b.xpitch * 2 / drcInfo.ScaleFactor;
            if (constraint["ored_terms"][0]["scalings"].size() < 2) {
              b.xflip = constraint["ored_terms"][0]["scalings"][0];
            }
          }
        }
      }
    }
  }
}

void Placer::setPlacementInfoFromJson(std::vector<PnRDB::hierNode>& nodeVec, string opath, PnRDB::Drc_info& drcInfo) {
  auto logger = spdlog::default_logger()->clone("placer.Placer.setPlacementInfoFromJson");
  logger->debug("Calling setPlacementInfoFromJson");
  json modules = json::parse(hyper.placement_info_json);
  design designData(nodeVec.back(), drcInfo);
  int idx = 0;
  //pad nodeVec to match the number of concretes in JSON file
  for (const auto& m : modules) {
    if (m["abstract_name"] == designData.name) {
      string concrete_template_name = m["concrete_name"];
      unsigned int start = 0;
      unsigned int slash = concrete_template_name.find_last_of('_');
      if (slash != string::npos) start = slash + 1;
      unsigned int end = concrete_template_name.size();
      idx = atoi(concrete_template_name.substr(start, end - start).c_str());
      if (idx >= nodeVec.size()) nodeVec.insert(nodeVec.end(), idx + 1 - nodeVec.size(), nodeVec.back());
    }
  }
  int nodeSize = nodeVec.size();
  int mode = 0;
  // Read design netlist and constraints
  // designData.PrintDesign();
  // Initialize simulate annealing with initial solution
  SeqPair curr_sp(designData, ceil(1. * log(hyper.T_MIN / hyper.T_INT) / log(hyper.ALPHA)));
  // curr_sp.PrintSeqPair();
  ILP_solver curr_sol(designData);
  std::vector<std::pair<SeqPair, ILP_solver>> spVec(nodeSize, make_pair(curr_sp, curr_sol));
  for (const auto& m : modules) {
    if (m["abstract_name"] == designData.name) {
      string concrete_template_name = m["concrete_name"];
      unsigned int start = 0;
      unsigned int slash = concrete_template_name.find_last_of('_');
      if (slash != string::npos) start = slash + 1;
      unsigned int end = concrete_template_name.size();
      idx = atoi(concrete_template_name.substr(start, end - start).c_str());
      if (idx >= nodeSize) continue;
      auto& sol = spVec[idx].second;
      auto& sp = spVec[idx].first;
      auto& Blocks = sol.Blocks;
      nodeVec[idx].concrete_name = m["concrete_name"];
      for (const auto& instance : m["instances"]) {
        int block_id = nodeVec.back().Block_name_map[instance["instance_name"]];
        int sel = -1;
        for (int i = 0; i < int(nodeVec.back().Blocks[block_id].instance.size()); i++) {
          if (nodeVec.back().Blocks[block_id].instance[i].lefmaster == instance["concrete_template_name"]) {
            sel = i;
            break;
          }
        }
        if (sel < 0) logger->error("instance_name: {0} concrete_template_name: {1} not found.", instance["instance_name"], instance["concrete_template_name"]);
        sp.selected[block_id] = sel;
        Blocks[block_id].x = (int)instance["transformation"]["oX"];
        Blocks[block_id].y = (int)instance["transformation"]["oY"];
        if (instance["transformation"]["sX"] == -1) {
          Blocks[block_id].H_flip = 1;
          Blocks[block_id].x -= nodeVec.back().Blocks[block_id].instance[sel].width;
        }
        if (instance["transformation"]["sY"] == -1) {
          Blocks[block_id].V_flip = 1;
          Blocks[block_id].y -= nodeVec.back().Blocks[block_id].instance[sel].height;
        }
      }
      sol.LL.x = INT_MAX, sol.LL.y = INT_MAX;
      sol.UR.x = INT_MIN, sol.UR.y = INT_MIN;
      for (int i = 0; i < designData.Blocks.size(); i++) {
        sol.LL.x = std::min(sol.LL.x, Blocks[i].x);
        sol.LL.y = std::min(sol.LL.y, Blocks[i].y);
        sol.UR.x = std::max(sol.UR.x, Blocks[i].x + nodeVec.back().Blocks[i].instance[sp.selected[i]].width);
        sol.UR.y = std::max(sol.UR.y, Blocks[i].y + nodeVec.back().Blocks[i].instance[sp.selected[i]].height);
      }
      sol.area = double(sol.UR.x - sol.LL.x) * double(sol.UR.y - sol.LL.y);
      sol.area_norm = sol.area * 0.1 / designData.GetMaxBlockAreaSum();
      sol.ratio = double(sol.UR.x - sol.LL.x) / double(sol.UR.y - sol.LL.y);
      sol.HPWL = 0;
      sol.HPWL_extend = 0;
      sol.HPWL_extend_terminal = 0;
      for (const auto& neti : designData.Nets) {
        int HPWL_min_x = sol.UR.x, HPWL_min_y = sol.UR.y, HPWL_max_x = 0, HPWL_max_y = 0;
        int HPWL_extend_min_x = sol.UR.x, HPWL_extend_min_y = sol.UR.y, HPWL_extend_max_x = 0, HPWL_extend_max_y = 0;
        for (const auto& connectedj : neti.connected) {
          if (connectedj.type == placerDB::Block) {
            int iter2 = connectedj.iter2, iter = connectedj.iter;
            for (const auto& centerk : designData.Blocks[iter2][sp.selected[iter2]].blockPins[iter].center) {
              // calculate contact center
              int pin_x = centerk.x;
              int pin_y = centerk.y;
              if (Blocks[iter2].H_flip) pin_x = designData.Blocks[iter2][sp.selected[iter2]].width - pin_x;
              if (Blocks[iter2].V_flip) pin_y = designData.Blocks[iter2][sp.selected[iter2]].height - pin_y;
              pin_x += Blocks[iter2].x;
              pin_y += Blocks[iter2].y;
              HPWL_min_x = std::min(HPWL_min_x, pin_x);
              HPWL_max_x = std::max(HPWL_max_x, pin_x);
              HPWL_min_y = std::min(HPWL_min_y, pin_y);
              HPWL_max_y = std::max(HPWL_max_y, pin_y);
            }
            for (const auto& boundaryk : designData.Blocks[iter2][sp.selected[iter2]].blockPins[iter].boundary) {
              int pin_llx = boundaryk.polygon[0].x, pin_urx = boundaryk.polygon[2].x;
              int pin_lly = boundaryk.polygon[0].y, pin_ury = boundaryk.polygon[2].y;
              if (Blocks[iter2].H_flip) {
                pin_llx = designData.Blocks[iter2][sp.selected[iter2]].width - boundaryk.polygon[2].x;
                pin_urx = designData.Blocks[iter2][sp.selected[iter2]].width - boundaryk.polygon[0].x;
              }
              if (Blocks[iter2].V_flip) {
                pin_lly = designData.Blocks[iter2][sp.selected[iter2]].height - boundaryk.polygon[2].y;
                pin_ury = designData.Blocks[iter2][sp.selected[iter2]].height - boundaryk.polygon[0].y;
              }
              pin_llx += Blocks[iter2].x;
              pin_urx += Blocks[iter2].x;
              pin_lly += Blocks[iter2].y;
              pin_ury += Blocks[iter2].y;
              HPWL_extend_min_x = std::min(HPWL_extend_min_x, pin_llx);
              HPWL_extend_max_x = std::max(HPWL_extend_max_x, pin_urx);
              HPWL_extend_min_y = std::min(HPWL_extend_min_y, pin_lly);
              HPWL_extend_max_y = std::max(HPWL_extend_max_y, pin_ury);
            }
          }
        }
        sol.HPWL += (HPWL_max_y - HPWL_min_y) + (HPWL_max_x - HPWL_min_x);
        sol.HPWL_extend += (HPWL_extend_max_y - HPWL_extend_min_y) + (HPWL_extend_max_x - HPWL_extend_min_x);
        bool is_terminal_net = false;
        for (const auto& c : neti.connected) {
          if (c.type == placerDB::Terminal) {
            is_terminal_net = true;
            break;
          }
        }
        if (is_terminal_net) sol.HPWL_extend_terminal += (HPWL_extend_max_y - HPWL_extend_min_y) + (HPWL_extend_max_x - HPWL_extend_min_x);
      }
      if (!designData.Nets.empty()) sol.HPWL_norm = sol.HPWL_extend / designData.GetMaxBlockHPWLSum() / double(designData.Nets.size());
      sol.cost = sol.CalculateCost(designData, sp);
      spVec[idx].second.updateTerminalCenter(designData, spVec[idx].first);
      spVec[idx].second.WritePlacement(designData, spVec[idx].first, opath + nodeVec.back().name + "_" + std::to_string(idx) + ".pl");
      spVec[idx].second.PlotPlacement(designData, spVec[idx].first, opath + nodeVec.back().name + "_" + std::to_string(idx) + ".plt");
      spVec[idx].second.UpdateHierNode(designData, spVec[idx].first, nodeVec[idx], drcInfo);
    }
  }
}

// PnRDB::hierNode Placer::CheckoutHierNode() {
//  return this->node;
//}





std::map<double, std::pair<SeqPair, ILP_solver>> Placer::PlacementCoreAspectRatio_ILP(design& designData, SeqPair& curr_sp, ILP_solver& curr_sol, int mode,
                                                                                      int nodeSize, int effort, PnRDB::Drc_info& drcInfo) {
  auto logger = spdlog::default_logger()->clone("placer.Placer.PlacementCoreAspectRatio_ILP");

  // Mode 0: graph bias; Mode 1: graph bias + net margin; Others: no bias/margin
  // cout<<"PlacementCore\n";
  std::map<double, std::pair<SeqPair, ILP_solver>> oData;
  //curr_sp.PrintSeqPair();
  double curr_cost = 0;
  int trial_count = 0;
  double mean_cache_miss{0};
  int num_perturb{0};

  if (!curr_sp.Enumerate() && hyper.use_ILP_placer) {
    logger->info("Placing using ILP");
    oData = curr_sol.PlaceUsingILP(designData, curr_sp, drcInfo, hyper.NUM_THREADS, nodeSize);
    if (!oData.empty()) {
      ReshapeSeqPairMap(oData, nodeSize);
      return oData;
    }
  }

  unsigned int seed = 0;
  if (hyper.SEED > 0) {
    seed = hyper.SEED;
    srand(seed);
    logger->debug("Random number generator seed={0}", seed);
  }

  if (curr_sp.Enumerate()) {
    const auto maxcount = ceil(log(hyper.T_MIN / hyper.T_INT) / log(hyper.ALPHA));
    size_t cnt{0};
    while (!curr_sp.EnumExhausted()) {
      ILP_solver tsol(designData, hyper.ilp_solver);
      curr_cost = tsol.GenerateValidSolution(designData, curr_sp, drcInfo, hyper.NUM_THREADS);
      tsol.cost = curr_cost;
      logger->debug("Solving enumeration {0} cost {1}", cnt, curr_cost);
      if (curr_cost >= 0) {
        oData[curr_cost] = std::make_pair(curr_sp, tsol);
        ReshapeSeqPairMap(oData, nodeSize);
      }
      curr_sp.PerturbationNew(designData);
      ++cnt;
      if (cnt >= maxcount) break; // should never happen; guard against any unseen scenario
    }
    if (curr_sp.EnumExhausted()) {
      logger->info("Exhausted all permutations of seq pairs and found {0} placement solution(s)", oData.size());
      return oData;
    }
    assert(0);
  }

  while (++trial_count < hyper.max_init_trial_count) {
    // curr_cost negative means infeasible (do not satisfy placement constraints)
    // Only positive curr_cost value is accepted.

    if (!curr_sp.isSeqInCache(designData)) {
      if (hyper.select_in_ILP)
        curr_cost = curr_sol.GenerateValidSolution_select(designData, curr_sp, drcInfo);
      else
        curr_cost = curr_sol.GenerateValidSolution(designData, curr_sp, drcInfo, hyper.NUM_THREADS);
      curr_sol.cost = curr_cost;
      curr_sp.cacheSeq(designData, curr_cost);
    }

    logger->debug("trial_count {0} curr_cost {1} ", trial_count, curr_cost);

    if (curr_cost > 0) {
      logger->info("Required {0} perturbations to generate a feasible solution.", trial_count);
      break;
    } else {
      curr_sp.PerturbationNew(designData);
    }
  }

  if (curr_cost < 0) {
    logger->error("Couldn't generate a feasible solution even after {0} perturbations.", hyper.max_init_trial_count);
    curr_cost = __DBL_MAX__;
  }

  curr_sol.cost = curr_cost;
  oData[curr_cost] = std::make_pair(curr_sp, curr_sol);
  ReshapeSeqPairMap(oData, nodeSize);

  // Simulated annealing
  double T = hyper.T_INT;
  double delta_cost;
  int update_index = 0;
  int T_index = 0;
  float per = 0.1;
  // int updateThrd = 100;
  float total_update_number = log(hyper.T_MIN / hyper.T_INT) / log(hyper.ALPHA);
  int total_candidates = 0;
  int total_candidates_infeasible = 0;

  logger->debug("sa__cost name={0} t_index={1} effort={2} cost={3} temp={4}", designData.name, T_index, 0, curr_cost, T);

  while (T > hyper.T_MIN) {
    int i = 1;
    int MAX_Iter = 1;
    if (effort <= 0) {
      MAX_Iter = 1;
    } else {
      MAX_Iter = effort;
    }
    while (i <= MAX_Iter) {

      // TODO: Refactor the logic below so that we never ever solve ILP for a SP that has been solved in the past!
      //  Store cost to the sequence pair cache 

      // cout<<"T "<<T<<" i "<<i<<endl;
      // Trival moves
      SeqPair trial_sp(curr_sp);
      // cout<<"before per"<<endl; trial_sp.PrintSeqPair();
      // SY: PerturbationNew honors order and symmetry. What could make the trial_sp infeasible? Aspect ratio, Align?
      int trial_cached = 0;
      while (++trial_cached < hyper.max_cache_hit_count) {
        if (!trial_sp.PerturbationNew(designData)) continue;
        if (!trial_sp.isSeqInCache(designData)) {
          break;
        }
      }
      mean_cache_miss += trial_cached;
      ++num_perturb;
      // cout<<"after per"<<endl; trial_sp.PrintSeqPair();
      ILP_solver trial_sol(designData, hyper.ilp_solver);
      double trial_cost = 0;
      bool fromCache{false};
      if (!trial_sp.isSeqInCache(designData, &trial_cost)) {
        if (hyper.select_in_ILP)
          trial_cost = trial_sol.GenerateValidSolution_select(designData, trial_sp, drcInfo);
        else
          trial_cost = trial_sol.GenerateValidSolution(designData, trial_sp, drcInfo, hyper.NUM_THREADS);
        trial_sp.cacheSeq(designData, trial_cost);
        if (trial_cost >= 0) {
          oData[trial_cost] = std::make_pair(trial_sp, trial_sol);
        }
      } else {
          fromCache = true;
      }
      /*if (designData._debugofs.is_open()) {
              designData._debugofs << "sp__cost : " << trial_sp.getLexIndex(designData) << ' ' << trial_cost << '\n';
      }*/
      total_candidates += 1;
      if (trial_cost >= 0) {
        bool Smark{false};
        delta_cost = trial_cost - curr_cost;
        if (delta_cost < 0) {
          Smark = true;
          logger->debug("sa__accept_better T={0} delta_cost={1} ", T, delta_cost);
        } else {
          double r = (double)rand() / RAND_MAX;
          // De-normalize the delta cost
          delta_cost = exp(delta_cost);
          if (r < exp((-1.0 * delta_cost) / T)) {
            Smark = true;
            logger->debug("sa__climbing_up T={0} delta_cost={1}", T, delta_cost);
          }
        }
        if (Smark) {
          if (fromCache) {
            if (hyper.select_in_ILP)
              trial_cost = trial_sol.GenerateValidSolution_select(designData, trial_sp, drcInfo);
            else
              trial_cost = trial_sol.GenerateValidSolution(designData, trial_sp, drcInfo, hyper.NUM_THREADS);
          }
          curr_cost = trial_cost;
          curr_sp = trial_sp;
          curr_sol = trial_sol;
          curr_sol.cost = curr_cost;
        }
      } else {
        ++total_candidates_infeasible;
        // logger->debug("sa__infeasible_candidate i={1}/{2} T={0} ", T, i, MAX_Iter);
      }
      ReshapeSeqPairMap(oData, nodeSize);
      // logger->debug("sa__cost name={0} t_index={1} effort={2} cost={3} temp={4}", designData.name, T_index, i, curr_cost, T);
      i++;
      update_index++;
    }
    T_index++;
    if (total_update_number * per < T_index) {
      logger->info("..... {0} %", (int)(per * 100));
      per = per + 0.1;
    }
    T *= hyper.ALPHA;
    // logger->debug("sa__reducing_temp T={0}", T);
  }

  if (num_perturb) mean_cache_miss /= num_perturb;
  logger->debug("sa__summary total_candidates={0} total_candidates_infeasible={1} mean_cache_miss={2}", total_candidates, total_candidates_infeasible,
               mean_cache_miss);

  // Write out placement results
  // cout << endl << "Placer-Info: optimal cost = " << curr_cost << endl;
  // curr_sp.PrintSeqPair();
  // curr_sol.updateTerminalCenter(designData, curr_sp);
  return oData;
}

void Placer::ReshapeSeqPairMap(std::map<double, SeqPair>& spMap, int nodeSize) {
  int idx = 0;
  std::map<double, SeqPair>::iterator it;
  for (it = spMap.begin(); it != spMap.end(); ++it, ++idx) {
    if (idx == nodeSize) {
      break;
    }
  }
  if (it != spMap.end()) {
    spMap.erase(it, spMap.end());
  }
}

void Placer::ReshapeSeqPairMap(std::map<double, std::pair<SeqPair, ILP_solver>>& Map, int nodeSize) {
  int idx = 0;
  auto it = Map.begin();
  for (; it != Map.end(); ++it, ++idx) {
    if (idx == nodeSize) {
      break;
    }
  }
  if (it != Map.end()) {
    Map.erase(it, Map.end());
  }
}

void Placer::PlacementRegularAspectRatio_ILP(std::vector<PnRDB::hierNode>& nodeVec, string opath, int effort, PnRDB::Drc_info& drcInfo) {
  auto logger = spdlog::default_logger()->clone("placer.Placer.PlacementRegularAspectRatio_ILP");
  int nodeSize = nodeVec.size();
// cout<<"Placer-Info: place "<<nodeVec.back().name<<" in aspect ratio mode "<<endl;
#ifdef RFLAG
  // cout<<"Placer-Info: run in random mode..."<<endl;
  srand(time(NULL));
#endif
#ifndef RFLAG
  // cout<<"Placer-Info: run in normal mode..."<<endl;
  srand(0);
#endif
  int mode = 0;
  // Read design netlist and constraints
  design designData(nodeVec.back(), drcInfo, hyper.SEED);
  _rng.seed(hyper.SEED);
  //designData.PrintDesign();
  // Initialize simulate annealing with initial solution
  SeqPair curr_sp(designData, ceil(log(hyper.T_MIN / hyper.T_INT) / log(hyper.ALPHA) * ((effort == 0) ? 1. : effort)));
  // curr_sp.PrintSeqPair();
  ILP_solver curr_sol(designData, hyper.ilp_solver);
  // clock_t start, finish;
  // double   duration;
  // start = clock();
  auto spVec = PlacementCoreAspectRatio_ILP(designData, curr_sp, curr_sol, mode, nodeSize, effort, drcInfo);
  // finish = clock();
  // duration = (double)(finish - start) / CLOCKS_PER_SEC;
  // logger->info("lpsolve time: {0}", duration);
  // curr_sol.updateTerminalCenter(designData, curr_sp);
  // curr_sol.PlotPlacement(designData, curr_sp, opath+nodeVec.back().name+"opt.plt");
  if ((int)spVec.size() < nodeSize) {
    nodeSize = spVec.size();
    nodeVec.resize(nodeSize);
  }
  int idx = 0;
  for (auto it = spVec.begin(); it != spVec.end() and idx < nodeSize; ++it, ++idx) {
    // std::cout<<"Placer-Info: cost "<<it->first<<std::endl;
    // vec_sol.ConstraintGraph(designData, it->second);
    // vec_sol.updateTerminalCenter(designData, it->second);
    // std::cout<<"wbxu check design\n";
    // designData.PrintDesign();
    // it->second.PrintSeqPair();
    // std::cout<<"write design "<<idx<<std::endl;
    it->second.second.updateTerminalCenter(designData, it->second.first);
    it->second.second.WritePlacement(designData, it->second.first, opath + nodeVec.back().name + "_" + std::to_string(idx) + ".pl");
    it->second.second.PlotPlacement(designData, it->second.first, opath + nodeVec.back().name + "_" + std::to_string(idx) + ".plt");
    it->second.second.UpdateHierNode(designData, it->second.first, nodeVec[idx], drcInfo);
  }
}

void Placer::PlacementRegularAspectRatio_ILP_Analytical(std::vector<PnRDB::hierNode>& nodeVec, string opath, int effort, PnRDB::Drc_info& drcInfo) {
  auto logger = spdlog::default_logger()->clone("placer.Placer.PlacementRegularAspectRatio_ILP");
  int nodeSize = nodeVec.size();
// cout<<"Placer-Info: place "<<nodeVec.back().name<<" in aspect ratio mode "<<endl;
#ifdef RFLAG
  // cout<<"Placer-Info: run in random mode..."<<endl;
  srand(time(NULL));
#endif
#ifndef RFLAG
  // cout<<"Placer-Info: run in normal mode..."<<endl;
  srand(0);
#endif
  // int mode=0;
  // Read design netlist and constraints
  design designData(nodeVec.back(),drcInfo);
  // designData.PrintDesign();
  // Initialize simulate annealing with initial solution
  // SeqPair curr_sp(designData);
  // curr_sp.PrintSeqPair();
  ILP_solver curr_sol(designData, nodeVec.back());
  curr_sol.GenerateValidSolutionAnalytical(designData, drcInfo, nodeVec.back());
  curr_sol.updateTerminalCenterAnalytical(designData);
  //curr_sol.PlotPlacementAnalytical(designData, opath + nodeVec.back().name + "_" + std::to_string(0) + ".plt", false, false, false);
  curr_sol.UpdateHierNodeAnalytical(designData, nodeVec.back(), drcInfo);
  // std::map<double, std::pair<SeqPair, ILP_solver>> spVec=PlacementCoreAspectRatio_ILP(designData, curr_sp, curr_sol, mode, nodeSize, effort, drcInfo);
  // curr_sol.updateTerminalCenter(designData, curr_sp);
  // curr_sol.PlotPlacement(designData, curr_sp, opath+nodeVec.back().name+"opt.plt");
  // if((int)spVec.size()<nodeSize) {
  // nodeSize=spVec.size();
  // nodeVec.resize(nodeSize);
  //}
  // int idx=0;
  // for(std::map<double, std::pair<SeqPair, ILP_solver>>::iterator it=spVec.begin(); it!=spVec.end() and idx<nodeSize; ++it, ++idx) {
  // std::cout<<"Placer-Info: cost "<<it->first<<std::endl;
  // vec_sol.ConstraintGraph(designData, it->second);
  // vec_sol.updateTerminalCenter(designData, it->second);
  // std::cout<<"wbxu check design\n";
  // designData.PrintDesign();
  // it->second.PrintSeqPair();
  // std::cout<<"write design "<<idx<<std::endl;
  //
  // it->second.second.WritePlacement(designData, it->second.first, opath + nodeVec.back().name + "_" + std::to_string(idx) + ".pl");
  // it->second.second.PlotPlacement(designData, it->second.first, opath + nodeVec.back().name + "_" + std::to_string(idx) + ".plt");
  //}
}

