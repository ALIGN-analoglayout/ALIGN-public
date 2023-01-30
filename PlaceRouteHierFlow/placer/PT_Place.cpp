#include "ILP_solver.h"

#include <stdexcept>
#include <algorithm>

#include "spdlog/spdlog.h"
#include "ILPSolverIf.h"
#include <signal.h>
#define BOOST_ALLOW_DEPRECATED_HEADERS
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/connected_components.hpp>


void ILP_solver::Metropolis(const double T, const int Numiter, const PnRDB::Drc_info& drcInfo, SeqPair& curr_sp, double& curr_cost, ILP_solver& curr_sol, const design& designData, const PlacerHyperparameters& hyper, SolutionMapSL& sol, const int iternum) {
  std::map<double, std::pair<SeqPair, ILP_solver>> oData;
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.Metropolis");

  double delta_cost{0.};
  for (int metiter = 0; metiter < Numiter; ++metiter) {
    SeqPair trial_sp(curr_sp);
    int trial_cached = 0;
    while (++trial_cached < hyper.max_cache_hit_count) {
      if (!trial_sp.PerturbationNew(const_cast<design&>(designData))) continue;
      if (!trial_sp.isSeqInCache(designData)) {
        break;
      }
    }
    ILP_solver trial_sol(const_cast<design&>(designData), hyper.ilp_solver);
    double trial_cost = 0;
    bool fromCache{false};
    if (!trial_sp.isSeqInCache(designData, &trial_cost)) {
      if (hyper.select_in_ILP)
        trial_cost = trial_sol.GenerateValidSolution_select(const_cast<design&>(designData), trial_sp, const_cast<PnRDB::Drc_info&>(drcInfo));
      else
        trial_cost = trial_sol.GenerateValidSolution(const_cast<design&>(designData), trial_sp, const_cast<PnRDB::Drc_info&>(drcInfo), hyper.NUM_THREADS);
      trial_sp.cacheSeq(const_cast<design&>(designData), trial_cost);
    } else {
      fromCache = true;
    }
    if (trial_cost >= 0) {
      bool Smark{false};
      delta_cost = trial_cost - curr_cost;
      if (delta_cost < 0 || curr_cost < 0) {
        Smark = true;
      } else {
        double r = (double)rand() / RAND_MAX;
        // De-normalize the delta cost
        delta_cost = exp(delta_cost);
        if (r < exp((-1.0 * delta_cost) / T)) {
          Smark = true;
        }
      }
      if (Smark) {
        if (fromCache) {
          if (hyper.select_in_ILP)
            trial_cost = trial_sol.GenerateValidSolution_select(const_cast<design&>(designData), trial_sp, const_cast<PnRDB::Drc_info&>(drcInfo));
          else
            trial_cost = trial_sol.GenerateValidSolution(const_cast<design&>(designData), trial_sp, const_cast<PnRDB::Drc_info&>(drcInfo), hyper.NUM_THREADS);
        }
        curr_cost = trial_cost;
        curr_sp = trial_sp;
        curr_sol = trial_sol;
        curr_sol.cost = curr_cost;
        sol.insert(curr_cost, std::make_pair(curr_sp, curr_sol));
        logger->debug("accepted cost : {0} {1} {2}", T, (iternum * Numiter + metiter), curr_cost);
      }
    }
  }
}

SolutionMap ILP_solver::PlaceUsingPT(const design& designData, const SeqPair& first_sp, const PnRDB::Drc_info& drcInfo, const PlacerHyperparameters& hyper, const int numsol) {

  SolutionMapSL sol(numsol);
  if (designData.Blocks.empty()) return sol.val();
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.PlaceUsingPT");
  ++const_cast<design&>(designData)._totalNumCostCalc;
  double decay = exp(log(hyper.PT_T_MIN / hyper.PT_T_INT) / (hyper.PT_NUM_TEMP - 1));
  ILP_solver curr_sol[hyper.PT_NUM_TEMP];
  SeqPair curr_sp[hyper.PT_NUM_TEMP];
  double curr_cost[hyper.PT_NUM_TEMP];

  curr_sp[0] = first_sp;

  double T[hyper.PT_NUM_TEMP];
  T[0] = hyper.PT_T_INT;
  for (int iT = 0; iT < hyper.PT_NUM_TEMP; ++iT) {
    curr_cost[iT] = -1;
    curr_sol[iT] = *this;
    if (iT > 0) T[iT] = T[iT - 1] * decay;
  }
  for (int iT = 0; iT < hyper.PT_NUM_TEMP; ++iT) {
    if (iT > 0) curr_sp[iT] = curr_sp[iT - 1];
    int trial_count{0};
    while (++trial_count < hyper.max_init_trial_count) {
      if (!curr_sp[iT].isSeqInCache(designData)) {
        curr_cost[iT] = curr_sol[iT].GenerateValidSolution(designData, curr_sp[iT], drcInfo, hyper.NUM_THREADS);
        curr_sol[iT].cost = curr_cost[iT];
        curr_sp[iT].cacheSeq(const_cast<design&>(designData), curr_cost[iT]);
      }
      if (curr_cost[iT] > 0) {
        logger->info("Required {0} perturbations to generate a feasible solution.", trial_count);
        break;
      } else {
        curr_sp[iT].PerturbationNew(const_cast<design&>(designData));
      }
    }
  }

  srand(hyper.SEED);
  for (int iexch = 0; iexch < hyper.PT_NUM_EXCH_ITERS; ++iexch) {
    for (int iT = 0; iT < hyper.PT_NUM_TEMP; ++iT) {
      Metropolis(T[iT], hyper.PT_NUM_PERT_PER_ITER, drcInfo, curr_sp[iT], curr_cost[iT], curr_sol[iT], designData, hyper, sol, iexch);
    }
    int numswaps = const_cast<design&>(designData).rand() % (hyper.PT_NUM_TEMP / 2) + 1;
    std::set<int> usedindices;
    std::set<std::pair<int,int>> swappairs, usedpairs;
    for (int i = 0; i < numswaps; ++i) {
      int index{-1}, numattempts{0};
      for (int nattempts = 0; nattempts <100 ; ++nattempts) {
        index = ( const_cast<design&>(designData).rand() % hyper.PT_NUM_TEMP);
        if (index == hyper.PT_NUM_TEMP - 1) --index;
        if (usedindices.find(index) == usedindices.end() && usedindices.find(index + 1) == usedindices.end()) {
          usedindices.insert(index);
          usedindices.insert(index + 1);
          swappairs.insert(std::make_pair(index, index + 1));
          break;
        } else index = -1;
      }
      if (index >= 0) {
        double delta_cost = exp(curr_cost[index] - curr_cost[index + 1]);
        double prob = min(1., exp(- delta_cost * (1./T[index] - 1./T[index + 1])));
        double r = (double)rand() / RAND_MAX;
        if (r < prob) {
          std::swap(curr_sp[index], curr_sp[index + 1]);
          std::swap(curr_cost[index], curr_cost[index + 1]);
          std::swap(curr_sol[index], curr_sol[index + 1]);
          usedpairs.insert(std::make_pair(index, index + 1));
        }
      }
    }
    std::string swapstr, usedstr;
    for (auto& v : swappairs) swapstr += (" (" + std::to_string(v.first) + "," + std::to_string(v.second) + ")");
    for (auto& v : usedpairs) usedstr += (" (" + std::to_string(v.first) + "," + std::to_string(v.second) + ")");
    logger->info("numswaps : {0}, swapped :{1} used :{2}", numswaps, swapstr, usedstr);
  }
  return sol.val();
}
