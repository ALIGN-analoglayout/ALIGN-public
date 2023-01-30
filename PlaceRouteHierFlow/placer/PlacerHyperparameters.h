#ifndef PLACERHYPERPARAMETERS_H_
#define PLACERHYPERPARAMETERS_H_

#include <string>

class PlacerHyperparameters {
  public:
  double T_INT       = 0.5;
  double T_MIN       = 0.05;
  double ALPHA       = 0.995;
  int SEED           = 0;
  size_t SA_MAX_ITER = 10000;

  // this needs to be connected to both the log-based cost funciton and the ILP formulation
  double LAMBDA = 1.0;

  bool use_analytical_placer       = false;
  std::string placement_info_json; // Should be initialized to the empty string
  bool use_external_placement_info = false;
  int max_init_trial_count         = 10000, max_cache_hit_count = 10;

  int NUM_THREADS       = 1;
  bool select_in_ILP    = false;
  int ilp_solver        = 0; // 0 : SYMPHONY, 1 : lpsolve
  bool use_ILP_placer   = false;
  bool use_PT_placer    = false;
  int ILP_runtime_limit = 0;

  double PT_T_INT       = 1.0;
  double PT_T_MIN       = 0.01;
  int PT_NUM_TEMP          = 10;
  int PT_NUM_EXCH_ITERS    = 10;
  int PT_NUM_PERT_PER_ITER = 100;

  std::string place_on_grid_constraints_json;
};

#endif
