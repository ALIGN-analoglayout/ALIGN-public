#ifndef PLACERHYPERPARAMETERS_H_
#define PLACERHYPERPARAMETERS_H_

#include <string>

class PlacerHyperparameters {
  public:
  double T_INT = 1e6;
  double T_MIN = 1e-6;
  double ALPHA = 0.995;
  int SEED = 0;
  int COUNT_LIMIT = 200;

  // this needs to be connected to both the log-based cost funciton and the ILP formulation
  double LAMBDA = 1.0;

  bool use_analytical_placer = false;
  std::string placement_info_json; // Should be initialized to the empty string
  bool use_external_placement_info = false;
  int max_init_trial_count = 10000, max_cache_hit_count = 10;
};

#endif
