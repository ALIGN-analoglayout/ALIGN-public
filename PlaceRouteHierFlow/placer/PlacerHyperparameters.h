#ifndef PLACERHYPERPARAMETERS_H_
#define PLACERHYPERPARAMETERS_H_

class PlacerHyperparameters {
public:  
  double T_INT = 1e6;
  double T_MIN = 1e-6;
  double ALPHA = 0.995;
  int COUNT_LIMIT = 200;
};

#endif
