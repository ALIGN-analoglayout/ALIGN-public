#ifndef MNASIMULATION_H_
#define MNASIMULATION_H_

class MNASimulation {

  private:
      std::vector<std::vector<double>> R;
      std::vector<double> I;
      std::vector<double> V;

  public:
      MNASimulation(std::vector<std::vector<double>> &out_R, std::vector<double>& out_I);
      //void ConstructR(PowerGrid &Grid);
      //void ConstructI();
      void SolveIR_drop();

};

#endif
