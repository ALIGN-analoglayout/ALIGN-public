#include "MNASimulation.h"
#include "slu_ddefs.h"

int main(){

  boost_matrix out_R,out_I;
  std::vector<std::vector<double>> Rstore,Istore,Vstore;
	/*
  Rstore.push_back(std::vector<double>{1,2,1});
  Istore.push_back(std::vector<double>{0,1,0.5});
  Vstore.push_back(std::vector<double>{2,0,1});
*/
  Rstore.push_back(std::vector<double>{0,2,4});
  Rstore.push_back(std::vector<double>{1,2,2});
  Rstore.push_back(std::vector<double>{0,3,8});
  Istore.push_back(std::vector<double>{2,1,1});
  Vstore.push_back(std::vector<double>{1,0,4});
  Vstore.push_back(std::vector<double>{3,2,8});
  MNASimulation A(out_R, out_I);
  A.ConstructR(Rstore,Vstore);
  A.ConstructI(Istore,Vstore,Rstore);
  A.SolveIR_drop();
  
  return 0;
}
