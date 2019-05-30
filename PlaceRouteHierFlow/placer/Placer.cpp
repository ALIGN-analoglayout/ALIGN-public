#include "Placer.h"
#define NUM_THREADS 8

Placer::Placer(PnRDB::hierNode& node) {
  //cout<<"Constructor placer"<<endl;
  //this->node=input_node;
  //this->designData=design(input_node);
  //cout<<"Complete construction"<<endl;
  //this->designData.PrintDesign();
  Placement(node);
}

//PnRDB::hierNode Placer::CheckoutHierNode() {
//  return this->node;
//}

bool Placer::GenerateValidSolution(design& mydesign, SeqPair& curr_sp, ConstGraph& curr_sol) {
  bool valid=false;
  int extCount=0;
  while( !valid ) {
    //cout<<"extCount "<<extCount<<endl;
    // 1. Check feasible sequence pair and perturbate seqeucen pair
    int intCount=0;
    bool spCheck;
    while( spCheck=curr_sp.FastInitialScan(mydesign) and intCount<COUNT_LIMIT ) {
      curr_sp.Perturbation(mydesign);
      //cout<<"intCount "<<intCount<<endl;
      intCount++;
    }
    // If no feasible sequence pair, break out
    if (spCheck) { 
      //cout<<"Placer-Warning: try "<<COUNT_LIMIT <<" perturbtions, but fail in generating feasible sequence pair..."<<endl;
      //cout<<"Placer-Warning: use one solution without constraints instead!"<<endl;
      //ConstGraph infea_sol(mydesign, curr_sp);
      //infea_sol.AddLargePenalty(); // ensure this infeasible soluton has huge cost
      //curr_sol=infea_sol;
      return false; 
    }
    //curr_sp.PrintSeqPair();
    // 2. Generate constraint graphs
    ConstGraph try_sol(mydesign, curr_sp);
    valid=try_sol.ConstraintGraph(mydesign, curr_sp);
    //cout<<"Valid ? "<<valid<<endl;
    //try_sol.CalculateCost(mydesign, curr_sp);
    //cout<<"Check "<<try_sol.FastInitialScan()<<endl;
    if (valid) {
      // If construct graphs sucessfully
      if( try_sol.FastInitialScan() ) { // If violation found
        if (extCount>=COUNT_LIMIT) { // If too many iteratons
          //cout<<"Placer-Warning: try "<<COUNT_LIMIT <<" perturbtions, but fail in generating feasible solution without violations..."<<endl;
          //cout<<"Placer-Warning: use one solution with violations instead!"<<endl;
          //curr_sol=try_sol;
          return false;
        } else {
          curr_sp.Perturbation(mydesign); valid=false;
        }
      } else { // If no violation
        curr_sol=try_sol; return true;
      }
    } else {
      // If fail in construction
      if (extCount>=COUNT_LIMIT) { // If too many iteratons
        //cout<<"Placer-Warning: try "<<COUNT_LIMIT <<" perturbtions, but fail in generating feasible constraint graphs..."<<endl;
        //cout<<"Placer-Warning: use one solution with partial constraints instead!"<<endl;
        //try_sol.AddLargePenalty(); // ensure this infeasible soluton has huge cost
        //curr_sol=try_sol;
        return false;
      } else {
        curr_sp.Perturbation(mydesign); valid=false;
      }
    }
    extCount++;
  }
  return false;
}


void Placer::ThreadFunc(Thread_data* MT) {
   MT->thread_trial_sp.Perturbation(MT->thread_designData);
   MT->thread_succeed=GenerateValidSolution(MT->thread_designData, MT->thread_trial_sp, MT->thread_trial_sol);
   if (MT->thread_succeed) {
     MT->thread_trial_cost=MT->thread_trial_sol.CalculateCost(MT->thread_designData, MT->thread_trial_sp);
   }
};

void Placer::Placement(PnRDB::hierNode& node) {
  cout<<"Placer-Info: place "<<node.name<<endl;
  #ifdef RFLAG
  cout<<"Placer-Info: run in random mode..."<<endl;
  srand (time(NULL));
  #endif
  #ifndef RFLAG
  cout<<"Placer-Info: run in normal mode..."<<endl;
  srand(0);
  #endif

  // Read design netlist and constraints
  //design designData(bfile.c_str(), nfile.c_str(), cfile.c_str());
  design designData(node);
  designData.PrintDesign();
  // Initialize simulate annealing with initial solution
  SeqPair curr_sp(designData);
  //curr_sp.PrintSeqPair();
  ConstGraph curr_sol;
  GenerateValidSolution(designData, curr_sp, curr_sol);
  //curr_sol.PrintConstGraph();
  double curr_cost=curr_sol.CalculateCost(designData, curr_sp);
  cout<<"Placer-Info: initial cost = "<<curr_cost<<endl;

  cout<<"Placer-Info: status ";cout.flush();
  // Aimulate annealing
  double T=T_INT;
  double delta_cost;
  int update_index =0;
  int T_index=0;
  float per = 0.1;
  float total_update_number = log(T_MIN/T_INT)/log(ALPHA);
  while(T>T_MIN) {
    int i=1;
    while(i<=1) {
      #ifdef MTMODE
      double trial_cost; 
      int id; int good_idx=-1;
      Thread_data td[NUM_THREADS];
      std::vector<std::thread> threads;
      // Create threads
      for( id = 0; id < NUM_THREADS; id++ ) {
        //cout <<"Placer-Info: creating thread, " << id << endl;
        td[id].thread_id = id;
        td[id].thread_designData=designData;
        td[id].thread_trial_sp=curr_sp;
        threads.push_back(std::thread(&Placer::ThreadFunc, this, td+id ) );
      }
      // Join threads
      for( id = 0; id < NUM_THREADS; id++ ) {
        threads.at(id).join();
        //cout<<"Placer-Info: joining thread, "<<id<<endl;
      }

      for( id = 0; id < NUM_THREADS; id++ ) {
        if( td[id].thread_succeed) {trial_cost=td[id].thread_trial_cost; good_idx=id; break;}
      }
      for( ; id < NUM_THREADS; id++ ) {
        if( td[id].thread_succeed and td[id].thread_trial_cost<trial_cost) {
          trial_cost=td[id].thread_trial_cost; good_idx=id;
        }
      }
      if(good_idx!=-1) {
        delta_cost=trial_cost-curr_cost;
        if(delta_cost<0) {
          curr_cost=trial_cost;
          curr_sp=td[good_idx].thread_trial_sp;
          curr_sol=td[good_idx].thread_trial_sol;
        } else {
          double r = (double)rand() / RAND_MAX;
          if( r < exp( (-1.0 * delta_cost)/T ) ) {
            curr_cost=trial_cost;
            curr_sp=td[good_idx].thread_trial_sp;
            curr_sol=td[good_idx].thread_trial_sol;
          }
        }
      }
      #endif

      #ifndef MTMODE
      double trial_cost; 
      //cout<<"T "<<T<<" i "<<i<<endl;
      // Trival moves
      SeqPair trial_sp(curr_sp);  
      //cout<<"before per"<<endl; trial_sp.PrintSeqPair();
      trial_sp.Perturbation(designData);
      //cout<<"after per"<<endl; trial_sp.PrintSeqPair();
      ConstGraph trial_sol;
      if(GenerateValidSolution(designData, trial_sp, trial_sol)) {
        trial_cost=trial_sol.CalculateCost(designData, trial_sp);

        delta_cost=trial_cost-curr_cost;
        if(delta_cost<0) {
          curr_cost=trial_cost;
          curr_sp=trial_sp;
          curr_sol=trial_sol;
        } else {
          double r = (double)rand() / RAND_MAX;
          if( r < exp( (-1.0 * delta_cost)/T ) ) {
            curr_cost=trial_cost;
            curr_sp=trial_sp;
            curr_sol=trial_sol;
          }
        }
      }
      #endif

      i++;
      update_index++;
      //cout<<update_index<<endl;
      if(update_index==100){
        curr_sol.Update_parameters(designData, curr_sp);
        curr_cost = curr_sol.CalculateCost(designData, curr_sp);
      }
    }
    T_index ++;
    if(total_update_number*per<T_index){
      cout<<"....."<<per*100<<"%"; cout.flush();
      per=per+0.1;
    }
    T*=ALPHA;
    //cout<<T<<endl;
  }

  // Write out placement results
  cout<<endl<<"Placer-Info: optimal cost = "<<curr_cost<<endl;
  //curr_sol.PrintConstGraph();
  //curr_sp.PrintSeqPair();
  curr_sol.updateTerminalCenter(designData, curr_sp);
  curr_sol.WritePlacement(designData, curr_sp, "./"+node.name+".pl");
  curr_sol.PlotPlacement(designData, curr_sp, "./"+node.name+".plt");
  curr_sol.UpdateHierNode(designData, curr_sp, node);
  //curr_sol.WritePlacement(designData, curr_sp, ofile.c_str());
  //curr_sol.PlotPlacement(designData, curr_sp, pfile.c_str());
}

