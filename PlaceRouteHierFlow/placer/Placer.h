#ifndef PLACER_H_
#define PLACER_H_

#include <thread>
#include <stdlib.h>     /* srand, rand */
#include <time.h>       /* time */
#include <cmath>
#include "design.h"
#include "SeqPair.h"
#include "ConstGraph.h"
#include "../PnRDB/datatype.h"
using std::cout;
using std::endl;

//#define MAX_TIMEOUT 4300000 //4.3 seconds = 4300000 us
#define T_INT 1e6
#define T_MIN 1e-5
#define ALPHA 0.85
#define COUNT_LIMIT 200

//#define MTMODE 1 // flag to turn on multi-threading

class Placer {
  private:
    struct Thread_data {
       int  thread_id;
       design thread_designData;
       SeqPair thread_trial_sp;
       ConstGraph thread_trial_sol;
       double thread_trial_cost=0.0;
       bool thread_succeed=false;
    };
    //design designData;
    //PnRDB::hierNode node;
    bool GenerateValidSolution(design& mydesign, SeqPair& curr_sp, ConstGraph& curr_sol);
    void Placement(PnRDB::hierNode& node); // do placement
    void ThreadFunc(Thread_data* MT);

  public:
    Placer(PnRDB::hierNode& node);
    //Placer(PnRDB::hierNode& input_node); // Constructor
    //PnRDB::hierNode CheckoutHierNode(); // Output hier Node after placement
};

#endif
