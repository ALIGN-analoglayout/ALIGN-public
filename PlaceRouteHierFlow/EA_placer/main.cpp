#include <iostream>

#include "placement.h"
//#include "layoutInfo.h"
//#include "legalization.h"

extern "C"{
#include "FFT/fft.h"
}


int main() {

    // grid_point a;
    Placement p2;

    //generating a test data for placer
    p2.generate_testing_data();
    std::cout<<"generate_testing_data"<<std::endl;
    p2.E_Placer();
    std::cout<<"generate_testing_data"<<std::endl;
    //compara fast exp and exp
    /*
    float result_fast = p2.Fast_Exp(1.2/0.1);
    float result_exp = p2.Exp_Function(1.2,0.1);
    std::cout<<"result_fast "<<result_fast<<std::endl;
    std::cout<<"result_exp "<<result_exp<<std::endl;
    */

    // Initialize layout information
    //LayoutInfo layoutInfo;
    //layoutInfo.init();

    // Do legalization for all blocks
    //Legalizer lg;
    //lg.roughLegalization(layoutInfo);
    
    std::cout << "End of placement" << endl;
    return 0;
}
