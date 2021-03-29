#ifndef PLACEMENT_H
#define PLACEMENT_H
#include "Pdatatype.h"
#include "FFT/fft.h"
#include "../PnRDB/datatype.h"
#include <iostream>
#include <cmath>
#include <random>
#include <set>
#include <fstream>
#include <string>

using namespace std;

class Placement {

private:
    int temp = 0; // for testing the code
    Ppoint_F Chip_D; //chip dimension for the placement
    Ppoint_F Bin_D; // Dimensions for each bin
    vector<block> Blocks; //blocks
    vector<net> Nets; //nets
    vector<vector<bin> > Bins; //bins inside the chip
    vector<vector<Ppoint_F> > symmetric_force_matrix;// sysmmtric force=M *x(y)
    vector<Alignment> Alignment_blocks;//store the alignment constrains.
    vector<AlignBlock> AlignBlocks;
    vector<pair<vector<int>, PnRDB::Smark>> Ordering_Constraints;//as same in PnRDB
    float gammar = 1.0f; //Q: need to ajust
    float lambda= 1.0f; //Q: need to ajust
    float beta = 1.0f;
    float sym_beta = 0.01f;//weigth for sym force,  need to ajust

    // for blocks
    float unit_x;
    float unit_y;
    int x_dimension; //number of bin, number of pe
    int y_dimension; //number of bin, number of pe
  
    // for bins
    float unit_x_bin;
    float unit_y_bin;
    int x_dimension_bin; //number of bin, number of pe
    int y_dimension_bin; //number of bin, number of pe  

    //donghao start
    //estimated required height y and width x, generally x = y
    Ppoint_F est_Size;
    //donghao end  

public:
    Placement();
    Placement(float chip_width, float chip_hight, float bin_width, float bin_hight);
    void Read_In_Blocks_Nets();
    void Create_Placement_Bins();
    void Initilize_Placement();
    void Cal_Density_Eforce();
    void Cal_Net_force();
    void Cal_force();
    void Nesterov_based_iteration(float &ac,vector<float> &uc,vector<float> &vc,vector<float> &vl,vector<float> &pre_vc,vector<float> &pre_vl,bool start_flag);

    //random functions for block and net generation
    void Random_Generation_Block_Nets();

    //small functions
    void Update_Bin_Density();
    bool Find_Common_Area(float x_center_block, float block_width, float x_center_bin, float bin_width, float &common_length);
    void Cal_Eforce_Block(int block_id);
    //functions for lse net smooth
    float Exp_Function(float x, float gammar);
    float LSE_block_N(int block_index, int x_or_y);
    float LSE_block_P(int block_index, int x_or_y);
    float LSE_Net_SUM_N(int net_index, bool x_or_y);
    float LSE_Net_SUM_P(int net_index, bool x_or_y);
    void Cal_LSE_Net_Force();
    //functions for wa net smooth
    float WA_Net_SUM_N(int net_index, bool x_or_y);
    float WA_Net_SUM_P(int net_index, bool x_or_y);
    void Cal_WA_Net_Force();
    //plt file
    void PlotPlacement(int index);
    float Cal_HPWL();
    //
    void BkTrk(float &ac, float &an, vector<float> &uc,vector<float> &vc,vector<float> &vl,vector<float> &pre_vc,vector<float> &pre_vl);
    float vector_fraction(vector<float> &vc, vector<float> &vl, vector<float> &pre_vc,vector<float> &pre_vl);
    void cal_hat_un(float &hat_ac, vector<float> &hat_un, vector<float> &vc, vector<float> &pre_vc);
    void cal_hat_vn(float &ac, float &an, vector<float> &hat_vn, vector<float> &hat_un, vector<float> &uc);
    void pre_conditioner(vector<float> &Pre_Conditioner,bool x_or_y);
    void LSE_pre_conditioner(vector<float> &HPWL_Pre_Conditioner, bool x_or_y);
    void WA_pre_conditioner(vector<float> &HPWL_Pre_Conditioner, bool x_or_y);
    float Fast_Exp(float a);
    void generate_testing_data();

    //
    void E_Placer();
    void Extract_Placement_Vectors(vector<float> &temp_vector, bool x_or_y);
    void Feedback_Placement_Vectors(vector<float> &temp_vector, bool x_or_y);
    void WriteOut_Blocks(int iteration);
    void WriteOut_Bins(int iteration);
    bool Stop_Condition(float density, float &max_density);
    void Pull_back();
    //donghao start
    Placement(PnRDB::hierNode &current_node);

    float readInputNode(PnRDB::hierNode &current_node);//return the total area of all blocks
    void Init_Placement(bool randomFlag);//random flag 0: scale the coordinate value into -1 to 1
    void Unify_blocks(float area, float scale_factor);
    void print_blocks_nets();
    void Cal_sym_Force();
    void read_alignment(PnRDB::hierNode &current_node);
    void read_order(PnRDB::hierNode &current_node);
    void force_alignment();
    void force_order();
    static bool comp_x(Ppoint_F c1, Ppoint_F c2);
    static bool comp_y(Ppoint_F c1, Ppoint_F c2);
    void writeback(PnRDB::hierNode &current_node);
    //donghao end

    float Cal_Overlap();
    void Pull_back_vector(vector<float> &temp_vector, bool x_or_y);
    void Initilize_lambda();
    void Initilize_sym_beta();

};
#endif
