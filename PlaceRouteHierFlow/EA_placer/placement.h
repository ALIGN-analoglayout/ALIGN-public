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
#ifdef PERFORMANCE_DRIVEN
#include <Python.h>
#endif

using namespace std;

class Placement {

private:
    string circuit_name = "";
    Ppoint_F Chip_BND;  // chip bounday for UT placer
    int temp = 0; // for testing the code
    Ppoint_F Chip_D; //chip dimension for the placement
    Ppoint_F Bin_D; // Dimensions for each bin
    vector<block> Blocks; //blocks
    vector<net> Nets; //nets
    vector<vector<bin> > Bins; //bins inside the chip
    vector<vector<Ppoint_F> > symmetric_force_matrix;// sysmmtric force=M *x(y)
    vector<SymmPairBlock> SPBlocks;
    vector<Alignment> Alignment_blocks;//store the alignment constrains.
    vector<AlignBlock> AlignBlocks;
    vector<pair<vector<int>, PnRDB::Smark>> Ordering_Constraints;//as same in PnRDB
    vector<originBlock> OriginBlocks;
    vector<commonCentroid> commonCentroids;
    map<int, int> new_to_original_block_map;
    map<int, int> original_to_new_block_map;
    map<string, int> cc_name_to_id_map;
    int originalBlockCNT;
    int originalNetCNT;
    float gammar = 1.0f; //Q: need to ajust
    float lambda= 0.01f; //Q: need to ajust
    float beta = 1.0f;
    float sym_beta = 0.01f;//weigth for sym force,  need to ajust
    float area_beta = 0.01f;//weight for area force, need to ajust
    float BND_beta = 0.01f;//weight for area force, need to ajust
    float OL_beta = 0.01f;//weight for area force, need to ajust

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
    Ppoint_F uni_cell;
    Ppoint_F uni_cell_Dpoint;

    float dummy_net_weight;
    float dummy_net_rate;
    float dummy_net_target;
    //donghao end  

public:
    Placement();
    Placement(float chip_width, float chip_hight, float bin_width, float bin_hight);
    void place(PnRDB::hierNode &current_node);
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
    #ifdef PERFORMANCE_DRIVEN
    void performance_gradient(vector<float> &uc_x, vector<float> &uc_y, PyObject *pFun_cal_grad, PyObject *sess, PyObject *X, PyObject *grads);
    #endif
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
    void force_alignment(vector<float> &vc_x,vector<float> &vl_x,vector<float> &vc_y,vector<float> &vl_y);
    void force_order(vector<float> &vc_x,vector<float> &vl_x,vector<float> &vc_y,vector<float> &vl_y);
    static bool comp_x(Ppoint_F c1, Ppoint_F c2);
    static bool comp_y(Ppoint_F c1, Ppoint_F c2);
    static bool comp_position(pair<pair<int,int>,int> p1,pair<pair<int,int>,int> p2);
    void writeback(PnRDB::hierNode &current_node);
    bool symCheck(float tol);
    void splitNode_MS(float uniHeight, float uniWidth);
    void addNet_for_one_split_Blocks(int blockID,Ppoint_I num);
    void update_netlist_after_split_MS();
    void match_vector_into_pairs(vector<int> &q, vector<pair<int,int>> &pairs);
    Ppoint_F find_uni_cell();
    void readCC();
    void addNet_after_split_Blocks(int tol_diff,float uniHeight, float uniWidth);//tol diff is the maximum difference of abs(shape.x - shape.y)
    Ppoint_I determineShape(int cellNum,int tol_diff);
    void addNet_commonCentroid(commonCentroid &CC,int cell_num,float uniHeight, float uniWidth);
    void restore_MS();
    void merge_two_vectors(vector<pair<int,int>> &v1,vector<pair<int,int>> &v2);//merge v1,v2 into v1
    void refine_CC();//need to change

    void update_hiernode(PnRDB::hierNode &current_node);

    void split_net();

    void merge_placement(PnRDB::hierNode &current_node);

    void modify_symm_after_split(PnRDB::hierNode &current_node);

    void restore_CC_in_square(bool isCompact);

    void restore_MS(PnRDB::hierNode &current_node);

    void split_CC(PnRDB::hierNode &current_node);
    //donghao end

    float Cal_Overlap();
    void Pull_back_vector(vector<float> &temp_vector, bool x_or_y);
    void Initilize_lambda();
    void Initilize_sym_beta();
    void match_pairs(commonCentroid &CC, int dummyNum);

    void plotPlacement(PnRDB::hierNode &current_node);

    void compact_cc();

    float cal_weight_init_increase(float &rate, float &init_val,float &target_val,float target_converge_iter);
    void cal_dummy_net_weight(float &weight, float &rate, float &increase);

    void set_dummy_net_weight(float init_weight, float rate, float targe);
    
    void break_merged_cc(PnRDB::hierNode &current_node);
    
    void update_pos(PnRDB::hierNode &current_node);

    float Area_SUM_P(bool x_or_y);
    float Area_SUM_N(bool x_or_y);
    void Cal_LSE_Area_Force();
    
    // for UT placer
    void UT_Placer();
    void Cal_LSE_BND_Force();
    void Cal_LSE_OL_Force();
    void Cal_UT_Force();
    float Cal_OL_MIN_SUM(bool x_or_y, int i, int j);
    float Cal_OL_Term(bool x_or_y, int i, int j);
    float Cal_OL_Term_Gradient(bool x_or_y, int i, int j);
    float Cal_OL_Gradient(bool x_or_y, int i, int j);

    void Extract_Gradient(vector<float> &gradient, bool x_or_y);
    void Cal_mn(vector<float> &mn, vector<float> &ml, float beta_1, vector<float> gradient);
    void Cal_mn_hat(vector<float> &mn_hat, vector<float> &mn, float beta_1);
    void Cal_vn(vector<float> &vn, vector<float> &vl, float beta_2, vector<float> gradient);
    void Cal_vn_hat(vector<float> &vn_hat, vector<float> &vn, float beta_2);
    void Cal_new_position(vector<float> &mn_hat, vector<float> &vn_hat, float step_size, vector<float> position_old, vector<float> &position_new);
    void place_ut(PnRDB::hierNode &current_node);

};
#endif
