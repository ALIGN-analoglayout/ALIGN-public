#include "placement.h"
// #define DEBUG
Placement::Placement() {

}

void Placement::Initilize_lambda(){

  Ppoint_F norm_wire_gradient;
  norm_wire_gradient.x=0;
  norm_wire_gradient.y=0;
  Ppoint_F norm_E_force_gradient;
  norm_E_force_gradient.x=0;
  norm_E_force_gradient.y=0;

  for(unsigned int i=0;i<Blocks.size();++i){
    norm_wire_gradient.x+=abs(Blocks[i].Netforce.x);
    norm_wire_gradient.y+=abs(Blocks[i].Netforce.y);
    norm_E_force_gradient.x+=abs(Blocks[i].Eforce.x);
    norm_E_force_gradient.y+=abs(Blocks[i].Eforce.y);
  }

  float lambda_x=beta*norm_wire_gradient.x/norm_E_force_gradient.x;
  float lambda_y=beta*norm_wire_gradient.y/norm_E_force_gradient.y;

  std::cout<<"lambda_x "<<lambda_x<<" "<<norm_wire_gradient.x/Blocks.size()<<" "<<norm_E_force_gradient.x/Blocks.size()<<std::endl;
  std::cout<<"lambda_y "<<lambda_y<<" "<<norm_wire_gradient.y/Blocks.size()<<" "<<norm_E_force_gradient.y/Blocks.size()<<std::endl;

  if(lambda_x<lambda_y){
    lambda = lambda_x;
  }else{
    lambda = lambda_y;
  }

}

Placement::Placement(PnRDB::hierNode &current_node) {
  //step 1: transfroming info. of current_node to Blocks and Nets
    //create a small function for this
    float area, scale_factor;
    int max_block_number = 1000;
    int max_net_number = 100;
    int max_conection_number = 100;

  
    
  
    // for bins
    unit_x_bin =(float) 1/16;
    unit_y_bin =(float) 1/16;
    x_dimension_bin = 16; //number of bin, number of pe
    y_dimension_bin = 16; //number of bin, number of pe
  
  
    

    Bin_D.x = unit_x_bin;
    Bin_D.y = unit_y_bin;
    std::cout<<"start reading node file"<<std::endl;
    area = readInputNode(current_node);
    // for blocks
    unit_x = (float)1/Blocks.size();
    unit_y = (float)1/Blocks.size();
    x_dimension = Blocks.size(); //number of pe
    y_dimension = x_dimension; //S number of pe
    Chip_D.x = (float) 1;
    Chip_D.y = (float) 1;


    for(unsigned int i=0;i<x_dimension_bin;++i){
     vector<bin> temp_bins;
     for(unsigned int j=0;j<y_dimension_bin;++j){
        bin temp_bin;
        temp_bin.Dpoint.x=unit_x_bin;
        temp_bin.Dpoint.y=unit_y_bin;
        temp_bin.Cpoint.x=i*unit_x_bin+unit_x_bin/2;
        temp_bin.Cpoint.y=j*unit_y_bin+unit_y_bin/2;
        temp_bin.Index.x = i;
        temp_bin.Index.y = j;
        temp_bins.push_back(temp_bin);
     }
     Bins.push_back(temp_bins);
  } 



  //step 2: Given a initial position for each block
    //create a small function for this
      // need to estimate a area to do placement
      // scale into 1x1
      // initial position for each block
    std::cout<<"Unify the block coordinate"<<std::endl;
    scale_factor = 40.0;
    Unify_blocks(area, scale_factor);

    //read alignment constrains
    read_alignment(current_node);
    read_order(current_node);
    Initilize_Placement();

    print_blocks_nets();  
  //step 3: call E_placer
  std::cout<<"start ePlacement"<<std::endl;
    E_Placer();
  //setp 4: write back to HierNode
  writeback(current_node);
}


Placement::Placement(float chip_width, float chip_hight, float bin_width, float bin_hight) {

  this->Chip_D.x = chip_width;
  this->Chip_D.y = chip_hight;
  this->Bin_D.x = bin_width;
  this->Bin_D.x = bin_hight;

}

void Placement::generate_testing_data(){
  #ifdef DEBUG
  std::cout<<"generating test 1"<<std::endl;
  #endif
  Random_Generation_Block_Nets();
  #ifdef DEBUG
  std::cout<<"generating test 2"<<std::endl;
  #endif
  Initilize_Placement();
  #ifdef DEBUG
  std::cout<<"generating test 3"<<std::endl;
  #endif
  PlotPlacement(0);

}

void Placement::Random_Generation_Block_Nets(){

  int max_block_number = 1000;
  int max_net_number = 100;
  int max_conection_number = 100;

  // for blocks
  unit_x = (float)1/64;
  unit_y = (float)1/64;
  x_dimension = 64; //number of bin, number of pe
  y_dimension = 64; //number of bin, number of pe
  
  // for bins
  unit_x_bin =(float) 1/16;
  unit_y_bin =(float) 1/16;
  x_dimension_bin = 16; //number of bin, number of pe
  y_dimension_bin = 16; //number of bin, number of pe
  
  
  Chip_D.x = (float) x_dimension * unit_x;
  Chip_D.y = (float) y_dimension * unit_y;

  Bin_D.x = unit_x_bin;
  Bin_D.y = unit_y_bin;
  

  for(unsigned int i=0;i<max_block_number;++i){
     block temp_block;
     temp_block.Dpoint.x = unit_x;
     temp_block.Dpoint.y = unit_y;
     temp_block.index = i;
     Blocks.push_back(temp_block);
  }

  for(unsigned int i=0;i<x_dimension_bin;++i){
     vector<bin> temp_bins;
     for(unsigned int j=0;j<y_dimension_bin;++j){
        bin temp_bin;
        temp_bin.Dpoint.x=unit_x_bin;
        temp_bin.Dpoint.y=unit_y_bin;
        temp_bin.Cpoint.x=i*unit_x_bin+unit_x_bin/2;
        temp_bin.Cpoint.y=j*unit_y_bin+unit_y_bin/2;
        temp_bin.Index.x = i;
        temp_bin.Index.y = j;
        temp_bins.push_back(temp_bin);
     }
     Bins.push_back(temp_bins);
  } 

  for(unsigned int i=0;i<max_net_number;++i){
     set<int> connection_index;
     for(unsigned int j=0;j<max_conection_number;++j){
        int random_block_index = rand() % max_block_number;
        connection_index.insert(random_block_index);
     }
     vector<int> connection_block_index;
     for(auto it=connection_index.begin();it!=connection_index.end();++it){
        connection_block_index.push_back(*it);
        Blocks[*it].connected_net.push_back(i);
     }
     net temp_net;
     temp_net.connected_block = connection_block_index;
     temp_net.index = i;
     Nets.push_back(temp_net);
  }


}

void Placement::Create_Placement_Bins(){
  //according to the chip area, bin dimension, create a vector<bin> Bins


}

void Placement::Pull_back(){

  for(unsigned int i=0;i<Blocks.size();++i){
    if(Blocks[i].Cpoint.x+Blocks[i].Dpoint.x/2>Chip_D.x){
       Blocks[i].Cpoint.x = Chip_D.x - Blocks[i].Dpoint.x/2-(1.5)*Bin_D.x/2;
       //Blocks[i].Cpoint.x = Chip_D.x - Blocks[i].Dpoint.x/2;
    }
    if(Blocks[i].Cpoint.y+Blocks[i].Dpoint.y/2>Chip_D.y){
       Blocks[i].Cpoint.y = Chip_D.y - Blocks[i].Dpoint.y/2-(1.5)*Bin_D.y/2;
       //Blocks[i].Cpoint.y = Chip_D.y - Blocks[i].Dpoint.y/2;
    }
    if(Blocks[i].Cpoint.x-Blocks[i].Dpoint.x/2<0){
       Blocks[i].Cpoint.x = Blocks[i].Dpoint.x/2+(1.5)*Bin_D.x/2;
       //Blocks[i].Cpoint.x = Blocks[i].Dpoint.x/2;
    }
    if(Blocks[i].Cpoint.y-Blocks[i].Dpoint.y/2<0){
       Blocks[i].Cpoint.y = Blocks[i].Dpoint.y/2+(1.5)*Bin_D.y/2;
       //Blocks[i].Cpoint.y = Blocks[i].Dpoint.y/2;
    }

  }

}

void Placement::Pull_back_vector(vector<float> &temp_vector, bool x_or_y){// 1 is x, 0 is y

  for(unsigned int i=0;i<temp_vector.size();++i){
    if(x_or_y){

      if(temp_vector[i]+Blocks[i].Dpoint.x/2>Chip_D.x){
         temp_vector[i] = Chip_D.x - Blocks[i].Dpoint.x/2-(1.5)*Bin_D.x/2;
         //temp_vector[i] = Chip_D.x - Blocks[i].Dpoint.x/2;
      }
      if(temp_vector[i]-Blocks[i].Dpoint.x/2<0){
         temp_vector[i] = Blocks[i].Dpoint.x/2+(1.5)*Bin_D.x/2;
         //temp_vector[i] = Blocks[i].Dpoint.x/2;
      }

    }else{

      if(temp_vector[i]+Blocks[i].Dpoint.y/2>Chip_D.y){
         temp_vector[i] = Chip_D.y - Blocks[i].Dpoint.y/2-(1.5)*Bin_D.y/2;
         //temp_vector[i] = Chip_D.y - Blocks[i].Dpoint.y/2;
      }
      if(temp_vector[i]-Blocks[i].Dpoint.y/2<0){
         temp_vector[i] = Blocks[i].Dpoint.y/2+(1.5)*Bin_D.y/2;
         //temp_vector[i] = Blocks[i].Dpoint.y/2;
      }


    }

  }

}


void Placement::Initilize_Placement(){

  for(unsigned int i=0;i<Blocks.size();++i){
    Blocks[i].Cpoint.x = 0.5+(float) (rand()% 100)/1000;
    Blocks[i].Cpoint.y = 0.5+(float) (rand()% 100)/1000;
  }

}

void Placement::Update_Bin_Density(){

  float unit_density = 1;

  for(unsigned int i=0;i<Bins.size();++i){
     for(unsigned int j=0;j<Bins[i].size();++j){
        Bins[i][j].density = 0.0;
     }
  } 

  for(unsigned int i=0;i<Bins.size();++i){
    
     for(unsigned int j=0;j<Bins[i].size();++j){
     
       for(unsigned int k=0;k<Blocks.size();++k){

          float x_common_length=0.0;
          bool x_common;
          x_common = Find_Common_Area(Blocks[k].Cpoint.x, Blocks[k].Dpoint.x, Bins[i][j].Cpoint.x, Bins[i][j].Dpoint.x, x_common_length);
          float y_common_length=0.0;
          bool y_common;
          y_common = Find_Common_Area(Blocks[k].Cpoint.y, Blocks[k].Dpoint.y, Bins[i][j].Cpoint.y, Bins[i][j].Dpoint.y, y_common_length);

          if(x_common and y_common){
            Bins[i][j].density += unit_density*x_common_length*y_common_length;
          }
       }

       Bins[i][j].density = Bins[i][j].density/(Bin_D.x*Bin_D.y);

     }
  }

}

bool Placement::Find_Common_Area(float x_center_block, float block_width, float x_center_bin, float bin_width, float &common_length){

  float x_lower_block = x_center_block - block_width/2;
  float x_upper_block = x_center_block + block_width/2;
  float x_lower_bin = x_center_bin - bin_width/2;
  float x_upper_bin = x_center_bin + bin_width/2;

  float eqv_x_lower = max(x_lower_block,x_lower_bin);
  float eqv_x_upper = min(x_upper_block,x_upper_bin);

  common_length = eqv_x_upper - eqv_x_lower;

  if(common_length>0){
    return true;
  }else{
    return false;
  }
  
}

void Placement::Cal_Eforce_Block(int block_id){
 
  //Q: should compare with replace's implementation
  Blocks[block_id].Eforce.x = 0.0;
  Blocks[block_id].Eforce.y = 0.0;

  for(unsigned int i=0;i<Bins.size();++i){

     for(unsigned int j=0;j<Bins[i].size();++j){

       float x_common_length;
       bool x_common;
       x_common = Find_Common_Area(Blocks[block_id].Cpoint.x, Blocks[block_id].Dpoint.x, Bins[i][j].Cpoint.x, Bins[i][j].Dpoint.x, x_common_length);
       float y_common_length;
       bool y_common;
       y_common = Find_Common_Area(Blocks[block_id].Cpoint.y, Blocks[block_id].Dpoint.y, Bins[i]
[j].Cpoint.y, Bins[i][j].Dpoint.y, y_common_length);

       if(x_common and y_common){ //Q: should be x_common_length*y_common_length?
          Blocks[block_id].Eforce.x += (y_common_length*x_common_length/(Bin_D.x*Bin_D.y))*Bins[i][j].Eforce.x;
          Blocks[block_id].Eforce.y += (y_common_length*x_common_length/(Bin_D.x*Bin_D.y))*Bins[i][j].Eforce.y;
       }

     }
     
  }
  #ifdef DEBUG
  std::cout<<"blocks gradient "<<Blocks[block_id].Eforce.x<<" "<<Blocks[block_id].Eforce.y<<std::endl;
  #endif
}

float Placement::Cal_HPWL(){
  
  float HPWL = 0;
  for(unsigned int i=0;i<Nets.size();++i){
    vector<float> x_value;
    vector<float> y_value;
    for(unsigned int j=0;j<Nets[i].connected_block.size();++j){
      int block_index = Nets[i].connected_block[j];
      x_value.push_back(Blocks[block_index].Cpoint.x);
      y_value.push_back(Blocks[block_index].Cpoint.y);
    }
    float max_x = x_value[0];
    float min_x = x_value[0];
    float max_y = y_value[0];
    float min_y = y_value[0];
    for(unsigned int j=0;j<x_value.size();++j){
       if(max_x<x_value[j]) max_x=x_value[j];
       if(min_x>x_value[j]) min_x=x_value[j];
       if(max_y<y_value[j]) max_y=y_value[j];
       if(min_y>y_value[j]) min_y=y_value[j];
    }
    HPWL += abs(max_x - min_x) + abs(max_y-min_y);
  }
  return HPWL;

}

void Placement::PlotPlacement(int index){
    string outfile = to_string(index)+".plt";
    #ifdef DEBUG
    cout<<"create gnuplot file"<<endl;
    #endif
    ofstream fout;
    fout.open(outfile.c_str());

    //set title
    fout<<"#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)"<<endl;
    fout<<"\nset title\" #Blocks= "<<Blocks.size()<<", #Nets= "<<Nets.size()<<", Area="<<Chip_D.x*Chip_D.y<<", HPWL= "<<Cal_HPWL()<<" \""<<endl;
    fout<<"\nset nokey"<<endl;
    fout<<"#   Uncomment these two lines starting with \"set\""<<endl;
    fout<<"#   to save an EPS file for inclusion into a latex document"<<endl;
    fout<<"# set terminal postscript eps color solid 20"<<endl;
    fout<<"# set output \"result.eps\""<<endl<<endl;
    fout<<"#   Uncomment these two lines starting with \"set\""<<endl;
    fout<<"#   to save a PS file for printing"<<endl;
    fout<<"set term jpeg"<<endl;
    fout<<"set output \""<<to_string(index)+".jpg"<<"\""<<endl<<endl;

    //set range
    float bias=0;
    fout<<"\nset xrange ["<<0.0-bias<<":"<<Chip_D.x+bias<<"]"<<endl;
    fout<<"\nset yrange ["<<0.0-bias<<":"<<Chip_D.y+bias<<"]"<<endl;

    // set labels for blocks
    /*
    for(int i=0;i<(int)Blocks.size();++i) {
      fout<<"\nset label \""<<" B"+to_string(i)<<"\" at "<<Blocks[i].Cpoint.x<<" , "<<Blocks[i].Cpoint.y<<" center "<<endl;
    }
    */

    for(int i=0;i<(int)Blocks.size();++i){
      fout<<"\nset label \""<<Blocks[i].blockname<<"\" at "<<Blocks[i].Cpoint.x<<" , "<<Blocks[i].Cpoint.y<<" center "<<endl;
    }
    
    fout<<"\nplot[:][:] \'-\' with lines linestyle 3, \'-\' with lines linestyle 7, \'-\' with lines linestyle 1, \'-\' with lines linestyle 0"<<endl<<endl;;

    for(int i=0;i<(int)Blocks.size();++i) {
      fout<<"\t"<<Blocks[i].Cpoint.x-Blocks[i].Dpoint.x/2<<"\t"<<Blocks[i].Cpoint.y-Blocks[i].Dpoint.y/2<<endl;
      fout<<"\t"<<Blocks[i].Cpoint.x-Blocks[i].Dpoint.x/2<<"\t"<<Blocks[i].Cpoint.y+Blocks[i].Dpoint.y/2<<endl;
      fout<<"\t"<<Blocks[i].Cpoint.x+Blocks[i].Dpoint.x/2<<"\t"<<Blocks[i].Cpoint.y+Blocks[i].Dpoint.y/2<<endl;
      fout<<"\t"<<Blocks[i].Cpoint.x+Blocks[i].Dpoint.x/2<<"\t"<<Blocks[i].Cpoint.y-Blocks[i].Dpoint.y/2<<endl;
      fout<<"\t"<<Blocks[i].Cpoint.x-Blocks[i].Dpoint.x/2<<"\t"<<Blocks[i].Cpoint.y-Blocks[i].Dpoint.y/2<<endl;
      fout<<endl;
    }
    fout<<"\nEOF"<<endl;
    /*
    // plot connections
    for(int i=0;i<Nets.size();i++){
      for(int j=0;j<Nets[i].connected_block.size()-1;j++){
        int first_block_index = Nets[i].connected_block[j];
        int second_block_index = Nets[i].connected_block[j+1];
        fout<<"\t"<<Blocks[first_block_index].Cpoint.x<<"\t"<<Blocks[first_block_index].Cpoint.y<<endl;
        fout<<"\t"<<Blocks[second_block_index].Cpoint.x<<"\t"<<Blocks[second_block_index].Cpoint.y<<endl;
        fout<<"\t"<<Blocks[first_block_index].Cpoint.x<<"\t"<<Blocks[first_block_index].Cpoint.y<<endl<<endl;   
      }
      if(Nets[i].connected_block.size()-1>0) fout<<"\nEOF"<<endl;
    }
    */

    fout.close();
}

//WA model
void Placement::Cal_WA_Net_Force(){

  for(unsigned int i=0;i<Nets.size();++i){

     Nets[i].PSumNetforce.x=LSE_Net_SUM_P(i,1);
     Nets[i].PSumNetforce.y=LSE_Net_SUM_P(i,0);
     Nets[i].NSumNetforce.x=LSE_Net_SUM_N(i,1);
     Nets[i].NSumNetforce.y=LSE_Net_SUM_N(i,0);

     Nets[i].PSumNetforce_WA.x=WA_Net_SUM_P(i,1);
     Nets[i].PSumNetforce_WA.y=WA_Net_SUM_P(i,0);
     Nets[i].NSumNetforce_WA.x=WA_Net_SUM_N(i,1);
     Nets[i].NSumNetforce_WA.y=WA_Net_SUM_N(i,0);     
     
  }

  for(unsigned int i=0;i<Blocks.size();++i){

     Blocks[i].Net_block_force_P.x=LSE_block_P(i,1);
     Blocks[i].Net_block_force_P.y=LSE_block_P(i,0);
     Blocks[i].Net_block_force_N.x=LSE_block_N(i,1);
     Blocks[i].Net_block_force_N.y=LSE_block_N(i,0);
  }

  for(unsigned int i=0;i<Blocks.size();++i){
     Blocks[i].Netforce.x = 0;
     Blocks[i].Netforce.y = 0;
     for(unsigned int j=0;j<Blocks[i].connected_net.size();j++){
        int net_index = Blocks[i].connected_net[j];

        Ppoint_F PSumNetforce = Nets[net_index].PSumNetforce;
        Ppoint_F NSumNetforce = Nets[net_index].NSumNetforce;
        Ppoint_F PSumNetforce_WA = Nets[net_index].PSumNetforce_WA;
        Ppoint_F NSumNetforce_WA = Nets[net_index].NSumNetforce_WA;
        float x_positive = ( (1+Blocks[i].Cpoint.x/gammar)*Blocks[i].Net_block_force_P.x*PSumNetforce.x - Blocks[i].Net_block_force_P.x*PSumNetforce_WA.x ) / (PSumNetforce.x * PSumNetforce.x);
        float x_nagative = ( (1+Blocks[i].Cpoint.x/gammar)*Blocks[i].Net_block_force_N.x*NSumNetforce.x - Blocks[i].Net_block_force_N.x*NSumNetforce_WA.x ) / (NSumNetforce.x * NSumNetforce.x);
        float y_positive = ( (1+Blocks[i].Cpoint.y/gammar)*Blocks[i].Net_block_force_P.y*PSumNetforce.y - Blocks[i].Net_block_force_P.y*PSumNetforce_WA.y ) / (PSumNetforce.y * PSumNetforce.y);
        float y_nagative = ( (1+Blocks[i].Cpoint.y/gammar)*Blocks[i].Net_block_force_N.y*NSumNetforce.y - Blocks[i].Net_block_force_N.y*NSumNetforce_WA.y ) / (NSumNetforce.y * NSumNetforce.y);
        Blocks[i].Netforce.x += x_positive - x_nagative;
        Blocks[i].Netforce.y += y_positive - y_nagative;
     }
  }


}

float Placement::WA_Net_SUM_P(int net_index, bool x_or_y){

  // 1/r *( sum xi*exp(xi/r) )

  float result = 0.0;
  
  for(unsigned int i =0;i<Nets[net_index].connected_block.size();i++){
     int block_index = Nets[net_index].connected_block[i];

     if(x_or_y){// 1 for x
        result += Blocks[block_index].Cpoint.x*Exp_Function(Blocks[block_index].Cpoint.x,gammar);
     }else{
        result += Blocks[block_index].Cpoint.y*Exp_Function(Blocks[block_index].Cpoint.y,gammar);
     }
  }

  return result/gammar;
}

float Placement::WA_Net_SUM_N(int net_index, bool x_or_y){

  // 1/r *( sum xi*exp(-xi/r) )

  float result = 0.0;
  
  for(unsigned int i =0;i<Nets[net_index].connected_block.size();i++){
     int block_index = Nets[net_index].connected_block[i];

     if(x_or_y){// 1 for x
        result += Blocks[block_index].Cpoint.x*Exp_Function(-Blocks[block_index].Cpoint.x,gammar);
     }else{
        result += Blocks[block_index].Cpoint.y*Exp_Function(-Blocks[block_index].Cpoint.y,gammar);
     }
  }

  return result/gammar;
}
//End WA model


//LSE model
void Placement::Cal_LSE_Net_Force(){

  for(unsigned int i=0;i<Nets.size();++i){
     Nets[i].PSumNetforce.x=LSE_Net_SUM_P(i,1);
     Nets[i].PSumNetforce.y=LSE_Net_SUM_P(i,0);
     Nets[i].NSumNetforce.x=LSE_Net_SUM_N(i,1);
     Nets[i].NSumNetforce.y=LSE_Net_SUM_N(i,0);
  }

  for(unsigned int i=0;i<Blocks.size();++i){
     Blocks[i].Net_block_force_P.x=LSE_block_P(i,1);
     Blocks[i].Net_block_force_P.y=LSE_block_P(i,0);
     Blocks[i].Net_block_force_N.x=LSE_block_N(i,1);
     Blocks[i].Net_block_force_N.y=LSE_block_N(i,0);
  }

  for(unsigned int i=0;i<Blocks.size();++i){
     Blocks[i].Netforce.x = 0;
     Blocks[i].Netforce.y = 0;
     for(unsigned int j=0;j<Blocks[i].connected_net.size();j++){
        int net_index = Blocks[i].connected_net[j];
        Ppoint_F PSumNetforce = Nets[net_index].PSumNetforce;
        Ppoint_F NSumNetforce = Nets[net_index].NSumNetforce;
        Blocks[i].Netforce.x += Blocks[i].Net_block_force_P.x/PSumNetforce.x - Blocks[i].Net_block_force_N.x/NSumNetforce.x;
        Blocks[i].Netforce.y += Blocks[i].Net_block_force_P.y/PSumNetforce.y - Blocks[i].Net_block_force_N.y/NSumNetforce.y;
     }
  }
}

float Placement::LSE_Net_SUM_P(int net_index, bool x_or_y){

  float result = 0.0;
  
  for(unsigned int i =0;i<Nets[net_index].connected_block.size();i++){
     int block_index = Nets[net_index].connected_block[i];

     if(x_or_y){// 1 for x
        result += Exp_Function(Blocks[block_index].Cpoint.x,gammar);
        #ifdef DEBUG
        std::cout<<"lse exp result "<<Exp_Function(Blocks[block_index].Cpoint.x,gammar)<<std::endl;
        #endif
     }else{
        result += Exp_Function(Blocks[block_index].Cpoint.y,gammar);
        #ifdef DEBUG
        std::cout<<"lse exp result "<<Exp_Function(Blocks[block_index].Cpoint.x,gammar)<<std::endl;
        #endif
     }
  }
  #ifdef DEBUG
  std::cout<<"lse exp sum result "<<result<<std::endl;
  #endif
  return result;
}

float Placement::LSE_Net_SUM_N(int net_index, bool x_or_y){

  float result = 0.0;
  
  for(unsigned int i =0;i<Nets[net_index].connected_block.size();i++){
     int block_index = Nets[net_index].connected_block[i];

     if(x_or_y){// 1 for x
        result += Exp_Function(-Blocks[block_index].Cpoint.x,gammar);
        #ifdef DEBUG
        std::cout<<"lse exp result "<<Exp_Function(Blocks[block_index].Cpoint.x,gammar)<<std::endl;
        #endif
     }else{
        result += Exp_Function(-Blocks[block_index].Cpoint.y,gammar);
        #ifdef DEBUG
        std::cout<<"lse exp result "<<Exp_Function(Blocks[block_index].Cpoint.x,gammar)<<std::endl;
        #endif
     }
  }
  #ifdef DEBUG
  std::cout<<"lse exp sum result "<<result<<std::endl;
  #endif
  return result;
}

float Placement::LSE_block_P(int block_index, int x_or_y){

  float result = 0.0;

  if(x_or_y){// 1 for x
      result += Exp_Function(Blocks[block_index].Cpoint.x,gammar);
  }else{
      result += Exp_Function(Blocks[block_index].Cpoint.y,gammar);
  }

  return result;
}

float Placement::LSE_block_N(int block_index, int x_or_y){

  float result = 0.0;

  if(x_or_y){// 1 for x
      result += Exp_Function(-Blocks[block_index].Cpoint.x,gammar);
  }else{
      result += Exp_Function(-Blocks[block_index].Cpoint.y,gammar);
  }

  return result;
}

float Placement::Exp_Function(float x, float gammar){

  //float result = exp(x/gammar);
  float offset = 0;
  //float result = Fast_Exp(x/gammar-offset);
  float result = exp(x/gammar-offset);
  #ifdef DEBUG
  std::cout<<"x "<<x<<"x/gammar "<<x/gammar<<" exp result "<<result<<std::endl;
  #endif
  return result;

}

//Q: might need a fast exp cal function
//END LSE model

void Placement::Cal_Density_Eforce(){
    #ifdef DEBUG
    cout<<"start test fft functions"<<endl;
    #endif
    #ifdef DEBUG
    std::cout<<"Cal_Density_Eforce debug 0"<<std::endl;
    #endif
    int binCntX=x_dimension_bin; 
    int binCntY=y_dimension_bin;
    float binSizeX= unit_x_bin;
    float binSizeY= unit_y_bin;
    #ifdef DEBUG
    std::cout<<"Cal_Density_Eforce debug 1"<<std::endl;
    #endif
    replace::FFT fft(binCntX, binCntY, binSizeX, binSizeY);
    #ifdef DEBUG
    cout<<"test flag 1"<<endl;
    std::cout<<"Cal_Density_Eforce debug 2"<<std::endl;   
    #endif
    for(unsigned int i=0;i<binCntX;++i){
       for(unsigned int j=0;j<binCntY;j++){
          #ifdef DEBUG
          std::cout<<"Bin: ("<<i<<", "<<j<<")"<<std::endl;
          std::cout<<"density:"<<Bins[i][j].density<<std::endl;
          #endif
          fft.updateDensity(i, j, Bins[i][j].density); 
       }
    }
    #ifdef DEBUG
    std::cout<<"Cal_Density_Eforce debug 3"<<std::endl;
    cout<<"test flag 2"<<endl;
    #endif
    fft.doFFT();
    #ifdef DEBUG
    std::cout<<"Cal_Density_Eforce debug 4"<<std::endl;
    cout<<"end test fft functions"<<endl;
    std::cout<<"Cal_Density_Eforce debug 5"<<std::endl;
    #endif
    for(unsigned int i=0;i<binCntX;++i) {
      #ifdef DEBUG
      std::cout<<"Cal_Density_Eforce debug 6"<<std::endl;
      #endif
      for(unsigned int j=0;j<binCntY;++j){
        auto eForcePair = fft.getElectroForce(i, j);
        Bins[i][j].Eforce.x = eForcePair.first;
        Bins[i][j].Eforce.y = eForcePair.second;
        #ifdef DEBUG
        std::cout<<"Bin force "<<Bins[i][j].Eforce.x<<" "<<Bins[i][j].Eforce.y<<std::endl;
        #endif
        float electroPhi = fft.getElectroPhi(i, j);
        Bins[i][j].Ephi = electroPhi;
      }
        //sumPhi_ += electroPhi*static_cast<float>(bin->nonPlaceArea()+bin->instPlacedArea()+bin->fillerArea());
    }
    #ifdef DEBUG
    std::cout<<"Cal_Density_Eforce debug 7"<<std::endl;
    #endif
    for(unsigned int i=0;i<Blocks.size();++i){
      Cal_Eforce_Block(i);
    }
    #ifdef DEBUG
    std::cout<<"Cal_Density_Eforce debug 8"<<std::endl;
    #endif
}

void Placement::Cal_Net_force(){
   //using lse or wa to calculated the force/gradient due to net
   //need a lse/wa kernel

   //lse functions?
   

   //wa functions?


}

void Placement::Cal_force(){

  for(unsigned int i=0;i<Blocks.size();++i){
    //  Blocks[i].Force.x = lambda*Blocks[i].Eforce.x - beta*Blocks[i].Netforce.x;
    //  Blocks[i].Force.y = lambda*Blocks[i].Eforce.y - beta*Blocks[i].Netforce.y;
     
     Blocks[i].Force.x = lambda*Blocks[i].Eforce.x - beta*Blocks[i].Netforce.x - sym_beta*Blocks[i].Symmetricforce.x;
     Blocks[i].Force.y = lambda*Blocks[i].Eforce.y - beta*Blocks[i].Netforce.y - sym_beta*Blocks[i].Symmetricforce.y;
    //  std::cout<<"symmetricforce/all"<<sym_beta*Blocks[i].Symmetricforce.x<<", "<<sym_beta*Blocks[i].Symmetricforce.y<<std::endl;
    //  if(isnan(Blocks[i].Force.x))
    //  {
    //    Blocks[i].Force.x = 0;
    //  }
    //  if(isnan(Blocks[i].Force.y))
    //  {
    //    Blocks[i].Force.y = 0;
    //  }
  }

}

bool Placement::Stop_Condition(float density, float &max_density){

  Pull_back();

  max_density = 0.0;
  for(unsigned int i=0;i<Bins.size();++i){
     for(unsigned int j=0;j<Bins[i].size();++j){
        if (Bins[i][j].density>max_density){
           max_density = Bins[i][j].density;
        }
     }
  }
  std::cout<<"max_density "<<max_density<<std::endl;
  if(max_density<density){
    std::cout<<"stop condition result: false"<<std::endl;
    return false;
  }else{
    std::cout<<"stop condition result: true"<<std::endl;
    return true;
  }

}

float Placement::Cal_Overlap(){

  float max_overlap = 0.0f;

  for(unsigned int i=0;i<Blocks.size();++i){
   
    Blocks[i].overlap = 0.0f;

    for(unsigned int j=0;j<Blocks.size();++j){

       if(i!=j){

          float x_common_length=0.0;
          bool x_common;
          x_common = Find_Common_Area(Blocks[i].Cpoint.x, Blocks[i].Dpoint.x, Blocks[j].Cpoint.x, Blocks[j].Dpoint.x, x_common_length);
          float y_common_length=0.0;
          bool y_common;
          y_common = Find_Common_Area(Blocks[i].Cpoint.y, Blocks[i].Dpoint.y, Blocks[j].Cpoint.y, Blocks[j].Dpoint.y, y_common_length);

          if(x_common and y_common){
            float overlap = x_common_length*y_common_length/(Blocks[i].Dpoint.x*Blocks[i].Dpoint.y);
            if(overlap>Blocks[i].overlap){
                 Blocks[i].overlap = overlap;
              }
            //Blocks[i].overlap += overlap;
            
          }

       }

    }

  }

  for(unsigned int i=0;i<Blocks.size();++i){

    if(max_overlap<Blocks[i].overlap){
        max_overlap = Blocks[i].overlap;
      }
    
  }

  std::cout<<"Max overlap "<<max_overlap<<std::endl;

  return max_overlap;

}

void Placement::E_Placer(){

  int i=0;
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 0"<<std::endl;
  #endif
  //force to align and order
  // force_alignment();
  force_order();
  force_alignment();
  
  Update_Bin_Density();
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 1"<<std::endl;
  #endif
  //gradient cal
  Cal_WA_Net_Force();
  //Cal_LSE_Net_Force();
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 2"<<std::endl;
  #endif
  Cal_Density_Eforce();
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 3"<<std::endl;
  #endif
  
  Cal_sym_Force();
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 3.5"<<std::endl;
  #endif
  Cal_force();
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 4"<<std::endl;
  #endif

  float ac_x=1.0f;
  vector<float> pre_vc_x, pre_vl_x;
  pre_conditioner(pre_vl_x,1); //1 x direction
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 5"<<std::endl;
  #endif
  vector<float> uc_x,vc_x,vl_x;
  Extract_Placement_Vectors(uc_x, 1);
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 6"<<std::endl;
  #endif
  Extract_Placement_Vectors(vc_x, 1);
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 7"<<std::endl;
  #endif
  Extract_Placement_Vectors(vl_x, 1);
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 8"<<std::endl;
  #endif

  float ac_y=1.0f;
  vector<float> pre_vc_y, pre_vl_y;
  pre_conditioner(pre_vl_y,0); //1 x direction
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 9"<<std::endl;
  #endif
  vector<float> uc_y,vc_y,vl_y;
  Extract_Placement_Vectors(uc_y, 0);
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 10"<<std::endl;
  #endif
  Extract_Placement_Vectors(vc_y, 0);
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 11"<<std::endl;
  #endif
  Extract_Placement_Vectors(vl_y, 0);
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 12"<<std::endl;
  #endif
  bool start_flag = 1;
  Update_Bin_Density();
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 13"<<std::endl;
  #endif

  float stop_density = 0.01;
  float max_density = 1.0;
  float current_max_density=10.0;
  int count_number = 0;
  int upper_count_number = 201;
  float symmetricMin = 1.0;//need to tune
  vector<float> Density;
  #ifdef DEBUG
  std::cout<<"E_placer debug flage: 14"<<std::endl;
  #endif
  PlotPlacement(0);
  Cal_Overlap();
  Initilize_lambda();
  while((Stop_Condition(stop_density,current_max_density) or symCheck(symmetricMin)) and count_number<upper_count_number ){//Q: stop condition
  // while(i<20){//Q: stop condition
     Density.push_back(current_max_density);
     Cal_Overlap();
     if(current_max_density<max_density){
        max_density = current_max_density;
        #ifdef DEBUG
        std::cout<<"E_placer debug flage: 16"<<std::endl;
        #endif
      }else if(current_max_density==Density.back()){
        #ifdef DEBUG
        std::cout<<"E_placer debug flage: 17"<<std::endl;
        #endif
        count_number++;
      }
      #ifdef DEBUG
      std::cout<<"E_placer debug flage: 15"<<std::endl;
      #endif
    //  Density.push_back(current_max_density);
     #ifdef DEBUG
     std::cout<<"Iteration "<<i<<std::endl;
     #endif
     //if(lambda<100)
    //  lambda = lambda *1.2;
     beta = beta*0.95;
     if(sym_beta < 0.1)
     {
        sym_beta = sym_beta*1.0125;
     }
    
      std::cout<<"sym_beta:= "<<sym_beta<<std::endl;
     //force to align
     if(i%10 == 0)
     {
       force_order();
       force_alignment();
       
      //  force_alignment();
       
     }
     

     PlotPlacement(i);

     Update_Bin_Density();
     //gradient cal
     Cal_WA_Net_Force();
     //Cal_LSE_Net_Force();
     Cal_Density_Eforce();
     #ifdef DEBUG
     std::cout<<"E_placer debug flag: 18"<<std::endl;
     #endif
     Cal_sym_Force();
     Cal_force();

     //WriteOut_Blocks(i);
     //WriteOut_Bins(i);
     //step size
     //two direction x
     #ifdef DEBUG
     std::cout<<"test 1"<<std::endl;
     #endif
     pre_conditioner(pre_vc_x,1); //1 x direction
     #ifdef DEBUG
     std::cout<<"test 1.1"<<std::endl;
     #endif
     //pre_conditioner(pre_vl_x,1); //1 x direction
     #ifdef DEBUG
     std::cout<<"test 1.2"<<std::endl;
     #endif
     Nesterov_based_iteration(ac_x,uc_x,vc_x,vl_x,pre_vc_x,pre_vl_x,start_flag);
     //two direction y
     #ifdef DEBUG
     std::cout<<"test 2"<<std::endl;
     #endif
     pre_conditioner(pre_vc_y,0); //0 y direction
     #ifdef DEBUG
     std::cout<<"test 2.1"<<std::endl;
     #endif
     //pre_conditioner(pre_vl_y,0); //0 y direction
     #ifdef DEBUG
     std::cout<<"test 2.1"<<std::endl;
     #endif
     Nesterov_based_iteration(ac_y,uc_y,vc_y,vl_y,pre_vc_y,pre_vl_y,start_flag);
     std::cout<<"iteration "<<i<<"step size "<<ac_x<<" "<<ac_y<<std::endl;
     #ifdef DEBUG
     std::cout<<"test 3"<<std::endl;
     #endif
     Feedback_Placement_Vectors(uc_x, 1);
     Feedback_Placement_Vectors(uc_y, 0);
     Pull_back_vector(vc_x,1);
     Pull_back_vector(vl_x,1);
     Pull_back_vector(vc_y,0);
     Pull_back_vector(vl_y,0);    
     //Pull_back();
     #ifdef DEBUG
     std::cout<<"test 4"<<std::endl;
     #endif
     start_flag=0;
     i++;
  }
  force_order();
  force_alignment();
  std::cout<<"iter num when stop:="<<count_number<<std::endl;

}

void Placement::Extract_Placement_Vectors(vector<float> &temp_vector, bool x_or_y){ //1 is x, 0 is y
  
  temp_vector.clear();
  for(unsigned int i=0;i<Blocks.size();++i){
     if(x_or_y){
         temp_vector.push_back(Blocks[i].Cpoint.x);
       }else{
         temp_vector.push_back(Blocks[i].Cpoint.y);
       }
  }

}

void Placement::Feedback_Placement_Vectors(vector<float> &temp_vector, bool x_or_y){ //1 is x, 0 is y
  
  for(unsigned int i=0;i<Blocks.size();++i){
     if(x_or_y){
         Blocks[i].Cpoint.x = temp_vector[i];
       }else{
         Blocks[i].Cpoint.y = temp_vector[i];
       }
  }

}

void Placement::Nesterov_based_iteration(float &ac,vector<float> &uc,vector<float> &vc,vector<float> &vl,vector<float> &pre_vc,vector<float> &pre_vl,bool start_flag){
   //Q:
   //Cal_WA_Net_Force();
   //Cal_LSE_Net_Force();
   //Cal_bin_force(); to be implemented
   //this function works for one direction, need to call twice x/y
   //Q:

   //start nesterov method
   //algorithm 1 of ePlace-MS: Electrostatics-Based Placement forMixed-Size Circuits
   float an; //current/last step size
   vector<float> un; //next/current/last vector u
   vector<float> vn; //next/current/last vector u
   //float ak = BkTrk(vc,vl,pre_vc,pre_vl); //Q: the port defination of BkTrk is not correct
   #ifdef DEBUG
   std::cout<<"Nesterov_based_iteration test 1"<<std::endl;
   #endif
   if(!start_flag){
   //if(0){
     BkTrk(ac,an,uc,vc,vl,pre_vc,pre_vl); //Q: the port defination of BkTrk is not correct
   }
   //Q: BkTrk need to be revised since back tracing is not considered
   #ifdef DEBUG
   std::cout<<"Nesterov_based_iteration test 2"<<std::endl;
   std::cout<<"un size "<<un.size()<<" uc size "<<uc.size()<<" pre_vc size "<<pre_vc.size()<<std::endl; 
   #endif
   for(unsigned int i=0;i<uc.size();++i){
      //un.push_back(vc[i]-ac*pre_vc[i]); //QQQ:LIYG Huge change
      un.push_back(vc[i]+ac*pre_vc[i]);
   }
   #ifdef DEBUG
   std::cout<<"Nesterov_based_iteration test 3"<<std::endl;
   #endif
   an= (1+sqrt(1+4*ac*ac))/2;

   for(unsigned int i=0;i<uc.size();++i){
      vn.push_back(un[i]+(ac-1)*(un[i]-uc[i])/an);
   }
   #ifdef DEBUG
   std::cout<<"Nesterov_based_iteration test 4"<<std::endl;
   #endif
   //ac = an;
   uc = un;
   vl = vc;
   vc = vn;
   pre_vl = pre_vc;
}

void Placement::BkTrk(float &ac, float &an, vector<float> &uc,vector<float> &vc,vector<float> &vl,vector<float> &pre_vc,vector<float> &pre_vl){

   //algorithm 2 of ePlace-MS: Electrostatics-Based Placement forMixed-Size Circuits
   #ifdef DEBUG
   std::cout<<"BkTrk 1"<<std::endl;
   #endif
   float hat_ac = vector_fraction(vc, vl, pre_vc, pre_vl);
   #ifdef DEBUG
   std::cout<<"BkTrk 2"<<std::endl;
   #endif
   vector<float> hat_un;
   cal_hat_un(hat_ac, hat_un, vc, pre_vc);
   #ifdef DEBUG
   std::cout<<"BkTrk 3"<<std::endl;
   #endif
   vector<float> hat_vn;
   cal_hat_vn(ac, an, hat_vn, hat_un, uc);
   #ifdef DEBUG
   std::cout<<"BkTrk 4"<<std::endl;
   #endif
   /*
   vector<float> pre_hat_vn; //Q this is not correct
   //this part could actually be ignored
   while(hat_ac>0.01*vector_fraction(hat_vn, vc, pre_hat_vn, pre_vc)){ //Q: what is stop condition Q://where is pre_hat_vn
     
     hat_ac = vector_fraction(hat_vn, vc, pre_hat_vn, pre_vc);
     cal_hat_un(hat_ac, hat_un, vc, pre_vc);
     cal_hat_vn(ac, an, hat_vn, hat_un, uc);
   }
   */

   //this part could actually be ignored
   #ifdef DEBUG
   std::cout<<"BkTrk 5"<<std::endl;
   #endif
   ac = hat_ac;

}

float Placement::vector_fraction(vector<float> &vc, vector<float> &vl, vector<float> &pre_vc,vector<float> &pre_vl){

   float sum_upper = 0.0;
   for(unsigned int i=0;i<vc.size();++i){
       sum_upper += (vc[i]-vl[i])*(vc[i]-vl[i]);
   }
   sum_upper = sqrt(sum_upper);
   float sum_lower = 0.0;
   for(unsigned int i=0;i<vc.size();++i){
       sum_lower += (pre_vc[i]-pre_vl[i])*(pre_vc[i]-pre_vl[i]);
   }
   sum_lower = sqrt(sum_lower);

   float hat_ac=sum_upper/sum_lower;
   return hat_ac;
}

void Placement::cal_hat_un(float &hat_ac, vector<float> &hat_un, vector<float> &vc, vector<float> &pre_vc){

   for(unsigned int i=0;i<vc.size();++i){
     hat_un.push_back(vc[i]-hat_ac*pre_vc[i]);
   }

}

void Placement::cal_hat_vn(float &ac, float &an, vector<float> &hat_vn, vector<float> &hat_un, vector<float> &uc){

   for(unsigned int i=0;i<hat_un.size();++i){
     hat_vn.push_back(hat_un[i]+(ac-1)*(hat_un[i]-uc[i])/an);
   }

}

//Calculating pre(vk) Q: also two directions
void Placement::pre_conditioner(vector<float> &Pre_Conditioner,bool x_or_y){ //1 is for x, 0 is for y

  vector<float> HPWL_Pre_Conditioner;
  //LSE_pre_conditioner(HPWL_Pre_Conditioner, x_or_y);
  WA_pre_conditioner(HPWL_Pre_Conditioner, x_or_y);
  //LSE_Pre_Conditioner  
  //LSE_Pre_Conditioner

  vector<float> Desity_Pre_Conditioner;
  for(unsigned int i=0;i<Blocks.size();++i){
     if(x_or_y){
       Desity_Pre_Conditioner.push_back(Blocks[i].Dpoint.x);
     }else{
       Desity_Pre_Conditioner.push_back(Blocks[i].Dpoint.y);
     }
  }

  Pre_Conditioner.clear();
  for(unsigned int i=0;i<Blocks.size();++i){
    if(x_or_y){
      Pre_Conditioner.push_back(1/(HPWL_Pre_Conditioner[i]+lambda*Desity_Pre_Conditioner[i])*(Blocks[i].Force.x));
    }else{
      Pre_Conditioner.push_back(1/(HPWL_Pre_Conditioner[i]+lambda*Desity_Pre_Conditioner[i])*(Blocks[i].Force.y));
    }
  }
}

void Placement::LSE_pre_conditioner(vector<float> &HPWL_Pre_Conditioner, bool x_or_y){

  HPWL_Pre_Conditioner.clear();

  for(unsigned int i=0;i<Blocks.size();++i){
     float sum = 0.0;
     for(unsigned int j=0;j<Blocks[i].connected_net.size();++j){
        int net_index = Blocks[i].connected_net[j];
        if(x_or_y){//1 x, 0 y
         float term1= Blocks[i].Net_block_force_P.x;
         float term2= Nets[net_index].PSumNetforce.x;
         float term3= Blocks[i].Net_block_force_N.x;
         float term4= Nets[net_index].NSumNetforce.x;
         sum += term1*(term2-term1)/(gammar*term2*term2)+term3*(term4-term3)/(gammar*term4*term4);
        }else{
         float term1= Blocks[i].Net_block_force_P.y;
         float term2= Nets[net_index].PSumNetforce.y;
         float term3= Blocks[i].Net_block_force_N.y;
         float term4= Nets[net_index].NSumNetforce.y;
         sum += term1*(term2-term1)/(gammar*term2*term2)+term3*(term4-term3)/(gammar*term4*term4);
        }
     }
    HPWL_Pre_Conditioner.push_back(sum);
  }

}

void Placement::WA_pre_conditioner(vector<float> &HPWL_Pre_Conditioner, bool x_or_y){

  HPWL_Pre_Conditioner.clear();

  for(unsigned int i=0;i<Blocks.size();++i){
     float sum = 0.0;
     sum = Blocks[i].connected_net.size();
     HPWL_Pre_Conditioner.push_back(sum);
  }

}

float Placement::Fast_Exp(float a){
  a = 1.0f + a / 1024.0f;
  a *= a;
  a *= a;
  a *= a;
  a *= a;
  a *= a;
  a *= a;
  a *= a;
  a *= a;
  a *= a;
  a *= a;
  return a;
}

void Placement::WriteOut_Blocks(int iteration){

  std::ofstream writoutfile;

  std::string file_name = to_string(iteration) + "_Iter_Blocks.txt";
  
  writoutfile.open(file_name);

  for(unsigned int i=0;i<Blocks.size();++i){

     writoutfile<<Blocks[i].Cpoint.x<<" "<<Blocks[i].Cpoint.y<<" "<<Blocks[i].Dpoint.x<<" "<<Blocks[i].Dpoint.y<<" "<<Blocks[i].Eforce.x<<" "<<Blocks[i].Eforce.y<<" "<<Blocks[i].Force.x<<" "<<Blocks[i].Force.y<<std::endl;

  }

  writoutfile.close();

}

void Placement::WriteOut_Bins(int iteration){

  std::ofstream writoutfile;

  std::string file_name = to_string(iteration) + "_Iter_Bins.txt";
  
  writoutfile.open(file_name);

  for(unsigned int i=0;i<Bins.size();++i){

     for(unsigned int j=0;j<Bins[i].size();j++){

       writoutfile<<Bins[i][j].Cpoint.x<<" "<<Bins[i][j].Cpoint.y<<" "<<Bins[i][j].Dpoint.x<<" "<<Bins[i][j].Dpoint.y<<" "<<Bins[i][j].density<<" "<<Bins[i][j].Ephi<<" "<<Bins[i][j].Eforce.x<<" "<<Bins[i][j].Eforce.y<<std::endl;

     }

  }

  writoutfile.close();

}


//donghao start
//return the total area of all blocks
float Placement::readInputNode(PnRDB::hierNode &current_node)
{
  int blockIndex = 0;
  float totalArea = 0;
  Blocks.clear();
  Nets.clear();
  std::cout<<"start reading blocks file"<<std::endl;
  int blockCNT = current_node.Blocks.size();
  //initialize sysmmtric matrix
  symmetric_force_matrix = vector<vector<Ppoint_F>>(blockCNT);
  for(int i = 0;i <  blockCNT;++i)
  {
    symmetric_force_matrix[i] = vector<Ppoint_F>(blockCNT);
    for(int j = 0;j < blockCNT;++j)
    {
      symmetric_force_matrix[i][j].x = 0;
      symmetric_force_matrix[i][j].y = 0;
    }
  }

  for(vector<PnRDB::blockComplex>::iterator it=current_node.Blocks.begin(); it!=current_node.Blocks.end(); ++it)
  {
    for(int i = 0;i < it->instNum;++i)
    {
      block tempblock;
      //update block name
      tempblock.blockname = it->instance[i].name;
      Ppoint_F tempPoint1,tempPoint2;
      //update center point
      tempPoint1.x = (float)it->instance[i].originCenter.x;
      tempPoint1.y = (float)it->instance[i].originCenter.y;
      tempblock.Cpoint = tempPoint1;

      //update height and width
      tempPoint2.x = (float)it->instance[i].height;
      tempPoint2.y = (float)it->instance[i].width;
      totalArea += tempPoint2.x * tempPoint2.y;
      tempblock.Dpoint = tempPoint2;

      //set the init force as zero
      tempblock.Force.x = 0;
      tempblock.Force.y = 0;
      tempblock.Netforce.x = 0;
      tempblock.Netforce.y = 0;
      tempblock.Eforce.x = 0;
      tempblock.Eforce.y = 0;
      //set the init NET_BLOCK_FORCE_P/N = 1
      tempblock.Net_block_force_N.x = 1;
      tempblock.Net_block_force_N.y = 1;
      tempblock.Net_block_force_P.x = 1;
      tempblock.Net_block_force_P.y = 1;
      tempblock.index = blockIndex;
      ++blockIndex;
      //connected net will be update later
      Blocks.push_back(tempblock);
    }
  }

  //update net information
  int netIndex = 0;
  std::cout<<"total block number: "<<blockIndex<<std::endl;
  std::cout<<"start reading net file"<<std::endl;
  for(vector<PnRDB::net>::iterator it=current_node.Nets.begin();it!=current_node.Nets.end();++it)
  {
    net tempNet;
    std::cout<<"current net id: "<<netIndex<<std::endl;
    //update name of net
    tempNet.netname = it->name;
    //based on my understanding, iter2 is the block id
    //I do not care about iter, which means block pin/terminal
    tempNet.connected_block.clear();
    for(int i = 0;i != it->connected.size();++i)
    {
      int iter2 = it->connected[i].iter2;
      std::cout<<"connected block id: "<<iter2<<std::endl;
      if(iter2 >= 0)
      {
        tempNet.connected_block.push_back(iter2);
        Blocks[iter2].connected_net.push_back(netIndex);
      }
      
    }
    //update net index
    tempNet.index = netIndex;
    ++netIndex;

    tempNet.NSumNetforce.x = 0;
    tempNet.NSumNetforce.y = 0;
    tempNet.NSumNetforce_WA.x=0;
    tempNet.NSumNetforce_WA.y=0;

    tempNet.PSumNetforce.x = 0;
    tempNet.PSumNetforce.y = 0;
    tempNet.PSumNetforce_WA.x = 0;
    tempNet.PSumNetforce_WA.y = 0;
    Nets.push_back(tempNet);
  }


  //read the symmtirc 
  // #ifdef DEBUG
      std::cout<<"number of sym constrain = "<<current_node.SPBlocks.size()<<endl;
    // #endif;
  for(vector<PnRDB::SymmPairBlock>::iterator it=current_node.SPBlocks.begin();it!= current_node.SPBlocks.end();++it)
  {
    // #ifdef DEBUG
      std::cout<<"sym group start"<<endl;
      std::cout<<"self size = "<<it->selfsym.size()<<", pair size = "<<it->sympair.size()<<endl;
    // #endif;
    SymmPairBlock tempSPB;
    
    tempSPB.selfsym.clear();
    tempSPB.sympair.clear();
    // tempSPB.selfsym = it->selfsym;
    // tempSPB.sympair = it->sympair;
    for(int i = 0;i < it->selfsym.size();++i)
    {
      tempSPB.selfsym.push_back(it->selfsym[i].first);
    }
    for(int i = 0;i < it->sympair.size();++i)
    {
      tempSPB.sympair.push_back(it->sympair[i]);
    }
    
    if(it->axis_dir ==PnRDB::V)
    {
      //cond 1: only one sym pair
      tempSPB.horizon = 0;
      if(it->sympair.size()== 1 && it->selfsym.size() == 0)
      {
        int id0 = it->sympair[0].first;
        int id1 = it->sympair[0].second;
        // #ifdef DEBUG
        std::cout<<"V: cond1, id0 = "<<id0<<", id1 = "<<id1<<endl;
        // #endif;
        symmetric_force_matrix[id0][id0].y+=2;
        symmetric_force_matrix[id0][id1].y-=2;
        symmetric_force_matrix[id1][id0].y-=2;
        symmetric_force_matrix[id1][id1].y+=2;

        tempSPB.axis.first = id0;
        tempSPB.axis.second = id1;
      }
      else if(it->selfsym.size()>0)//exist self sym, consider the first self sym block center as axis = x0
      {
        int base = it->selfsym[0].first;
        tempSPB.axis.first = base;
        tempSPB.axis.second = base;
        // #ifdef DEBUG
        std::cout<<"V: cond2, base = "<<base<<endl;
        // #endif;
        //for self sym (xi - x0)^2
        for(int i = 1;i < it->selfsym.size();++i)
        {
          int id = it->selfsym[i].first;
          std::cout<<"V: cond2, id = "<<id<<endl;
          symmetric_force_matrix[id][id].x += 2;
          symmetric_force_matrix[id][base].x -= 2;
          symmetric_force_matrix[base][id].x -= 2;
          symmetric_force_matrix[base][base].x += 2;
        }
        //for pair sym (xi + xj - 2*x0)^2
        for(int i = 0;i < it->sympair.size();++i)
        {
          int id0 = it->sympair[i].first;
          int id1 = it->sympair[i].second;
          std::cout<<"V: cond2, id0 = "<<id0<<", id1"<<id1<<endl;
          //(yi - yj)^2
          symmetric_force_matrix[id0][id0].y+=2;
          symmetric_force_matrix[id0][id1].y-=2;
          symmetric_force_matrix[id1][id0].y-=2;
          symmetric_force_matrix[id1][id1].y+=2;

          //(xi + xj - 2*x0)^2
          symmetric_force_matrix[id0][id0].x+=2;
          symmetric_force_matrix[id0][id1].x+=2;
          symmetric_force_matrix[id0][base].x-=4;

          symmetric_force_matrix[id1][id0].x+=2;
          symmetric_force_matrix[id1][id1].x+=2;
          symmetric_force_matrix[id1][base].x-=4;

          symmetric_force_matrix[base][id0].x-=2;
          symmetric_force_matrix[base][id1].x-=2;
          symmetric_force_matrix[base][base].x+=4;
        }

      }
      else if(it->sympair.size()>1) //no self sym, consider the center of first sym pair of blocks as axis = 1/2*(x0.first + x0.second)
      {
        int idbase0 = it->sympair[0].first;
        int idbase1 = it->sympair[0].second;
        tempSPB.axis.first = idbase0;
        tempSPB.axis.second = idbase1;
        // #ifdef DEBUG
        std::cout<<"V: cond3, idbase0 = "<<idbase0<<", idbase1 = "<<idbase1<<endl;
        // #endif;
        symmetric_force_matrix[idbase0][idbase0].y+=2;
        symmetric_force_matrix[idbase0][idbase1].y-=2;
        symmetric_force_matrix[idbase1][idbase0].y-=2;
        symmetric_force_matrix[idbase1][idbase1].y+=2;
        for(int i = 1;i < it->sympair.size();++i)
        {
          int id0 = it->sympair[i].first;
          int id1 = it->sympair[i].second;
          // #ifdef DEBUG
          std::cout<<"V: cond3, id0 = "<<id0<<", id1 = "<<id1<<endl;
          // #endif;
          //(yi - yj)^2
          symmetric_force_matrix[id0][id0].y+=2;
          symmetric_force_matrix[id0][id1].y-=2;
          symmetric_force_matrix[id1][id0].y-=2;
          symmetric_force_matrix[id1][id1].y+=2;
          //(xi + xj - x0 - x1)^2
          symmetric_force_matrix[id0][id0].x+=2;
          symmetric_force_matrix[id0][id1].x+=2;
          symmetric_force_matrix[id0][idbase0].x-=2;
          symmetric_force_matrix[id0][idbase1].x-=2;

          symmetric_force_matrix[id1][id0].x+=2;
          symmetric_force_matrix[id1][id1].x+=2;
          symmetric_force_matrix[id1][idbase0].x-=2;
          symmetric_force_matrix[id1][idbase1].x-=2;

          symmetric_force_matrix[idbase0][id0].x-=2;
          symmetric_force_matrix[idbase0][id1].x-=2;
          symmetric_force_matrix[idbase0][idbase0].x+=2;
          symmetric_force_matrix[idbase0][idbase1].x+=2;

          symmetric_force_matrix[idbase1][id0].x-=2;
          symmetric_force_matrix[idbase1][id1].x-=2;
          symmetric_force_matrix[idbase1][idbase0].x+=2;
          symmetric_force_matrix[idbase1][idbase1].x+=2;
        }
      }
      else{
        continue;
      }
    }
    else //axis : H
    {
      tempSPB.horizon = 1;
      //cond 1: only one sym pair
      if(it->sympair.size()== 1 && it->selfsym.size() == 0)
      {
        int id0 = it->sympair[0].first;
        int id1 = it->sympair[1].second;
        tempSPB.axis.first = id0;
        tempSPB.axis.second = id1;
        // #ifdef DEBUG
        std::cout<<"H: cond1, id0 = "<<id0<<", idb1 = "<<id1<<endl;
        // #endif;
        symmetric_force_matrix[id0][id0].x+=2;
        symmetric_force_matrix[id0][id1].x-=2;
        symmetric_force_matrix[id1][id0].x-=2;
        symmetric_force_matrix[id1][id1].x+=2;
      }
      else if(it->selfsym.size()>0)//exist self sym, consider the first self sym block center as axis = x0
      {
        int base = it->selfsym[0].first;
        tempSPB.axis.first = base;
        tempSPB.axis.second = base;
        //for self sym (yi - y0)^2
        // #ifdef DEBUG
        std::cout<<"H: cond2, base = "<<base<<endl;
        // #endif;
        for(int i = 1;i < it->selfsym.size();++i)
        {
          int id = it->selfsym[i].first;
          // #ifdef DEBUG
          std::cout<<"H: cond2, id = "<<id<<endl;
          // std::cout<<"matrix size:"<<symmetric_force_matrix.size()<<", "<<symmetric_force_matrix[0].size()<<endl;
          // #endif;
          symmetric_force_matrix[id][id].y += 2;
          symmetric_force_matrix[id][base].y -= 2;
          symmetric_force_matrix[base][id].y -= 2;
          symmetric_force_matrix[base][base].y += 2;
        }
        //for pair sym (xi + xj - 2*x0)^2
        for(int i = 0;i < it->sympair.size();++i)
        {
          int id0 = it->sympair[i].first;
          int id1 = it->sympair[i].second;
          // #ifdef DEBUG
          std::cout<<"V: cond2, id0 = "<<id0<<", id1 = "<<id1<<endl;
          // #endif;
          //(xi - xj)^2
          symmetric_force_matrix[id0][id0].x+=2;
          symmetric_force_matrix[id0][id1].x-=2;
          symmetric_force_matrix[id1][id0].x-=2;
          symmetric_force_matrix[id1][id1].x+=2;

          //(yi + yj - 2*y0)^2
          symmetric_force_matrix[id0][id0].y+=2;
          symmetric_force_matrix[id0][id1].y+=2;
          symmetric_force_matrix[id0][base].y-=4;

          symmetric_force_matrix[id1][id0].y+=2;
          symmetric_force_matrix[id1][id1].y+=2;
          symmetric_force_matrix[id1][base].y-=4;

          symmetric_force_matrix[base][id0].y-=2;
          symmetric_force_matrix[base][id1].y-=2;
          symmetric_force_matrix[base][base].y+=4;
        }
      }
      else if(it->sympair.size()>1) //no self sym, consider the center of first sym pair of blocks as axis = 1/2*(x0.first + x0.second)
      {
        int idbase0 = it->sympair[0].first;
        int idbase1 = it->sympair[0].second;
        tempSPB.axis.first = idbase0;
        tempSPB.axis.second = idbase1;
        // #ifdef DEBUG
        std::cout<<"H: cond3, idbase0 = "<<idbase0<<", idbase1 = "<<idbase1<<endl;
        // #endif;
        symmetric_force_matrix[idbase0][idbase0].x+=2;
        symmetric_force_matrix[idbase0][idbase1].x-=2;
        symmetric_force_matrix[idbase1][idbase0].x-=2;
        symmetric_force_matrix[idbase1][idbase1].x+=2;
        for(int i = 1;i < it->sympair.size();++i)
        {
          int id0 = it->sympair[i].first;
          int id1 = it->sympair[i].second;
          // #ifdef DEBUG
          std::cout<<"H: cond3, id0 = "<<id0<<", id1 = "<<id1<<endl;
          // #endif;
          //(xi - xj)^2
          symmetric_force_matrix[id0][id0].x+=2;
          symmetric_force_matrix[id0][id1].x-=2;
          symmetric_force_matrix[id1][id0].x-=2;
          symmetric_force_matrix[id1][id1].x+=2;
          //(yi + yj - y0 - y1)^2
          symmetric_force_matrix[id0][id0].y+=2;
          symmetric_force_matrix[id0][id1].y+=2;
          symmetric_force_matrix[id0][idbase0].y-=2;
          symmetric_force_matrix[id0][idbase1].y-=2;

          symmetric_force_matrix[id1][id0].y+=2;
          symmetric_force_matrix[id1][id1].y+=2;
          symmetric_force_matrix[id1][idbase0].y-=2;
          symmetric_force_matrix[id1][idbase1].y-=2;

          symmetric_force_matrix[idbase0][id0].y-=2;
          symmetric_force_matrix[idbase0][id1].y-=2;
          symmetric_force_matrix[idbase0][idbase0].y+=2;
          symmetric_force_matrix[idbase0][idbase1].y+=2;

          symmetric_force_matrix[idbase1][id0].y-=2;
          symmetric_force_matrix[idbase1][id1].y-=2;
          symmetric_force_matrix[idbase1][idbase0].y+=2;
          symmetric_force_matrix[idbase1][idbase1].y+=2;
        }
      }
      else{
        continue;
      }
    }
    SPBlocks.push_back(tempSPB);
    
  }
  //PRINT symmetric _force matrix
  std::cout<<"symmetric_force matrix"<<std::endl;
  for(int i = 0;i < blockCNT;++i)
  {
    for(int j = 0;j< blockCNT;++j)
    {
      std::cout<<"("<<symmetric_force_matrix[i][j].x<<", "<<symmetric_force_matrix[i][j].y<<")";
    }
    std::cout<<std::endl;
  }
  //return the total area
  
  return totalArea;
}

void Placement::Unify_blocks(float area, float scale_factor)
{
  float height = sqrt(scale_factor * area);
  this->est_Size.x = height;
  this->est_Size.y = height;

  for(int i = 0;i < Blocks.size();i++)
  {
    Blocks[i].Cpoint.x /= height;
    Blocks[i].Cpoint.y /= height;
    Blocks[i].Dpoint.x /= height;
    Blocks[i].Dpoint.y /= height;
  }
}
//donghao end

void Placement::print_blocks_nets()
{
  std::cout<<"print information about blocks"<<std::endl;
  for(int i = 0;i <  Blocks.size();++i)
  {
    std::cout<<"block id"<<Blocks[i].index;
    std::cout<<"block position: ("<<Blocks[i].Cpoint.x<<", "<<Blocks[i].Cpoint.y<<")"<<"d:("<<Blocks[i].Dpoint.x<<", "<<Blocks[i].Dpoint.y<<")"<<std::endl;


    std::cout<<"connect net:";
    for(int j = 0;j < Blocks[i].connected_net.size();++j)
    {
      std::cout<<Blocks[i].connected_net[j]<<" "; 
    }
    std::cout<<std::endl;
  }
}

void Placement::Cal_sym_Force()
{
  #ifdef DEBUG
  std::cout<<"Cal_sym_Force debug flag: 1"<<std::endl;
  #endif
  for(int i = 0;i < symmetric_force_matrix.size();++i)
  {
    Blocks[i].Symmetricforce.x = 0;
    Blocks[i].Symmetricforce.y = 0;
    for(int j = 0;j < symmetric_force_matrix[i].size();++j)
    {
      #ifdef DEBUG
      std::cout<<"Cal_sym_Force debug flag: 3"<<std::endl;
      std::cout<<"force x="<<symmetric_force_matrix[i][j].x<<", force y="<<symmetric_force_matrix[i][j].y;
      std::cout<<"center x="<<Blocks[j].Cpoint.x<<", center y="<<Blocks[j].Cpoint.y<<std::endl;
      #endif
      Blocks[i].Symmetricforce.x += symmetric_force_matrix[i][j].x * Blocks[j].Cpoint.x;
      Blocks[i].Symmetricforce.y += symmetric_force_matrix[i][j].y * Blocks[j].Cpoint.y;
      #ifdef DEBUG
      std::cout<<"Cal_sym_Force debug flag: 4"<<std::endl;
      #endif
    }
    if(isnan(Blocks[i].Symmetricforce.x ))
    { 
      #ifdef DEBUG
      std::cout<<"Cal_sym_Force debug flag: 5"<<std::endl;
      #endif
      Blocks[i].Symmetricforce.x = 0;
    }
    if(isnan(Blocks[i].Symmetricforce.y ))
    {
      #ifdef DEBUG
      std::cout<<"Cal_sym_Force debug flag: 6"<<std::endl;
      #endif
      Blocks[i].Symmetricforce.y = 0;
    }
  }
  #ifdef DEBUG
  std::cout<<"Cal_sym_Force debug flag: 2"<<std::endl;
  #endif
}

void Placement::read_alignment(PnRDB::hierNode &current_node)
{
  //###############################################
    //old version using struct Alignment//
    //###############################################
  // float height = this->est_Size.y;
  // float weight = this->est_Size.x;
  // Alignment_blocks.clear();

  // for(int i = 0;i < current_node.Alignment_blocks.size();++i)
  // {
    
    
    // Alignment temp;
    // //find the larger blocks
    // float s1,s2;
    // int id1,id2;
    // id1 = current_node.Alignment_blocks[i].blockid1;
    // id2 = current_node.Alignment_blocks[i].blockid2;

    // s1 = Blocks[id1].Dpoint.x * Blocks[id1].Dpoint.y;
    // s2 = Blocks[id2].Dpoint.x * Blocks[id2].Dpoint.y;
    // if(s2 > s1)
    // {
    //   temp.blockid1 = id2;
    //   temp.blockid2 = id1;
    // }
    // else
    // {
    //   temp.blockid1 = id1;
    //   temp.blockid2 = id2;
    // }

    // temp.horizon = current_node.Alignment_blocks[i].horizon;
    // if(temp.horizon == 1)//LL1.x = LL2.x ->c1.x - d1.x/2 = c2.x - d2.x/2
    // //distance = c2.x - c1.x = d2.x/2 - d1.x/2
    // {
    //   temp.distance = 0.5*(Blocks[temp.blockid2].Dpoint.x - Blocks[temp.blockid1].Dpoint.x);
    // }
    // else
    // {
    //   temp.distance = 0.5*(Blocks[temp.blockid2].Dpoint.y - Blocks[temp.blockid1].Dpoint.y);
    // }

    // Alignment_blocks.push_back(temp);

    //###############################################
    //new version using struct AlignBLock//
    //###############################################

  // }
  AlignBlocks.clear();
  for(int i = 0;i<current_node.Align_blocks.size();++i)
  {
    AlignBlock temp;
    PnRDB::AlignBlock *curAlign = &current_node.Align_blocks[i];
    temp.blocks.clear();
    temp.blocks = curAlign->blocks;
    temp.horizon = curAlign->horizon;
    //find the largest blocks and put it into begin()
    AlignBlocks.push_back(temp);
  }
}

void Placement::force_alignment()
{
  //###############################################
  //old version using struct Alignment//
  //###############################################

  // for(int i = 0;i < Alignment_blocks.size();++i)
  // {
  //   int id1 = Alignment_blocks[i].blockid1;
  //   int id2 = Alignment_blocks[i].blockid2;
  //   float distance = Alignment_blocks[i].distance;
  //   if(Alignment_blocks[i].horizon == 1)
  //   {
  //     Blocks[id2].Cpoint.x = Blocks[id1].Cpoint.x + distance;
  //   }
  //   else
  //   {
  //     Blocks[id2].Cpoint.y = Blocks[id1].Cpoint.y + distance;
  //   }
  // }
  std::cout<<"force align begin"<<std::endl;
  for(int i = 0;i < AlignBlocks.size();++i)
  {
    int headIdx = AlignBlocks[i].blocks[0];
    Ppoint_F head_pos = Blocks[headIdx].Cpoint;
    Ppoint_F head_dem = Blocks[headIdx].Dpoint;
    if(AlignBlocks[i].horizon)
    {
      for(int j = 1;j<AlignBlocks[i].blocks.size();++j)
      {
        int cur_idx = AlignBlocks[i].blocks[j];
        Ppoint_F cur_dem = Blocks[cur_idx].Dpoint;
        
        float distance = 1/2*(cur_dem.y - head_dem.y);
        Blocks[cur_idx].Cpoint.y = head_pos.y + distance;
      }
    }
    else
    {
      for(int j = 1;j<AlignBlocks[i].blocks.size();++j)
      {
        int cur_idx = AlignBlocks[i].blocks[j];
        Ppoint_F cur_dem = Blocks[cur_idx].Dpoint;
        
        float distance = 1/2*(cur_dem.x - head_dem.x);
        Blocks[cur_idx].Cpoint.x = head_pos.x + distance;
      }
    }
  }
  std::cout<<"force align finish"<<std::endl;
}

void Placement::read_order(PnRDB::hierNode &current_node)
{
  Ordering_Constraints = current_node.Ordering_Constraints;
  std::cout<<"ordering constraints size: "<<Ordering_Constraints.size()<<std::endl;
}

void Placement::force_order()
{
  //step 1: put the Cpoint into verctor
  for(int i = 0;i < Ordering_Constraints.size();++i)
  {
    vector<Ppoint_F> Centers = vector<Ppoint_F>();
    for(int j = 0;j <Ordering_Constraints[i].first.size();++j)
    {
      std::cout<<"ordering id before sort: "<< Ordering_Constraints[i].first[j];
      Centers.push_back(Blocks[Ordering_Constraints[i].first[j]].Cpoint);
      std::cout<<"pos:"<<Centers[j].x<<", "<<Centers[j].y<<std::endl;
    }
    //step 2: sort the Cpoint vector
    if(Ordering_Constraints[i].second == PnRDB::H)
    {
      sort(Centers.begin(),Centers.end(),comp_x);
    }
    else
    {
      sort(Centers.begin(),Centers.end(),comp_y);
    }
    //step 3: assign the sorted cpoint 

    for(int j = 0;j <Ordering_Constraints[i].first.size();++j)
    {
      int id = Ordering_Constraints[i].first[j];
      std::cout<<"ordering id after sort: "<< id;
      if(Ordering_Constraints[i].second == PnRDB::H)
      {
        Blocks[id].Cpoint.x = Centers[j].x;
      }
      else
      {
        Blocks[id].Cpoint.y = Centers[j].y;
      }
      
      std::cout<<"pos:"<<Centers[j].x<<", "<<Centers[j].y<<std::endl;
    }
  }
  
  
}

bool Placement::comp_x(Ppoint_F c1, Ppoint_F c2)
{
  return c1.x < c2.x;
}

bool Placement::comp_y(Ppoint_F c1, Ppoint_F c2)
{
  return c1.y > c2.y;
}

void Placement::writeback(PnRDB::hierNode &current_node)
{
  int idx = 0;
  for(vector<PnRDB::blockComplex>::iterator it=current_node.Blocks.begin(); it!=current_node.Blocks.end(); ++it)
  {
    for(int i = 0;i < it->instNum;++i)
    {
      it->instance[i].placedCenter.x = (int)(est_Size.x * Blocks[idx].Cpoint.x);
      it->instance[i].placedCenter.y = (int)(est_Size.y * Blocks[idx].Cpoint.y);

      it->instance[i].placedBox.LL.x = (int)(est_Size.x*Blocks[idx].Cpoint.x ) - it->instance[i].width/2;
      it->instance[i].placedBox.LL.y = (int)(est_Size.y*Blocks[idx].Cpoint.y ) - it->instance[i].height/2;

      it->instance[i].placedBox.UR.x = (int)(est_Size.x*Blocks[idx].Cpoint.x ) + it->instance[i].width/2;
      it->instance[i].placedBox.UR.y = (int)(est_Size.y*Blocks[idx].Cpoint.y ) + it->instance[i].height/2;
      it->instance[i].orient = PnRDB::N;
      ++idx;
    }
  }

}

bool Placement::symCheck(float tol)
{
  float tot_bias = 0;
  for(int i = 0;i < SPBlocks.size();++i)
  {
    if(SPBlocks[i].horizon)
    {
      //step 1: find the axis 
      float axis,axis_double;
      int baseid0,baseid1;
      baseid0 = SPBlocks[i].axis.first;
      baseid1 = SPBlocks[i].axis.second;
      axis = 0.5*(Blocks[baseid0].Cpoint.y +Blocks[baseid1].Cpoint.y );
      axis_double = axis*2;
      //step 2: evalue all modules in sympair
      for(int j = 0;j < SPBlocks[i].sympair.size();++j)
      {
        int id0 = SPBlocks[i].sympair[j].first;
        int id1 = SPBlocks[i].sympair[j].second;
        tot_bias += fabs(Blocks[id0].Cpoint.y+Blocks[id1].Cpoint.y - axis_double);
      }
      //step 3: evalue all modules in selfsym
      for(int j = 0;j < SPBlocks[i].selfsym.size();++j)
      {
        int id0 = SPBlocks[i].selfsym[j];
        tot_bias += fabs(Blocks[id0].Cpoint.y - axis);
      }
    }
    else
    {
      //step 1: find the axis 
      float axis,axis_double;
      int baseid0,baseid1;
      baseid0 = SPBlocks[i].axis.first;
      baseid1 = SPBlocks[i].axis.second;
      axis = 0.5*(Blocks[baseid0].Cpoint.x +Blocks[baseid1].Cpoint.x );
      axis_double = axis*2;
      //step 2: evalue all modules in sympair
      for(int j = 0;j < SPBlocks[i].sympair.size();++j)
      {
        int id0 = SPBlocks[i].sympair[j].first;
        int id1 = SPBlocks[i].sympair[j].second;
        tot_bias += fabs(Blocks[id0].Cpoint.x+Blocks[id1].Cpoint.x - axis_double);
      }
      //step 3: evalue all modules in selfsym
      for(int j = 0;j < SPBlocks[i].selfsym.size();++j)
      {
        int id0 = SPBlocks[i].selfsym[j];
        tot_bias += fabs(Blocks[id0].Cpoint.x - axis);
      }
    }
    
  }
  std::cout<<"tot_symmetric bias = "<<tot_bias<<std::endl;
  return tot_bias>tol;
}