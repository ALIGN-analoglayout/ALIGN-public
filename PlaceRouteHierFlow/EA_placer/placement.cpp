#include "placement.h"
//#define DEBUG
Placement::Placement() {

}

Placement::Placement(PnRDB::hierNode &current_node) {
  //step 1: transfroming info. of current_node to Blocks and Nets
    //create a small function for this

  //step 2: Given a initial position for each block
    //create a small function for this
      // need to estimate a area to do placement
      // scale into 1x1
      // initial position for each block

  //step 3: call E_placer
  

}


Placement::Placement(float chip_width, float chip_hight, float bin_width, float bin_hight) {

  this->Chip_D.x = chip_width;
  this->Chip_D.y = chip_hight;
  this->Bin_D.x = bin_width;
  this->Bin_D.x = bin_hight;

}

void Placement::generate_testing_data(){
  std::cout<<"generating test 1"<<std::endl;
  Random_Generation_Block_Nets();
  std::cout<<"generating test 2"<<std::endl;
  Initilize_Placement();
  std::cout<<"generating test 3"<<std::endl;
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

       #ifdef DEBUG
       std::cout<<"Bin density"<<Bins[i][j].density<<std::endl;
       Bins[i][j].density = Bins[i][j].density/(Bin_D.x*Bin_D.y);
       #endif

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
      y_value.push_back(Blocks[block_index].Cpoint.x);
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
    float bias=1;
    fout<<"\nset xrange ["<<0.0-bias<<":"<<Chip_D.x+bias<<"]"<<endl;
    fout<<"\nset yrange ["<<0.0-bias<<":"<<Chip_D.y+bias<<"]"<<endl;

    // set labels for blocks
    /*
    for(int i=0;i<(int)Blocks.size();++i) {
      fout<<"\nset label \""<<" B"+to_string(i)<<"\" at "<<Blocks[i].Cpoint.x<<" , "<<Blocks[i].Cpoint.y<<" center "<<endl;
    }
    */
    
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
        float x_positive = ( (1+Blocks[i].Cpoint.x/gammar)*Blocks[i].Net_block_force_P.x*PSumNetforce.x + Blocks[i].Net_block_force_P.x*PSumNetforce_WA.x ) / (PSumNetforce.x * PSumNetforce.x);
        float x_nagative = ( (1+Blocks[i].Cpoint.x/gammar)*Blocks[i].Net_block_force_N.x*NSumNetforce.x + Blocks[i].Net_block_force_N.x*NSumNetforce_WA.x ) / (NSumNetforce.x * NSumNetforce.x);
        float y_positive = ( (1+Blocks[i].Cpoint.y/gammar)*Blocks[i].Net_block_force_P.y*PSumNetforce.y + Blocks[i].Net_block_force_P.y*PSumNetforce_WA.y ) / (PSumNetforce.y * PSumNetforce.y);
        float y_nagative = ( (1+Blocks[i].Cpoint.y/gammar)*Blocks[i].Net_block_force_N.y*NSumNetforce.y + Blocks[i].Net_block_force_N.y*NSumNetforce_WA.y ) / (NSumNetforce.y * NSumNetforce.y);
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

    int binCntX=x_dimension_bin; 
    int binCntY=y_dimension_bin;
    float binSizeX= unit_x_bin;
    float binSizeY= unit_y_bin;
    
    replace::FFT fft(binCntX, binCntY, binSizeX, binSizeY);
    #ifdef DEBUG
    cout<<"test flag 1"<<endl;
    #endif

    for(unsigned int i=0;i<binCntX;++i){
       for(unsigned int j=0;j<binCntY;j++){
          fft.updateDensity(i, j, Bins[i][j].density); 
       }
    }

    #ifdef DEBUG
    cout<<"test flag 2"<<endl;
    #endif
    fft.doFFT();

    #ifdef DEBUG
    cout<<"end test fft functions"<<endl;
    #endif

    for(unsigned int i=0;i<binCntX;++i) {
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

    for(unsigned int i=0;i<Blocks.size();++i){
      Cal_Eforce_Block(i);
    }

}

void Placement::Cal_Net_force(){
   //using lse or wa to calculated the force/gradient due to net
   //need a lse/wa kernel

   //lse functions?
   

   //wa functions?


}

void Placement::Cal_force(){

  for(unsigned int i=0;i<Blocks.size();++i){
     Blocks[i].Force.x = lambda*Blocks[i].Eforce.x - Blocks[i].Netforce.x;
     Blocks[i].Force.y = lambda*Blocks[i].Eforce.y - Blocks[i].Netforce.y;
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
    return false;
  }else{
    return true;
  }

}

void Placement::E_Placer(){

  int i=0;

  Update_Bin_Density();
  //gradient cal
  //Cal_WA_Net_Force();
  Cal_LSE_Net_Force();
  Cal_Density_Eforce();
  Cal_force();

  float ac_x=1.0f;
  vector<float> pre_vc_x, pre_vl_x;
  pre_conditioner(pre_vl_x,1); //1 x direction
  vector<float> uc_x,vc_x,vl_x;
  Extract_Placement_Vectors(uc_x, 1);
  Extract_Placement_Vectors(vc_x, 1);
  Extract_Placement_Vectors(vl_x, 1);

  float ac_y=1.0f;
  vector<float> pre_vc_y, pre_vl_y;
  pre_conditioner(pre_vl_y,0); //1 x direction
  vector<float> uc_y,vc_y,vl_y;
  Extract_Placement_Vectors(uc_y, 0);
  Extract_Placement_Vectors(vc_y, 0);
  Extract_Placement_Vectors(vl_y, 0);
  bool start_flag = 1;
  Update_Bin_Density();

  float stop_density = 0.01;
  float max_density = 1.0;
  float current_max_density=1.0;
  int count_number = 0;
  int upper_count_number = 20;
  vector<float> Density;

  while(Stop_Condition(stop_density,current_max_density) and count_number<upper_count_number){//Q: stop condition
  //while(i<200){//Q: stop condition
     if(current_max_density<max_density){
        max_density = current_max_density;
      }else if(current_max_density==Density.back()){
        count_number++;
      }
     Density.push_back(current_max_density);
     std::cout<<"Iteration "<<i<<std::endl;
     //if(lambda<100)
     lambda = lambda *1.20;
     PlotPlacement(i);

     Update_Bin_Density();
     //gradient cal
     Cal_WA_Net_Force();
     //Cal_LSE_Net_Force();
     Cal_Density_Eforce();
     Cal_force();

     WriteOut_Blocks(i);
     WriteOut_Bins(i);
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
     #ifdef DEBUG
     std::cout<<"test 4"<<std::endl;
     #endif
     start_flag=0;
     i++;
  }

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





