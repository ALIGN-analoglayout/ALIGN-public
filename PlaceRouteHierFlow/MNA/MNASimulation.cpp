#include "MNASimulation.h"
#include <iostream>
#include <cstdlib>
#include <ctime>
#include "slu_ddefs.h"
#include "assert.h"

std::string MNASimulation::Index_Postion(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, int index){

  std::string position_string;
  for(auto it=point_set.begin();it!=point_set.end();++it){
     if(it->index==index && it->metal_layer>=0 && it->power!=0){
           position_string = std::to_string(it->metal_layer)+"_"+std::to_string(it->x)+"_"+std::to_string(it->y)+"_v";
           break;
     }else if(it->index==index && it->metal_layer>=0 && it->power==0){
           position_string = std::to_string(it->metal_layer)+"_"+std::to_string(it->x)+"_"+std::to_string(it->y)+"_g";
           break;
     }else if(it->index==index && it->metal_layer<0 && it->power!=0){
           position_string = "n_"+std::to_string(abs(it->metal_layer))+"_"+std::to_string(it->x)+"_"+std::to_string(it->y)+"_v";
           break;
     }else if(it->index==index && it->metal_layer<0 && it->power==0){
           position_string = "n_"+std::to_string(abs(it->metal_layer))+"_"+std::to_string(it->x)+"_"+std::to_string(it->y)+"_g";
           break;
     }
  }
 return position_string;
};

std::string MNASimulation::Index_Postion_New(int index, bool start_end){

  std::string position_string;
  MDB::metal_point temp_point;

  if(start_end){
    temp_point = Power_Grid_devices[index].start_point;
  }else{
    temp_point = Power_Grid_devices[index].end_point;
  }
  
  if(temp_point.metal_layer>=0 && temp_point.power==0)
      position_string = std::to_string(temp_point.metal_layer)+"_"+std::to_string(temp_point.x)+"_"+std::to_string(temp_point.y)+"_g";
  if(temp_point.metal_layer>=0 && temp_point.power!=0)
      position_string = std::to_string(temp_point.metal_layer)+"_"+std::to_string(temp_point.x)+"_"+std::to_string(temp_point.y)+"_v";
  if(temp_point.metal_layer<0 && temp_point.power==0)
      position_string = "n_"+std::to_string(temp_point.metal_layer)+"_"+std::to_string(temp_point.x)+"_"+std::to_string(temp_point.y)+"_g";
  if(temp_point.metal_layer<0 && temp_point.power!=0)
      position_string = "n_"+std::to_string(temp_point.metal_layer)+"_"+std::to_string(temp_point.x)+"_"+std::to_string(temp_point.y)+"_v";

  return position_string;
};



void MNASimulation::WriteOut_Spice(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set){
  
  //open file
  std::string spice_file_name="test.sp";
  std::ofstream spicefile;
  spicefile.open(spice_file_name);

  //test seting  
  std::string setting1=".TEMP 25.0";
  spicefile<<setting1<<std::endl;
  std::string setting2=".OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST";
  spicefile<<setting2<<std::endl;
  std::string setting3=".TRAN 10e-12 30e-9 START=0";
  spicefile<<setting3<<std::endl;

  //RIV element
  //node: m2_x_y_power - 1_0_0_v/g
  //dummy node: n?_x1_y1_power - n1_0_0_v/g or n2_0_0_v/g
  for(unsigned int i=0;i<Power_Grid_devices.size();i++){

     if(Power_Grid_devices[i].device_type==MDB::R){
        std::string post_index_start = Index_Postion_New(i,1);
        std::string post_index_end =  Index_Postion_New(i,0);
        spicefile<<"R_"+std::to_string(Power_Grid_devices[i].start_point_index)+"_"+std::to_string(Power_Grid_devices[i].end_point_index)+" "+post_index_start+" "+post_index_end+" "+std::to_string(Power_Grid_devices[i].value)<<std::endl;
     }else if(Power_Grid_devices[i].device_type==MDB::I){
        std::string post_index_start = Index_Postion_New(i,1);
        std::string post_index_end =  Index_Postion_New(i,0);
        spicefile<<"I_"+std::to_string(Power_Grid_devices[i].start_point_index)+"_"+std::to_string(Power_Grid_devices[i].end_point_index)+" "+post_index_start+" "+post_index_end+" "+std::to_string(Power_Grid_devices[i].value)<<std::endl;
     }else if(Power_Grid_devices[i].device_type==MDB::V){
        std::string post_index_start = Index_Postion_New(i,1);
        std::string post_index_end =  "0";
        spicefile<<"V_"+std::to_string(Power_Grid_devices[i].start_point_index)+"_"+std::to_string(0)+" "+post_index_start+" "+post_index_end+" "+std::to_string(Power_Grid_devices[i].value)<<std::endl;
     }
  }

  //print out testresults
  //node: m2_x1_y1_x2_y2 - 1_0_0
  //dummy node: n?_x1_y1_x2_y2 - n1_0_0 or n2_0_0
  //only print m2?
  spicefile<<".PRINT ";
  for(auto it=point_set.begin();it!=point_set.end();++it){
     std::string post_index = Index_Postion(point_set,it->index);
     spicefile<<"v("+post_index+") ";
  }  

  spicefile<<std::endl;
  spicefile<<".END"; 
  //close file
  spicefile.close();
};

MNASimulation::MNASimulation(PnRDB::hierNode &current_node, PnRDB::Drc_info &drc_info, std::string inputfile, std::string outputfile, std::string outputem){

  auto logger = spdlog::default_logger()->clone("MNA.MNASimulation.MNASimulation");

  boost_matrix out_R, out_I; 
  std::vector<std::vector<double> > Istore,Vstore,Rstore;
  std::vector<int> mark_point;
  this->Drc_info = drc_info;

  this->R = out_R;
  this->I = out_I;

  std::set<MDB::metal_point, MDB::Compare_metal_point> point_set;
  ExtractPowerGrid(current_node.Vdd, current_node.Gnd, drc_info, Power_Grid_devices, mark_point, point_set, inputfile);

  //std::cout<<"Start Writing spice file"<<std::endl;
  //WriteOut_Spice(point_set);
  //std::cout<<"End Writing spice file"<<std::endl;

  std::set<MDB::metal_point, MDB::Compare_metal_point> vdd_point_set;
  std::set<MDB::metal_point, MDB::Compare_metal_point> gnd_point_set;

  //std::cout<<"Vdd Devices"<<std::endl;
  Print_Devices(Power_Grid_devices);

  SuperMatrix A, L, U, B, X;
  double   *a, *rhs;
  //double   s, u, p, e, r, l;
  int      *asub, *xa;
  int      *perm_r; /* row permutations from partial pivoting */
  int      *perm_c; /* column permutation vector */
  int      nrhs, info, i, m, n, nnz;//, permc_spec;
  superlu_options_t options;
  SuperLUStat_t stat;

  int node_num1 = nodenum(Power_Grid_devices);

  //int maxx,maxy; 
  //int layer = 6;
  //maxx = MaxX(gnd_point_set,layer);
  //maxy = MaxY(gnd_point_set,layer);
  //std::cout << "maxx = "<< maxx <<" maxy= " << maxy << std::endl;

  int powerdev = 0;
  int currentdev = 0;
  //int zeropower = 0;
  for(unsigned int it=0;it<Power_Grid_devices.size();++it){
	  if(Power_Grid_devices[it].device_type == MDB::V){
	    powerdev++;
	  }
	  if(Power_Grid_devices[it].device_type == MDB::I){
	    currentdev++;
	  }
  }
  //std::cout<<"power dev = " << powerdev << std::endl;
	nrhs = 1;
  m = node_num1 + powerdev;

  //handing rhs only, current source is -J or J, voltage source is V
  if ( !(rhs = doubleMalloc(m * nrhs)) ) ABORT("Malloc fails for rhs[].");
  for (int i = 0; i < m; ++i) rhs[i] = 0.0;
  for (int i =0.0 ; i < node_num1; i++){ //start is -current, end is current
	  for(unsigned int it=0;it<Power_Grid_devices.size();++it){
	    if(Power_Grid_devices[it].device_type == MDB::I){
		    int start = Power_Grid_devices[it].start_point_index-1;
		    int end = Power_Grid_devices[it].end_point_index-1;
		    double current = Power_Grid_devices[it].value;
		    rhs[start] = -current;
		    if (end >= 0)		
		      rhs[end] = current;
		  }
	
	    if (Power_Grid_devices[it].device_type == MDB::V){ //start is +1, end is -1
		    //int start = Power_Grid_devices[it].start_point_index-1;
		    int end = Power_Grid_devices[it].end_point_index;
		    //end = -1;
		    double power = Power_Grid_devices[it].value;
		    if (power > 0){
		    rhs[node_num1 -1 - end] = power; //this is strange, why node_num1 - end ; end is a nagetive number; one only one Q: need to combine some when the voltage have some start node number
        }
		  }
	  }
  }

  dCreate_Dense_Matrix(&B, m, nrhs, rhs, m, SLU_DN, SLU_D, SLU_GE);
  dCreate_Dense_Matrix(&X, m, nrhs, rhs, m, SLU_DN, SLU_D, SLU_GE);

  dPrint_Dense_Matrix("B",&B);
    /* Initialize matrix A. */

  int count = 0;
  logger->debug("count= {0}" , count);
  std::vector<double> store;

  count = 2 * (int(Power_Grid_devices.size())-currentdev) + node_num1;

  logger->debug("count= {0}",count);
  m = n = node_num1 + powerdev;
  nnz = count;
 
  if ( !(a = doubleMalloc(nnz)) ) ABORT("Malloc fails for a[].");
  //std::cout<<"checkcheck"<<std::endl;
  if ( !(asub = intMalloc(nnz)) ) ABORT("Malloc fails for asub[].");
  if ( !(xa = intMalloc(n+1)) ) ABORT("Malloc fails for xa[].");
  xa[n] = count;
  count = 0;

  //changing A matrix into the superlu format
  for(int i = 0; i < node_num1 + powerdev; i++){
	  std::vector<double> temp(node_num1+powerdev,0);//powerdev should be number of voltage source
	  int flag = 0;
    if(i<node_num1){
	    double self = 0.0;	
	    for(unsigned int j = 0; j<Power_Grid_devices.size(); ++j){
	      if(Power_Grid_devices[j].device_type== 0 && Power_Grid_devices[j].start_point_index == i+1){//Resistance
		      int position = Power_Grid_devices[j].end_point_index-1;
		      double value = Power_Grid_devices[j].value;
		      double data = temp[position];
	        data = data - 1.0/value;
		      self = self + 1.0/value;
		      temp[position] = data;
		    }
	      if(Power_Grid_devices[j].device_type == 0 && Power_Grid_devices[j].end_point_index == i+1){
		     int position = Power_Grid_devices[j].start_point_index-1;
		     double value = Power_Grid_devices[j].value;
		     double data = temp[position];
	       data = data - 1.0/value;
		     self = self + 1.0/value;
		     temp[position] = data;
		    }
	      if(Power_Grid_devices[j].device_type == 2 && Power_Grid_devices[j].start_point_index == i+1){
		    double value = Power_Grid_devices[j].value;
		    int flag = -1;
		    if(value > 0) flag = 0; //Q: why need to distinguish this one?		
		    int position = node_num1 -Power_Grid_devices[j].end_point_index - 0.5*powerdev*flag - 1; //vdd and gnd power devices have different index? or their end?
		    temp[position] = 1.0; // here is only 1, the other node is gnd, so can be ignored
		    }
	    }
	    temp[i] = self; // this flag might be some problem?
	    for (unsigned int j = 0;j <temp.size();++j){
		    if (temp[j]!=0){
			    if (flag == 0){
				    flag = 1;
				    xa[i]=count;
			    }
			    a[count] = temp[j];
			    asub[count] = j;
			    count = count + 1;
		    }
      }
    }else{
	    std::vector<double> temp(node_num1+powerdev,0);
	    for(unsigned int j = 0; j<Power_Grid_devices.size(); ++j){
		    if(Power_Grid_devices[j].device_type == 2 && Power_Grid_devices[j].value != 0){
			    int start = Power_Grid_devices[j].start_point_index-1;
			    if(-Power_Grid_devices[j].end_point_index == i+1-node_num1){
				    temp[start] = 1.0;
			    }
		    } //why we need this one? seems we have some power devices, which have 0 values //Vdd and gnd Values?
		    if (Power_Grid_devices[j].device_type == 2 && Power_Grid_devices[j].value == 0){
			    int start = Power_Grid_devices[j].start_point_index-1;
			    if (-Power_Grid_devices[j].end_point_index == i+1-node_num1 - 0.5 *powerdev){
				    temp[start] = 1.0;
			    }
	  	  }
	    }
	    for (unsigned int j = 0;j <temp.size();++j){
	      //store.push_back(temp[j]);
	      if (temp[j]!=0){
			    if (flag == 0){
				    flag = 1;
				    xa[i]=count;
			    }
			    a[count] = temp[j];
			    asub[count] = j;
			    count = count + 1;
		    }
	    }
    }
}

  //std::cout<<"check point1"<<std::endl;
  /* Create matrix A in the format expected by SuperLU. */
  dCreate_CompCol_Matrix(&A, m, n, nnz, a, asub, xa, SLU_NC, SLU_D, SLU_GE);
  //std::cout<<"check point2"<<std::endl;
  dPrint_CompCol_Matrix("A", &A);
  //char equed[1] = {'B'};
  int *etree;
  int ldx;
  double *R, *C, *xact;
  double *work = NULL;
  //trans_t  trans;
  //trans = NOTRANS;
  xact = doubleMalloc(n * nrhs);
  ldx = n;
  dGenXtrue(n, nrhs, xact, ldx);
  //dFillRHS(trans, nrhs, xact, ldx, &A, &B);

  if ( !(etree = intMalloc(n)) ) ABORT("Malloc fails for etree[].");
  if ( !(R = (double *) SUPERLU_MALLOC(A.nrow * sizeof(double))) )
  ABORT("SUPERLU_MALLOC fails for R[].");
  if ( !(C = (double *) SUPERLU_MALLOC(A.ncol * sizeof(double))) )
  ABORT("SUPERLU_MALLOC fails for C[].");
  //double rpg, rcond;
  //mem_usage_t   mem_usage;
  //GlobalLU_t  Glu;
  int lwork = 0;
  if ( lwork > 0 ) {
    work = (double *) SUPERLU_MALLOC(lwork);
    if ( !work ) ABORT("Malloc fails for work[].");
  }
  if (!(perm_r = intMalloc(m)))
    ABORT("Malloc fails for perm_r[].");
  if (!(perm_c = intMalloc(n)))
    ABORT("Malloc fails for perm_c[].")
  //dPrint_CompCol_Matrix("A",&A);
  // ilu_set_default_options(&options);  
  set_default_options(&options);
  //std::cout<<"check point3"<<std::endl;
  //options.PivotGrowth = YES;/* Compute reciprocal pivot growth */
  //options.ConditionNumber = YES;
  //options.ILU_DropTol= 0.00000001;
  //options.ILU_FillTol=0.00001;
  options.ColPerm = COLAMD;
  //options.IterRefine = SLU_DOUBLE;
  //options.DiagPivotThresh = 0.000001;
  //std::cout<<"check point4"<<std::endl;
  /* Initialize the statistics variables. */
  StatInit(&stat);
  //std::cout<<"check point5"<<std::endl;
  /* Solve the linear system. */
  /*
  dgsisx(&options, &A, perm_c, perm_r, etree, equed, R, C,
	&L, &U, work, lwork, &B, &B, &rpg, &rcond, &Glu,
	&mem_usage, &stat, &info);*/

  dgssv(&options, &A, perm_c, perm_r, &L, &U, &B, &stat, &info);
  logger->debug("check point6 info == {0}", info);  
  
  dPrint_CompCol_Matrix("A", &A);
  //dPrint_CompCol_Matrix("U", &U);
  //dPrint_SuperNode_Matrix("L", &L);
  //print_int_vec("\nperm_r", m, perm_r);
  //std::cout<<"check point7"<<std::endl;  
  dPrint_Dense_Matrix("B",&B);
  //std::cout<<"check point8"<<std::endl;
  /*Detect the result*/
  DNformat* Bstore = (DNformat*) B.Store;
  register int k, j, lda = Bstore->lda;
  double* dp;
  double* volt;
  dp = (double*) Bstore->nzval; 

  //int vol_count = 0;
  if (!(volt = doubleMalloc(n)))    ABORT("Malloc fails for volt[].")
    //std::cout<<"check point9"<<std::endl;  
  //int num_nodes         = m_Gmat->GetNumNodes();
  for (i = 0; i < n; ++i) {
    for (j = 0; j < B.ncol; ++j) {
      for (k = 0; k < B.nrow; ++k) {
        volt[i] = dp[k + j * lda ];
        // sum_volt   = sum_volt + volt;
      }
    }
  }
  for (k = 0; k < B.nrow; ++k){
    logger->debug("dp[ {0} ]= {1} ", k, dp[k]);
  }

  Print_Result(point_set, dp, outputfile);
  //Print_Grid(point_set,Power_Grid_devices);
  Print_EM(point_set,Power_Grid_devices,B.nrow,dp, outputem);
  /*	
  for (int j = 0; j < n; j++){
    std::cout<<"volt[" << j << "]=" << volt[j] <<std::endl;
  }*/
  //std::cout<<"check point10"<<std::endl;
  double min = 0.8;
  for (int i = 0; i < B.nrow; i++){
    if (dp[i] < min ){
       for(auto it = point_set.begin(); it != point_set.end(); it++){
         //pythonfile<< it->x << " " << it->y << " " << it->metal_layer << " "<< dp[it->index - 1] << " " << it->power <<std::endl;
         if (it->power != 0 && it->index == i + 1)  min = dp[i];			
         }		
    }
  }
  result = min;
  logger->debug("result= {0}" , result);

  //std::cout<<"check point11"<<std::endl;
  /* De-allocate storage */
  SUPERLU_FREE (rhs);
  SUPERLU_FREE (perm_r);
  SUPERLU_FREE (perm_c);
  //std::free (volt);
  Destroy_CompCol_Matrix(&A);
  Destroy_SuperMatrix_Store(&B);
  Destroy_SuperMatrix_Store(&X);
  Destroy_SuperNode_Matrix(&L);
  Destroy_CompCol_Matrix(&U);
  StatFree(&stat);
};

void MNASimulation::Print_Result(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set,double* dp, std::string outputfile){
  // data format: x y voltage vdd/gnd
  // now only print lowest metal, and vdd
  //int target_metal_layer_index = 2;
  //int target_power_grid_index = 1;
  //dp the voltage solution
  std::ofstream pythonfile;
  pythonfile.open(outputfile);
  for(auto it = point_set.begin(); it != point_set.end(); it++){
          pythonfile<< it->x << " " << it->y << " " << it->metal_layer << " "<< dp[it->index - 1] << " " << it->power <<std::endl;
          /*
	  if(it->metal_layer == target_metal_layer_index && it->power != 0){
	    pythonfile<< it->x << " " << it->y << " " << it->metal_layer << " "<< dp[it->index - 1] << " " << it->power <<std::endl;
	  }
	  if(it->metal_layer == target_metal_layer_index && it->power == 0){
	    pythonfile<< it->x << " " << it->y << " " << it->metal_layer << " "<< dp[it->index - 1] << " " << it->power <<std::endl;
	  }
          */
  }
  pythonfile.close();
};

void MNASimulation::Print_Grid(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, std::vector<MDB::device> &temp_devices){

  std::ofstream pythonfile;
  pythonfile.open("gridresult.txt");
  for(unsigned int i=0;i<temp_devices.size();i++){
    if(temp_devices[i].device_type==0){
  	  int first = temp_devices[i].start_point_index;
	    int second = temp_devices[i].end_point_index;
	    for(auto it = point_set.begin(); it != point_set.end(); it++){
		    if(it->index == first)
		      pythonfile<< it->x << " " << it->y << " " << it->metal_layer << " " << it->power << " ";
  	  }
	    for(auto it = point_set.begin(); it != point_set.end(); it++){
		    if(it->index == second)
		     pythonfile<< it->x << " " << it->y << " " << it->metal_layer << " " << it->power <<std::endl;
  	  }
    }
  }
  pythonfile.close();
};

void MNASimulation::Print_EM(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, std::vector<MDB::device> &temp_devices, int size, double* dp, std::string outputem){

  auto logger = spdlog::default_logger()->clone("MNA.MNASimulation.Print_EM");

  std::ofstream pythonfile;
  pythonfile.open(outputem);
  //int size = dp.size(); 
  std::vector<double> em(size,0);
  for(unsigned int i=0;i<temp_devices.size();i++){
    if(temp_devices[i].device_type==0){
       int first = temp_devices[i].start_point_index;
       int second = temp_devices[i].end_point_index;
       //double resistance = temp_devices[i].value;
       //int x1,x2,y1,y2,
       //int layer1,layer2,
       int index1,index2;
       //int flag = 0;
       double v1,v2;
       for(auto it = point_set.begin(); it != point_set.end(); it++){
          if(it->index == first){
             //x1 = it->x;
             //y1 = it->y;
             //layer1 = it->metal_layer;
             index1 = it->index - 1;
             v1 = dp[it->index - 1];		
             }
          if(it->index == second){
             //x2 = it->x;
             //y2 = it->y;
             //layer2 = it->metal_layer;
             index2 = it->index - 1;
             v2 = dp[it->index - 1];		
             }
          // pythonfile<< it->x << " " << it->y << " " << it->metal_layer << " " << it->power << " ";
        }
      //Q: dp is voltage, while em should be current-related?  
      //int layer = layer1;
      //if (layer2 < layer1) layer = layer2;
      double diff = abs(v1-v2);
      if (diff > em[index1]){
        em[index1]=diff;
      }	
      if (diff > em[index2]){
        em[index2]=diff;
      }
    }
  }
  int target_metal_layer_index = 2;
  //int target_power_grid_index = 1;
  logger->debug("finish em");
  for(auto it = point_set.begin(); it != point_set.end(); it++){
    if(it->metal_layer == target_metal_layer_index && it->power !=0){
      pythonfile<< it->x << " " << it->y << " " << it->metal_layer << " "<< em[it->index - 1] << " " << it->power <<std::endl;
      }
  }
  pythonfile.close();
};

void MNASimulation::Print_Devices(std::vector<MDB::device> &temp_devices){

  auto logger = spdlog::default_logger()->clone("MNA.MNASimulation.Print_Devices");

  for(unsigned int i=0;i<temp_devices.size();i++){
    logger->debug("devices type {0} point1 {1} point2 {2} {3} ",temp_devices[i].device_type,temp_devices[i].start_point_index,temp_devices[i].end_point_index, temp_devices[i].value);
  }
};

void MNASimulation::Clear_Power_Grid(PnRDB::PowerGrid &temp_grid){
  temp_grid.metals.clear();
  temp_grid.vias.clear();
  temp_grid.power=1;
};

int MNASimulation::nodenum(std::vector<MDB::device> &temp_devices){
  int num = 0;
  for(unsigned int i=0;i<temp_devices.size();i++){
     //if (temp_devices[i].device_type == 0){
     int start = temp_devices[i].start_point_index;
     int end = temp_devices[i].end_point_index;
     if (num < start) num = start;
     if (num < end) num = end;//}
     }
  return num;
}

int MNASimulation::MapX(std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, int match){
  int x;
  for(auto it = temp_set.begin(); it != temp_set.end(); ++it){
    //std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
	  //std::cout<<it->x<<"\t"<<it->y<<"\t"<<it->index<<"\t"<<it->metal_layer<<std::endl;
    if (it -> index == match){
	    x = it->x;
	    //y = it->y;
    }
  }
  return x;
}

int MNASimulation::MaxX(std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, int layer){
  int max=0;
  for(auto it = temp_set.begin(); it != temp_set.end(); ++it){
    if(it->metal_layer == layer){
       //std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
       //std::cout<<it->x<<"\t"<<it->y<<"\t"<<it->index<<"\t"<<it->metal_layer<<std::endl;
       if(it->x > max){
          max = it->x;
         }
    }
  }   
  return max;
}

int MNASimulation::MapY(std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, int match){
  int y;
  for(auto it = temp_set.begin(); it != temp_set.end(); ++it){
     //std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
     //std::cout<<it->x<<"\t"<<it->y<<"\t"<<it->index<<"\t"<<it->metal_layer<<std::endl;
     if(it -> index == match){
        //x = it->x;
        y = it->y;
       }
     }
  return y;
}

int MNASimulation::MaxY(std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, int layer){
  int max=0;
  for(auto it = temp_set.begin(); it != temp_set.end(); ++it){
     if(it->metal_layer == layer){
     //std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
     //std::cout<<it->x<<"\t"<<it->y<<"\t"<<it->index<<"\t"<<it->metal_layer<<std::endl;
     if (it->y > max){
        max = it->y;
        }
     }
  }     
  return max;
}

int MNASimulation::MapPoint(std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set1, int x, int y, int layer){
	// return a index, which match x, y, layer best
  int match;
	int diffx = INT_MAX, diffy = INT_MAX;
	int bestx = 0, besty = 0;

  for(auto it = temp_set1.begin(); it != temp_set1.end(); ++it){
    if(it->metal_layer == layer){
	    int tempx, tempy;
	    tempx = it->x - x;
	    if (tempx < 0) tempx = -1*tempx;
	    tempy = it->y - y;
	    if (tempy < 0) tempy = -1*tempy;
      if (tempx < diffx){
		    diffx = tempx;
		    bestx = it->x;
   	  }
      if (tempy < diffy){
		    diffy = tempy;
		    besty = it->y;
  	  }
    }
  }

  for(auto it = temp_set1.begin(); it != temp_set1.end(); ++it){
    if (it -> x == bestx && it ->y == besty && it->metal_layer==layer){
      //Q: need it->metal_layer==layer?
	    match = it->index;
	  }
  }
  return match;
};

void MNASimulation::AddingI(std::vector<MDB::metal_point> &I_point_v, std::vector<MDB::metal_point> &I_point_g, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, std::vector<MDB::device> &Power_Grid_devices, double current){

   auto logger = spdlog::default_logger()->clone("MNA.MNASimulation.AddingI");

   for(unsigned int i=0;i<I_point_v.size();++i){
       MDB::device temp_device;
       auto first_point = temp_set.find(I_point_v[i]);
       int start_index = first_point->index;
       logger->debug("First Point (x,y) index metal {0} {1} {2} {3}",first_point->x,first_point->y,start_index,first_point->metal_layer);
       auto second_point = temp_set.find(I_point_g[i]);
       int end_index = second_point->index;
       logger->debug("Second Point (x,y) index metal {0} {1} {2} {3} ",second_point->x,second_point->y,end_index,second_point->metal_layer);
       temp_device.device_type = MDB::I;
       temp_device.start_point_index = start_index;
       temp_device.end_point_index = end_index;  
       temp_device.value = current;
       Power_Grid_devices.push_back(temp_device);
     }

};

void MNASimulation::AddingPower(std::vector<MDB::metal_point> &power_points, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, std::vector<MDB::device> &Power_Grid_devices, double power){

   int end_index = -1;
   for(unsigned int i=0;i<power_points.size();++i){
       MDB::device temp_device;
       auto first_point = temp_set.find(power_points[i]);
       int start_index = first_point->index;
       temp_device.start_point.x = first_point->x;
       temp_device.start_point.y = first_point->y;
       temp_device.start_point.metal_layer = first_point->metal_layer;
       temp_device.start_point.power = first_point->power;
       //std::cout<<"First Point (x,y) index metal "<<first_point->x<<" "<<first_point->y<<" "<<start_index<<" "<<first_point->metal_layer<<std::endl;
       //  std::cout<<"Second Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<end_index<<" "<<temp_point.metal_layer<<std::endl;
       temp_device.device_type = MDB::V;
       temp_device.start_point_index = start_index;
       temp_device.end_point_index = end_index;  
       temp_device.value = power;
       Power_Grid_devices.push_back(temp_device);
       end_index--;
     }
};

void MNASimulation::ExtractPowerGridPoint(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, int &highest_metal, int &lowest_metal, double power){
  MDB::metal_point temp_point; 
  for(unsigned int i=0;i<temp_grid.metals.size();++i){
     temp_point.metal_layer = temp_grid.metals[i].MetalIdx;
     if(temp_point.metal_layer<lowest_metal){
       lowest_metal = temp_point.metal_layer;
     }
     if(temp_point.metal_layer>highest_metal){
       highest_metal = temp_point.metal_layer;
     }
     temp_point.index = -1;
     temp_point.power = power;
     temp_point.x = temp_grid.metals[i].LinePoint[0].x;
     temp_point.y = temp_grid.metals[i].LinePoint[0].y;
     temp_set.insert(temp_point);
     temp_point.power = power;
     temp_point.x = temp_grid.metals[i].LinePoint[1].x;
     temp_point.y = temp_grid.metals[i].LinePoint[1].y;
     temp_set.insert(temp_point);
  }
};

void MNASimulation::ExtractPowerGridWireR(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices, double power){

   for(unsigned int i=0;i<temp_grid.metals.size();++i){
       MDB::device temp_device;
       MDB::metal_point temp_point; 
       
       if(temp_grid.metals[i].LinePoint[0].x != temp_grid.metals[i].LinePoint[1].x || temp_grid.metals[i].LinePoint[0].y != temp_grid.metals[i].LinePoint[1].y){
          temp_point.metal_layer = temp_grid.metals[i].MetalIdx;
          temp_point.index = -1;
          temp_point.power = power;
          temp_point.x = temp_grid.metals[i].LinePoint[0].x;
          temp_point.y = temp_grid.metals[i].LinePoint[0].y;
          auto frist_point = temp_set.find(temp_point);
          int start_index = frist_point->index;
          temp_device.start_point = temp_point;
          // std::cout<<"First Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<start_index<<" "<<temp_point.metal_layer<<std::endl;
          //temp_device.metal_layer1 = temp_point.metal_layer;
          temp_point.metal_layer = temp_grid.metals[i].MetalIdx;
          temp_point.index = -1;
	        temp_point.power = power;
          temp_point.x = temp_grid.metals[i].LinePoint[1].x;
          temp_point.y = temp_grid.metals[i].LinePoint[1].y;
          auto second_point = temp_set.find(temp_point);
          int end_index = second_point->index;
          temp_device.end_point = temp_point;
          //std::cout<<"Second Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<end_index<<" "<<temp_point.metal_layer<<std::endl;
          temp_device.device_type = MDB::R;
          temp_device.start_point_index = start_index;
          temp_device.end_point_index = end_index;
          //temp_device.metal_layer = temp_point.metal_layer;
          int metal_index = temp_grid.metals[i].MetalIdx;
          int metal_width = temp_grid.metals[i].width;
          int single_width = drc_info.Metal_info[metal_index].width;
          double unit_R = drc_info.Metal_info[metal_index].unit_R;
          double times = (double) metal_width / (double) single_width;
          //std::cout<<"unit_R "<<unit_R<<" "<<drc_info.Metal_info[metal_index].unit_R<<std::endl;
          temp_device.value = ((double) abs(frist_point->x-second_point->x) + (double) abs(frist_point->y-second_point->y))*unit_R/times;
          //temp_device.value = temp_device.value / 10.0;
          Power_Grid_devices.push_back(temp_device);
        } 
     }
};

void MNASimulation::ExtractPowerGridViaR(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices, double power, std::vector<int> vianumber){
   //Q value number is a fixed number? now seems is fixed in the pdk json?
   for(unsigned int i=0;i<temp_grid.vias.size();++i){
       MDB::device temp_device;
       MDB::metal_point temp_point;
       int model_index = temp_grid.vias[i].model_index;
       int x = temp_grid.vias[i].placedpos.x;
       int y = temp_grid.vias[i].placedpos.y;	   
       temp_point.metal_layer = drc_info.Via_model[model_index].LowerIdx;
       temp_point.index = -1;
	     temp_point.power = power;
       temp_point.x = x;
       temp_point.y = y;
	     //std::cout << "layer1= "<< temp_point.metal_layer <<" index1= "<<temp_point.index <<" power1= "<< temp_point.power << " x1= "<< temp_point.x <<" y1= "<< temp_point.y << std::endl;
	     if(temp_set.find(temp_point)==temp_set.end()){continue;}
       auto frist_point = temp_set.find(temp_point);
       int start_index = frist_point->index;
       temp_device.start_point = temp_point;
	     //temp_device.metal_layer1 = temp_point.metal_layer;       
       temp_point.metal_layer = drc_info.Via_model[model_index].UpperIdx;
       temp_point.index = -1;
	     temp_point.power = power;
       temp_point.x = x;
       temp_point.y = y;
	     //std::cout << "layer2= "<< temp_point.metal_layer << " index2= "<<temp_point.index <<" power2= "<< temp_point.power << " x2= "<< temp_point.x <<" y2= "<< temp_point.y << std::endl;
	     if(temp_set.find(temp_point)==temp_set.end()){continue;}
       auto second_point = temp_set.find(temp_point);
       int end_index = second_point->index;
       temp_device.end_point = temp_point;
       temp_device.device_type = MDB::R;
       temp_device.start_point_index = start_index;
       temp_device.end_point_index = end_index;
	     //temp_device.metal_layer2 = temp_point.metal_layer;
	     //temp_device.value = drc_info.Via_model[model_index].R/4.0;
	     //int number = rand() % vianumber[drc_info.Via_model[model_index].LowerIdx] + 1;
	     double number = vianumber[drc_info.Via_model[model_index].LowerIdx];
       temp_device.value = drc_info.Via_model[model_index].R / number ;
	     // temp_device.value = 1;  
       Power_Grid_devices.push_back(temp_device);
     }
};

void MNASimulation::FindPowerPoints(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, double power, int metal_layer, int power_number, std::vector<MDB::metal_point> &power_points){
  //need to change this code, this code is meaningless
  std::set<MDB::metal_point, MDB::Compare_metal_point> power_point_set;
  std::vector<MDB::metal_point> prime_power_points;
  std::set<int> x_set;
  std::set<int> y_set;
  std::vector<int> x_v;
  std::vector<int> y_v;
  MDB::metal_point temp_point;
  temp_point.metal_layer = metal_layer;
  temp_point.power = power;
  //std::cout<<"size of point set"<< point_set.size() <<std::endl;
  for(auto it = point_set.begin(); it != point_set.end(); ++it){
  //std::cout<<"metal layer = " << metal_layer <<" it layer = "<< it->metal_layer <<" power = "<<power << " it power = "<< it->power << std::endl;
       if(it->metal_layer == metal_layer && it->power == power){
         power_point_set.insert(*it);
         x_set.insert(it->x);
         y_set.insert(it->y);
       }
  }
  //std::cout <<"size of x_set= " << x_set.size()<<std::endl;
  //std::cout <<"size of y_set= " << y_set.size()<<std::endl;
  for(auto it = x_set.begin(); it != x_set.end(); ++it){
     x_v.push_back(*it);
  }
  //std::cout <<"size of x_v= " << x_v.size()<<std::endl;
  for(auto it = y_set.begin(); it != y_set.end(); ++it){
     y_v.push_back(*it);
  }
  //std::cout <<"size of y_v= " << y_v.size()<<std::endl;
  //need revise
  int x_number = sqrt(power_number);
  int y_number = sqrt(power_number);
  int xsize, ysize;
	xsize = int(x_v.size());
	ysize = int(y_v.size());
  //if (x_v.size()%x_number == 0) x
	int xstep = ceil((double) x_v.size()/x_number);
	int ystep = ceil((double) y_v.size()/y_number);
	int xstep_s = xstep/2;
	int ystep_s = ystep/2;
	if(ysize<=3) ystep = 1;
	if(xsize<=3) xstep = 1;

  for(unsigned int i =xstep_s;i<x_v.size();i=i+xstep){
     for(unsigned int j =ystep_s;j<y_v.size();j=j+ystep){
        temp_point.x = x_v[i];
        temp_point.y = y_v[j];
        power_points.push_back(temp_point);
	      //std::cout<<"i="<<i<<"j="<<j<<std::endl;
      }
  }
  //std::cout<<"in find power point size = " << power_points.size()<<std::endl;
};

void MNASimulation::FindPowerPoints_New(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, double power, int metal_layer, int power_number, std::vector<MDB::metal_point> &power_points){
  //need to change this code, this code is meaningless
  std::set<MDB::metal_point, MDB::Compare_metal_point> power_point_set;
  std::vector<MDB::metal_point> prime_power_points;
  std::set<int> x_set;
  std::set<int> y_set;
  std::vector<int> x_v;
  std::vector<int> y_v;
  MDB::metal_point temp_point;
  temp_point.metal_layer = metal_layer;
  temp_point.power = power;
  //std::cout<<"size of point set"<< point_set.size() <<std::endl;
  for(auto it = point_set.begin(); it != point_set.end(); ++it){
  //std::cout<<"metal layer = " << metal_layer <<" it layer = "<< it->metal_layer <<" power = "<<power << " it power = "<< it->power << std::endl;
       if(it->metal_layer == metal_layer && it->power == power){
         power_point_set.insert(*it);
         x_set.insert(it->x);
         y_set.insert(it->y);
       }
  }
  //std::cout <<"size of x_set= " << x_set.size()<<std::endl;
  //std::cout <<"size of y_set= " << y_set.size()<<std::endl;
  for(auto it = x_set.begin(); it != x_set.end(); ++it){
     x_v.push_back(*it);
  }
  //std::cout <<"size of x_v= " << x_v.size()<<std::endl;
  for(auto it = y_set.begin(); it != y_set.end(); ++it){
     y_v.push_back(*it);
  }
  //std::cout <<"size of y_v= " << y_v.size()<<std::endl;
  //need revise
  int x_number = sqrt(power_number);
  int y_number = power_number/x_number;

  int xsize, ysize;
	xsize = int(x_v.size());
	ysize = int(y_v.size());

  double range_x = (double)(x_v[xsize-1]-x_v[0])/(x_number+1);
  double range_y = (double) (y_v[ysize-1]-y_v[0])/(y_number+1);

  vector<double> candidate_x;
  vector<double> candidate_y;

  //std::cout<<"x_number "<<x_number<<" "<<y_number<<std::endl;
  //std::cout<<"power mesh range "<<range_x<<" "<<range_y<<std::endl;

  for(int i=1;i<=x_number;i++){
     candidate_x.push_back((double)x_v[0]+i*range_x);
     //std::cout<<"candidate_x "<<(double)x_v[0]+i*range_x<<" ";
  }
  //std::cout<<std::endl;

  for(int i=1;i<=y_number;i++){
     candidate_y.push_back((double) y_v[0]+i*range_y);
     //std::cout<<"candidate_y "<<(double) y_v[0]+i*range_y<<" ";
  }
  //std::cout<<std::endl;

  for(unsigned int i =0;i<candidate_x.size();i++){
    for(unsigned int j=0;j<candidate_y.size();j++){
      temp_point.x = find_nearest(candidate_x[i],x_v);
      temp_point.y = find_nearest(candidate_y[j],y_v);
      power_points.push_back(temp_point);
      //std::cout<<"power points "<<temp_point.x<<" "<<temp_point.y<<std::endl;
    }
  }
};

int MNASimulation::find_nearest(double x, vector<int> &x_v){
    int index=0;
    double error=INT_MAX;
    for(unsigned int i=0;i<x_v.size();i++){
      if(abs( (double) x_v[i]-x)<error){
        error = abs((double) x_v[i]-x);
        index = i;
      }
    }
    return x_v[index];      
}

void MNASimulation::ExtractPowerGrid(PnRDB::PowerGrid &vdd, PnRDB::PowerGrid &gnd, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices, std::vector<int> &mark_point, std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, std::string inputfile){

   unsigned seed;
   seed = time(0);
   srand(seed);
   //Q: fixed via and via number?
   vector<int> vianumber;
   int temp_via_number = 4;
   for (unsigned int i = 0; i<drc_info.Via_info.size(); i++){
	   vianumber.push_back(temp_via_number);
   }

   std::ifstream in("Power_Grid_Conf.txt");
   std::string line;
   getline(in, line);
   getline(in, line);
   std::stringstream ss(line);
   std::string tmp;
   std::vector<double> v;
   while (getline(ss, tmp, ' ')){
	   v.push_back(stod(tmp));//stod: string->double
   }
   //std::cout<<"v number "<<v.size()<<" vianumber size "<<vianumber.size()<<std::endl;
   //assert(0);
   for(unsigned int i=0;i<v.size();i++){
     vianumber[i]=v[i];
   }

   int highest_metal = INT_MIN;
   int lowest_metal = INT_MAX;
   double VDD = 0.8;

   ExtractPowerGridPoint(vdd, point_set, highest_metal, lowest_metal, VDD);
   ExtractPowerGridPoint(gnd, point_set, highest_metal, lowest_metal, 0.0);

   int refresh_index = 1;
   //std::cout<<"Gnd Point Set"<<std::endl;
   for(auto it = point_set.begin(); it != point_set.end(); ++it){
       it->index = refresh_index;
	     if(it->metal_layer == lowest_metal || it->metal_layer == lowest_metal + 1){
	       mark_point.push_back(refresh_index);
	    }
   //std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
      //std::cout<<it->x<<"\t"<<it->y<<"\t"<<it->index<<"\t"<<it->metal_layer<<std::endl;
      refresh_index = refresh_index + 1;
    }

   refresh_index = 1;
  
   ExtractPowerGridWireR(vdd, point_set, drc_info, Power_Grid_devices,VDD);
   ExtractPowerGridWireR(gnd, point_set, drc_info, Power_Grid_devices,0.0);

   ExtractPowerGridViaR(vdd, point_set, drc_info, Power_Grid_devices,VDD,vianumber);
   ExtractPowerGridViaR(gnd, point_set, drc_info, Power_Grid_devices,0.0,vianumber);

   std::vector<MDB::metal_point> vdd_points;
   std::vector<MDB::metal_point> gnd_points;
   std::vector<MDB::metal_point> I_points_v;
   std::vector<MDB::metal_point> I_points_g;

   int power_number = 9;
   //int current_number = 1;
   FindPowerPoints(point_set, VDD, highest_metal, power_number, vdd_points);
   FindPowerPoints(point_set, 0.0, highest_metal, power_number, gnd_points);
   //what if I_points_v!=I_points_g
   //what if I_points_g.size()<4?
   //need revise this part
   //FindPowerPoints_New(point_set, VDD, lowest_metal, current_number, I_points_v);
   //FindPowerPoints_New(point_set, 0.0, lowest_metal, current_number, I_points_g);

   //here some function to calculate vdd_points, gnd_points, I_points_v and I_points_g;
   //std::cout<< "vdd points "<< vdd_points.size()<<" gnd points "<< gnd_points.size() << " I point v "<< I_points_v.size() << " I point g"<< I_points_g.size()<< std::endl;
   AddingPower(vdd_points, point_set, Power_Grid_devices, VDD);
   AddingPower(gnd_points, point_set, Power_Grid_devices, 0.0);
   //double current = 0.001;
   std::vector<std::vector<double>> currentstore;
   ReadCurrent(currentstore,inputfile);
   Map_new(currentstore,point_set,Power_Grid_devices,lowest_metal);

 };

void MNASimulation::ReadCurrent(std::vector<std::vector<double>> &currentstore, std::string inputfile){
  std::ifstream in(inputfile);
  //std::ifstream inputfile;
  //inputfile.open("InputCurrent.txt");
  std::string line;
  //vector<vector<double>> vv;
  while (getline(in, line)){
    std::stringstream ss(line);
    std::string tmp;
    std::vector<double> v;
    while (getline(ss, tmp, ' ')){
      v.push_back(stod(tmp));//stod: string->double
    }
    currentstore.push_back(v);
  }
};


void MNASimulation::Map(std::vector<std::vector<double>> &currentstore, std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, std::vector<MDB::device> &Power_Grid_devices, int metal_layer){

  // it is adding some current devices 
  for(unsigned int i=0;i<currentstore.size();++i){
	  double startx,starty,endx,endy,value;
          MDB::metal_point start_metal_point;
          MDB::metal_point end_metal_point;
          double initial_x, initial_y;

          initial_x = currentstore[i][0];
	  initial_y = currentstore[i][1];

	  startx = currentstore[i][0];
	  starty = currentstore[i][1];
	  endx = currentstore[i][2];
	  endy = currentstore[i][3];
	  value = currentstore[i][4];
	  int start_index,end_index;
	  double vdd_maxx,vdd_maxy,gnd_maxx,gnd_maxy;


	  for(auto it = point_set.end(); it != point_set.begin(); it--){
	    if (it->metal_layer == metal_layer && it->power != 0){
		    vdd_maxx = it->x;
		    vdd_maxy = it->y;
		    break;
	    }
	  }
	  for(auto it = point_set.end(); it != point_set.begin(); it--){
	    if (it->metal_layer == metal_layer && it->power == 0){
		    gnd_maxx = it->x;
		    gnd_maxy = it->y;
		    break;
	   	}
	  }

	  //maxx = flag->x;
	  //maxy = flag->y;
	  if(startx > vdd_maxx) startx = vdd_maxx;
	  if(starty > vdd_maxy) starty = vdd_maxy;
	  if(endx > gnd_maxx) endx = gnd_maxx;
	  if(endy > gnd_maxy) endy = gnd_maxy;
	
    for(auto it = point_set.begin(); it != point_set.end(); ++it){
	    if (it->x >= startx && it->y >= starty && it->metal_layer == metal_layer && it->power != 0){
		    start_index = it->index;
                    start_metal_point.x = it->x;
                    start_metal_point.y = it->y;
                    start_metal_point.metal_layer = it->metal_layer;
                    start_metal_point.power = it->power;
		    break;
		  }
	  }
    for(auto it = point_set.begin(); it != point_set.end(); ++it){
	     if (it->x >= endx && it->y >= endy && it->metal_layer == metal_layer && it->power == 0){
		    end_index = it->index;
                    end_metal_point.x = it->x;
                    end_metal_point.y = it->y;
                    end_metal_point.metal_layer = it->metal_layer;
                    end_metal_point.power = it->power;
		     break;
	 	    }
	  }

    int max_index = 0;

    for(auto it = point_set.begin(); it != point_set.end(); ++it){
         if (it->index > max_index){
              max_index = it->index;
            }
    }

    //add new nodes
    int multi_connection = 3;
    MDB::metal_point source_temp_point;
    source_temp_point.x = initial_x;
    source_temp_point.y = initial_y;
    source_temp_point.power = 0.8;
    source_temp_point.metal_layer = -1;
    source_temp_point.index = max_index +1;

    if(point_set.find(source_temp_point)!=point_set.end()){
      continue;
    }

    MDB::device temp_device;
    temp_device.start_point = start_metal_point;
    temp_device.end_point = source_temp_point; 
    temp_device.device_type = MDB::R;
    temp_device.start_point_index = start_index;
    temp_device.end_point_index = max_index +1;
    double unit_r = this->Drc_info.Metal_info[metal_layer].unit_R;
    temp_device.value = (abs(initial_x-startx)+abs(initial_y-starty))/multi_connection*unit_r;
    //std::cout<<"power mesh multi-connection "<<initial_x<<" "<<initial_y<<" "<<startx<<" "<<starty<<" "<<multi_connection<<" "<<unit_r<<" "<<temp_device.value<<std::endl;
    Power_Grid_devices.push_back(temp_device);
    
    MDB::metal_point end_temp_point;
    end_temp_point.x = initial_x;
    end_temp_point.y = initial_y;
    end_temp_point.power = 0.0;
    end_temp_point.metal_layer = -2;
    end_temp_point.index = max_index +2;

    point_set.insert(source_temp_point);
    point_set.insert(end_temp_point);

    temp_device.start_point = end_temp_point;
    temp_device.end_point = end_metal_point; 
    temp_device.device_type = MDB::R;
    temp_device.start_point_index = max_index +2;
    temp_device.end_point_index = end_index;  
    temp_device.value = (abs(initial_x-endx)+abs(initial_y-endy))/multi_connection*unit_r;
    //std::cout<<"power mesh multi-connection "<<initial_x<<" "<<initial_y<<" "<<endx<<" "<<endy<<" "<<multi_connection<<" "<<unit_r<<" "<<temp_device.value<<std::endl;
    Power_Grid_devices.push_back(temp_device);

    temp_device.device_type = MDB::I;
    temp_device.start_point = source_temp_point;
    temp_device.end_point = end_temp_point;     
    temp_device.start_point_index = max_index +1;
    temp_device.end_point_index = max_index +2;  
    temp_device.value = value;
    Power_Grid_devices.push_back(temp_device);
  }
};

void MNASimulation::Map_old(std::vector<std::vector<double>> &currentstore, std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, std::vector<MDB::device> &Power_Grid_devices, int metal_layer){

  // it is adding some current devices 
  for(unsigned int i=0;i<currentstore.size();++i){
	  double startx,starty,endx,endy,value;
	
	  startx = currentstore[i][0];
	  starty = currentstore[i][1];
	  endx = currentstore[i][2];
	  endy = currentstore[i][3];
	  value = currentstore[i][4];
	  int start_index,end_index;
	  double vdd_maxx,vdd_maxy,gnd_maxx,gnd_maxy;
	  for(auto it = point_set.end(); it != point_set.begin(); it--){
	    if (it->metal_layer == metal_layer && it->power != 0){
		    vdd_maxx = it->x;
		    vdd_maxy = it->y;
		    break;
	    }
	  }
	  for(auto it = point_set.end(); it != point_set.begin(); it--){
	    if (it->metal_layer == metal_layer && it->power == 0){
		    gnd_maxx = it->x;
		    gnd_maxy = it->y;
		    break;
	   	}
	  }
	  //maxx = flag->x;
	  //maxy = flag->y;
	  if(startx > vdd_maxx) startx = vdd_maxx;
	  if(starty > vdd_maxy) starty = vdd_maxy;
	  if(endx > gnd_maxx) endx = gnd_maxx;
	  if(endy > gnd_maxy) endy = gnd_maxy;
	
    for(auto it = point_set.begin(); it != point_set.end(); ++it){
	    if (it->x >= startx && it->y >= starty && it->metal_layer == metal_layer && it->power != 0){
		    start_index = it->index;
		    break;
		  }
	  }
  	for(auto it = point_set.begin(); it != point_set.end(); ++it){
	     if (it->x >= endx && it->y >= endy && it->metal_layer == metal_layer && it->power == 0){
		     end_index = it->index;
		     break;
	 	    }
	  }
	  MDB::device temp_device;
	  temp_device.device_type = MDB::I;
    temp_device.start_point_index = start_index;
    temp_device.end_point_index = end_index;  
    temp_device.value = value;
    Power_Grid_devices.push_back(temp_device);
  }
};

void MNASimulation::Map_new(std::vector<std::vector<double>> &currentstore, std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, std::vector<MDB::device> &Power_Grid_devices, int metal_layer){

  // it is adding some current devices 
  for(unsigned int i=0;i<currentstore.size();++i){
	  //double startx,starty,endx,endy,
    double value;
          MDB::metal_point start_metal_point;
          MDB::metal_point end_metal_point;
          double initial_x, initial_y;

          initial_x = currentstore[i][0];
	  initial_y = currentstore[i][1];

	  //startx = currentstore[i][0];
	  //starty = currentstore[i][1];
	  //endx = currentstore[i][2];
	  //endy = currentstore[i][3];
	  value = currentstore[i][4];
	  int start_index,end_index;
	  double vdd_maxx,vdd_maxy,gnd_maxx,gnd_maxy;

          int diff = INT_MAX;

	  for(auto it = point_set.end(); it != point_set.begin(); it--){
	    if (it->metal_layer == metal_layer && it->power != 0){
                    int temp_diff = abs(it->x-initial_x)+abs(it->y-initial_y);
                    if(temp_diff<diff){
		      vdd_maxx = it->x;
		      vdd_maxy = it->y;
                      diff = temp_diff;
                    }
	    }
	  }

          diff = INT_MAX;
	  for(auto it = point_set.end(); it != point_set.begin(); it--){
	    if (it->metal_layer == metal_layer && it->power == 0){
                    int temp_diff = abs(it->x-initial_x)+abs(it->y-initial_y);
                    if(temp_diff<diff){
		      gnd_maxx = it->x;
		      gnd_maxy = it->y;
                      diff = temp_diff;
                    }
	    }
	  }
	
    for(auto it = point_set.begin(); it != point_set.end(); ++it){
	    if (it->x >= vdd_maxx && it->y >= vdd_maxy && it->metal_layer == metal_layer && it->power != 0){
		    start_index = it->index;
                    start_metal_point.x = it->x;
                    start_metal_point.y = it->y;
                    start_metal_point.metal_layer = it->metal_layer;
                    start_metal_point.power = it->power;
		    break;
		  }
	  }
    for(auto it = point_set.begin(); it != point_set.end(); ++it){
	     if (it->x >= gnd_maxx && it->y >= gnd_maxx && it->metal_layer == metal_layer && it->power == 0){
		    end_index = it->index;
                    end_metal_point.x = it->x;
                    end_metal_point.y = it->y;
                    end_metal_point.metal_layer = it->metal_layer;
                    end_metal_point.power = it->power;
		     break;
	 	    }
	  }

    int max_index = 0;

    for(auto it = point_set.begin(); it != point_set.end(); ++it){
         if (it->index > max_index){
              max_index = it->index;
            }
    }

    //add new nodes
    int multi_connection = 1;
    MDB::metal_point source_temp_point;
    source_temp_point.x = initial_x;
    source_temp_point.y = initial_y;
    source_temp_point.power = 0.8;
    source_temp_point.metal_layer = -1;
    source_temp_point.index = max_index +1;

    if(point_set.find(source_temp_point)!=point_set.end()){
      continue;
    }

    MDB::device temp_device;
    temp_device.start_point = start_metal_point;
    temp_device.end_point = source_temp_point; 
    temp_device.device_type = MDB::R;
    temp_device.start_point_index = start_index;
    temp_device.end_point_index = max_index +1;
    double unit_r = this->Drc_info.Metal_info[metal_layer].unit_R;
    temp_device.value = (abs(initial_x-vdd_maxx)+abs(initial_y-vdd_maxy))/multi_connection*unit_r+2*25/multi_connection;
    //std::cout<<"power mesh multi-connection "<<initial_x<<" "<<initial_y<<" "<<vdd_maxx<<" "<<vdd_maxy<<" "<<multi_connection<<" "<<unit_r<<" "<<temp_device.value<<std::endl;
    Power_Grid_devices.push_back(temp_device);
    
    MDB::metal_point end_temp_point;
    end_temp_point.x = initial_x;
    end_temp_point.y = initial_y;
    end_temp_point.power = 0.0;
    end_temp_point.metal_layer = -2;
    end_temp_point.index = max_index +2;

    point_set.insert(source_temp_point);
    point_set.insert(end_temp_point);

    temp_device.start_point = end_temp_point;
    temp_device.end_point = end_metal_point; 
    temp_device.device_type = MDB::R;
    temp_device.start_point_index = max_index +2;
    temp_device.end_point_index = end_index;  
    temp_device.value = (abs(initial_x-gnd_maxx)+abs(initial_y-gnd_maxy))/multi_connection*unit_r+2*25/multi_connection;
    //std::cout<<"power mesh multi-connection "<<initial_x<<" "<<initial_y<<" "<<gnd_maxx<<" "<<gnd_maxy<<" "<<multi_connection<<" "<<unit_r<<" "<<temp_device.value<<std::endl;
    Power_Grid_devices.push_back(temp_device);

    temp_device.device_type = MDB::I;
    temp_device.start_point = source_temp_point;
    temp_device.end_point = end_temp_point;     
    temp_device.start_point_index = max_index +1;
    temp_device.end_point_index = max_index +2;  
    temp_device.value = value;
    Power_Grid_devices.push_back(temp_device);
  }
};

