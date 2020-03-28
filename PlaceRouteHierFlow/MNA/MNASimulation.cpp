	#include "MNASimulation.h"
#include "/home/grads/x/xurishang/research/test/superlu/SuperLU_5.2.1/SRC/slu_ddefs.h"
//#include </home/grads/w/wbxu/share/opt/boost/numeric/ublas/operation.hpp>

MNASimulation::MNASimulation(PnRDB::hierNode &current_node, PnRDB::Drc_info &drc_info){
//MNASimulation::MNASimulation(boost_matrix &out_R, boost_matrix &out_I){

boost_matrix out_R, out_I; 
std::vector<std::vector<double> > Istore,Vstore,Rstore;
std::vector<int> mark_point;
this->R = out_R;
this->I = out_I;

//Test_superlu();

//ExtractPowerGrid(current_node.Vdd, current_node.Gnd, drc_info, Power_Grid_devices_Vdd, Power_Grid_devices_Gnd);
ExtractPowerGrid(current_node.Vdd, current_node.Gnd, drc_info, Power_Grid_devices, mark_point);
  
  std::set<MDB::metal_point, MDB::Compare_metal_point> vdd_point_set;
  std::set<MDB::metal_point, MDB::Compare_metal_point> gnd_point_set;

  //ExtractPowerGridPoint(current_node.Vdd, vdd_point_set);
  //ExtractPowerGridPoint(current_node.Gnd, gnd_point_set);
 // ExtractPowerGridPoint(vdd, vdd_point_set, highest_metal, lowest_metal, 1);
 // ExtractPowerGridPoint(gnd, gnd_point_set, highest_metal, lowest_metal, 0);
/*
MDB::device temp_device;
	temp_device.device_type = MDB::I;
       temp_device.start_point_index = 1;
       temp_device.end_point_index = 2;  
       temp_device.value = 2;
       Power_Grid_devices.push_back(temp_device);
	temp_device.device_type = MDB::V;
       temp_device.start_point_index = 1;
       temp_device.end_point_index = -1;  
       temp_device.value = 1;
	Power_Grid_devices.push_back(temp_device);
	temp_device.device_type = MDB::V;
       temp_device.start_point_index = 2;
       temp_device.end_point_index = -1;  
       temp_device.value = 0;
       Power_Grid_devices.push_back(temp_device);
	temp_device.device_type = MDB::R;
       temp_device.start_point_index = 1;
       temp_device.end_point_index = 0;  
       temp_device.value = 1;
       Power_Grid_devices.push_back(temp_device);
	temp_device.device_type = MDB::R;
       temp_device.start_point_index = 1;
       temp_device.end_point_index = 2;  
       temp_device.value = 0.5;
       Power_Grid_devices.push_back(temp_device);
	temp_device.device_type = MDB::R;
       temp_device.start_point_index = 2;
       temp_device.end_point_index = 0;  
       temp_device.value = 0.25;
       Power_Grid_devices.push_back(temp_device);
*/

std::cout<<"Vdd Devices"<<std::endl;
Print_Devices(Power_Grid_devices);
/*std::cout<<"Gnd Devices"<<std::endl;
Print_Devices(Power_Grid_devices_Gnd);
*/

    SuperMatrix A, L, U, B;
    double   *a, *rhs;
    double   s, u, p, e, r, l;
    int      *asub, *xa;
    int      *perm_r; /* row permutations from partial pivoting */
    int      *perm_c; /* column permutation vector */
    int      nrhs, info, i, m, n, nnz, permc_spec;
    superlu_options_t options;
    SuperLUStat_t stat;


//Transfer(Power_Grid_devices_Gnd, Power_Grid_devices_Vdd, Rstore);
//Transfer(Power_Grid_devices, Power_Grid_devices, Rstore,Istore, Vstore);
/*
for (int i = 0; i < Rstore.size(); i++){
std::cout << "start "<< Rstore[i][0] <<" end " << Rstore[i][1]<< " value " << Rstore[i][2] << std::endl;
}

std::cout << "R store print end" << std::endl;

ConstructI(Istore,Vstore,Rstore);

ConstructR(Rstore,Vstore);
*/
/*
int Rsize = 0;
 for (int i = 0; i < Rstore.size(); i++){
 if (Rsize < Rstore[i][0])
	Rsize = Rstore[i][0];
 if (Rsize < Rstore[i][1])
	Rsize = Rstore[i][1];
}
*/

// result = SolveIR_drop(Rsize);

int node_num1 = nodenum(Power_Grid_devices);

int maxx,maxy;
int layer = 6;
maxx = MaxX(gnd_point_set,layer);
maxy = MaxY(gnd_point_set,layer);
std::cout << "maxx = "<< maxx <<" maxy= " << maxy << std::endl;
/*
double nn;
nn = 4.0;
for (double i =1.0 ; i < nn ; i++){
double temp = i / (nn-1.0);
int mark = temp * node_num1-1;
std::cout << "start "<< mark+node_num1 <<" end " << mark << " temp " << temp << std::endl;
Vstore.push_back(std::vector<double>{node_num1+mark,0,1});
}

Vstore.push_back(std::vector<double>{node_num1+1,0,1});*/
/*
double num_lowlayer = 0.0;



for(int j=0;j<node_num1;j++){
	for(int i=0;i<Power_Grid_devices_Gnd.size();i++){
		if ((Power_Grid_devices_Gnd[i].metal_layer1 == layer && Power_Grid_devices_Gnd[i].start_point_index == j) ||
			(Power_Grid_devices_Gnd[i].metal_layer2 == layer && Power_Grid_devices_Gnd[i].end_point_index == j)){
		num_lowlayer = num_lowlayer + 1.0;
		break;
		}
		
	}
}
std::cout << "numlowlayer= "<< num_lowlayer <<"total is "<< node_num1 << std::endl;
double current;
current = 0.024 / 4.0;
*/
//Istore.push_back(std::vector<double>{0,node_num1,current});
int powerdev = 0;
int currentdev = 0;
//int zeropower = 0;
for(int it=0;it<Power_Grid_devices.size();++it){
	if (Power_Grid_devices[it].device_type == MDB::V){
	powerdev++;
	}
	if (Power_Grid_devices[it].device_type == MDB::I){
	currentdev++;
	}
}
std::cout<<"power dev = " << powerdev << std::endl;
	nrhs = 1;
    m = node_num1 + powerdev;
    if ( !(rhs = doubleMalloc(m * nrhs)) ) ABORT("Malloc fails for rhs[].");
    for (i = 0; i < m; ++i) rhs[i] = 0.0;
//    for (i = m-8; i < m-4; ++i) rhs[i] = 1.0;
//    rhs[0] = current;

for (int i =0.0 ; i < node_num1; i++){
//int is_low = 0;

	//for(auto it = Power_Grid_devices.begin(); it != Power_Grid_devices.end(); ++it){
	for(int it=0;it<Power_Grid_devices.size();++it){
	if (Power_Grid_devices[it].device_type == MDB::I){
		int start = Power_Grid_devices[it].start_point_index-1;
		int end = Power_Grid_devices[it].end_point_index-1;
		double current = Power_Grid_devices[it].value;
		rhs[start] = -current;
		if (end >= 0)		
		rhs[end] = current;

		}
	
	if (Power_Grid_devices[it].device_type == MDB::V){
		int start = Power_Grid_devices[it].start_point_index-1;
		int end = Power_Grid_devices[it].end_point_index;
		//end = -1;
		double power = Power_Grid_devices[it].value;
			
		if (power > 0){
		rhs[node_num1 -1 - end] = power;
		}
		//if (power == 0){
		//rhs[node_num1 -1 + powerdev - end] = power;
		//zeropower++;
		//}
	
	
		//rhs[end] = -power;
//		powerdev++;
		}
	}

}

    dCreate_Dense_Matrix(&B, m, nrhs, rhs, m, SLU_DN, SLU_D, SLU_GE);
/*for (i = 0; i < m; ++i){
 std::cout<<"rhs[" << i << "]=" << rhs[i] <<std::endl;
} */ 
	
    dPrint_Dense_Matrix("B",&B);
    /* Initialize matrix A. */

int count = 0;
std::cout<<"count=" << count <<std::endl;
std::vector<std::vector<double>> store;

for (int i = 0; i < node_num1; i++){
	std::vector<double> temp(node_num1+powerdev,0);
	double self = 0.0;
		
	for (int j = 0; j<Power_Grid_devices.size(); ++j){
	if (Power_Grid_devices[j].device_type== 0 && Power_Grid_devices[j].start_point_index == i+1){
		int position = Power_Grid_devices[j].end_point_index-1;
		double value = Power_Grid_devices[j].value;
		double data = temp[position];
	        data = data - 1.0/value;
		self = self + 1.0/value;
		temp[position] = data;
		}
	if (Power_Grid_devices[j].device_type == 0 && Power_Grid_devices[j].end_point_index == i+1){
		int position = Power_Grid_devices[j].start_point_index-1;
		double value = Power_Grid_devices[j].value;
		double data = temp[position];
	        data = data - 1.0/value;
		self = self + 1.0/value;
		temp[position] = data;
		}
	if (Power_Grid_devices[j].device_type == 2 && Power_Grid_devices[j].start_point_index == i+1){
		double value = Power_Grid_devices[j].value;		
		int position = node_num1 -Power_Grid_devices[j].end_point_index - 0.5*powerdev*(value-1) - 1;
		temp[position] = 1.0;
		}
	}
	temp[i] = self;
	store.push_back(temp);

}

for (int i = 1; i <= powerdev; i++){
	std::vector<double> temp(node_num1+powerdev,0);
	for (int j = 0; j<Power_Grid_devices.size(); ++j){
		if (Power_Grid_devices[j].device_type == 2 && Power_Grid_devices[j].value == 1){
			int start = Power_Grid_devices[j].start_point_index-1;
			if (-Power_Grid_devices[j].end_point_index == i){
				temp[start] = 1.0;
			}
		}
		if (Power_Grid_devices[j].device_type == 2 && Power_Grid_devices[j].value == 0){
			int start = Power_Grid_devices[j].start_point_index-1;
			if (-Power_Grid_devices[j].end_point_index == i - 0.5 *powerdev){
				temp[start] = 1.0;
			}
		}
	}
	store.push_back(temp);
}

std::cout<<"size of store is"<< store.size()<<" row = " << store[0].size()<<std::endl;
/*
for (int i = 0; i < node_num1+powerdev; i++){
	for (int j = 0; j < node_num1+powerdev; j++){
		std::cout<<store[j][i]<< "\t" ;
	}
	std::cout<<std::endl;
}*/

count = 2 * (Power_Grid_devices.size()-currentdev) + node_num1;
//int powerdev = 0 ;

std::cout<<"count=" << count <<std::endl;
    m = n = node_num1 + powerdev;
    nnz = count;
 
    if ( !(a = doubleMalloc(nnz)) ) ABORT("Malloc fails for a[].");
std::cout<<"checkcheck"<<std::endl;
    if ( !(asub = intMalloc(nnz)) ) ABORT("Malloc fails for asub[].");
    if ( !(xa = intMalloc(n+1)) ) ABORT("Malloc fails for xa[].");
std::cout<<"count=" << count <<std::endl;
xa[n] = count;
count = 0;

for (int j = 0; j < node_num1+powerdev; j++)
{
	int flag = 0;
	for (int i =0; i < node_num1+powerdev; i++){
		double value = store[j][i];
		if (value != 0){
			if (flag == 0 ){
			xa[j] = count; //
			flag = 1;
			}			
			a[count] = value;
			asub[count] = i;
			count = count + 1;
			//std::cout<<"value!!"<<value <<std::endl;
		}

	}
	
}

/*
	for (int i = 0; i < count; i++){
 std::cout<<"a[" << i << "]=" << a[i] <<std::endl;
 std::cout<<"asub[" << i << "]=" << asub[i] <<std::endl;

}
	for (int j = 0; j <node_num1+powerdev; j++){
 std::cout<<"xa[" << j << "]=" << xa[j] <<std::endl;
}*/
    std::cout<<"check point1"<<std::endl;
/*   
 s = 19.0; u = 21.0; p = 16.0; e = 5.0; r = 18.0; l = 12.0;
    a[0] = s; a[1] = l; a[2] = l; a[3] = u; a[4] = l; a[5] = l;
    a[6] = u; a[7] = p; a[8] = u; a[9] = e; a[10]= u; a[11]= r;
    asub[0] = 0; asub[1] = 1; asub[2] = 4; asub[3] = 1;
    asub[4] = 2; asub[5] = 4; asub[6] = 0; asub[7] = 2;
    asub[8] = 0; asub[9] = 3; asub[10]= 3; asub[11]= 4;
    xa[0] = 0; xa[1] = 3; xa[2] = 6; xa[3] = 8; xa[4] = 10; xa[5] = 12;

    /* Create matrix A in the format expected by SuperLU. */
    dCreate_CompCol_Matrix(&A, m, n, nnz, a, asub, xa, SLU_NC, SLU_D, SLU_GE);
std::cout<<"check point2"<<std::endl;
  if (!(perm_r = intMalloc(m)))
    ABORT("Malloc fails for perm_r[].");
  if (!(perm_c = intMalloc(n)))
    ABORT("Malloc fails for perm_c[].")
  //dPrint_CompCol_Matrix("A",&A);
  set_default_options(&options);
std::cout<<"check point3"<<std::endl;
    options.ColPerm = NATURAL;
std::cout<<"check point4"<<std::endl;
    /* Initialize the statistics variables. */
    StatInit(&stat);
std::cout<<"check point5"<<std::endl;
    /* Solve the linear system. */
    dgssv(&options, &A, perm_c, perm_r, &L, &U, &B, &stat, &info);
  std::cout<<"check point6 info == "<< info <<std::endl;  
  
  dPrint_CompCol_Matrix("A", &A);
//    dPrint_CompCol_Matrix("U", &U);
//    dPrint_SuperNode_Matrix("L", &L);
//    print_int_vec("\nperm_r", m, perm_r);
std::cout<<"check point7"<<std::endl;  
dPrint_Dense_Matrix("B",&B);
std::cout<<"check point8"<<std::endl;
	/*Detect the result*/
  DNformat*    Bstore = (DNformat*) B.Store;
  register int k, j, lda = Bstore->lda;
  double*      dp;
  double*       volt;
  dp = (double*) Bstore->nzval;
  int vol_count = 0;
if (!(volt = doubleMalloc(n)))    ABORT("Malloc fails for volt[].")
std::cout<<"check point9"<<std::endl;  
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
std::cout<<"dp[" << k << "]=" << dp[k] <<std::endl;
}
/*	
for (int j = 0; j < n; j++){
 std::cout<<"volt[" << j << "]=" << volt[j] <<std::endl;
}*/
std::cout<<"check point10"<<std::endl;  
	double max = 1.0;
	
	for (int i = 0; i < B.nrow; i++){
		if (max > dp[i] && dp[i] > 0.5)
	max = dp[i];
	}
	max = 1 - max;
	result = max;
std::cout<<"result=" << result <<std::endl;

double markdrop = 1.0;
	for (int i = 0; i < mark_point.size(); i++){
		int ind = mark_point[i];
		if (markdrop > dp[ind] && dp[ind] > 0.5)
	markdrop = dp[ind];
	}
	markdrop = 1 - markdrop;
std::cout<<"mark drop =" << markdrop <<std::endl;

std::cout<<"check point11"<<std::endl;
    /* De-allocate storage */
    SUPERLU_FREE (rhs);
    SUPERLU_FREE (perm_r);
    SUPERLU_FREE (perm_c);
    //std::free (volt);
    Destroy_CompCol_Matrix(&A);
    Destroy_SuperMatrix_Store(&B);
    Destroy_SuperNode_Matrix(&L);
    Destroy_CompCol_Matrix(&U);
    StatFree(&stat);




//use for ppt
//result = node_num1;

//how to output result
//++

//result = 0.9;
};

void MNASimulation::Print_Devices(std::vector<MDB::device> &temp_devices){

  for(int i=0;i<temp_devices.size();i++){

     std::cout<<"devices type "<<temp_devices[i].device_type<<" point 1 "<<temp_devices[i].start_point_index<<" point 2 "<<temp_devices[i].end_point_index<<" value "<< temp_devices[i].value <<std::endl;

  }

};

void MNASimulation::Clear_Power_Grid(PnRDB::PowerGrid &temp_grid){

  temp_grid.metals.clear();
  temp_grid.vias.clear();
  temp_grid.power=1;


};

int MNASimulation::nodenum(std::vector<MDB::device> &temp_devices){
	int num = 0;
	for(int i=0;i<temp_devices.size();i++){
		//if (temp_devices[i].device_type == 0){
		int start = temp_devices[i].start_point_index;
		int end = temp_devices[i].end_point_index;
		if (num < start) num = start;
		if (num < end) num = end;
		//}
	}
	return num;
}

void MNASimulation::Transfer(std::vector<MDB::device> &temp_devices, std::vector<MDB::device> &temp2_devices, std::vector<std::vector<double> > &Rstore, std::vector<std::vector<double> > &Istore, std::vector<std::vector<double> > &Vstore){
	int start,end,flag;
	flag = 0;
	double value;
	std::vector<std::vector<double> > store;
	// std::vector<double> temp;
	for(int i=0;i<temp_devices.size();i++){
		if (temp_devices[i].device_type == 0){
		start = temp_devices[i].start_point_index;
		end = temp_devices[i].end_point_index;
		value = temp_devices[i].value;
		store.push_back(std::vector<double>{start,end,value});
		if (flag < start) flag = start;
		if (flag < end) flag = end;
		}
	}
	flag++;


	Rstore = store;
	store.clear();
	for(int i=0;i<temp_devices.size();i++){
		if (temp_devices[i].device_type == 1){
		start = temp_devices[i].start_point_index;
		end = temp_devices[i].end_point_index;
		value = temp_devices[i].value;
		store.push_back(std::vector<double>{start,end,value});
		if (flag < start) flag = start;
		if (flag < end) flag = end;
		}
	}
	Istore = store;
	store.clear();
	
	for(int i=0;i<temp_devices.size();i++){
		if (temp_devices[i].device_type == 2){
		start = temp_devices[i].start_point_index;
		end = temp_devices[i].end_point_index;
		value = temp_devices[i].value;
		store.push_back(std::vector<double>{start,end,value});
		if (flag < start) flag = start;
		if (flag < end) flag = end;
		}
	}
	Vstore = store;
	store.clear();

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
     		if (it->x > max){
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
     if (it -> index == match){
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
	int match;
//	int x,y;
//  MDB::metal_point temp_point; 
 /*
for(auto it = temp_set.begin(); it != temp_set.end(); ++it){
      //std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
	//std::cout<<it->x<<"\t"<<it->y<<"\t"<<it->index<<"\t"<<it->metal_layer<<std::endl;
     if (it -> index == matchpoint){
	x = it->x;
	y = it->y;
}
     }
*/
	int diffx = 10000, diffy = 10000;
	int bestx = 0, besty = 0;

for(auto it = temp_set1.begin(); it != temp_set1.end(); ++it){
      //std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
	//std::cout<<it->x<<"\t"<<it->y<<"\t"<<it->index<<"\t"<<it->metal_layer<<std::endl;
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
      //std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
	//std::cout<<it->x<<"\t"<<it->y<<"\t"<<it->index<<"\t"<<it->metal_layer<<std::endl;
     if (it -> x == bestx && it ->y == besty){
	match = it->index;
	}
     }

return match;

};

void MNASimulation::AddingI(std::vector<MDB::metal_point> &I_point_v, std::vector<MDB::metal_point> &I_point_g, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, std::vector<MDB::device> &Power_Grid_devices, double current){

//std::cout<<"current size"<< I_point_v.size()<<std::endl;

   for(unsigned int i=0;i<I_point_v.size();++i){

       MDB::device temp_device;
       auto frist_point = temp_set.find(I_point_v[i]);
       int start_index = frist_point->index;
       // std::cout<<"First Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<start_index<<" "<<temp_point.metal_layer<<std::endl;
       auto second_point = temp_set.find(I_point_g[i]);
       int end_index = second_point->index;
       //  std::cout<<"Second Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<end_index<<" "<<temp_point.metal_layer<<std::endl;
       temp_device.device_type = MDB::I;
       temp_device.start_point_index = start_index;
       temp_device.end_point_index = end_index;  
       temp_device.value = current;
       Power_Grid_devices.push_back(temp_device);

     }

};


void MNASimulation::AddingPower(std::vector<MDB::metal_point> &power_points, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, std::vector<MDB::device> &Power_Grid_devices, double power){

std::cout << "power size" << power_points.size()<<std::endl;
   int end_index = -1;
   for(unsigned int i=0;i<power_points.size();++i){

       MDB::device temp_device;
       auto frist_point = temp_set.find(power_points[i]);
       int start_index = frist_point->index;
       // std::cout<<"First Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<start_index<<" "<<temp_point.metal_layer<<std::endl;
       
       //  std::cout<<"Second Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<end_index<<" "<<temp_point.metal_layer<<std::endl;
       temp_device.device_type = MDB::V;
       temp_device.start_point_index = start_index;
       temp_device.end_point_index = end_index;  
       temp_device.value = power;
       Power_Grid_devices.push_back(temp_device);
       end_index--;
     }

};






void MNASimulation::ExtractPowerGridPoint(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, int &highest_metal, int &lowest_metal, int power){
 MDB::metal_point temp_point; 

//std::cout<<"temp grid name "<< temp_grid.power << std::endl;
   
for(unsigned int i=0;i<temp_grid.vias.size();++i){

//std::cout<< "model index= " << temp_grid.vias[i].model_index <<" x= " << temp_grid.vias[i].placedpos.x << " y= " << temp_grid.vias[i].placedpos.y <<std::endl;
}

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
 //    std::cout<<"temp grid metal= "<<temp_grid.metals[i].MetalIdx <<" x[0]= "<<temp_grid.metals[i].LinePoint[0].x<<" y0= "<<temp_grid.metals[i].LinePoint[0].y << " x1= " << temp_grid.metals[i].LinePoint[1].x << " y1= " << temp_grid.metals[i].LinePoint[1].y <<std::endl;
  }



};

void MNASimulation::ExtractPowerGridWireR(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices, int power){

   for(unsigned int i=0;i<temp_grid.metals.size();++i){
     
       MDB::device temp_device;
       MDB::metal_point temp_point; 
       
       if(temp_grid.metals[i].LinePoint[0].x != temp_grid.metals[i].LinePoint[1].x or temp_grid.metals[i].LinePoint[0].y != temp_grid.metals[i].LinePoint[1].y){

          temp_point.metal_layer = temp_grid.metals[i].MetalIdx;
          temp_point.index = -1;
	  temp_point.power = power;
          temp_point.x = temp_grid.metals[i].LinePoint[0].x;
          temp_point.y = temp_grid.metals[i].LinePoint[0].y;
          auto frist_point = temp_set.find(temp_point);
          int start_index = frist_point->index;
         // std::cout<<"First Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<start_index<<" "<<temp_point.metal_layer<<std::endl;
//	temp_device.metal_layer1 = temp_point.metal_layer;


          temp_point.metal_layer = temp_grid.metals[i].MetalIdx;
          temp_point.index = -1;
	  temp_point.power = power;
          temp_point.x = temp_grid.metals[i].LinePoint[1].x;
          temp_point.y = temp_grid.metals[i].LinePoint[1].y;
          auto second_point = temp_set.find(temp_point);
          int end_index = second_point->index;
        //  std::cout<<"Second Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<end_index<<" "<<temp_point.metal_layer<<std::endl;

          temp_device.device_type = MDB::R;
          temp_device.start_point_index = start_index;
          temp_device.end_point_index = end_index;
 //         temp_device.metal_layer = temp_point.metal_layer;

          int metal_index = temp_grid.metals[i].MetalIdx;
          int metal_width = temp_grid.metals[i].width;
          int single_width = drc_info.Metal_info[metal_index].width;
          double unit_R = drc_info.Metal_info[metal_index].unit_R;
          double times = (double) metal_width / (double) single_width;
       //   std::cout<<"unit_R "<<unit_R<<" "<<drc_info.Metal_info[metal_index].unit_R<<std::endl;
          temp_device.value = ((double) abs(frist_point->x-second_point->x) + (double) abs(frist_point->y-second_point->y))*unit_R/times;
          
          Power_Grid_devices.push_back(temp_device);

        } 

     }


};

void MNASimulation::ExtractPowerGridViaR(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices, int power){

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

       temp_device.device_type = MDB::R;
       temp_device.start_point_index = start_index;
       temp_device.end_point_index = end_index;
	//temp_device.metal_layer2 = temp_point.metal_layer;
      // temp_device.value = drc_info.Via_model[model_index].R ;
	temp_device.value = 1;  
     Power_Grid_devices.push_back(temp_device);

     }


};


void MNASimulation::FindPowerPoints(std::set<MDB::metal_point, MDB::Compare_metal_point> &point_set, int power, int metal_layer, int power_number, std::vector<MDB::metal_point> &power_points){

  std::set<MDB::metal_point, MDB::Compare_metal_point> power_point_set;
  std::vector<MDB::metal_point> prime_power_points;
  std::set<int> x_set;
  std::set<int> y_set;
  std::vector<int> x_v;
  std::vector<int> y_v;
  MDB::metal_point temp_point;
  temp_point.metal_layer = metal_layer;
  temp_point.power = power;
//  std::cout<<"size of point set"<< point_set.size() <<std::endl;
  for(auto it = point_set.begin(); it != point_set.end(); ++it){
//	std::cout<<"metal layer = " << metal_layer <<" it layer = "<< it->metal_layer <<" power = "<<power << " it power = "<< it->power << std::endl;
       if(it->metal_layer == metal_layer and it->power == power){
         power_point_set.insert(*it);
         x_set.insert(it->x);
         y_set.insert(it->y);
       }

     }
//  std::cout <<"size of x_set= " << x_set.size()<<std::endl;
 // std::cout <<"size of y_set= " << y_set.size()<<std::endl;
  for(auto it = x_set.begin(); it != x_set.end(); ++it){

     x_v.push_back(*it);

     }
//  std::cout <<"size of x_v= " << x_v.size()<<std::endl;
  for(auto it = y_set.begin(); it != y_set.end(); ++it){

     y_v.push_back(*it);

     }
//  std::cout <<"size of y_v= " << y_v.size()<<std::endl;
  //need revise
  int x_number = sqrt(power_number);
  int y_number = sqrt(power_number);
  int xsize, ysize;
	xsize = x_v.size();
	ysize = y_v.size();
//	if (x_v.size()%x_number == 0) x

  for(int i =0;i<x_v.size();i=i+ceil((double) x_v.size()/x_number)){
     for(int j =0;j<y_v.size();j=j+ceil((double) y_v.size()/y_number)){
        temp_point.x = x_v[i];
        temp_point.y = y_v[j];
        power_points.push_back(temp_point);
	std::cout<<"i="<<i<<"j="<<j<<std::endl;
        }
  }
  std::cout<<"in find power point size = " << power_points.size()<<std::endl;
  //

};



void MNASimulation::ExtractPowerGrid(PnRDB::PowerGrid &vdd, PnRDB::PowerGrid &gnd, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices, std::vector<int> &mark_point){

  
  std::set<MDB::metal_point, MDB::Compare_metal_point> point_set;
 // std::set<MDB::metal_point, MDB::Compare_metal_point> gnd_point_set;

  int highest_metal = INT_MIN;
  int lowest_metal = INT_MAX;

  //ExtractPowerGridPoint(vdd, vdd_point_set);
  //ExtractPowerGridPoint(gnd, gnd_point_set);

  ExtractPowerGridPoint(vdd, point_set, highest_metal, lowest_metal, 1);
  ExtractPowerGridPoint(gnd, point_set, highest_metal, lowest_metal, 0);

  int refresh_index = 1;

  std::cout<<"Gnd Point Set"<<std::endl;
  for(auto it = point_set.begin(); it != point_set.end(); ++it){
     
       it->index = refresh_index;
	if (it->metal_layer == lowest_metal || it->metal_layer == lowest_metal + 1){
	mark_point.push_back(refresh_index);
	}
       //std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
	 std::cout<<it->x<<"\t"<<it->y<<"\t"<<it->index<<"\t"<<it->metal_layer<<std::endl;
       refresh_index = refresh_index + 1;
     
     }

  refresh_index = 1;

/*
  std::cout<<"Vdd Point Set"<<std::endl;
  for(auto it = vdd_point_set.begin(); it != vdd_point_set.end(); ++it){
       
       it->index = refresh_index;
       //std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
	std::cout<<it->x<<"\t"<<it->y<<"\t"<<it->index<<"\t"<<it->metal_layer<<std::endl;
	refresh_index = refresh_index + 1;
     
     }
*/
/*
  ExtractPowerGridWireR(vdd, vdd_point_set, drc_info, Power_Grid_devices_Vdd);
  ExtractPowerGridWireR(gnd, gnd_point_set, drc_info, Power_Grid_devices_Gnd);

  ExtractPowerGridViaR(vdd, vdd_point_set, drc_info, Power_Grid_devices_Vdd);
  ExtractPowerGridViaR(gnd, gnd_point_set, drc_info, Power_Grid_devices_Gnd);
*/

  ExtractPowerGridWireR(vdd, point_set, drc_info, Power_Grid_devices,1);
  ExtractPowerGridWireR(gnd, point_set, drc_info, Power_Grid_devices,0);

  ExtractPowerGridViaR(vdd, point_set, drc_info, Power_Grid_devices,1);
  ExtractPowerGridViaR(gnd, point_set, drc_info, Power_Grid_devices,0);

  std::vector<MDB::metal_point> vdd_points;
  std::vector<MDB::metal_point> gnd_points;
  std::vector<MDB::metal_point> I_points_v;
  std::vector<MDB::metal_point> I_points_g;

  int power_number = 4;
  int current_number = 4;
  FindPowerPoints(point_set, 1, highest_metal, power_number, vdd_points);
  FindPowerPoints(point_set, 0, highest_metal, power_number, gnd_points);
  //what if I_points_v!=I_points_g
  //what if I_points_g.size()<4?
  //need revise this part
  FindPowerPoints(point_set, 1, lowest_metal, current_number, I_points_v);
  FindPowerPoints(point_set, 0, lowest_metal, current_number, I_points_g);

  //here some function to calculate vdd_points, gnd_points, I_points_v and I_points_g;
//  std::cout<< "vdd points "<< vdd_points.size()<<" gnd points "<< gnd_points.size() << " I point v "<< I_points_v.size() << " I point g"<< I_points_g.size()<< std::endl;
  AddingPower(vdd_points, point_set, Power_Grid_devices, 1.0);
  AddingPower(gnd_points, point_set, Power_Grid_devices, 0.0);
  double current = 0.024/4.0;
  AddingI(I_points_v, I_points_g, point_set, Power_Grid_devices, current);
//  std::cout<<"Vdd device number "<<Power_Grid_devices_Vdd.size()<<std::endl;
//  std::cout<<"Gnd device number "<<Power_Grid_devices_Gnd.size()<<std::endl;

}

void MNASimulation::ConstructI(std::vector<std::vector<double>> Istore, std::vector<std::vector<double>> Vstore, std::vector<std::vector<double>> Rstore){
 int Rsize = 0, size;
 for (int i = 0; i < Rstore.size(); i++){
 if (Rsize < Rstore[i][0])
	Rsize = Rstore[i][0];
 if (Rsize < Rstore[i][1])
	Rsize = Rstore[i][1];
}
 size = Rsize + Vstore.size();
 boost_matrix II (size, 1);
 for (unsigned j = 0 ; j < II.size1 (); ++j)
 	II (j, 0) = 0;


if (Istore.size() > 0){
 for (int i = 0; i < Istore.size(); i++){
 	 int start = Istore[i][0]-1;
	 int end = Istore[i][1]-1;
	 double value = Istore[i][2];
	//std::cout << "start I" << start <<", end I" << end << std::endl;
		if (start >= 0 )
		II (start, 0) = value;
		if (end >= 0 )
		II (end, 0) = -value;
	}
}



 for (int i = 0; i < Vstore.size(); i++){
 int start = Vstore[i][0] - 1;
 double value = Vstore[i][2];
	if (start >= 0 )
 	II (Rsize + i, 0) = value;
}

 for (unsigned i = 0; i < II.size1 (); ++ i)
        for (unsigned j = 0; j < II.size2 (); ++ j)
            std::cout << "I(" << i <<"," << j <<")=" << II (i, j)  << std::endl;


  I=II;
}

void MNASimulation::ConstructR(std::vector<std::vector<double>> Rstore, std::vector<std::vector<double>> Vstore){
 int size = 0, Rsize = 0;
 for (int i = 0; i < Rstore.size(); i++){
 if (size < Rstore[i][0])
	size = Rstore[i][0];
 if (size < Rstore[i][1])
	size = Rstore[i][1];
}
	//std::cout << "size=" << size << std::endl;
 Rsize = size;
 size += Vstore.size();
 boost_matrix RR (size, size);
 // boost matrix start the index from 1
 for (unsigned i = 0; i < RR.size1 (); ++ i)
        for (unsigned j = 0; j < RR.size2 (); ++ j)
            RR (i, j) = 0;

 for (int i = 0; i < Rstore.size(); i++){
 int col,row;
 double value;
 col = Rstore[i][0]-1;
 row = Rstore[i][1]-1;
 value = 1.0/Rstore[i][2];
// std::cout << "R is " << Rstore[i][2] << " 1/R value is "<< value << std::endl;
 if (col >= 0)
 RR(col,col) += value;
 if (row >= 0)
 RR(row,row) += value;
 if (row >= 0 && col >= 0){
 	RR(col,row) -= value;
 	RR(row,col) -= value;
 	}
 }
 


 for (int i = 0; i <Vstore.size(); i++){
 int start,end;
 start = Vstore[i][0]-1;
 end = Vstore[i][1]-1;
 if (start >= 0){
 RR(start, Rsize + i) = 1;
 RR(Rsize + i, start) = 1;
 }
 if (end >= 0){
 RR(end, Rsize + i) = -1;
 RR(Rsize + i, end) = -1;
 }
 
}

for (unsigned i = 0; i < RR.size1 (); ++ i){
        for (unsigned j = 0; j < RR.size2 (); ++ j){
            std::cout << RR (i, j) <<"\t";
//"R(" << i <<"," << j <<")=" 
	}
	std::cout<<std::endl;
}

 R = RR;
}


double MNASimulation::SolveIR_drop(int Rsize){


	int width = R.size1();	
        boost_matrix VV (width,1);
	//V=prod(R,I);
	bool flag = false;
	boost_matrix inv (width,width);
	//std::cout << "R is " << R << std::endl;
	inv = gjinverse(R,flag);
	//std::cout<< inv << std::endl;
        //bool    init = true
   
	//std::cout << R << std::endl;
	VV = prod (inv,I);

	V = VV;

	for (unsigned i = 0; i < V.size1(); ++i){
	std::cout<< V(i,0)<<std::endl;
}

	//std::cout << "V is " << V << std::endl;
	double max = 1.0;
	for (unsigned i = 0; i < Rsize; ++i){
	if (max > V(i, 0) && V(i,0) > 0.5)
	max = V(i, 0);
	}
	max = 1 - max;	

	return max;
}




void MNASimulation::Test_superlu()
{
/*
 * Purpose
 * =======
 * 
 * This is the small 5x5 example used in the Sections 2 and 3 of the 
 * Users' Guide to illustrate how to call a SuperLU routine, and the
 * matrix data structures used by SuperLU.
 *
 */
    SuperMatrix A, L, U, B;
    double   *a, *rhs;
    double   s, u, p, e, r, l;
    int      *asub, *xa;
    int      *perm_r; /* row permutations from partial pivoting */
    int      *perm_c; /* column permutation vector */
    int      nrhs, info, i, m, n, nnz, permc_spec;
    superlu_options_t options;
    SuperLUStat_t stat;

    /* Initialize matrix A. */
    m = n = 5;
    nnz = 12;
    if ( !(a = doubleMalloc(nnz)) ) ABORT("Malloc fails for a[].");
    if ( !(asub = intMalloc(nnz)) ) ABORT("Malloc fails for asub[].");
    if ( !(xa = intMalloc(n+1)) ) ABORT("Malloc fails for xa[].");
    s = 19.0; u = 21.0; p = 16.0; e = 5.0; r = 18.0; l = 12.0;
	//for
    a[0] = s; a[1] = l; a[2] = l; a[3] = u; a[4] = l; a[5] = l;
    a[6] = u; a[7] = p; a[8] = u; a[9] = e; a[10]= u; a[11]= r;
    asub[0] = 0; asub[1] = 1; asub[2] = 4; asub[3] = 1;
    asub[4] = 2; asub[5] = 4; asub[6] = 0; asub[7] = 2;
    asub[8] = 0; asub[9] = 3; asub[10]= 3; asub[11]= 4;
    xa[0] = 0; xa[1] = 3; xa[2] = 6; xa[3] = 8; xa[4] = 10; xa[5] = 12;

    /* Create matrix A in the format expected by SuperLU. */
    dCreate_CompCol_Matrix(&A, m, n, nnz, a, asub, xa, SLU_NC, SLU_D, SLU_GE);
    
    /* Create right-hand side matrix B. */
    nrhs = 1;
    if ( !(rhs = doubleMalloc(m * nrhs)) ) ABORT("Malloc fails for rhs[].");
    for (i = 0; i < m; ++i) rhs[i] = 1.0;
    dCreate_Dense_Matrix(&B, m, nrhs, rhs, m, SLU_DN, SLU_D, SLU_GE);

    if ( !(perm_r = intMalloc(m)) ) ABORT("Malloc fails for perm_r[].");
    if ( !(perm_c = intMalloc(n)) ) ABORT("Malloc fails for perm_c[].");

    /* Set the default input options. */
    set_default_options(&options);
    options.ColPerm = NATURAL;

    /* Initialize the statistics variables. */
    StatInit(&stat);

    /* Solve the linear system. */
    dgssv(&options, &A, perm_c, perm_r, &L, &U, &B, &stat, &info);
    
    dPrint_CompCol_Matrix("A", &A);
    dPrint_CompCol_Matrix("U", &U);
    dPrint_SuperNode_Matrix("L", &L);
    print_int_vec("\nperm_r", m, perm_r);

    /* De-allocate storage */
    SUPERLU_FREE (rhs);
    SUPERLU_FREE (perm_r);
    SUPERLU_FREE (perm_c);
    Destroy_CompCol_Matrix(&A);
    Destroy_SuperMatrix_Store(&B);
    Destroy_SuperNode_Matrix(&L);
    Destroy_CompCol_Matrix(&U);
    StatFree(&stat);
}

