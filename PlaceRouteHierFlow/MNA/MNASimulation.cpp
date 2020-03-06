#include "MNASimulation.h"
#include <assert.h>
//#include </home/grads/w/wbxu/share/opt/boost/numeric/ublas/operation.hpp>

MNASimulation::MNASimulation(PnRDB::hierNode &current_node, PnRDB::Drc_info &drc_info){
//MNASimulation::MNASimulation(boost_matrix &out_R, boost_matrix &out_I){
Test_superlu();
assert(0);
boost_matrix out_R, out_I; 
std::vector<std::vector<double> > Istore,Vstore,Rstore;
this->R = out_R;
this->I = out_I;

ExtractPowerGrid(current_node.Vdd, current_node.Gnd, drc_info, Power_Grid_devices);

/*
std::cout<<"Vdd Devices"<<std::endl;
Print_Devices(Power_Grid_devices_Vdd);
std::cout<<"Gnd Devices"<<std::endl;
Print_Devices(Power_Grid_devices_Gnd);
*/

Transfer(Power_Grid_devices, Power_Grid_devices, Rstore);
/*
for (int i = 0; i < Rstore.size(); i++){
std::cout << "start "<< Rstore[i][0] <<" end " << Rstore[i][1]<< " value " << Rstore[i][2] << std::endl;
}*/

int node_num1 = nodenum(Power_Grid_devices);
//int node_num2 = nodenum(Power_Grid_devices_Vdd);

Vstore.push_back(std::vector<double>{node_num1+1,1,1});
Vstore.push_back(std::vector<double>{node_num1+5,5,1});
Vstore.push_back(std::vector<double>{node_num1+6,6,1});
//Vstore.push_back(std::vector<double>{node_num1+7,7,1});
Istore.push_back(std::vector<double>{2,node_num1+2,0.0003});
Istore.push_back(std::vector<double>{3,node_num1+3,0.0005});
Istore.push_back(std::vector<double>{4,node_num1+4,0.0007});



ConstructI(Istore,Vstore,Rstore);
ConstructR(Rstore,Vstore);

int Rsize = 0;
 for (int i = 0; i < Rstore.size(); i++){
 if (Rsize < Rstore[i][0])
	Rsize = Rstore[i][0];
 if (Rsize < Rstore[i][1])
	Rsize = Rstore[i][1];
}


 result = SolveIR_drop(Rsize);

//use for ppt
result = node_num1;

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

void MNASimulation::Transfer(std::vector<MDB::device> &temp_devices, std::vector<MDB::device> &temp2_devices, std::vector<std::vector<double> > &Rstore){
	int start,end,flag;
	flag = 0;
	double value;
	std::vector<std::vector<double> > store;
	// std::vector<double> temp;
	for(int i=0;i<temp_devices.size();i++){
		//if (temp_devices[i].device_type == 0){
		start = temp_devices[i].start_point_index;
		end = temp_devices[i].end_point_index;
		value = temp_devices[i].value;
		store.push_back(std::vector<double>{start,end,value});
		if (flag < start) flag = start;
		if (flag < end) flag = end;
		//}
	}
	flag++;
//	int size = temp_devices.size();
	for(int i=0;i<temp2_devices.size();i++){
		//if (temp2_devices[i].device_type == 0){
		start = flag + temp2_devices[i].start_point_index;
		end = flag + temp2_devices[i].end_point_index;
		value = temp2_devices[i].value;
		store.push_back(std::vector<double>{start,end,value});
		
		//}
	}
	
	Rstore = store;
	store.clear();

}

void MNASimulation::AddingI(std::vector<MDB::metal_point> &I_point_v, std::vector<MDB::metal_point> &I_point_g, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, std::vector<MDB::device> &Power_Grid_devices, double current){

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

   for(unsigned int i=0;i<power_points.size();++i){
     
       MDB::device temp_device;
       auto frist_point = temp_set.find(power_points[i]);
       int start_index = frist_point->index;
       // std::cout<<"First Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<start_index<<" "<<temp_point.metal_layer<<std::endl;
       int end_index = -1;
       //  std::cout<<"Second Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<end_index<<" "<<temp_point.metal_layer<<std::endl;
       temp_device.device_type = MDB::V;
       temp_device.start_point_index = start_index;
       temp_device.end_point_index = end_index;  
       temp_device.value = power;
       Power_Grid_devices.push_back(temp_device);

     }

};


void MNASimulation::ExtractPowerGridPoint(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, int highest_metal, int lowest_metal, int power){

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
       if(temp_set.find(temp_point)==temp_set.end()){continue;}
       auto frist_point = temp_set.find(temp_point);
       int start_index = frist_point->index;
       
       temp_point.metal_layer = drc_info.Via_model[model_index].UpperIdx;
       temp_point.index = -1;
       temp_point.power = 1-power;
       temp_point.x = x;
       temp_point.y = y;
       if(temp_set.find(temp_point)==temp_set.end()){continue;}
       auto second_point = temp_set.find(temp_point);
       int end_index = second_point->index;

       temp_device.device_type = MDB::R;
       temp_device.start_point_index = start_index;
       temp_device.end_point_index = end_index;
       temp_device.value = drc_info.Via_model[model_index].R;
       //temp_device.value = 1;  
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
  
  for(auto it = point_set.begin(); it != point_set.end(); ++it){
     
       if(it->metal_layer == metal_layer and it->power == power){
         power_point_set.insert(*it);
         x_set.insert(it->x);
         y_set.insert(it->y);
       }
     
     }

  for(auto it = x_set.begin(); it != x_set.end(); ++it){

     x_v.push_back(*it);

     }

  for(auto it = y_set.begin(); it != y_set.end(); ++it){

     y_v.push_back(*it);

     }
  //need revise
  int x_number = sqrt(power_number);
  int y_number = sqrt(power_number);
  
  for(int i =0;i<x_v.size();i=i+ceil(x_v.size()/x_number)){
     for(int j =0;j<y_v.size();j=j+ceil(y_v.size()/y_number)){
        temp_point.x = x_v[i];
        temp_point.y = y_v[j];
        power_points.push_back(temp_point);
        }
  }

  //

  
};

void MNASimulation::ExtractPowerGrid(PnRDB::PowerGrid &vdd, PnRDB::PowerGrid &gnd, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices){

  
  std::set<MDB::metal_point, MDB::Compare_metal_point> point_set;
  //std::set<MDB::metal_point, MDB::Compare_metal_point> gnd_point_set;
  int highest_metal = INT_MIN;
  int lowest_metal = INT_MAX;

  ExtractPowerGridPoint(vdd, point_set, highest_metal, lowest_metal, 1);
  ExtractPowerGridPoint(gnd, point_set, highest_metal, lowest_metal, 0);


  int refresh_index = 1;

  std::cout<<"Gnd Point Set"<<std::endl;
  for(auto it = point_set.begin(); it != point_set.end(); ++it){
     
       it->index = refresh_index;
       //std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
	std::cout<<it->x<<"\t"<<it->y<<"\t"<<it->index<<"\t"<<it->metal_layer<<std::endl;
       refresh_index = refresh_index + 1;
     
     }

  //refresh_index = 1;

/*
  std::cout<<"Vdd Point Set"<<std::endl;
  for(auto it = vdd_point_set.begin(); it != vdd_point_set.end(); ++it){
       
       it->index = refresh_index;
       //std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
	std::cout<<it->x<<"\t"<<it->y<<"\t"<<it->index<<"\t"<<it->metal_layer<<std::endl;
	refresh_index = refresh_index + 1;
     
     }
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

  AddingPower(vdd_points, point_set, Power_Grid_devices, 1.0);
  AddingPower(gnd_points, point_set, Power_Grid_devices, 0.0);
  double current = 1.0;

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
/*
 for (unsigned i = 0; i < II.size1 (); ++ i)
        for (unsigned j = 0; j < II.size2 (); ++ j)
            std::cout << "I(" << i <<"," << j <<")=" << II (i, j)  << std::endl;
*/

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
/*
for (unsigned i = 0; i < RR.size1 (); ++ i)
        for (unsigned j = 0; j < RR.size2 (); ++ j)
            std::cout << "R(" << i <<"," << j <<")=" << RR (i, j)  << std::endl;
*/
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
