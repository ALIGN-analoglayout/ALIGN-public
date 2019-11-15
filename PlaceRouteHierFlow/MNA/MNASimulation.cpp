#include "MNASimulation.h"
//#include </home/grads/w/wbxu/share/opt/boost/numeric/ublas/operation.hpp>

MNASimulation::MNASimulation(PnRDB::hierNode &current_node, PnRDB::Drc_info &drc_info){

boost_matrix out_R, out_I; 
this->R = out_R;
this->I = out_I;
ExtractPowerGrid(current_node.Vdd, current_node.Gnd, drc_info, Power_Grid_devices_Vdd, Power_Grid_devices_Gnd);

std::cout<<"Vdd Devices"<<std::endl;
Print_Devices(Power_Grid_devices_Vdd);
std::cout<<"Gnd Devices"<<std::endl;
Print_Devices(Power_Grid_devices_Gnd);

//++

};

void MNASimulation::Print_Devices(std::vector<MDB::device> &temp_devices){

  for(int i=0;i<temp_devices.size();i++){

     std::cout<<"devices type "<<temp_devices[i].device_type<<" point 1 "<<temp_devices[i].start_point_index<<" point 2 "<<temp_devices[i].end_point_index<<" value "<< temp_devices[i].value <<std::endl;

  }

};

void MNASimulation::ExtractPowerGridPoint(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set){

  MDB::metal_point temp_point; 
 
  for(unsigned int i=0;i<temp_grid.metals.size();++i){
     temp_point.metal_layer = temp_grid.metals[i].MetalIdx;
     temp_point.index = -1;
     temp_point.x = temp_grid.metals[i].LinePoint[0].x;
     temp_point.y = temp_grid.metals[i].LinePoint[0].y;
     temp_set.insert(temp_point);
     temp_point.x = temp_grid.metals[i].LinePoint[1].x;
     temp_point.y = temp_grid.metals[i].LinePoint[1].y;
     temp_set.insert(temp_point);
  }

};

void MNASimulation::ExtractPowerGridWireR(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices){

   for(unsigned int i=0;i<temp_grid.metals.size();++i){
     
       MDB::device temp_device;
       MDB::metal_point temp_point; 
       
       if(temp_grid.metals[i].LinePoint[0].x != temp_grid.metals[i].LinePoint[1].x or temp_grid.metals[i].LinePoint[0].y != temp_grid.metals[i].LinePoint[1].y){

          temp_point.metal_layer = temp_grid.metals[i].MetalIdx;
          temp_point.index = -1;
          temp_point.x = temp_grid.metals[i].LinePoint[0].x;
          temp_point.y = temp_grid.metals[i].LinePoint[0].y;
          auto frist_point = temp_set.find(temp_point);
          int start_index = frist_point->index;
          std::cout<<"First Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<start_index<<" "<<temp_point.metal_layer<<std::endl;

          temp_point.metal_layer = temp_grid.metals[i].MetalIdx;
          temp_point.index = -1;
          temp_point.x = temp_grid.metals[i].LinePoint[1].x;
          temp_point.y = temp_grid.metals[i].LinePoint[1].y;
          auto second_point = temp_set.find(temp_point);
          int end_index = second_point->index;
          std::cout<<"Second Point (x,y) index metal "<<temp_point.x<<" "<<temp_point.y<<" "<<end_index<<" "<<temp_point.metal_layer<<std::endl;

          temp_device.device_type = MDB::R;
          temp_device.start_point_index = start_index;
          temp_device.end_point_index = end_index;
          
          int metal_index = temp_grid.metals[i].MetalIdx;
          int metal_width = temp_grid.metals[i].width;
          int single_width = drc_info.Metal_info[metal_index].width;
          double unit_R = drc_info.Metal_info[metal_index].unit_R;
          double times = (double) metal_width / (double) single_width;
          std::cout<<"unit_R "<<unit_R<<" "<<drc_info.Metal_info[metal_index].unit_R<<std::endl;
          temp_device.value = ((double) abs(frist_point->x-second_point->x) + (double) abs(frist_point->y-second_point->y))*unit_R/times;
          
          Power_Grid_devices.push_back(temp_device);

        } 

     }


};

void MNASimulation::ExtractPowerGridViaR(PnRDB::PowerGrid &temp_grid, std::set<MDB::metal_point, MDB::Compare_metal_point> &temp_set, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices){

   for(unsigned int i=0;i<temp_grid.vias.size();++i){
     
       MDB::device temp_device;
       MDB::metal_point temp_point;

       int model_index = temp_grid.vias[i].model_index;
       int x = temp_grid.vias[i].placedpos.x;
       int y = temp_grid.vias[i].placedpos.y;

       temp_point.metal_layer = drc_info.Via_model[model_index].LowerIdx;
       temp_point.index = -1;
       temp_point.x = x;
       temp_point.y = y;
       auto frist_point = temp_set.find(temp_point);
       int start_index = frist_point->index;
       
       temp_point.metal_layer = drc_info.Via_model[model_index].UpperIdx;
       temp_point.index = -1;
       temp_point.x = x;
       temp_point.y = y;
       auto second_point = temp_set.find(temp_point);
       int end_index = second_point->index;

       temp_device.device_type = MDB::R;
       temp_device.start_point_index = start_index;
       temp_device.end_point_index = end_index;
       temp_device.value = drc_info.Via_model[model_index].R;
       Power_Grid_devices.push_back(temp_device);

     }


};

void MNASimulation::ExtractPowerGrid(PnRDB::PowerGrid &vdd, PnRDB::PowerGrid &gnd, PnRDB::Drc_info &drc_info, std::vector<MDB::device> &Power_Grid_devices_Vdd, std::vector<MDB::device> &Power_Grid_devices_Gnd){

  
  std::set<MDB::metal_point, MDB::Compare_metal_point> vdd_point_set;
  std::set<MDB::metal_point, MDB::Compare_metal_point> gnd_point_set;

  ExtractPowerGridPoint(vdd, vdd_point_set);
  ExtractPowerGridPoint(gnd, gnd_point_set);

  int refresh_index = 0;

  std::cout<<"Vdd Point Set"<<std::endl;
  for(auto it = vdd_point_set.begin(); it != vdd_point_set.end(); ++it){
       
       it->index = refresh_index;
       std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
       refresh_index = refresh_index + 1;
     
     }

  refresh_index = 0;

  std::cout<<"Gnd Point Set"<<std::endl;
  for(auto it = gnd_point_set.begin(); it != gnd_point_set.end(); ++it){
     
       it->index = refresh_index;
       std::cout<<"(x,y) index metal "<<it->x<<" "<<it->y<<" "<<it->index<<" "<<it->metal_layer<<std::endl;
       refresh_index = refresh_index + 1;
     
     }


  ExtractPowerGridWireR(vdd, vdd_point_set, drc_info, Power_Grid_devices_Vdd);
  ExtractPowerGridWireR(gnd, gnd_point_set, drc_info, Power_Grid_devices_Gnd);

  ExtractPowerGridViaR(vdd, vdd_point_set, drc_info, Power_Grid_devices_Vdd);
  ExtractPowerGridViaR(gnd, gnd_point_set, drc_info, Power_Grid_devices_Gnd);

  std::cout<<"Vdd device number "<<Power_Grid_devices_Vdd.size()<<std::endl;
  std::cout<<"Gnd device number "<<Power_Grid_devices_Gnd.size()<<std::endl;

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
	 double value = Istore[i][2];
		if (start >= 0 )
		II (start, 0) = value;
	}
}

 for (unsigned i = 0; i < II.size1 (); ++ i)
        for (unsigned j = 0; j < II.size2 (); ++ j)
            std::cout << "I(" << i <<"," << j <<")=" << II (i, j)  << std::endl;


 for (int i = 0; i < Vstore.size(); i++){
 int start = Vstore[i][0] - 1;
 double value = Vstore[i][2];
	if (start >= 0 )
 	II (Rsize + i, 0) = value;
}

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

for (unsigned i = 0; i < RR.size1 (); ++ i)
        for (unsigned j = 0; j < RR.size2 (); ++ j)
            std::cout << "R(" << i <<"," << j <<")=" << RR (i, j)  << std::endl;

 R = RR;
}


int MNASimulation::SolveIR_drop(){

	/*
	boost_matrix R (3, 3);
    for (unsigned i = 0; i < R.size1 (); ++ i)
        for (unsigned j = 0; j < R.size2 (); ++ j)
            R (i, j) = 3 * i + j;

	boost_matrix I (3, 3);
    for (unsigned i = 0; i < I.size1 (); ++ i)
        for (unsigned j = 0; j < I.size2 (); ++ j)
            I (i, j) = 3 * i + j;
	//boost_matrix Rinv = gjinverse(R,false);
	R(0,0)=(1,1);
	R(1,1)=(1,1);
	R(2,2)=(1,1);


	boost_matrix I (2, 1);
	for (unsigned i = 0; i < I.size1(); ++i)
		I (i, 0) = 0;
	I (0, 0) = 2;
/*
	boost_matrix R (2, 2);
	R(0,0) = 0.5;
	R(0,1) = 1;
	R(1,0) = 1;
	R(1,1) = 0;*/
	int width = R.size1();	
        boost_matrix VV (width,1);
	//V=prod(R,I);
	bool flag = false;
	boost_matrix inv (width,width);
	std::cout << "R is " << R << std::endl;
	inv = gjinverse(R,flag);
	//std::cout<< inv << std::endl;
        //bool    init = true
   
	//std::cout << R << std::endl;
	VV = prod (inv,I);
  //solve it;
  /*BOOST_UBLAS_INLINE M& axpy_prod (const matrix_expression< R > &out_R,
        const matrix_expression< I > &out_I,
        V &V,
        bool    init = true
    ) */
	V = VV;
	std::cout << "V is " << V << std::endl;
	return 0;
}
