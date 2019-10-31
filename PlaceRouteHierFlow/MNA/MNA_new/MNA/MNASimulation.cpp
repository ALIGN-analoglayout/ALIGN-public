#include "MNASimulation.h"
//#include </home/grads/w/wbxu/share/opt/boost/numeric/ublas/operation.hpp>

MNASimulation::MNASimulation(boost_matrix &out_R, boost_matrix &out_I){

this->R = out_R;
this->I = out_I;

}

void read(){
/*
  struct element{
   std::string key = [r,i,v,c,l];
  //  start point
  //  end point
  //  value
  }
*/
 // map<pair<int,int> index> node_map;

//  vector<element> circuits;

}

void MNASimulation::ConstructI(std::vector<std::vector<double>> Istore, std::vector<std::vector<double>> Vstore, std::vector<std::vector<double>> Rstore){
 int Rsize = 0, size;
 for (int i = 0; i < Rstore.size(); i++){
 if (Rsize < Rstore[i][0])
	Rsize = Rstore[i][0];
 else if (Rsize < Rstore[i][1])
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
 	II (Rsize + start, 0) = value;
}

  I=II;
}

void MNASimulation::ConstructR(std::vector<std::vector<double>> Rstore, std::vector<std::vector<double>> Vstore){
 int size = 0, Rsize = 0;
 for (int i = 0; i < Rstore.size(); i++){
 if (size < Rstore[i][0])
	size = Rstore[i][0];
 else if (size < Rstore[i][1])
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

  R;
  I;
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
