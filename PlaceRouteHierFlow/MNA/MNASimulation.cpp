#include <MNASimulation.h>
//#include </home/grads/w/wbxu/share/opt/boost/numeric/ublas/operation.hpp>

MNASimulation::MNASimulation(boost_matrix &out_R, boost_matrix &out_I){

this->R = out_R;
this->I = out_I;

}

void MNASimulation::ExtractPowerGrid(){


}

boost_matrix MNASimulation::ConstructI(std::vector<std::vector<double>> Istore, std::vector<std::vector<double>> Vstore, std::vector<std::vector<double>> Rstore){
 int Rsize = 0;
 for (int i = 0; i < Rstore.size(); i++){
 if (Rsize < Rstore[i][0])
	Rsize = Rstore[i][0];
 else if (Rsize < Rstore[i][1])
	Rsize = Rstore[i][1];
}
 size = Rsize + Vstore.size();
 boost_matrix I (size, 1);
 for (unsigned j = 0 ; j < I.size1 (); ++j)
 	I (j, 1) = 0;
 
 for (int i = 0; i < Istore.size(); i++){
 int start = Istore[i][0];
 double value = Istore[i][2];
	I (start, 1) = value;
}

 for (int i = 0; i < Vstore.size(); i++){
 int start = Vstore[i][0];
 double value = Vstore[i][2];
 	I (Rsize + start, 1) = value;
}
}

boost_matrix MNASimulation::ConstructR(std::vector<std::vector<double>> Rstore, std::vector<std::vector<double>> Vstore){
 int size = 0, Rsize = 0;
 for (int i = 0; i < Rstore.size(); i++){
 if (size < Rstore[i][0])
	size = Rstore[i][0];
 else if (size < Rstore[i][1])
	size = Rstore[i][1];
}
 Rsize = size;
 size += Vstore.size();
 boost_matrix R (size, size);
 // boost matrix start the index from 1
 for (unsigned i = 0; i < R.size1 (); ++ i)
        for (unsigned j = 0; j < R.size2 (); ++ j)
            R (i, j) = 0;

 for (int i = 0; i < Rstore.size(); i++){
 int col,row;
 double value;
 col = Rstore[i][0];
 row = Rstore[i][1];
 value = 1.0/Rstore[i][2];
 if (col > 0)
 R(col,col) += value;
 if (row > 0)
 R(row,row) += value;
 if (row > 0 && col > 0){
 	R(col,row) -= value;
 	R(row,col) -= value;
 	}
 }
 
 for (int i = 0; i <Vstore.size(); i++){
 int start,end;
 start = Vstore[i][0];
 end = Vstore[i][1];
 if (start > 0){
 R(start, Rsize + i + 1) = 1;
 R(Rsize + i + 1, start) = 1;
 }
 if (end > 0){
 R(end, Rsize + i + 1) = -1;
 R(Rsize + i + 1, end) = -1;
 }
 return R;
}

}


int MNASimulation::SolveIR_drop(){

  R;
  I;

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

	
        boost_matrix V (3,3);
	//V=prod(R,I);
	bool flag = false;
	boost_matrix inv (3,3);
	inv = gjinverse(R,flag);
	//std::cout<< inv << std::endl;
        //bool    init = true
   
	//std::cout << R << std::endl;
	V = prod (inv,I);
  //solve it;
  /*BOOST_UBLAS_INLINE M& axpy_prod (const matrix_expression< R > &out_R,
        const matrix_expression< I > &out_I,
        V &V,
        bool    init = true
    ) */
	std::cout << V << std::endl;
}
