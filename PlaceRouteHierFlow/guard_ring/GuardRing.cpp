#include "GuardRing.h"

void GuardRing::Pcell_info(int pcell_width, int pcell_height){
  pcell_size.width = pcell_width;
  pcell_size.height = pcell_height;
};

void GuardRing::Wcell_info(PnRDB::hierNode &node){
  wcell_ll.x = node.LL.x;
  wcell_ll.y = node.LL.y;
  wcell_ur.x = node.LL.x + node.width;
  wcell_ur.y = node.LL.y + node.height;
  wcell_size.width = node.width;
  wcell_size.height = node.height;
}

GuardRing::GuardRing(int Minimal_x, int Minimal_y, int pcell_width, int pcell_height, PnRDB::hierNode &node){
  
  Pcell_info(pcell_width, pcell_height);
  Wcell_info(node);
  //Print wcell & pcell info
  std::cout << "wcell_ll[x,y] = " << wcell_ll.x << "," << wcell_ll.y << std::endl;
  std::cout << "wcell_ur[x,y] = " << wcell_ur.x << "," << wcell_ur.y << std::endl;
  std::cout << "node_width = " << node.width << std::endl;
  std::cout << "node_height = " << node.height << std::endl;
  std::cout << "node_ll[x,y] = " << node.LL.x << "," << node.LL.y << std::endl;
  std::cout << "node_ur[x,y] = " << node.UR.x << "," << node.UR.y << std::endl;

  //calculate cell number
  int x_number, y_number;
  x_number = ceil(wcell_size.width / pcell_size.width) + 3;
  y_number = ceil(wcell_size.height / pcell_size.height) + 1;

  //store lower left coordinate of guard ring primitive cell
  //start from Pcell0 which is at the southwest corner of wrapped cell
  GuardRingDB::point southwest, southeast, northeast, northwest; //guard ring primitive cells at corner.
  if (((((x_number-2) * pcell_size.width) - wcell_size.width)/2) < Minimal_x)
    southwest.x = wcell_ll.x - pcell_size.width - Minimal_x;
  else
    southwest.x = wcell_ll.x - pcell_size.width - (((x_number-2) * pcell_size.width) - wcell_size.width)/2;
  if (((((x_number-2) * pcell_size.width) - wcell_size.width)/2) < Minimal_y)
    southwest.y = wcell_ll.y - pcell_size.height - Minimal_y;
  else
    southwest.y = wcell_ll.y - pcell_size.height - (((y_number * pcell_size.height) - wcell_size.height)/2);
  temp_point.x = southwest.x;
  temp_point.y = southwest.y;
  stored_point_ll.push_back(temp_point);

  //store south side pcell's coordinates
  for (int i_s=1; i_s<x_number; i_s++)
  {
    temp_point.x = southwest.x + i_s*pcell_size.width;
    temp_point.y = southwest.y;
    stored_point_ll.push_back(temp_point);
  }
  southeast.x = temp_point.x;
  southeast.y = temp_point.y;

  //store east side pcell's coordinates
  for (int i_e=1; i_e< y_number+2; i_e++)
  {
    temp_point.x = southeast.x;
    temp_point.y = southeast.y + (i_e)*pcell_size.height;
    stored_point_ll.push_back(temp_point);
  }
  northeast.x = temp_point.x;
  northeast.y = temp_point.y;

  //store north side pcell's coordinates
  for (int i_n=1; i_n<x_number; i_n++)
  {
    temp_point.x = northeast.x - i_n*pcell_size.width;
    temp_point.y = northeast.y;
    stored_point_ll.push_back(temp_point);
  }
  northwest.x = temp_point.x;
  northwest.y = temp_point.y;

  //Store west side pcells' coordinate
  for (int i_w=1; i_w<y_number+1; i_w++)
  {
    temp_point.x = northwest.x;
    temp_point.y = northwest.y - i_w*pcell_size.height;
    stored_point_ll.push_back(temp_point);
  }

  if(northwest.x != southwest.x)
    std::cout << "Error: misaligned!!!\n";

  //calculate upper right coordinates of stored points
  for (int i_ur = 0; i_ur < stored_point_ll.size(); i_ur++) 
  {
    temp_point.x = stored_point_ll[i_ur].x + pcell_size.width;
    temp_point.y = stored_point_ll[i_ur].y + pcell_size.height;
    stored_point_ur.push_back(temp_point);
  }
    
  std::cout << "\nThe stored points are:\n"; 
  for (int i_print = 0; i_print < stored_point_ll.size(); i_print++) 
    std::cout << "lower left: " << stored_point_ll[i_print].x << "," << stored_point_ll[i_print].y << " " << "upper right: " << stored_point_ur[i_print].x << "," << stored_point_ur[i_print].y <<std::endl;
  
  gnuplot();
};

void GuardRing::gnuplot(){
  //Plot GuardRing Place
  std::cout<<"Placer-Router-GuardRing-Info: create gnuplot file"<<std::endl;
  std::ofstream fout;
  fout.open("guardringplot");

  //set title
  fout<<"#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)"<<std::endl;
  fout<<"\nset title\" #GuardRing Pcells= "<<stored_point_ll.size()<<" \""<<std::endl;
  fout<<"\nset nokey"<<std::endl;
  fout<<"#   Uncomment these two lines starting with \"set\""<<std::endl;
  fout<<"#   to save an EPS file for inclusion into a latex document"<<std::endl;
  fout<<"# set terminal postscript eps color solid 20"<<std::endl;
  fout<<"# set output \"result.eps\""<<std::endl<<std::endl;
  fout<<"#   Uncomment these two lines starting with \"set\""<<std::endl;
  fout<<"#   to save a PS file for printing"<<std::endl;
  fout<<"set term png"<<std::endl;
  fout<<"set output \"result.png\""<<std::endl;

  //set range
  fout<<"\nset xrange ["<<wcell_ll.x-4*pcell_size.width<<":"<<wcell_ur.x+4*pcell_size.width<<"]"<<std::endl;
  fout<<"\nset yrange ["<<wcell_ll.y-4*pcell_size.height<<":"<<wcell_ur.y+4*pcell_size.height<<"]"<<std::endl;

  //set label for Pcells
  for(int i=0; i<stored_point_ll.size(); i++)
  {
	  fout<<"\nset label \"" << i <<"\" at "<<(stored_point_ll[i].x + stored_point_ur[i].x)/2<<","<<(stored_point_ll[i].y + stored_point_ur[i].y)/2<<" center "<<std::endl;
  }
	//set label for Wrapped cell
	fout<<"\nset label \""<<"Wrapped Cell"<<"\" at "<< (wcell_ll.x + wcell_ur.x)/2 <<","<< (wcell_ll.y + wcell_ur.y)/2 <<" center "<<std::endl;

  //plot blocks
  for(int i=0; i<stored_point_ll.size(); i++)
  {
    fout<<"\nset object \"" << i+1 << "\" rectangle from "<<stored_point_ll[i].x <<"," <<stored_point_ll[i].y<<" to "<<stored_point_ur[i].x << ","<<stored_point_ur[i].y<<" back"<<std::endl;
  }
  fout<<"\nset object \"" << stored_point_ll.size()+1 << "\" rectangle from "<<wcell_ll.x<<","<<wcell_ll.y<<" to "<<wcell_ur.x<< ","<<wcell_ur.y<<" back"<<std::endl;
  fout<<"plot "<<"["<<wcell_ll.x-4*pcell_size.width<<":"<<wcell_ur.x+4*pcell_size.width<<"] "<<"["<<wcell_ll.y-4*pcell_size.height<<":"<<wcell_ur.y+4*pcell_size.height<<"] "<<wcell_ur.y+4*pcell_size.height+1<<" title "<<"\"#GuardRing Pcells= "<<stored_point_ll.size()<<"\"";

  fout.close();
}

