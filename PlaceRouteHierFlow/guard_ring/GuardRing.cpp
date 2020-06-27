#include "GuardRing.h"

GuardRing::Pcell_info(int pcell_width, int pcell_length){
  pcell_size.width = pcell_width;
  pcell_size.length = pcell_length;
};

GuardRing::Wcell_info(PnRDB::hierNode &node){
  wcell_ll.x = node.LL.x;
  wcell_ll.y = node.LL.y;
  wcell_ur.x = node.UR.x;
  wcell_ur.y = node.UR.y;
  wcell_size.width = node.UR.x - node.LL.x;
  wcell_size.length = node.UR.y - node.LL.y;
}

GuardRing::GuardRing(int Minimal_x, int Minimal_y){
  //calculate cell number
  int x_number, y_number;
  x_number = ceil(wcell_size.width / pcell_size.width) + 2;
  y_number = ceil(wcell_size.length / pcell_size.length);

  //store lower left coordinate of guard ring primitive cell
  //start from Pcell0 which is at the southwest corner of wrapped cell
<<<<<<< HEAD
  GuardRingDB::point southwest, southeast, northeast, northwest; //guard ring primitive cells at corner.
  if (((((x_number-2) * pcell_size.width) - wcell_size.width)/2) < Minimal_x)
    southwest.x = wcell_ll.x - pcell_size.width - Minimal_x;
  else
    southwest.x = wcell_ll.x - pcell_size.width - (((x_number-2) * pcell_size.width) - wcell_size.width)/2;
  if (((((x_number-2) * pcell_size.width) - wcell_size.width)/2) < Minimal_y)
    southwest.y = wcell_ll.y - pcell_size.length - Minimal_y;
  else
    southwest.y = wcell_ll.y - pcell_size.length - (((y_number * pcell_size.length) - wcell_size.length)/2;
  temp_point.x = southwest.x;
  temp_point.y = southwest.y;
  stored_point_ll.push_back(temp_point);
=======
  int southwestx = wcell_ll.x - pcell_size.xs - (((x_number-2) * pcell_size.xs) - wcell_size.xs)/2;
  int southwesty = wcell_ll.y - pcell_size.ys - (((y_number * pcell_size.ys) - wcell_size.ys)/2;
  temp_point.x = southwestx;
  temp_point.y = southwesty;
  stored_point.push_back(temp_point);
>>>>>>> 7dccd45ab468beda027d8f924a1ed5f729db481c
  return;

  //store south side pcell's coordinates
  for (int i_s=1; i_s<x_number; i_s++)
  {
    temp_point.x = southwestx + i_s*pcell_size.width;
    temp_point.y = southwesty;
    stored_point_ll.push_back(temp_point);
  }
  southeast.x = temp_point.x;
  southeast.y = temp_point.y;

  //store east side pcell's coordinates
  for (int i_e=1; i_e< y_number+2; i_e++)
  {
    temp_point.x = southeastx;
    temp_point.y = southeasty + (i_e)*pcell_size.length;
    stored_point_ll.push_back(temp_point);
  }
  northeast.x = temp_point.x;
  northeast.y = temp_point.y;

  //store north side pcell's coordinates
  for (int i_n=1; i_n<x_number; i_n++)
  {
    temp_point.x = northeastx - i_n*pcell_size.width;
    temp_point.y = northeasty;
    stored_point_ll.push_back(temp_point);
  }
  northwest.x = temp_point.x;
  northwest.y = temp_point.y;

  //Store west side pcells' coordinate
  for (int i_w=1; i_w<y_number+1; i_w++)
  {
    temp_point.x = northwestx;
    temp_point.y = northwesty - i_w*pcell_size.length;
    stored_point_ll.push_back(temp_point);
  }

  if(northwest.x != southwest.x)
    cout << "Error: misaligned!!!\n"

  //calculate upper right coordinates of stored points
  for (int i_ur = 0; i_ur < stored_point_ll.size(); i_ur++) 
  {
    temp_point.x = stored_point_ll[i_ur].x + pcell_size.width;
    temp_point.y = stored_point_ll[i_ur].y + pcell_size.length;
    stored_point_ur.push_back(temp_point);
  }
    
  cout << "\nThe stored points are:\n"; 
  for (int i_print = 0; i_print < stored_point_ll.size(); i_print++) 
    cout << "lower left: " << stored_point_ll[i_print].x << "," << stored_point_ll[i_print].y << " " << "upper right: " << stored_point_ur[i_print].x << "," << stored_point_ur[i_print].y <<endl;

};

GuardRing::gnuplot(){
  //Plot GuardRing Place
  cout<<"Placer-Router-GuardRing-Info: create gnuplot file"<<endl;
  ofstream fout;
  fout.open("guardringplot");

  //set title
  fout<<"#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)"<<endl;
  fout<<"\nset title\" #GuardRing Pcells= "<<stored_point_ll.size()<<" \""<<endl;
  fout<<"\nset nokey"<<endl;
  fout<<"#   Uncomment these two lines starting with \"set\""<<endl;
  fout<<"#   to save an EPS file for inclusion into a latex document"<<endl;
  fout<<"# set terminal postscript eps color solid 20"<<endl;
  fout<<"# set output \"result.eps\""<<endl<<endl;
  fout<<"#   Uncomment these two lines starting with \"set\""<<endl;
  fout<<"#   to save a PS file for printing"<<endl;
  fout<<"set term png"<<endl;
  fout<<"set output \"result.png\""<<endl;

  //set range
  fout<<"\nset xrange ["<<wcell_ll.x-4*pcell_size.width<<":"<<wcell_ur.x+4*pcell_size.width<<"]"<<endl;
  fout<<"\nset yrange ["<<wcell_ll.y-4*pcell_size.length<<":"<<wcell_ur.y+4*pcell_size.length<<"]"<<endl;

  //set label for Pcells
  for(int i=0; i<stored_point_ll.size(); i++)
  {
	  fout<<"\nset label \"" << i <<"\" at "<<(stored_point_ll[i].x + stored_point_ur[i].x)/2<<","<<(stored_point_ll[i].y + stored_point_ur[i].y)/2<<" center "<<endl;
  }
	//set label for Wrapped cell
	fout<<"\nset label \""<<"Wrapped Cell"<<"\" at "<< (wcell_ll.x + wcell_ur.x)/2 <<","<< (wcell_ll.y + wcell_ur.y)/2 <<" center "<<endl;

  //plot blocks
  for(int i=0; i<stored_point_ll.size(); i++)
  {
    fout<<"\nset object \"" << i+1 << "\" rectangle from "<<stored_point_ll[i].x <<"," <<stored_point_ll[i].y<<" to "<<stored_point_ur[i].x << ","<<stored_point_ur[i].y<<" back"<<endl;
  }
  fout<<"\nset object \"" << stored_point_ll.size()+1 << "\" rectangle from "<<wcell_ll.x<<","<<wcell_ll.y<<" to "<<wcell_ur.x<< ","<<wcell_ur.y<<" back"<<endl;
  fout<<"plot "<<"["<<wcell_ll.x-4*pcell_size.width<<":"<<wcell_ur.x+4*pcell_size.width<<"] "<<"["<<wcell_ll.y-4*pcell_size.length<<":"<<wcell_ur.y+4*pcell_size.length<<"] "<<wcell_ur.y+4*pcell_size.length+1<<" title "<<"\"#GuardRing Pcells= "<<stored_point_ll.size()<<"\"";

  fout.close();
}

