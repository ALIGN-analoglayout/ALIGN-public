#include "GuardRing.h"

GuardRing::Pcell_info(int xs, int ys){
  pcell_size.xs = xs;
  pcell_size.ys = ys;
};

GuardRing::Wcell_info(PnRDB::hierNode &node){
  wcell_ll.x = node.LL.x;
  wcell_ll.y = node.LL.y;
  wcell_size.xs = node.UR.x - node.LL.x;
  wcell_size.ys = node.UR.y - node.LL.y;
}

GuardRing::GuardRing(){
  //calculate cell number
  int x_number, y_number, pcell_number;
  if (wcell_size.xs % pcell_size.xs == 0)
    x_number = (wcell_size.xs / pcell_size.xs) + 2;
  else
    x_number = (wcell_size.xs / pcell_size.xs) + 3;
  if (wcell_size.ys % pcell_size.ys == 0)
    y_number = (wcell_size.ys / pcell_size.ys);
  else
    y_number = (wcell_size.ys / pcell_size.ys) + 1;
  pcell_number = (x_number + y_number) * 2;

  //store lower left coordinate of guard ring primitive cell
  //start from Pcell0 which is at the southwest corner of wrapped cell
  int southwestx = wcell_ll.x - pcell_size.xs - (((x_number-2) * pcell_size.xs) - wcell_size.xs)/2;
  int southwesty = wcell_ll.y - pcell_size.ys - (((y_number * pcell_size.ys) - wcell_size.ys)/2;
  temp_point.x = swx;
  temp_point.y = swy;
  stored_point.push_back(temp_point);
  return;

  //store south side pcell's coordinates
  for (int i_s=1; i_s<x_number; i_s++)
  {
    temp_point.x = southwestx + i_s*pcell_size.xs;
    temp_point.y = southwesty;
    stored_point.push_back(temp_point);
  }
  int southeastx = temp_point.x;
  int southeasty = temp_point.y;

  //store east side pcell's coordinates
  for (int i_e=1; i_e< y_number+2; i_e++)
  {
    temp_point.x = southeastx;
    temp_point.y = southeasty + (i_e)*pcell_size.ys;
    stored_point.push_back(temp_point);
  }
  int northeastx = temp_point.x;
  int northeasty = temp_point.y;

  //store north side pcell's coordinates
  for (int i_n=1; i_n<x_number; i_n++)
  {
    temp_point.x = northeastx - i_n*pcell_size.xs;
    temp_point.y = northeasty;
    stored_point.push_back(temp_point);
  }
  int northwestx = temp_point.x;
  int northwesty = temp_point.y;

  //Store west side pcells' coordinate
  for (int i_w=1; i_w<y_number+1; i_w++)
  {
    temp_point.x = northwestx;
    temp_point.y = northwesty - i_w*pcell_size.ys;
    stored_point.push_back(temp_point);
  }

  if(northwestx != southwestx)
    cout << "Error: misaligned!!!\n"

  cout << "\nThe stored points (lower left coordinates) are:\n"; 
  for (int i_print = 0; i_print < stored_point.size(); i_print++) 
    cout << " " << stored_point[i_print].x << "," << stored_point[i_print].y << endl;
  
  return 0;
};

