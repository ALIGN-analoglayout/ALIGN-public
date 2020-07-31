#include "GuardRing.h"

//set guard ring primitive cell width and height information
void GuardRing::Pcell_info(const map<string, PnRDB::lefMacro>& lefData){
  std::cout<<"step1.0"<<std::endl;
  //std::cout<<"guard ring primitive cell name"<<guard_ring<<std::endl;
  if(lefData.find("guard_ring")==lefData.end()){
    std::cout<<"Guard_ring primitive cell error, check guard ring primitive cell in lef, gds, and const file"<<std::endl;
    assert(0);
    }
  else
  {
    const auto &uc = lefData.at("guard_ring");
    pcell_size.width = uc.macroPins[0].pinContacts[0].originBox.UR.x - uc.macroPins[0].pinContacts[0].originBox.LL.x;
    pcell_size.height = uc.macroPins[0].pinContacts[0].originBox.UR.y - uc.macroPins[0].pinContacts[0].originBox.LL.y;
    offset.width = uc.macroPins[0].pinContacts[0].originBox.LL.x;
    offset.height = uc.macroPins[0].pinContacts[0].originBox.LL.y;
    minimal_PC.width = uc.width - uc.macroPins[0].pinContacts[0].originBox.UR.x;
    minimal_PC.height = uc.height - uc.macroPins[0].pinContacts[0].originBox.UR.y;
  }
}

//set wrapped cell lower left & upper right coordinate and width & height
void GuardRing::Wcell_info(PnRDB::hierNode &node){
  std::cout<<"step2.0"<<std::endl;
  wcell_ll.x = 0;
  wcell_ll.y = 0;
  wcell_ur.x = node.width;
  wcell_ur.y = node.height;
  wcell_size.width = node.width;
  wcell_size.height = node.height;
}

void GuardRing::DRC_Read(const PnRDB::Drc_info& drc_info){
  std::cout<<"step3.0"<<std::endl;
  minimal.width = drc_info.Guardring_info.xspace;
  minimal.height = drc_info.Guardring_info.yspace;
  minimal.width = minimal.width + minimal_PC.width;
  minimal.height = minimal.height + minimal_PC.height;
}

//main function
GuardRing::GuardRing(PnRDB::hierNode &node, const map<string, PnRDB::lefMacro>& lefData, const PnRDB::Drc_info& drc_info){
  
  Pcell_info(lefData);
  Wcell_info(node);
  DRC_Read(drc_info);

  //Print wcell & pcell info
  
  std::cout << "wcell_ll[x,y] = " << wcell_ll.x << "," << wcell_ll.y << std::endl;
  std::cout << "wcell_ur[x,y] = " << wcell_ur.x << "," << wcell_ur.y << std::endl;
  std::cout << "node_width = " << node.width << std::endl;
  std::cout << "node_height = " << node.height << std::endl;
  std::cout << "node_ll[x,y] = " << node.LL.x << "," << node.LL.y << std::endl;
  std::cout << "node_ur[x,y] = " << node.UR.x << "," << node.UR.y << std::endl;
  std::cout << "pcell_ll width = " << pcell_size.width << " pcell_ll height = " << pcell_size.height << std::endl;
  std::cout << "offset width = " << offset.width << " offset height = " << offset.height << std::endl;
  std::cout << "minimal x = " << minimal.width << " minimal y = " << minimal.height << std::endl;
  assert(0);

  //calculate cell number
  int x_number, y_number;
  x_number = ceil((wcell_size.width + 2*minimal.width )/ pcell_size.width) + 2;//number of guard ring cells at the bottom or top, including corner
  y_number = ceil((wcell_size.height + 2*minimal.height)/ pcell_size.height);//excluding corner

  //store lower left coordinate of guard ring primitive cell
  //start from Pcell0 which is at the southwest corner of wrapped cell
  GuardRingDB::point southwest, southeast, northeast, northwest; //guard ring primitive cells at corner.
  southwest.x = wcell_ll.x - minimal.width - pcell_size.width - ((((x_number-2) * pcell_size.width) - (wcell_size.width + 2*minimal.width))/2);
  southwest.y = wcell_ll.y - minimal.height - pcell_size.height - (((y_number * pcell_size.height) - (wcell_size.height + 2*minimal.height))/2);

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
  {
    std::cout << "Error: misaligned!!!\n";
  }
  
  //calculate shift distance
  //GuardRingDB::point shift;
  shift.x = - southwest.x + offset.width;
  shift.y = - southwest.y + offset.height;
  
  //recalculate lower left coordinates of stored points
  for (int i_ll = 0; i_ll < stored_point_ll.size(); i_ll++) 
  {
    stored_point_ll[i_ll].x = stored_point_ll[i_ll].x + shift.x;
    stored_point_ll[i_ll].y = stored_point_ll[i_ll].y + shift.y;
  }

  //calculate upper right coordinates of stored points
  for (int i_ur = 0; i_ur < stored_point_ll.size(); i_ur++) 
  {
    temp_point.x = stored_point_ll[i_ur].x + pcell_size.width;
    temp_point.y = stored_point_ll[i_ur].y + pcell_size.height;
    stored_point_ur.push_back(temp_point);
  }
    
  std::cout << "\nThe stored points are:\n"; 
  for (int i_print = 0; i_print < stored_point_ll.size(); i_print++)
  {
    std::cout << "lower left: " << stored_point_ll[i_print].x << "," << stored_point_ll[i_print].y << " " << "upper right: " << stored_point_ur[i_print].x << "," << stored_point_ur[i_print].y <<std::endl;
  }

  //update wcell ll & ur information
  wcell_ll.x = wcell_ll.x + shift.x;
  wcell_ll.y = wcell_ll.y + shift.y;
  wcell_ur.x = wcell_ur.x + shift.x;
  wcell_ur.y = wcell_ur.y + shift.y;

  gnuplot();
  storegrhierNode(node);
  movehierNode(node);

};

//store guard ring primitive cell information into Hiernode
void GuardRing::storegrhierNode(PnRDB::hierNode &node){
  PnRDB::contact temp_contact;
  PnRDB::pin temp_pin;
  for (int i_store = 0; i_store < stored_point_ll.size(); i_store++) 
  {
    temp_gr.LL.x = stored_point_ll[i_store].x;
    temp_gr.LL.y = stored_point_ll[i_store].y;
    temp_gr.UR.x = stored_point_ur[i_store].x;
    temp_gr.UR.y = stored_point_ur[i_store].y;
    temp_gr.center.x = (stored_point_ll[i_store].x + stored_point_ur[i_store].x)/2;
    temp_gr.center.y = (stored_point_ll[i_store].y + stored_point_ur[i_store].y)/2;
    //write contact information
    //temp_contact.metal = "";
    temp_contact.placedBox.LL.x = stored_point_ll[i_store].x;
    temp_contact.placedBox.LL.y = stored_point_ll[i_store].y;
    temp_contact.placedBox.UR.x = stored_point_ur[i_store].x;
    temp_contact.placedBox.UR.y = stored_point_ur[i_store].y;
    temp_contact.placedCenter.x = temp_gr.center.x;
    temp_contact.placedCenter.y = temp_gr.center.y;
    temp_gr.interMetals.push_back(temp_contact);
    //Write pin information
    temp_pin.name = "";
    temp_pin.type = "";
    temp_pin.use = "";
    temp_pin.pinContacts.push_back(temp_contact);
    temp_gr.blockPins.push_back(temp_pin);
    //Write node GuardRings information
    node.GuardRings.push_back(temp_gr);
  }
  //return node;
}

//return hiernode for movement
PnRDB::hierNode GuardRing::movehierNode(PnRDB::hierNode &node){
  //node.LL.x = 0;
  //node.LL.y = 0;
  //node.UR.x = node.LL.x + node.width;
  //node.UR.y = node.LL.y + node.height;
  node.width += 2*shift.x;
  node.height += 2*shift.y;
  // LL
  // movepoint(node.LL);
  // UR
  // movepoint(node.UR);
  // Blocks
  movevecblockcomplex(node.Blocks);
  //Nets
  for (int i_nets = 0; i_nets < node.Nets.size(); i_nets++) 
  {
    movenet(node.Nets[i_nets]);
  }
  //Terminals
  for (int i_ter = 0; i_ter < node.Terminals.size(); i_ter++) 
  {
    moveterminal(node.Terminals[i_ter]);
  }
  //PowerNets
  movevecpowernet(node.PowerNets);
  //blockPins
  movevecpin(node.blockPins);
  //interMetals
  moveveccontact(node.interMetals);
  //interVias
  movevecvia(node.interVias);
  //PnRAS
  for (int i_pnras = 0; i_pnras < node.PnRAS.size(); i_pnras++) 
  {
    movevecblockcomplex(node.PnRAS[i_pnras].Blocks);
    for (int i_net = 0; i_net < node.PnRAS[i_pnras].Nets.size(); i_net++) 
    {
    movenet(node.PnRAS[i_pnras].Nets[i_net]);
    }
    for (int i_terminal = 0; i_terminal < node.PnRAS[i_pnras].Terminals.size(); i_terminal++) 
    {
    moveterminal(node.PnRAS[i_pnras].Terminals[i_terminal]);
    }
    movepoint(node.PnRAS[i_pnras].LL);
    movepoint(node.PnRAS[i_pnras].UR);
  }
  //SNets
  for (int i_snets = 0; i_snets < node.SNets.size(); i_snets++) 
  {
    movenet(node.SNets[i_snets].net1);
    movenet(node.SNets[i_snets].net2);
  }
  return node;
}

//move datatype point with shift
void GuardRing::movepoint(PnRDB::point &point){
  point.x = point.x + shift.x;
  point.y = point.y + shift.y;
}

//move datatype bbox
void GuardRing::movebbox(PnRDB::bbox &bbox){
  movepoint(bbox.LL);
  movepoint(bbox.UR);
}

//move datatype contact
void GuardRing::movecontact(PnRDB::contact &contact){
  movebbox(contact.placedBox);
  movepoint(contact.placedCenter);
}

//move datatype block
void GuardRing::moveblock(PnRDB::block &block){
  movebbox(block.placedBox);
  movepoint(block.placedCenter);
  movevecpowernet(block.PowerNets);
  movevecpin(block.blockPins);
  moveveccontact(block.interMetals);
  movevecvia(block.interVias);
  movevecpin(block.dummy_power_pin);
}

//move datatype terminal
void GuardRing::moveterminal(PnRDB::terminal &terminal){
  moveveccontact(terminal.termContacts);
}

//move datatype net
void GuardRing::movenet(PnRDB::net &net){
  moveveccontact(net.segments);
  moveveccontact(net.interVias);
  movevecmetal(net.path_metal);
  movevecvia(net.path_via);
  for (int i_cc = 0; i_cc < net.connectedContact.size(); i_cc++) 
  {
    movecontact(net.connectedContact[i_cc].conTact);
  }
}

//move datatype metal
void GuardRing::movemetal(PnRDB::Metal &metal){
  for (int i_lp = 0; i_lp < metal.LinePoint.size(); i_lp++) 
  {
    movepoint(metal.LinePoint[i_lp]);
  }
  movecontact(metal.MetalRect);
}

//move datatype via
void GuardRing::movevia(PnRDB::Via &via){
  movepoint(via.placedpos);
  movecontact(via.UpperMetalRect);
  movecontact(via.LowerMetalRect);
  movecontact(via.ViaRect);
}

//move datatype pin
void GuardRing::movepin(PnRDB::pin &pin){
  moveveccontact(pin.pinContacts);
  movevecvia(pin.pinVias);
}

//move datatype powernet
void GuardRing::movepowernet(PnRDB::PowerNet &powernet){
  movevecpin(powernet.Pins);
  movevecmetal(powernet.path_metal);
  movevecvia(powernet.path_via);
}

//move datatype vector<contact>
void GuardRing::moveveccontact(std::vector<PnRDB::contact> &contactvector){
  for (int i_veccon = 0; i_veccon < contactvector.size(); i_veccon++) 
  {
    movecontact(contactvector[i_veccon]);
  }
}

//move datatype vector<via>
void GuardRing::movevecvia(std::vector<PnRDB::Via> &vecvia){
  for (int i_vecvia = 0; i_vecvia < vecvia.size(); i_vecvia++) 
  {
    movevia(vecvia[i_vecvia]);
  }
}

//move datatype vector<pin>
void GuardRing::movevecpin(std::vector<PnRDB::pin> &vecpin){
  for (int i_vecpin = 0; i_vecpin < vecpin.size(); i_vecpin++) 
  {
    movepin(vecpin[i_vecpin]);
  }
}

//move datatype vector<powernet>
void GuardRing::movevecpowernet(std::vector<PnRDB::PowerNet> &vecpowernet){
  for (int i_vecpow = 0; i_vecpow < vecpowernet.size(); i_vecpow++) 
  {
    movepowernet(vecpowernet[i_vecpow]);
  }
}

//move datatype vector<metal>
void GuardRing::movevecmetal(std::vector<PnRDB::Metal> &vecmetal){
  for (int i_vecmet = 0; i_vecmet < vecmetal.size(); i_vecmet++) 
  {
    movemetal(vecmetal[i_vecmet]);
  }
}

//move datatype vector<blockcomplex>
void GuardRing::movevecblockcomplex(std::vector<PnRDB::blockComplex> &vecbc){
  for (int i_vecbc = 0; i_vecbc < vecbc.size(); i_vecbc++) 
  {
    for (int j_inst = 0; j_inst < vecbc[i_vecbc].instance.size(); j_inst++) 
    {
      moveblock(vecbc[i_vecbc].instance[j_inst]);
    }
  }
}



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

