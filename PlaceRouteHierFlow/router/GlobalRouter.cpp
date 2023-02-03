#include "GlobalRouter.h"

#include <cassert>

// wbxu: 20190708 the following codes are to enable ILP to choose candidates
// extern "C"
//{
//#include <stdio.h>
//#include "lp_lib.h"
//#define LPSOLVEAPIFROMLIBDEF
//#include "lp_explicit.h"
//}
// wbxu-end?

GlobalRouter::GlobalRouter(){

};

GlobalRouter::GlobalRouter(PnRDB::hierNode& node, PnRDB::Drc_info& drcData, int Lmetal, int Hmetal, const std::string& binaryDIR) {
  // std::cout<<"Start of gr" <<std::endl ;
  getDRCdata(drcData);
  getData(node, Lmetal, Hmetal);
  // std::cout<<"End of gr" <<std::endl ;
  //  //update Nets, Blocks according to node. LL, UR;
  placeTerminals();
  listSegments(binaryDIR);
  // for(unsigned int i=0;i<node.Nets.size();i++) {
  // std::cout<<"Net "<<i<<" has segment "<<this->Nets.at(i).seg.size()<<std::endl;
  //}
  //
  //  //CreateGrid for within the region LL, UR
  // std::cout<<"Router-Info: start to create global grid "<<std::endl;
  Grid grid(this->drc_info, this->LL, this->UR, Lmetal, Hmetal, this->grid_scale);
  // std::cout<<"Router-Info: handling internal metals "<<std::endl;
  // grid.InactiveGlobalInternalMetal(this->Blocks); //move this to two part plist create by glocal router, inactive by grid with plist
  // std::cout<<"Router-Info: end of creating grid "<<std::endl;
  //
  //
  for (unsigned int i = 0; i < this->Nets.size(); i++) {
    std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp> Smap;
    for (unsigned int j = 0; j < this->Nets.at(i).seg.size(); j++) {
      std::vector<RouterDB::contact> Terminal_contact =
          grid.setSrcDest(this->Nets.at(i).seg.at(j).sourceList, this->Nets.at(i).seg.at(j).destList, this->width, this->height, Smap);
      // std::cout<<"Info: set source dest"<<std::endl;
      if (this->isTop && Nets[i].isTerminal && Terminal_contact.size() > 0) {
        Terminals[Nets[i].terminal_idx].termContacts.clear();
        // std::cout<<"Info:: update terminal "<<Nets[i].terminal_idx<<" contact\n";
        for (unsigned int k = 0; k < Terminal_contact.size(); k++) {
          Terminals[Nets[i].terminal_idx].termContacts.push_back(Terminal_contact[k]);
          // std::cout<<"\tinsert terminal metal "<<Terminals[Nets[i].terminal_idx].termContacts.back().metal<<"
          // "<<Terminals[Nets[i].terminal_idx].termContacts.back().placedLL.x<<", "<<Terminals[Nets[i].terminal_idx].termContacts.back().placedLL.y<<"
          // "<<Terminals[Nets[i].terminal_idx].termContacts.back().placedUR.x<<", "<<Terminals[Nets[i].terminal_idx].termContacts.back().placedUR.y<<std::endl;
        }
      }
      grid.ActivateSourceDest();
      // std::vector<RouterDB::point> newArea=GetMaxMinSrcDest( this->Nets.at(i).seg.at(j).sourceList, this->Nets.at(i).seg.at(j).destList );
      std::vector<RouterDB::point> newArea = grid.GetMaxMinSrcDest();
      // std::cout<<"area-> "<< newArea.at(0).x<<" "<<newArea.at(0).y<<" "<<newArea.at(1).x<<" " <<newArea.at(1).y<<std::endl;
      grid.PrepareGraphVertices(newArea.at(0).x, newArea.at(0).y, newArea.at(1).x, newArea.at(1).y);
      // std::cout<<"Start graph (global router), ";
      // Graph graph(grid, this->path_number);
      Graph graph(grid);
      bool pathMark = graph.FindFeasiblePath(grid, this->path_number);
      // std::cout<<"End graph (global router)"<<std::endl;
      if (pathMark) {
        std::vector<std::vector<RouterDB::Metal> > physical_path = graph.ConvertPathintoPhysical(grid);
        UpdateCandidate(physical_path, i, j);
        GetPhsical_Metal_Via(i, j);
      }
      grid.InactivateSourceDest();  // added by yg 3/12
    }
  }
  //  for(net i seg j){
  //    //create
  //    (source, dest)=UpdateLLURSD(i,j); //for each seg of net, create LL_graph, UR_graph && Sour Dest.
  //    std::vector<RouterDB::contact> Terminal_contact=grid.setSrcDest();
  //    if(Nets[i].terminal_idx ==1){
  //       Terminals.pinContacts.clear();
  //       for(int k=0;k<Terminal_contact.size();k++){
  //             Terminals[Nets[i].terminal_idx].pinContacts.push_back(Terminal_contact[k]);
  //           }
  //    }
  //    grid.activeSourceDest(source, dest);
  //    grid.PrepareGraphVertices(LLx, LLy, URx, URy);
  //    //grid.UpdateLLURSD_global(*this); //Update LL_graph, UR_graph Source & Dest
  //    //find shortest path && get shortest path
  //    //need LLURSD
  //    Graph graph(grid);
  //    path=graph.GetShorestPath();
  //    grid.inactiveSourceDest(srouce, dest);
  //    physical=graph.ConvertPathintoPhysical(path)
  //    UpdateCandidate(physical);
  //    //after this return path to Nets
  //    }
  //

  // wbxu: 20190708 the following codes is set to always choose the first candidate for each segment
  for (unsigned int i = 0; i < this->Nets.size(); ++i) {
    for (unsigned int j = 0; j < this->Nets.at(i).seg.size(); ++j) {
      this->Nets.at(i).seg.at(j).candis.at(0).chosen = true;
      this->Nets.at(i).seg.at(j).chosenCand = 0;
      // std::cout<<"choose: "<<i<<" net "<<j<<" seg "<<0<<" cand "<<std::endl;
    }
  }
  // wbxu-end
  // wbxu: 20190708 the following codes are to use ILP to choose candidates
  // int sb=250;
  // ILPSolveRouting();
  // wbxu-end

  //  DesignRuleCheck();
  //  //LP solver
  //  LP_solver();
  //
  ReturnHierNode(node);
  //  //after this return path to Nets
  //  UpdateHierNode();
};

// std::vector<RouterDB::point> GlobalRouter::GetMaxMinSrcDest(std::vector<RouterDB::SinkData>& source, std::vector<RouterDB::SinkData>& dest) {
//  int x=INT_MAX, y=INT_MAX, X=INT_MIN, Y=INT_MIN;
//  for(std::vector<RouterDB::SinkData>::iterator it=source.begin(); it!=source.end(); it++ ) {
//    for(std::vector<RouterDB::point>::iterator it2=it->coord.begin(); it2!=it->coord.end(); it2++) {
//      if(it2->x>X) {X=it2->x;}
//      if(it2->x<x) {x=it2->x;}
//      if(it2->y>Y) {Y=it2->y;}
//      if(it2->y<y) {y=it2->y;}
//    }
//  }
//  for(std::vector<RouterDB::SinkData>::iterator it=dest.begin(); it!=dest.end(); it++ ) {
//    for(std::vector<RouterDB::point>::iterator it2=it->coord.begin(); it2!=it->coord.end(); it2++) {
//      if(it2->x>X) {X=it2->x;}
//      if(it2->x<x) {x=it2->x;}
//      if(it2->y>Y) {Y=it2->y;}
//      if(it2->y<y) {y=it2->y;}
//    }
//  }
//  int xMar, yMar;
//  if(this->drc_info.Metal_info.at(this->highest_metal).direct==0) { // vertical
//    xMar=this->drc_info.Metal_info.at(this->highest_metal).grid_unit_x*this->grid_scale;
//    yMar=this->drc_info.Metal_info.at(this->highest_metal-1).grid_unit_y*this->grid_scale;
//  } else { // horizontal
//    yMar=this->drc_info.Metal_info.at(this->highest_metal).grid_unit_y*this->grid_scale;
//    xMar=this->drc_info.Metal_info.at(this->highest_metal-1).grid_unit_x*this->grid_scale;
//  }
//  RouterDB::point newnode;
//  std::vector<RouterDB::point> newlist;
//  newnode.x=x-2*xMar; newnode.y=y-2*yMar;
//  if(newnode.x<0) {newnode.x=0;}
//  if(newnode.y<0) {newnode.y=0;}
//  newlist.push_back(newnode);
//  newnode.x=X+2*xMar; newnode.y=Y+2*yMar;
//  if(newnode.x>this->width) {newnode.x=this->width;}
//  if(newnode.y>this->height) {newnode.y=this->height;}
//  newlist.push_back(newnode);
//  return newlist;
//};

/*

void GlobalRouter::GenerateLLUPSD(){



};
*/

// added by wbxu
void GlobalRouter::placeTerminals() {
  // Limitation: assume that only 1 terminal for each net
  // bool mark;
  int mj;
  for (unsigned int i = 0; i < this->Nets.size(); i++) {
    this->Nets.at(i).isTerminal = false;
    bool mark = false;
    for (unsigned int j = 0; j < this->Nets.at(i).connected.size(); j++) {
      if (this->Nets.at(i).connected.at(j).type == RouterDB::TERMINAL) {
        mj = j;
        mark = true;
        break;
      }
    }
    if (mark) {
      if (!this->isTop) {
        this->Nets.at(i).connected.erase(this->Nets.at(i).connected.begin() + mj);
        this->Nets.at(i).degree--;
      }
      this->Nets.at(i).isTerminal = true;
    }
  }
}

void GlobalRouter::listSegments(const std::string& binaryDIR) {
  int num_scale = 1000000;
  std::string binary_directory = binaryDIR + "router";
  char* getcwd_result = getcwd(cwd, sizeof(cwd));
  assert(!getcwd_result);
  std::string string_cwd(cwd);
  std::string string_steiner =
      binary_directory + "/FastSteinerUM/steiner -rectilinear -seed 0 <" + string_cwd + "/output.txt -print_tree >" + string_cwd + "/vals";
  // std::cout<<string_steiner<<std::endl;

  RouterDB::point newnode;
  // std::string  temp;
  std::string segnaming, dummy;
  std::ofstream myfile, matlabfile;
  std::ifstream input;
  // matlabfile.open("output_matlab.txt");
  for (unsigned int i = 0; i < this->Nets.size(); i++) {
    // added by yg
    std::vector<std::pair<int, int> > original_coord;
    std::vector<std::pair<int, int> > stiner_coord;
    std::pair<int, int> coord;
    // added by yg
    if (this->Nets.at(i).degree == 0 || this->Nets.at(i).degree == 1) {
      // std::cout<<"Router-Info: no need to route net"<<this->Nets.at(i).netName<<std::endl;
      this->Nets.at(i).numSeg = 0;
      this->Nets.at(i).seg.clear();
    } else if (this->Nets.at(i).degree > 2) {
      // std::cout<<"Router-Info: decompose net "<<this->Nets.at(i).netName<<std::endl;
      myfile.open("output.txt");
      myfile << this->Nets.at(i).degree;
      myfile << "\n";
      for (unsigned int p = 0; p < this->Nets.at(i).connected.size(); p++) {
        if (this->Nets.at(i).connected.at(p).type == RouterDB::BLOCK) {
          // for multi-contact pins, pick one contact to represent all contacts
          int curr = this->Blocks.at(this->Nets[i].connected[p].iter2).pins.at(this->Nets[i].connected[p].iter).pinContacts.size() / 2;
          coord.first = this->Blocks.at(this->Nets[i].connected[p].iter2).pins.at(this->Nets[i].connected[p].iter).pinContacts.at(curr).placedCenter.x;
          coord.second = this->Blocks.at(this->Nets[i].connected[p].iter2).pins.at(this->Nets[i].connected[p].iter).pinContacts.at(curr).placedCenter.y;
          original_coord.push_back(coord);
          myfile << coord.first;
          myfile << " ";
          myfile << coord.second;
          myfile << "\n";
        } else if (this->Nets.at(i).connected.at(p).type == RouterDB::TERMINAL) {
          if (this->isTop) {
            coord.first = this->Terminals.at(this->Nets[i].connected[p].iter).termContacts[0].placedCenter.x;
            coord.second = this->Terminals.at(this->Nets[i].connected[p].iter).termContacts[0].placedCenter.y;
            original_coord.push_back(coord);
            myfile << coord.first;
            myfile << " ";
            myfile << coord.second;
            myfile << "\n";
          }
        }
      }
      myfile.close();
      int rc = system(string_steiner.c_str());
      assert(rc == 0);
      // system("/bin/cat vals >> all_vals");
      // system("/bin/cat output.txt >> all_output.txt");
      input.open("vals");
      input >> this->Nets.at(i).numSeg;
      for (int a = 0; a < this->Nets.at(i).numSeg; a++) {
        RouterDB::Segment tempSeg;
        RouterDB::point tmpsource, tmpdest;
        input >> dummy;
        tmpsource.x = get_number(dummy) / num_scale;
        input >> dummy;
        tmpsource.y = get_number(dummy) / num_scale;
        input >> dummy;
        input >> dummy;
        tmpdest.x = get_number(dummy) / num_scale;
        input >> dummy;
        tmpdest.y = get_number(dummy) / num_scale;
        for (unsigned int p = 0; p < this->Nets.at(i).connected.size(); p++) {
          int iter2 = this->Nets.at(i).connected.at(p).iter2;
          int iter = this->Nets.at(i).connected.at(p).iter;
          int xx, yy;
          if (this->Nets.at(i).connected.at(p).type == RouterDB::BLOCK) {  // Block pins
            int cur = this->Blocks[iter2].pins[iter].pinContacts.size() / 2;
            int csize = this->Blocks[iter2].pins[iter].pinContacts.size();
            xx = this->Blocks[iter2].pins[iter].pinContacts[cur].placedCenter.x;
            yy = this->Blocks[iter2].pins[iter].pinContacts[cur].placedCenter.y;
            if (tmpsource.x == xx && tmpsource.y == yy) {  // source matched
              for (int w = 0; w < csize; w++) {
                tempSeg.sourceList.resize(tempSeg.sourceList.size() + 1);
                tempSeg.sourceList.back().metalIdx = this->Blocks[iter2].pins[iter].pinContacts[w].metal;
                newnode.x = this->Blocks[iter2].pins[iter].pinContacts[w].placedLL.x;
                newnode.y = this->Blocks[iter2].pins[iter].pinContacts[w].placedLL.y;
                tempSeg.sourceList.back().coord.push_back(newnode);
                newnode.x = this->Blocks[iter2].pins[iter].pinContacts[w].placedUR.x;
                newnode.y = this->Blocks[iter2].pins[iter].pinContacts[w].placedUR.y;
                tempSeg.sourceList.back().coord.push_back(newnode);
              }
              tempSeg.sourceType.type = RouterDB::BLOCK;
              tempSeg.sourceType.iter = iter;
              tempSeg.sourceType.iter2 = iter2;
            } else if (tmpdest.x == xx && tmpdest.y == yy) {  // dest matched
              for (int w = 0; w < csize; w++) {
                tempSeg.destList.resize(tempSeg.destList.size() + 1);
                tempSeg.destList.back().metalIdx = this->Blocks[iter2].pins[iter].pinContacts[w].metal;
                newnode.x = this->Blocks[iter2].pins[iter].pinContacts[w].placedLL.x;
                newnode.y = this->Blocks[iter2].pins[iter].pinContacts[w].placedLL.y;
                tempSeg.destList.back().coord.push_back(newnode);
                newnode.x = this->Blocks[iter2].pins[iter].pinContacts[w].placedUR.x;
                newnode.y = this->Blocks[iter2].pins[iter].pinContacts[w].placedUR.y;
                tempSeg.destList.back().coord.push_back(newnode);
              }
              tempSeg.destType.type = RouterDB::BLOCK;
              tempSeg.destType.iter = iter;
              tempSeg.destType.iter2 = iter2;
            }
          } else if (this->Nets.at(i).connected.at(p).type == RouterDB::TERMINAL && this->isTop) {
            // only top level has terminals
            xx = this->Terminals[iter].termContacts[0].placedCenter.x;
            yy = this->Terminals[iter].termContacts[0].placedCenter.y;
            if (tmpsource.x == xx && tmpsource.y == yy) {  // source matched
              tempSeg.sourceList.resize(tempSeg.sourceList.size() + 1);
              tempSeg.sourceList.back().metalIdx = 0;
              newnode.x = xx;
              newnode.y = yy;
              tempSeg.sourceList.back().coord.push_back(newnode);
              tempSeg.sourceType.type = RouterDB::TERMINAL;
              tempSeg.sourceType.iter = iter;
              tempSeg.sourceType.iter2 = -1;
            } else if (tmpdest.x == xx && tmpdest.y == yy) {
              tempSeg.destList.resize(tempSeg.destList.size() + 1);
              tempSeg.destList.back().metalIdx = 0;
              newnode.x = xx;
              newnode.y = yy;
              tempSeg.destList.back().coord.push_back(newnode);
              tempSeg.destType.type = RouterDB::TERMINAL;
              tempSeg.destType.iter = iter;
              tempSeg.destType.iter2 = -1;
            }
          }
        }
        if (tempSeg.sourceList.empty()) {
          tempSeg.sourceList.resize(tempSeg.sourceList.size() + 1);
          tempSeg.sourceList.back().metalIdx = -1;
          newnode.x = tmpsource.x;
          newnode.y = tmpsource.y;
          tempSeg.sourceList.back().coord.push_back(newnode);
          tempSeg.sourceType.type = RouterDB::TERMINAL;
          tempSeg.sourceType.iter = -2;
          tempSeg.sourceType.iter2 = -1;
        }
        if (tempSeg.destList.empty()) {
          tempSeg.destList.resize(tempSeg.destList.size() + 1);
          tempSeg.destList.back().metalIdx = -1;
          newnode.x = tmpdest.x;
          newnode.y = tmpdest.y;
          tempSeg.destList.back().coord.push_back(newnode);
          tempSeg.destType.type = RouterDB::TERMINAL;
          tempSeg.destType.iter = -2;
          tempSeg.destType.iter2 = -1;
        }
        input >> dummy;
        // temp=a+1;
        input >> dummy;
        if (dummy != "NUM_TERM:") {
          this->Nets.at(i).numSeg = get_number(dummy);
        }
        this->Nets.at(i).seg.push_back(tempSeg);
      }
      // segnaming=nets.at(i).netName+temp;
      input.close();
    } else {  // degree==2
      // std::cout<<"Router-Info: 2-pin net "<<this->Nets.at(i).netName<<std::endl;
      RouterDB::Segment tempSeg;
      this->Nets.at(i).numSeg = 1;
      // source
      if (this->Nets.at(i).connected.at(0).type == RouterDB::BLOCK) {
        int iter2 = this->Nets.at(i).connected.at(0).iter2;
        int iter = this->Nets.at(i).connected.at(0).iter;
        int cur = this->Blocks[iter2].pins[iter].pinContacts.size() / 2;
        int csize = this->Blocks[iter2].pins[iter].pinContacts.size();
        coord.first = this->Blocks[iter2].pins[iter].pinContacts[cur].placedCenter.x;
        coord.second = this->Blocks[iter2].pins[iter].pinContacts[cur].placedCenter.y;
        original_coord.push_back(coord);
        for (int w = 0; w < csize; w++) {
          tempSeg.sourceList.resize(tempSeg.sourceList.size() + 1);
          tempSeg.sourceList.back().metalIdx = this->Blocks[iter2].pins[iter].pinContacts[w].metal;
          newnode.x = this->Blocks[iter2].pins[iter].pinContacts[w].placedLL.x;
          newnode.y = this->Blocks[iter2].pins[iter].pinContacts[w].placedLL.y;
          tempSeg.sourceList.back().coord.push_back(newnode);
          newnode.x = this->Blocks[iter2].pins[iter].pinContacts[w].placedUR.x;
          newnode.y = this->Blocks[iter2].pins[iter].pinContacts[w].placedUR.y;
          tempSeg.sourceList.back().coord.push_back(newnode);
        }
        tempSeg.sourceType.type = RouterDB::BLOCK;
        tempSeg.sourceType.iter = iter;
        tempSeg.sourceType.iter2 = iter2;
      } else if (this->Nets.at(i).connected.at(0).type == RouterDB::TERMINAL && isTop) {
        tempSeg.sourceList.resize(tempSeg.sourceList.size() + 1);
        tempSeg.sourceList.back().metalIdx = 0;
        newnode.x = this->Terminals[Nets[i].connected[0].iter].termContacts[0].placedCenter.x;
        newnode.y = this->Terminals[Nets[i].connected[0].iter].termContacts[0].placedCenter.y;
        tempSeg.sourceList.back().coord.push_back(newnode);
        coord.first = newnode.x;
        coord.second = newnode.y;
        original_coord.push_back(coord);
        tempSeg.sourceType.type = RouterDB::TERMINAL;
        tempSeg.sourceType.iter = Nets[i].connected[0].iter;
        tempSeg.sourceType.iter2 = -1;
      }
      // dest
      if (this->Nets.at(i).connected.at(1).type == RouterDB::BLOCK) {
        int iter2 = this->Nets.at(i).connected.at(1).iter2;
        int iter = this->Nets.at(i).connected.at(1).iter;
        int cur = this->Blocks[iter2].pins[iter].pinContacts.size() / 2;
        int csize = this->Blocks[iter2].pins[iter].pinContacts.size();
        coord.first = this->Blocks[iter2].pins[iter].pinContacts[cur].placedCenter.x;
        coord.second = this->Blocks[iter2].pins[iter].pinContacts[cur].placedCenter.y;
        original_coord.push_back(coord);
        for (int w = 0; w < csize; w++) {
          tempSeg.destList.resize(tempSeg.destList.size() + 1);
          tempSeg.destList.back().metalIdx = this->Blocks[iter2].pins[iter].pinContacts[w].metal;
          newnode.x = this->Blocks[iter2].pins[iter].pinContacts[w].placedLL.x;
          newnode.y = this->Blocks[iter2].pins[iter].pinContacts[w].placedLL.y;
          tempSeg.destList.back().coord.push_back(newnode);
          newnode.x = this->Blocks[iter2].pins[iter].pinContacts[w].placedUR.x;
          newnode.y = this->Blocks[iter2].pins[iter].pinContacts[w].placedUR.y;
          tempSeg.destList.back().coord.push_back(newnode);
        }
        tempSeg.destType.type = RouterDB::BLOCK;
        tempSeg.destType.iter = iter;
        tempSeg.destType.iter2 = iter2;
      } else if (this->Nets.at(i).connected.at(1).type == RouterDB::TERMINAL && isTop) {
        tempSeg.destList.resize(tempSeg.destList.size() + 1);
        tempSeg.destList.back().metalIdx = 0;
        newnode.x = this->Terminals[Nets[i].connected[1].iter].termContacts[0].placedCenter.x;
        newnode.y = this->Terminals[Nets[i].connected[1].iter].termContacts[0].placedCenter.y;
        tempSeg.destList.back().coord.push_back(newnode);
        coord.first = newnode.x;
        coord.second = newnode.y;
        original_coord.push_back(coord);
        tempSeg.destType.type = RouterDB::TERMINAL;
        tempSeg.destType.iter = Nets[i].connected[1].iter;
        tempSeg.destType.iter2 = -1;
      }
      this->Nets.at(i).seg.push_back(tempSeg);
      // segnaming=this->Nets.at(i).netName+"_1";
    }

    // if(original_coord.size()!=0){
    //  matlabfile <<"0 ";
    //  for(int k=0;k<original_coord.size();k++){
    //    matlabfile<<original_coord[k].first;
    //    matlabfile<<" ";
    //    matlabfile<<original_coord[k].second;
    //    matlabfile<<" ";
    //  }
    //  matlabfile<<std::endl;
    //}
  }
  // matlabfile.close();
}

long int GlobalRouter::get_number(string str) {
  long int val = 0;
  for (unsigned int number = 0; number < str.length(); number++) {
    if (isdigit(str[number])) val = (10 * val) + (str[number] - 48);
  }
  return val;
};

void GlobalRouter::CreateMetalViaPieces() {
  // MetalPieces.clear(); ViaPieces.clear();
  // MetalPieces.resize(this->drc_info.Metal_info.size());
  // ViaPieces.resize(this->drc_info.Via_info.size());
  RouterDB::SegPiece tmpSP;
  for (unsigned int i = 0; i < this->Blocks.size(); i++) {
    // for each block
    tmpSP.valIdx = -1;
    tmpSP.aiter = i;
    for (unsigned int j = 0; j < this->Blocks.at(i).InternalMetal.size(); j++) {
      // for each block internal metal
      tmpSP.biter = j;
      tmpSP.citer = -1;
      tmpSP.diter = -1;
      tmpSP.type = RouterDB::IMM;
      tmpSP.layerIdx = this->Blocks.at(i).InternalMetal.at(j).metal;
      tmpSP.LLx = this->Blocks.at(i).InternalMetal.at(j).placedLL.x;
      tmpSP.LLy = this->Blocks.at(i).InternalMetal.at(j).placedLL.y;
      tmpSP.URx = this->Blocks.at(i).InternalMetal.at(j).placedUR.x;
      tmpSP.URy = this->Blocks.at(i).InternalMetal.at(j).placedUR.y;
      MetalPieces.at(tmpSP.layerIdx).push_back(tmpSP);
    }
    for (unsigned int j = 0; j < this->Blocks.at(i).InternalVia.size(); j++) {
      // for each block internal via
      tmpSP.biter = j;
      tmpSP.citer = -1;
      tmpSP.diter = -1;
      tmpSP.type = RouterDB::IVM;
      // upper metal of iva
      tmpSP.layerIdx = this->Blocks.at(i).InternalVia.at(j).UpperMetalRect.metal;
      tmpSP.LLx = this->Blocks.at(i).InternalVia.at(j).UpperMetalRect.placedLL.x;
      tmpSP.LLy = this->Blocks.at(i).InternalVia.at(j).UpperMetalRect.placedLL.y;
      tmpSP.URx = this->Blocks.at(i).InternalVia.at(j).UpperMetalRect.placedUR.x;
      tmpSP.URy = this->Blocks.at(i).InternalVia.at(j).UpperMetalRect.placedUR.y;
      MetalPieces.at(tmpSP.layerIdx).push_back(tmpSP);
      // lower metal of via
      tmpSP.layerIdx = this->Blocks.at(i).InternalVia.at(j).LowerMetalRect.metal;
      tmpSP.LLx = this->Blocks.at(i).InternalVia.at(j).LowerMetalRect.placedLL.x;
      tmpSP.LLy = this->Blocks.at(i).InternalVia.at(j).LowerMetalRect.placedLL.y;
      tmpSP.URx = this->Blocks.at(i).InternalVia.at(j).LowerMetalRect.placedUR.x;
      tmpSP.URy = this->Blocks.at(i).InternalVia.at(j).LowerMetalRect.placedUR.y;
      MetalPieces.at(tmpSP.layerIdx).push_back(tmpSP);
      // via layer of via
      tmpSP.type = RouterDB::IVV;
      tmpSP.layerIdx = this->Blocks.at(i).InternalVia.at(j).ViaRect.metal;
      tmpSP.LLx = this->Blocks.at(i).InternalVia.at(j).ViaRect.placedLL.x;
      tmpSP.LLy = this->Blocks.at(i).InternalVia.at(j).ViaRect.placedLL.y;
      tmpSP.URx = this->Blocks.at(i).InternalVia.at(j).ViaRect.placedUR.x;
      tmpSP.URy = this->Blocks.at(i).InternalVia.at(j).ViaRect.placedUR.y;
      ViaPieces.at(tmpSP.layerIdx).push_back(tmpSP);
    }
    for (unsigned int j = 0; j < this->Blocks.at(i).pins.size(); j++) {
      // for each block pin
      tmpSP.biter = j;
      for (unsigned int k = 0; k < this->Blocks.at(i).pins.at(j).pinContacts.size(); k++) {
        // for each block pin metal
        tmpSP.citer = k;
        tmpSP.diter = -1;
        tmpSP.type = RouterDB::PMM;
        tmpSP.layerIdx = this->Blocks.at(i).pins.at(j).pinContacts.at(k).metal;
        tmpSP.LLx = this->Blocks.at(i).pins.at(j).pinContacts.at(k).placedLL.x;
        tmpSP.LLy = this->Blocks.at(i).pins.at(j).pinContacts.at(k).placedLL.y;
        tmpSP.URx = this->Blocks.at(i).pins.at(j).pinContacts.at(k).placedUR.x;
        tmpSP.URy = this->Blocks.at(i).pins.at(j).pinContacts.at(k).placedUR.y;
        MetalPieces.at(tmpSP.layerIdx).push_back(tmpSP);
      }
      for (unsigned int k = 0; k < this->Blocks.at(i).pins.at(j).pinVias.size(); k++) {
        // for each block pin via
        tmpSP.citer = k;
        tmpSP.diter = -1;
        tmpSP.type = RouterDB::PVM;
        // for upper metal of via
        tmpSP.layerIdx = this->Blocks.at(i).pins.at(j).pinVias.at(k).UpperMetalRect.metal;
        tmpSP.LLx = this->Blocks.at(i).pins.at(j).pinVias.at(k).UpperMetalRect.placedLL.x;
        tmpSP.LLy = this->Blocks.at(i).pins.at(j).pinVias.at(k).UpperMetalRect.placedLL.y;
        tmpSP.URx = this->Blocks.at(i).pins.at(j).pinVias.at(k).UpperMetalRect.placedUR.x;
        tmpSP.URy = this->Blocks.at(i).pins.at(j).pinVias.at(k).UpperMetalRect.placedUR.y;
        MetalPieces.at(tmpSP.layerIdx).push_back(tmpSP);
        // for lower metal of via
        tmpSP.layerIdx = this->Blocks.at(i).pins.at(j).pinVias.at(k).LowerMetalRect.metal;
        tmpSP.LLx = this->Blocks.at(i).pins.at(j).pinVias.at(k).LowerMetalRect.placedLL.x;
        tmpSP.LLy = this->Blocks.at(i).pins.at(j).pinVias.at(k).LowerMetalRect.placedLL.y;
        tmpSP.URx = this->Blocks.at(i).pins.at(j).pinVias.at(k).LowerMetalRect.placedUR.x;
        tmpSP.URy = this->Blocks.at(i).pins.at(j).pinVias.at(k).LowerMetalRect.placedUR.y;
        MetalPieces.at(tmpSP.layerIdx).push_back(tmpSP);
        // for via layer of via
        tmpSP.type = RouterDB::PVV;
        tmpSP.layerIdx = this->Blocks.at(i).pins.at(j).pinVias.at(k).ViaRect.metal;
        tmpSP.LLx = this->Blocks.at(i).pins.at(j).pinVias.at(k).ViaRect.placedLL.x;
        tmpSP.LLy = this->Blocks.at(i).pins.at(j).pinVias.at(k).ViaRect.placedLL.y;
        tmpSP.URx = this->Blocks.at(i).pins.at(j).pinVias.at(k).ViaRect.placedUR.x;
        tmpSP.URy = this->Blocks.at(i).pins.at(j).pinVias.at(k).ViaRect.placedUR.y;
        ViaPieces.at(tmpSP.layerIdx).push_back(tmpSP);
      }
    }
  }
  int val = 0;
  for (unsigned int i = 0; i < this->Nets.size(); i++) {
    tmpSP.aiter = i;
    for (unsigned int j = 0; j < this->Nets.at(i).seg.size(); j++) {
      tmpSP.biter = j;
      for (unsigned int k = 0; k < this->Nets.at(i).seg.at(j).candis.size(); k++) {
        tmpSP.citer = k;
        tmpSP.valIdx = val;
        val++;
        // for each candidate metal
        for (unsigned int m = 0; m < this->Nets.at(i).seg.at(j).candis.at(k).metals.size(); m++) {
          tmpSP.diter = m;
          tmpSP.type = RouterDB::CMM;
          tmpSP.layerIdx = this->Nets.at(i).seg.at(j).candis.at(k).metals.at(m).MetalIdx;
          tmpSP.LLx = this->Nets.at(i).seg.at(j).candis.at(k).metals.at(m).MetalRect.placedLL.x;
          tmpSP.LLy = this->Nets.at(i).seg.at(j).candis.at(k).metals.at(m).MetalRect.placedLL.y;
          tmpSP.URx = this->Nets.at(i).seg.at(j).candis.at(k).metals.at(m).MetalRect.placedUR.x;
          tmpSP.URy = this->Nets.at(i).seg.at(j).candis.at(k).metals.at(m).MetalRect.placedUR.y;
          MetalPieces.at(tmpSP.layerIdx).push_back(tmpSP);
        }
        // for each candidate via
        for (unsigned int m = 0; m < this->Nets.at(i).seg.at(j).candis.at(k).vias.size(); m++) {
          tmpSP.diter = m;
          tmpSP.type = RouterDB::CVM;
          // Upper metal of Via
          tmpSP.layerIdx = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).UpperMetalRect.metal;
          tmpSP.LLx = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).UpperMetalRect.placedLL.x;
          tmpSP.LLy = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).UpperMetalRect.placedLL.y;
          tmpSP.URx = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).UpperMetalRect.placedUR.x;
          tmpSP.URy = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).UpperMetalRect.placedUR.y;
          MetalPieces.at(tmpSP.layerIdx).push_back(tmpSP);
          // Lower metal of Via
          tmpSP.layerIdx = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).LowerMetalRect.metal;
          tmpSP.LLx = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).LowerMetalRect.placedLL.x;
          tmpSP.LLy = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).LowerMetalRect.placedLL.y;
          tmpSP.URx = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).LowerMetalRect.placedUR.x;
          tmpSP.URy = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).LowerMetalRect.placedUR.y;
          MetalPieces.at(tmpSP.layerIdx).push_back(tmpSP);
          // Via layer
          tmpSP.type = RouterDB::CVV;
          tmpSP.layerIdx = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).ViaRect.metal;
          tmpSP.LLx = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).ViaRect.placedLL.x;
          tmpSP.LLy = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).ViaRect.placedLL.y;
          tmpSP.URx = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).ViaRect.placedUR.x;
          tmpSP.URy = this->Nets.at(i).seg.at(j).candis.at(k).vias.at(m).ViaRect.placedUR.y;
          ViaPieces.at(tmpSP.layerIdx).push_back(tmpSP);
        }
      }
    }
  }
}

// added by yg
void GlobalRouter::UpdateCandidate(std::vector<std::vector<RouterDB::Metal> >& phsical_path, int i, int j) {
  for (unsigned int k = 0; k < phsical_path.size(); k++) {
    RouterDB::Candidate temp_candis;
    temp_candis.metals = phsical_path[k];
    temp_candis.CandiBend = phsical_path[k].size() - 1;
    int sum = 0;
    for (unsigned int l = 0; l < phsical_path[k].size(); l++) {
      sum = sum + (abs(phsical_path[k][l].LinePoint[0].x - phsical_path[k][l].LinePoint[1].x) +
                   abs(phsical_path[k][l].LinePoint[0].y - phsical_path[k][l].LinePoint[1].y)) *
                      drc_info.metal_weight[phsical_path[k][l].MetalIdx];
    }
    temp_candis.TotMetalWeightByLength = sum;
    Nets[i].seg[j].candis.push_back(temp_candis);
  }
};

void GlobalRouter::getData(PnRDB::hierNode& node, int Lmetal, int Hmetal) {
  auto logger = spdlog::default_logger()->clone("router.GlobalRouter.getData");

  // std::cout<<"Router-Info: begin to import data"<<std::endl;
  this->isTop = node.isTop;
  this->topName = node.name;
  this->width = node.width;
  this->height = node.height;
  this->LL.x = 0;
  this->LL.y = 0;
  this->UR.x = node.width;
  this->UR.y = node.height;
  this->path_number = 5;  // number of candidates
  int max_width = node.width;
  int max_height = node.height;
  // int threshold = 10000000;
  lowest_metal = Lmetal;
  highest_metal = Hmetal;

  // grid_alpha should be adjusted according to the size of node
  // more adjust is necessry for detail router?
  if (max_height * max_width <= 10000) {
    grid_scale = 1;
  } else if (max_height * max_width <= 1000000) {
    grid_scale = 2;
  } else if (max_height * max_width <= 100000000) {
    grid_scale = 4;
  } else if (max_height * max_width <= 10000000000) {
    grid_scale = 10;
  } else {
    grid_scale = 20;
  }
  // if(max_height*max_width<=100000000){
  //   grid_scale = 1;
  //  }else if (max_height*max_width<=1000000000000){
  //   grid_scale = 4;
  //  } else {
  //   grid_scale = 10;
  //  }

  // For terminals
  for (unsigned int i = 0; i < node.Terminals.size(); i++) {
    RouterDB::terminal temp_terminal;
    temp_terminal.netIter = node.Terminals[i].netIter;
    if (isTop) {
      for (unsigned int j = 0; j < node.Terminals[i].termContacts.size(); j++) {
        RouterDB::contact temp_contact;
        // cout<<node.Terminals[i].termContacts[j].metal<<endl;
        // if(drc_info.Metalmap.find(node.Terminals[i].termContacts[j].metal)!=drc_info.Metalmap.end()){
        //  temp_contact.metal = drc_info.Metalmap[node.Terminals[i].termContacts[j].metal];
        // wbxu: Terminals in hierNode only has placedCenter field
        // temp_contact.placedLL.x =node.Terminals[i].termContacts[j].placedBox.LL.x;
        // temp_contact.placedLL.y =node.Terminals[i].termContacts[j].placedBox.LL.y;
        // temp_contact.placedUR.x =node.Terminals[i].termContacts[j].placedBox.UR.x;
        // temp_contact.placedUR.y =node.Terminals[i].termContacts[j].placedBox.UR.y;
        temp_contact.placedCenter.x = node.Terminals[i].termContacts[j].placedCenter.x;
        temp_contact.placedCenter.y = node.Terminals[i].termContacts[j].placedCenter.y;
        temp_terminal.termContacts.push_back(temp_contact);
        //}else{
        //  std::cout<<"Router-Error: incorrect metal for contact - from node to router"<<std::endl;
        //}
      }
    }
    temp_terminal.name = node.Terminals[i].name;
    Terminals.push_back(temp_terminal);
  }

  int temp_type;
  // For nets
  // need modify with power router.... here the method is just remove the single terminal, but not vdd/gnd
  // wbxu: pay attention to dangling nets and power nets
  for (unsigned int i = 0; i < node.Nets.size(); i++) {
    RouterDB::Net temp_net;
    // if(node.Nets[i].connected.size()!=1){
    // temp_net.isTerminal=0;
    temp_net.degree = node.Nets[i].degree;
    temp_net.netName = node.Nets[i].name;
    temp_net.shielding = node.Nets[i].shielding;
    temp_net.sink2Terminal = node.Nets[i].sink2Terminal;
    temp_net.symCounterpart = node.Nets[i].symCounterpart;
    temp_net.iter2SNetLsit = node.Nets[i].iter2SNetLsit;
    temp_net.priority = node.Nets[i].priority;
    /*
    if(temp_net.symCounterpart!=-1){
       if(i < temp_net.symCounterpart){
          symnet_idx.push_back(temp_net.symCounterpart);
         }else{
          symnet_idx.push_back(i);
         }
      }  // wbxu? symnet_idx undefined
     */

    for (unsigned int j = 0; j < node.Nets[i].connected.size(); j++) {
      RouterDB::connectNode temp_connectNode;
      temp_type = RouterDB::NType(node.Nets[i].connected[j].type);  // wbxu? Not Omark, replace with NType

      if (temp_type == 0) {
        temp_connectNode.type = RouterDB::BLOCK;
      } else {
        temp_connectNode.type = RouterDB::TERMINAL;
        temp_net.isTerminal = 1;
        temp_net.terminal_idx = node.Nets[i].connected[j].iter;
      }
      // assume that at most one terminal connected to one net
      temp_connectNode.iter = node.Nets[i].connected[j].iter;
      temp_connectNode.iter2 = node.Nets[i].connected[j].iter2;
      temp_net.connected.push_back(temp_connectNode);
    }
    Nets.push_back(temp_net);
    //}else{
    // cout<<"Remove one connection terminal"<<endl;
    //}
  }

  // For blocks
  for (unsigned int i = 0; i < node.Blocks.size(); i++) {
    RouterDB::Block temp_block;
    int sel = node.Blocks[i].selectedInstance;
    temp_block.blockName = node.Blocks[i].instance[sel].name;
    temp_block.blockMaster = node.Blocks[i].instance[sel].master;
    temp_block.gdsfile = node.Blocks[i].instance[sel].gdsFile;
    temp_block.numTerminals = node.Blocks[i].instance[sel].blockPins.size();
    temp_block.orient = RouterDB::Omark(node.Blocks[i].instance[sel].orient);
    temp_block.isLeaf = node.Blocks[i].instance[sel].isLeaf;
    temp_block.width = node.Blocks[i].instance[sel].width;
    temp_block.height = node.Blocks[i].instance[sel].height;
    temp_block.area = temp_block.width * temp_block.height;
    temp_block.placedLL.x = node.Blocks[i].instance[sel].placedBox.LL.x;
    temp_block.placedLL.y = node.Blocks[i].instance[sel].placedBox.LL.y;
    temp_block.placedUR.x = node.Blocks[i].instance[sel].placedBox.UR.x;
    temp_block.placedUR.y = node.Blocks[i].instance[sel].placedBox.UR.y;
    // temp_block.originLL.x=node.Blocks[i].instance[sel].originBox.LL.x;
    // temp_block.originLL.y=node.Blocks[i].instance[sel].originBox.LL.y;
    // temp_block.originUR.x=node.Blocks[i].instance[sel].originBox.UR.x;
    // temp_block.originUR.y=node.Blocks[i].instance[sel].originBox.UR.y;

    for (unsigned int j = 0; j < node.Blocks[i].instance[sel].blockPins.size(); j++) {
      RouterDB::Pin temp_pin;
      temp_pin.pinName = node.Blocks[i].instance[sel].blockPins[j].name;
      temp_pin.netIter = node.Blocks[i].instance[sel].blockPins[j].netIter;
      for (unsigned int k = 0; k < node.Blocks[i].instance[sel].blockPins[j].pinContacts.size(); k++) {
        RouterDB::contact temp_contact;
        if (drc_info.Metalmap.find(node.Blocks[i].instance[sel].blockPins[j].pinContacts[k].metal) != drc_info.Metalmap.end()) {
          temp_contact.metal = drc_info.Metalmap[node.Blocks[i].instance[sel].blockPins[j].pinContacts[k].metal];
        } else {
          logger->error("Router-Error: the metal pin contact of block is not found");
        }
        temp_contact.placedLL.x = node.Blocks[i].instance[sel].blockPins[j].pinContacts[k].placedBox.LL.x;
        temp_contact.placedLL.y = node.Blocks[i].instance[sel].blockPins[j].pinContacts[k].placedBox.LL.y;
        temp_contact.placedUR.x = node.Blocks[i].instance[sel].blockPins[j].pinContacts[k].placedBox.UR.x;
        temp_contact.placedUR.y = node.Blocks[i].instance[sel].blockPins[j].pinContacts[k].placedBox.UR.y;
        temp_contact.placedCenter.x = node.Blocks[i].instance[sel].blockPins[j].pinContacts[k].placedCenter.x;
        temp_contact.placedCenter.y = node.Blocks[i].instance[sel].blockPins[j].pinContacts[k].placedCenter.y;
        temp_pin.pinContacts.push_back(temp_contact);
      }

      for (unsigned int k = 0; k < node.Blocks[i].instance[sel].blockPins[j].pinVias.size(); k++) {
        RouterDB::Via temp_via;
        temp_via.model_index = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].model_index;
        temp_via.position.x = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].placedpos.x;
        temp_via.position.y = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].placedpos.y;
        // ViaRect

        if (drc_info.Viamap.find(node.Blocks[i].instance[sel].blockPins[j].pinVias[k].ViaRect.metal) != drc_info.Viamap.end()) {
          temp_via.ViaRect.metal = drc_info.Viamap[node.Blocks[i].instance[sel].blockPins[j].pinVias[k].ViaRect.metal];
        } else {
          logger->error("Router-Error: - Viamap Error");
        }
        temp_via.ViaRect.placedLL.x = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].ViaRect.placedBox.LL.x;
        temp_via.ViaRect.placedLL.y = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].ViaRect.placedBox.LL.y;
        temp_via.ViaRect.placedUR.x = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].ViaRect.placedBox.UR.x;
        temp_via.ViaRect.placedUR.y = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].ViaRect.placedBox.UR.y;
        temp_via.ViaRect.placedCenter.x = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].ViaRect.placedCenter.x;
        temp_via.ViaRect.placedCenter.y = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].ViaRect.placedCenter.y;
        // LowerRect //LowerMetalRect
        if (drc_info.Metalmap.find(node.Blocks[i].instance[sel].blockPins[j].pinVias[k].LowerMetalRect.metal) != drc_info.Metalmap.end()) {
          temp_via.LowerMetalRect.metal = drc_info.Metalmap[node.Blocks[i].instance[sel].blockPins[j].pinVias[k].LowerMetalRect.metal];
        } else {
          logger->error("Router-Error: Metal map error");
        }
        temp_via.LowerMetalRect.placedLL.x = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].LowerMetalRect.placedBox.LL.x;
        temp_via.LowerMetalRect.placedLL.y = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].LowerMetalRect.placedBox.LL.y;
        temp_via.LowerMetalRect.placedUR.x = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].LowerMetalRect.placedBox.UR.x;
        temp_via.LowerMetalRect.placedUR.y = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].LowerMetalRect.placedBox.UR.y;
        temp_via.LowerMetalRect.placedCenter.x = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].LowerMetalRect.placedCenter.x;
        temp_via.LowerMetalRect.placedCenter.y = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].LowerMetalRect.placedCenter.y;
        // UpperRect //UpperMetalRect
        if (drc_info.Metalmap.find(node.Blocks[i].instance[sel].blockPins[j].pinVias[k].UpperMetalRect.metal) != drc_info.Metalmap.end()) {
          temp_via.UpperMetalRect.metal = drc_info.Metalmap[node.Blocks[i].instance[sel].blockPins[j].pinVias[k].UpperMetalRect.metal];
        } else {
          logger->error("Router-Error: Metal map error");
        }
        temp_via.UpperMetalRect.placedLL.x = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].UpperMetalRect.placedBox.LL.x;
        temp_via.UpperMetalRect.placedLL.y = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].UpperMetalRect.placedBox.LL.y;
        temp_via.UpperMetalRect.placedUR.x = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].UpperMetalRect.placedBox.UR.x;
        temp_via.UpperMetalRect.placedUR.y = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].UpperMetalRect.placedBox.UR.y;
        temp_via.UpperMetalRect.placedCenter.x = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].UpperMetalRect.placedCenter.x;
        temp_via.UpperMetalRect.placedCenter.y = node.Blocks[i].instance[sel].blockPins[j].pinVias[k].UpperMetalRect.placedCenter.y;

        temp_pin.pinVias.push_back(temp_via);
      }

      temp_block.pins.push_back(temp_pin);
    }

    for (unsigned int j = 0; j < node.Blocks[i].instance[sel].interMetals.size(); j++) {
      RouterDB::contact temp_metal;
      if (drc_info.Metalmap.find(node.Blocks[i].instance[sel].interMetals[j].metal) != drc_info.Metalmap.end()) {
        temp_metal.metal = drc_info.Metalmap[node.Blocks[i].instance[sel].interMetals[j].metal];
        // temp_metal.width=drc_info.Metal_info[temp_metal.MetalIdx].width;
      } else {
        logger->error("Router-Error: interMetal info missing metal");
      }
      RouterDB::point temp_point;
      temp_metal.placedLL.x = node.Blocks[i].instance[sel].interMetals[j].placedBox.LL.x;
      temp_metal.placedLL.y = node.Blocks[i].instance[sel].interMetals[j].placedBox.LL.y;
      temp_metal.placedUR.x = node.Blocks[i].instance[sel].interMetals[j].placedBox.UR.x;
      temp_metal.placedUR.y = node.Blocks[i].instance[sel].interMetals[j].placedBox.UR.y;
      temp_metal.placedCenter.x = (temp_metal.placedLL.x + temp_metal.placedUR.x) / 2;
      temp_metal.placedCenter.y = (temp_metal.placedLL.y + temp_metal.placedUR.y) / 2;
      temp_block.InternalMetal.push_back(temp_metal);
    }

    for (unsigned int j = 0; j < node.Blocks[i].instance[sel].interVias.size(); j++) {
      RouterDB::Via temp_via;
      temp_via.model_index = node.Blocks[i].instance[sel].interVias[j].model_index;
      temp_via.position.x = node.Blocks[i].instance[sel].interVias[j].placedpos.x;
      temp_via.position.y = node.Blocks[i].instance[sel].interVias[j].placedpos.y;
      // ViaRect

      if (drc_info.Viamap.find(node.Blocks[i].instance[sel].interVias[j].ViaRect.metal) != drc_info.Metalmap.end()) {
        temp_via.ViaRect.metal = drc_info.Viamap[node.Blocks[i].instance[sel].interVias[j].ViaRect.metal];
      } else {
        logger->error("Router-Error: - Viamap Error");
      }
      temp_via.ViaRect.placedLL.x = node.Blocks[i].instance[sel].interVias[j].ViaRect.placedBox.LL.x;
      temp_via.ViaRect.placedLL.y = node.Blocks[i].instance[sel].interVias[j].ViaRect.placedBox.LL.y;
      temp_via.ViaRect.placedUR.x = node.Blocks[i].instance[sel].interVias[j].ViaRect.placedBox.UR.x;
      temp_via.ViaRect.placedUR.y = node.Blocks[i].instance[sel].interVias[j].ViaRect.placedBox.UR.y;
      temp_via.ViaRect.placedCenter.x = node.Blocks[i].instance[sel].interVias[j].ViaRect.placedCenter.x;
      temp_via.ViaRect.placedCenter.y = node.Blocks[i].instance[sel].interVias[j].ViaRect.placedCenter.y;
      // LowerRect //LowerMetalRect
      if (drc_info.Metalmap.find(node.Blocks[i].instance[sel].interVias[j].LowerMetalRect.metal) != drc_info.Metalmap.end()) {
        temp_via.LowerMetalRect.metal = drc_info.Metalmap[node.Blocks[i].instance[sel].interVias[j].LowerMetalRect.metal];
      } else {
        logger->error("Router-Error: Metal map error");
      }
      temp_via.LowerMetalRect.placedLL.x = node.Blocks[i].instance[sel].interVias[j].LowerMetalRect.placedBox.LL.x;
      temp_via.LowerMetalRect.placedLL.y = node.Blocks[i].instance[sel].interVias[j].LowerMetalRect.placedBox.LL.y;
      temp_via.LowerMetalRect.placedUR.x = node.Blocks[i].instance[sel].interVias[j].LowerMetalRect.placedBox.UR.x;
      temp_via.LowerMetalRect.placedUR.y = node.Blocks[i].instance[sel].interVias[j].LowerMetalRect.placedBox.UR.y;
      temp_via.LowerMetalRect.placedCenter.x = node.Blocks[i].instance[sel].interVias[j].LowerMetalRect.placedCenter.x;
      temp_via.LowerMetalRect.placedCenter.y = node.Blocks[i].instance[sel].interVias[j].LowerMetalRect.placedCenter.y;
      // UpperRect //UpperMetalRect
      if (drc_info.Metalmap.find(node.Blocks[i].instance[sel].interVias[j].UpperMetalRect.metal) != drc_info.Metalmap.end()) {
        temp_via.UpperMetalRect.metal = drc_info.Metalmap[node.Blocks[i].instance[sel].interVias[j].UpperMetalRect.metal];
      } else {
        logger->error("Router-Error: Metal map error");
      }
      temp_via.UpperMetalRect.placedLL.x = node.Blocks[i].instance[sel].interVias[j].UpperMetalRect.placedBox.LL.x;
      temp_via.UpperMetalRect.placedLL.y = node.Blocks[i].instance[sel].interVias[j].UpperMetalRect.placedBox.LL.y;
      temp_via.UpperMetalRect.placedUR.x = node.Blocks[i].instance[sel].interVias[j].UpperMetalRect.placedBox.UR.x;
      temp_via.UpperMetalRect.placedUR.y = node.Blocks[i].instance[sel].interVias[j].UpperMetalRect.placedBox.UR.y;
      temp_via.UpperMetalRect.placedCenter.x = node.Blocks[i].instance[sel].interVias[j].UpperMetalRect.placedCenter.x;
      temp_via.UpperMetalRect.placedCenter.y = node.Blocks[i].instance[sel].interVias[j].UpperMetalRect.placedCenter.y;

      temp_block.InternalVia.push_back(temp_via);
    }
    Blocks.push_back(temp_block);
  }

  // getPowerGridData(node);
  // getPowerNetData(node);

  // std::cout<<"Router-Info: complete importing data"<<std::endl;
};

/*
void GlobelRouter::getPowerNetData(PnRDB::hierNode& node){

  //For power net

  for(int i=0;i<node.PowerNets.size();i++){
      RouterDB::PowerNet temp_net;
      temp_net.netName = node.PowerNets[i].name;
      //temp_net.shielding = node.Nets[i].shielding;
      temp_net.power = node.PowerNets[i].power;
      //path_metal
      for(int j=0;j<node.PowerNets[i].path_metal.size();j++){
          RouterDB::Metal temp_metal;
          ConvertMetal(temp_metal, node.PowerNets[i].path_metal[j]);
          temp_net.path_metal.push_back(temp_metal);
         }

      //path via
      for(int j=0;j<node.PowerNets[i].path_via.size();j++){
          RouterDB::Via temp_via;
          ConvertVia(temp_via,node.PowerNets[i].path_via[j]);
          temp_net.path_via.push_back(temp_via);

         }

      //pins

      for(int j=0;j<node.PowerNets[i].Pins.size();j++){
          RouterDB::Pin temp_pin;
          ConvertPin(temp_pim, node.PowerNets[i].Pins[j]);
          temp_net.pins.push_back(temp_pin);
      }


      PowerNets.push_back(temp_net);

     }
};

void GlobalRouter::ConverContact(RouterDB::contact& temp_metal, PnRDB::contact& pnr_metal){

  //RouterDB::contact temp_metal;
  if(drc_info.Metalmap.find(pnr_metal.metal)!=drc_info.Metalmap.end()){
      temp_metal.metal=drc_info.Metalmap[pnr_metal.metal];
      //temp_metal.width=drc_info.Metal_info[temp_metal.MetalIdx].width;
    }else{
      std::cout<<"Router-Error: interMetal info missing metal"<<std::endl;
    }
   RouterDB::point temp_point;
   temp_metal.placedLL.x = pnr_metal.placedBox.LL.x;
   temp_metal.placedLL.y = pnr_metal.placedBox.LL.y;
   temp_metal.placedUR.x = pnr_metal.placedBox.UR.x;
   temp_metal.placedUR.y = pnr_metal.placedBox.UR.y;
   temp_metal.placedCenter.x = (temp_metal.placedLL.x + temp_metal.placedUR.x)/2;
   temp_metal.placedCenter.y = (temp_metal.placedLL.y + temp_metal.placedUR.y)/2;
   //temp_block.InternalMetal.push_back(temp_metal);

};

void GlobalRouter::ConvertMetal(RouterDB::Metal& temp_metal,PnRDB::Metal& pnr_metal){

  //RouterDB::Metal temp_metal;
  temp_metal.MetalIdx = pnr_metal.MetalIdx;
  temp_metal.LinePoint[0].x = pnr_metal.LinePoint[0].x;
  temp_metal.LinePoint[0].y = pnr_metal.LinePoint[0].y;
  temp_metal.LinePoint[1].x = pnr_metal.LinePoint[1].x;
  temp_metal.LinePoint[1].y = pnr_metal.LinePoint[1].y;
  temp_metal.width = pnr_metal.width;
  //contact
  RouterDB::contact temp_contact;

  if(drc_info.Metalmap.find(pnr_metal.MetalRect.metal)!=drc_info.Metalmap.end()){
    temp_contact.metal=drc_info.Metalmap[pnr_metal.MetalRect.metal];
  }else{
    std::cout<<"Router-Error: the metal pin contact of block is not found"<<std::endl;
  }

  //temp_contact.metal = drc_info.Metalmap[node.Nets[i].path_metal[j].MetalRect.metal];

  temp_contact.placedLL.x = pnr_metal.MetalRect.placedBox.LL.x;
  temp_contact.placedLL.y = pnr_metal.MetalRect.placedBox.LL.y;
  temp_contact.placedUR.x = pnr_metal.MetalRect.placedBox.UR.x;
  temp_contact.placedUR.y = pnr_metal.MetalRect.placedBox.UR.y;
  temp_contact.placedCenter.x = pnr_metal.MetalRect.placedCenter.x;
  temp_contact.placedCenter.y = pnr_metal.MetalRect.placedCenter.y;
  temp_metal.MetalRect = temp_contact;

};


void GlobalRouter::getPowerGridData(PnRDB::hierNode & node){


  //Vdd_grid
  Vdd_grid.power = node.Vdd.power;

  for(int i =0;i<node.Vdd.metals.size();i++){
       RouterDB::Metal temp_metal;
       ConvertMetal(temp_metal, node.Vdd.metals[i]);
       Vdd_grid.metals.push_back(temp_metal);
     }

  for(int i =0;i<node.Vdd.vias.size();i++){
       RouterDB::Via temp_via;
       ConvertVia(temp_via, node.Vdd.vias[i]);
       Vdd_grid.vias.push_back(temp_via);
     }

  //Gnd_grid
  Gnd_grid.power = node.Gnd.power;

  for(int i =0;i<node.Gnd.metals.size();i++){
       RouterDB::Metal temp_metal;
       ConvertMetal(temp_metal, node.Gnd.metals[i]);
       Gnd_grid.metals.push_back(temp_metal);
     }

  for(int i =0;i<node.Gnd.vias.size();i++){
       RouterDB::Via temp_via;
       ConvertVia(temp_via, node.Gnd.vias[i]);
       Gnd_grid.vias.push_back(temp_via);
     }

};

void GlobelRouter::ConvertVia(RouterDB::Via &temp_via,PnRDB::Via& pnr_via){

  //RouterDB::Via temp_via;

  temp_via.model_index = pnr_via.model_index;
  temp_via.position.x = pnr_via.placedpos.x;
  temp_via.position.y = pnr_via.placedpos.y;
  //ViaRect

  if(drc_info.Viamap.find(pnr_via.ViaRect.metal)!=drc_info.Viamap.end()){
      temp_via.ViaRect.metal = drc_info.Viamap[pnr_via.ViaRect.metal];
     }else{
      std::cout<<"Router-Error: - Viamap Error"<<std::endl;
     }

  temp_via.ViaRect.placedLL.x = pnr_via.ViaRect.placedBox.LL.x;
  temp_via.ViaRect.placedLL.y = pnr_via.ViaRect.placedBox.LL.y;
  temp_via.ViaRect.placedUR.x = pnr_via.ViaRect.placedBox.UR.x;
  temp_via.ViaRect.placedUR.y = pnr_via.ViaRect.placedBox.UR.y;
  temp_via.ViaRect.placedCenter.x= pnr_via.ViaRect.placedCenter.x;
  temp_via.ViaRect.placedCenter.y= pnr_via.ViaRect.placedCenter.y;
  //LowerRect //LowerMetalRect
  if(drc_info.Metalmap.find(pnr_via.LowerMetalRect.metal)!=drc_info.Metalmap.end()){
      temp_via.LowerMetalRect.metal = drc_info.Metalmap[pnr_via.LowerMetalRect.metal];
     }else{
      std::cout<<"Router-Error: Metal map error"<<std::endl;
     }
  temp_via.LowerMetalRect.placedLL.x = pnr_via.LowerMetalRect.placedBox.LL.x;
  temp_via.LowerMetalRect.placedLL.y = pnr_via.LowerMetalRect.placedBox.LL.y;
  temp_via.LowerMetalRect.placedUR.x = pnr_via.LowerMetalRect.placedBox.UR.x;
  temp_via.LowerMetalRect.placedUR.y = pnr_via.LowerMetalRect.placedBox.UR.y;
  temp_via.LowerMetalRect.placedCenter.x= pnr_via.LowerMetalRect.placedCenter.x;
  temp_via.LowerMetalRect.placedCenter.y= pnr_via.LowerMetalRect.placedCenter.y;
  //UpperRect //UpperMetalRect
  if(drc_info.Metalmap.find(pnr_via.UpperMetalRect.metal)!=drc_info.Metalmap.end()){
       temp_via.UpperMetalRect.metal = drc_info.Metalmap[pnr_via.UpperMetalRect.metal];
     }else{
       std::cout<<"Router-Error: Metal map error"<<std::endl;
     }
  temp_via.UpperMetalRect.placedLL.x = pnr_via.UpperMetalRect.placedBox.LL.x;
  temp_via.UpperMetalRect.placedLL.y = pnr_via.UpperMetalRect.placedBox.LL.y;
  temp_via.UpperMetalRect.placedUR.x = pnr_via.UpperMetalRect.placedBox.UR.x;
  temp_via.UpperMetalRect.placedUR.y = pnr_via.UpperMetalRect.placedBox.UR.y;
  temp_via.UpperMetalRect.placedCenter.x = pnr_via.UpperMetalRect.placedCenter.x;
  temp_via.UpperMetalRect.placedCenter.y = pnr_via.UpperMetalRect.placedCenter.y;

};

void GlobalRouter::ConvertPin(RouterDB::Pin& temp_pin,PnRDB::pin& pnr_pin){

  //RouterDB::Pin temp_pin;
  temp_pin.pinName=pnr_pin.name;
  temp_pin.netIter=pnr_pin.netIter;
  for(int k=0;k<pnr_pin.pinContacts.size();k++){
       RouterDB::contact temp_contact;
       if(drc_info.Metalmap.find(pnr_pin.pinContacts[k].metal)!=drc_info.Metalmap.end()){
           temp_contact.metal=drc_info.Metalmap[pnr_pin.pinContacts[k].metal];
        }else{
           std::cout<<"Router-Error: the metal pin contact of block is not found"<<std::endl;
        }
       temp_contact.placedLL.x=pnr_pin.pinContacts[k].placedBox.LL.x;
       temp_contact.placedLL.y=pnr_pin.pinContacts[k].placedBox.LL.y;
       temp_contact.placedUR.x=pnr_pin.pinContacts[k].placedBox.UR.x;
       temp_contact.placedUR.y=pnr_pin.pinContacts[k].placedBox.UR.y;
       temp_contact.placedCenter.x=pnr_pin.pinContacts[k].placedCenter.x;
       temp_contact.placedCenter.y=pnr_pin.pinContacts[k].placedCenter.y;
       temp_pin.pinContacts.push_back(temp_contact);
      }


  for(int k=0;k<pnr_pin.pinVias.size();k++){
        RouterDB::Via temp_via;
        temp_via.model_index = pnr_pin.pinVias[k].model_index;
        temp_via.position.x = pnr_pin.pinVias[k].placedpos.x;
        temp_via.position.y = pnr_pin.pinVias[k].placedpos.y;
        //ViaRect

        if(drc_info.Viamap.find(pnr_pin.pinVias[k].ViaRect.metal)!=drc_info.Viamap.end()){
             temp_via.ViaRect.metal = drc_info.Viamap[pnr_pin.pinVias[k].ViaRect.metal];
          }else{
             std::cout<<"Router-Error: - Viamap Error"<<std::endl;
          }
        temp_via.ViaRect.placedLL.x = pnr_pin.pinVias[k].ViaRect.placedBox.LL.x;
        temp_via.ViaRect.placedLL.y = pnr_pin.pinVias[k].ViaRect.placedBox.LL.y;
        temp_via.ViaRect.placedUR.x = pnr_pin.pinVias[k].ViaRect.placedBox.UR.x;
        temp_via.ViaRect.placedUR.y = pnr_pin.pinVias[k].ViaRect.placedBox.UR.y;
        temp_via.ViaRect.placedCenter.x= pnr_pin.pinVias[k].ViaRect.placedCenter.x;
        temp_via.ViaRect.placedCenter.y= pnr_pin.pinVias[k].ViaRect.placedCenter.y;
        //LowerRect //LowerMetalRect
        if(drc_info.Metalmap.find(pnr_pin.pinVias[k].LowerMetalRect.metal)!=drc_info.Metalmap.end()){
             temp_via.LowerMetalRect.metal = drc_info.Metalmap[pnr_pin.pinVias[k].LowerMetalRect.metal];
           }else{
             std::cout<<"Router-Error: Metal map error"<<std::endl;
           }
         temp_via.LowerMetalRect.placedLL.x = pnr_pin.pinVias[k].LowerMetalRect.placedBox.LL.x;
         temp_via.LowerMetalRect.placedLL.y = pnr_pin.pinVias[k].LowerMetalRect.placedBox.LL.y;
         temp_via.LowerMetalRect.placedUR.x = pnr_pin.pinVias[k].LowerMetalRect.placedBox.UR.x;
         temp_via.LowerMetalRect.placedUR.y = pnr_pin.pinVias[k].LowerMetalRect.placedBox.UR.y;
         temp_via.LowerMetalRect.placedCenter.x= pnr_pin.pinVias[k].LowerMetalRect.placedCenter.x;
         temp_via.LowerMetalRect.placedCenter.y= pnr_pin.pinVias[k].LowerMetalRect.placedCenter.y;
         //UpperRect //UpperMetalRect
         if(drc_info.Metalmap.find(pnr_pin.pinVias[k].UpperMetalRect.metal)!=drc_info.Metalmap.end()){
              temp_via.UpperMetalRect.metal = drc_info.Metalmap[pnr_pin.pinVias[k].UpperMetalRect.metal];
            }else{
              std::cout<<"Router-Error: Metal map error"<<std::endl;
            }
         temp_via.UpperMetalRect.placedLL.x = pnr_pin.pinVias[k].UpperMetalRect.placedBox.LL.x;
         temp_via.UpperMetalRect.placedLL.y = pnr_pin.pinVias[k].UpperMetalRect.placedBox.LL.y;
         temp_via.UpperMetalRect.placedUR.x = pnr_pin.pinVias[k].UpperMetalRect.placedBox.UR.x;
         temp_via.UpperMetalRect.placedUR.y = pnr_pin.pinVias[k].UpperMetalRect.placedBox.UR.y;
         temp_via.UpperMetalRect.placedCenter.x = pnr_pin.pinVias[k].UpperMetalRect.placedCenter.x;
         temp_via.UpperMetalRect.placedCenter.y = pnr_pin.pinVias[k].UpperMetalRect.placedCenter.y;

         temp_pin.pinVias.push_back(temp_via);
      }


};
*/

void GlobalRouter::getDRCdata(PnRDB::Drc_info& drcData) { drc_info = drcData; };

void GlobalRouter::GetPhsical_Metal_Via(int i, int j) {
  // for each candidate
  for (unsigned int k = 0; k < Nets[i].seg[j].candis.size(); k++) {
    // for each metal in candidate
    for (unsigned int h = 0; h < Nets[i].seg[j].candis[k].metals.size(); h++) {
      // get phsical metal
      Nets[i].seg[j].candis[k].metals[h].MetalRect.metal = Nets[i].seg[j].candis[k].metals[h].MetalIdx;
      Nets[i].seg[j].candis[k].metals[h].MetalRect.placedCenter.x =
          (Nets[i].seg[j].candis[k].metals[h].LinePoint[0].x + Nets[i].seg[j].candis[k].metals[h].LinePoint[1].x) / 2;
      Nets[i].seg[j].candis[k].metals[h].MetalRect.placedCenter.y =
          (Nets[i].seg[j].candis[k].metals[h].LinePoint[0].y + Nets[i].seg[j].candis[k].metals[h].LinePoint[1].y) / 2;
      if (drc_info.Metal_info[Nets[i].seg[j].candis[k].metals[h].MetalIdx].direct == 1) {
        if (Nets[i].seg[j].candis[k].metals[h].LinePoint[0].x <= Nets[i].seg[j].candis[k].metals[h].LinePoint[1].x) {
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedLL.x = Nets[i].seg[j].candis[k].metals[h].LinePoint[0].x;
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedLL.y =
              Nets[i].seg[j].candis[k].metals[h].LinePoint[0].y - Nets[i].seg[j].candis[k].metals[h].width / 2;
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedUR.x = Nets[i].seg[j].candis[k].metals[h].LinePoint[1].x;
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedUR.y =
              Nets[i].seg[j].candis[k].metals[h].LinePoint[1].y + Nets[i].seg[j].candis[k].metals[h].width / 2;
        } else {
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedLL.x = Nets[i].seg[j].candis[k].metals[h].LinePoint[1].x;
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedLL.y =
              Nets[i].seg[j].candis[k].metals[h].LinePoint[1].y - Nets[i].seg[j].candis[k].metals[h].width / 2;
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedUR.x = Nets[i].seg[j].candis[k].metals[h].LinePoint[0].x;
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedUR.y =
              Nets[i].seg[j].candis[k].metals[h].LinePoint[0].y + Nets[i].seg[j].candis[k].metals[h].width / 2;
        }
      } else {
        if (Nets[i].seg[j].candis[k].metals[h].LinePoint[0].y <= Nets[i].seg[j].candis[k].metals[h].LinePoint[1].y) {
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedLL.x =
              Nets[i].seg[j].candis[k].metals[h].LinePoint[0].x - Nets[i].seg[j].candis[k].metals[h].width / 2;
          ;
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedLL.y = Nets[i].seg[j].candis[k].metals[h].LinePoint[0].y;
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedUR.x =
              Nets[i].seg[j].candis[k].metals[h].LinePoint[1].x + Nets[i].seg[j].candis[k].metals[h].width / 2;
          ;
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedUR.y = Nets[i].seg[j].candis[k].metals[h].LinePoint[1].y;
        } else {
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedLL.x =
              Nets[i].seg[j].candis[k].metals[h].LinePoint[1].x - Nets[i].seg[j].candis[k].metals[h].width / 2;
          ;
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedLL.y = Nets[i].seg[j].candis[k].metals[h].LinePoint[1].y;
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedUR.x =
              Nets[i].seg[j].candis[k].metals[h].LinePoint[0].x + Nets[i].seg[j].candis[k].metals[h].width / 2;
          ;
          Nets[i].seg[j].candis[k].metals[h].MetalRect.placedUR.y = Nets[i].seg[j].candis[k].metals[h].LinePoint[0].y;
        }
      }
    }
    // add via
    for (unsigned int h = 0; h < Nets[i].seg[j].candis[k].metals.size() - 1; h++) {
      int found_index = 0;
      vector<int> via_model;
      for (unsigned int p = 0; p < Nets[i].seg[j].candis[k].metals[h].LinePoint.size(); p++) {
        for (unsigned int q = 0; q < Nets[i].seg[j].candis[k].metals[h + 1].LinePoint.size(); q++) {
          if (Nets[i].seg[j].candis[k].metals[h].LinePoint[p].x == Nets[i].seg[j].candis[k].metals[h + 1].LinePoint[q].x &&
              Nets[i].seg[j].candis[k].metals[h].LinePoint[p].y == Nets[i].seg[j].candis[k].metals[h + 1].LinePoint[q].y) {
            found_index = p;
          }
        }
      }
      // found via model index here
      int metal_min;
      int metal_max;
      if (Nets[i].seg[j].candis[k].metals[h].MetalIdx < Nets[i].seg[j].candis[k].metals[h + 1].MetalIdx) {
        metal_min = Nets[i].seg[j].candis[k].metals[h].MetalIdx;
        metal_max = Nets[i].seg[j].candis[k].metals[h + 1].MetalIdx;
      } else {
        metal_min = Nets[i].seg[j].candis[k].metals[h + 1].MetalIdx;
        metal_max = Nets[i].seg[j].candis[k].metals[h].MetalIdx;
      }

      int via_index = metal_min;
      while (via_index < metal_max) {
        via_model.push_back(via_index);
        via_index = via_index + 1;
      }

      for (unsigned int q = 0; q < via_model.size(); q++) {
        RouterDB::Via temp_via;
        temp_via.model_index = via_model[q];
        temp_via.position.x = Nets[i].seg[j].candis[k].metals[h].LinePoint[found_index].x;
        temp_via.position.y = Nets[i].seg[j].candis[k].metals[h].LinePoint[found_index].y;
        // ViaRect
        temp_via.ViaRect.metal = via_model[q];
        temp_via.ViaRect.placedCenter = temp_via.position;
        temp_via.ViaRect.placedLL.x = drc_info.Via_model[temp_via.model_index].ViaRect[0].x + temp_via.position.x;
        temp_via.ViaRect.placedLL.y = drc_info.Via_model[temp_via.model_index].ViaRect[0].y + temp_via.position.y;
        temp_via.ViaRect.placedUR.x = drc_info.Via_model[temp_via.model_index].ViaRect[1].x + temp_via.position.x;
        temp_via.ViaRect.placedUR.y = drc_info.Via_model[temp_via.model_index].ViaRect[1].y + temp_via.position.y;
        // LowerMetalRect
        temp_via.LowerMetalRect.metal = drc_info.Via_model[temp_via.model_index].LowerIdx;
        temp_via.LowerMetalRect.placedCenter = temp_via.position;
        temp_via.LowerMetalRect.placedLL.x = drc_info.Via_model[temp_via.model_index].LowerRect[0].x + temp_via.position.x;
        temp_via.LowerMetalRect.placedLL.y = drc_info.Via_model[temp_via.model_index].LowerRect[0].y + temp_via.position.y;
        temp_via.LowerMetalRect.placedUR.x = drc_info.Via_model[temp_via.model_index].LowerRect[1].x + temp_via.position.x;
        temp_via.LowerMetalRect.placedUR.y = drc_info.Via_model[temp_via.model_index].LowerRect[1].y + temp_via.position.y;
        // UpperMetalRect
        temp_via.UpperMetalRect.metal = drc_info.Via_model[temp_via.model_index].UpperIdx;
        temp_via.UpperMetalRect.placedCenter = temp_via.position;
        temp_via.UpperMetalRect.placedLL.x = drc_info.Via_model[temp_via.model_index].UpperRect[0].x + temp_via.position.x;
        temp_via.UpperMetalRect.placedLL.y = drc_info.Via_model[temp_via.model_index].UpperRect[0].y + temp_via.position.y;
        temp_via.UpperMetalRect.placedUR.x = drc_info.Via_model[temp_via.model_index].UpperRect[1].x + temp_via.position.x;
        temp_via.UpperMetalRect.placedUR.y = drc_info.Via_model[temp_via.model_index].UpperRect[1].y + temp_via.position.y;
        Nets[i].seg[j].candis[k].vias.push_back(temp_via);
      }
    }
  }
};

void GlobalRouter::NetToNodeNet(PnRDB::hierNode& HierNode, RouterDB::Net& net, int net_index) {
  PnRDB::point tpoint;
  // including via
  // std::cout<<"Start NetToNodeNet"<<std::endl;
  for (unsigned int i = 0; i < net.seg.size(); i++) {
    // std::cout<<"seg "<<i<<std::endl;
    if (net.seg[i].chosenCand == -1) {
      continue;
    }
    for (unsigned int j = 0; j < net.seg[i].candis[net.seg[i].chosenCand].metals.size(); j++) {
      // std::cout<<"metal "<<j<< "size "<<net.seg[i].candis[net.seg[i].chosenCand].metals.size()<<std::endl;
      PnRDB::Metal temp_metal;
      temp_metal.MetalIdx = net.seg[i].candis[net.seg[i].chosenCand].metals[j].MetalIdx;
      temp_metal.width = net.seg[i].candis[net.seg[i].chosenCand].metals[j].width;
      // std::cout<<"checkpoint 1"<<std::endl;
      tpoint.x = net.seg[i].candis[net.seg[i].chosenCand].metals[j].LinePoint[0].x;
      tpoint.y = net.seg[i].candis[net.seg[i].chosenCand].metals[j].LinePoint[0].y;
      temp_metal.LinePoint.push_back(tpoint);
      tpoint.x = net.seg[i].candis[net.seg[i].chosenCand].metals[j].LinePoint[1].x;
      tpoint.y = net.seg[i].candis[net.seg[i].chosenCand].metals[j].LinePoint[1].y;
      temp_metal.LinePoint.push_back(tpoint);
      temp_metal.MetalRect.metal = drc_info.Metal_info[net.seg[i].candis[net.seg[i].chosenCand].metals[j].MetalRect.metal].name;
      // std::cout<<"checkpoint 2"<<std::endl;
      temp_metal.MetalRect.placedBox.LL.x = net.seg[i].candis[net.seg[i].chosenCand].metals[j].MetalRect.placedLL.x;
      temp_metal.MetalRect.placedBox.LL.y = net.seg[i].candis[net.seg[i].chosenCand].metals[j].MetalRect.placedLL.y;
      temp_metal.MetalRect.placedBox.UR.x = net.seg[i].candis[net.seg[i].chosenCand].metals[j].MetalRect.placedUR.x;
      temp_metal.MetalRect.placedBox.UR.y = net.seg[i].candis[net.seg[i].chosenCand].metals[j].MetalRect.placedUR.y;
      temp_metal.MetalRect.placedCenter.x = net.seg[i].candis[net.seg[i].chosenCand].metals[j].MetalRect.placedCenter.x;
      temp_metal.MetalRect.placedCenter.y = net.seg[i].candis[net.seg[i].chosenCand].metals[j].MetalRect.placedCenter.y;
      // std::cout<<"checkpoint 3"<<std::endl;
      HierNode.Nets[net_index].path_metal.push_back(temp_metal);
    }

    for (unsigned int j = 0; j < net.seg[i].candis[net.seg[i].chosenCand].vias.size(); j++) {
      // std::cout<<"vias "<<j<<" size "<<net.seg[i].candis[net.seg[i].chosenCand].vias.size()<<std::endl;
      PnRDB::Via temp_via;
      ConvertToViaPnRDB_Placed_Placed(temp_via, net.seg[i].candis[net.seg[i].chosenCand].vias[j]);
      HierNode.Nets[net_index].path_via.push_back(temp_via);
    }
  }
};
/*
void GlobalRouter::PowerNetToNodePowerNet(PnRDB::hierNode& HierNode, RouterDB::PowerNet& net, int net_index){
  PnRDB::point tpoint;

  for(int i=0;i<net.path_metal.size();i++){
             PnRDB::Metal temp_metal;
             temp_metal.MetalIdx = net.path_metal[j].MetalIdx;
             temp_metal.width = net.path_metal[j].width;
             //std::cout<<"checkpoint 1"<<std::endl;
             tpoint.x = net.path_metal[j].LinePoint[0].x;
             tpoint.y = net.path_metal[j].LinePoint[0].y;
             temp_metal.LinePoint.push_back(tpoint);
             tpoint.x = net.path_metal[j].LinePoint[1].x;
             tpoint.y = net.path_metal[j].LinePoint[1].y;
             temp_metal.LinePoint.push_back(tpoint);
             temp_metal.MetalRect.metal = drc_info.Metal_info[net.path_metal[j].MetalRect.metal].name;
             //std::cout<<"checkpoint 2"<<std::endl;
             temp_metal.MetalRect.placedBox.LL.x = net.path_metal[j].MetalRect.placedLL.x;
             temp_metal.MetalRect.placedBox.LL.y = net.path_metal[j].MetalRect.placedLL.y;
             temp_metal.MetalRect.placedBox.UR.x = net.path_metal[j].MetalRect.placedUR.x;
             temp_metal.MetalRect.placedBox.UR.y = net.path_metal[j].MetalRect.placedUR.y;
             temp_metal.MetalRect.placedBox.UL.x = net.path_metal[j].MetalRect.placedLL.x;
             temp_metal.MetalRect.placedBox.UL.y = net.path_metal[j].MetalRect.placedUR.y;
             temp_metal.MetalRect.placedBox.LR.x = net.path_metal[j].MetalRect.placedUR.x;
             temp_metal.MetalRect.placedBox.LR.y = net.path_metal[j].MetalRect.placedLL.y;
             temp_metal.MetalRect.placedCenter.x = net.path_metal[j].MetalRect.placedCenter.x;
             temp_metal.MetalRect.placedCenter.y = net.path_metal[j].MetalRect.placedCenter.y;
             //std::cout<<"checkpoint 3"<<std::endl;
             HierNode.PowerNets[net_index].path_metal.push_back(temp_metal);
      }

  for(int i=0;i<net.path_via.size();i++){
             PnRDB::Via temp_via;
ConvertToViaPnRDB_Placed_Placed(temp_via,net.path_via[i]);
             HierNode.PowerNets[net_index].path_via.push_back(temp_via);

     }

};


void GlobalRouter::PowerNetToNodeInterMetal(PnRDB::hierNode& HierNode, RouterDB::PowerNet& net){
  //std::cout<<"Start NetToNodeInterMetal"<<std::endl;
  //blockspin to intermetal

  for(int i=0;i<net.path_metal.size();i++){
             PnRDB::contact temp_contact;
             ConvertToContactPnRDB_Placed_Origin(temp_contact, net.path_metal[i].MetalRect);
             HierNode.interMetals.push_back(temp_contact);
     }

  for(int i=0;i<net.path_via.size()i++){
             PnRDB::Via temp_via;
ConvertToViaPnRDB_Placed_Origin(temp_via, net.path_via[i]);
             HierNode.interVias.push_back(temp_via);

     }

};

void GlobalRouter::PowerGridToNodeInterMetal(PnRDB::hierNode& HierNode, RouterDB::PowerGrid& net){
  //std::cout<<"Start NetToNodeInterMetal"<<std::endl;
  //blockspin to intermetal

  for(int i=0;i<net.metals.size();i++){
             PnRDB::contact temp_contact;
             ConvertToContactPnRDB_Placed_Origin(temp_contact, net.metals[i].MetalRect);
             HierNode.interMetals.push_back(temp_contact);
     }

  for(int i=0;i<net.vias.size()i++){
             PnRDB::Via temp_via;
ConvertToViaPnRDB_Placed_Origin(temp_via, net.vias[i]);
             HierNode.interVias.push_back(temp_via);

     }

};
*/

void GlobalRouter::NetToNodeInterMetal(PnRDB::hierNode& HierNode, RouterDB::Net& net) {
  // std::cout<<"Start NetToNodeInterMetal"<<std::endl;
  // blockspin to intermetal
  for (unsigned int i = 0; i < net.connected.size(); i++) {
    if (net.connected[i].type == RouterDB::BLOCK) {
      for (unsigned int j = 0; j < Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts.size(); j++) {
        PnRDB::contact temp_contact;
        ConvertToContactPnRDB_Placed_Origin(temp_contact, Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts[j]);
        HierNode.interMetals.push_back(temp_contact);
      }
      for (unsigned int j = 0; j < Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias.size(); j++) {
        PnRDB::Via temp_via;
        ConvertToViaPnRDB_Placed_Origin(temp_via, Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias[j]);
        HierNode.interVias.push_back(temp_via);
      }
    }
  }

  // std::cout<<"Via"<<std::endl;
  // including via
  for (unsigned int i = 0; i < net.seg.size(); i++) {
    // std::cout<<"seg "<<i<<std::endl;
    if (net.seg[i].chosenCand == -1) {
      continue;
    }
    for (unsigned int j = 0; j < net.seg[i].candis[net.seg[i].chosenCand].metals.size(); j++) {
      // std::cout<<"metals "<<j<<std::endl;

      PnRDB::contact temp_contact;
      ConvertToContactPnRDB_Placed_Origin(temp_contact, net.seg[i].candis[net.seg[i].chosenCand].metals[j].MetalRect);
      HierNode.interMetals.push_back(temp_contact);
    }
    for (unsigned int j = 0; j < net.seg[i].candis[net.seg[i].chosenCand].vias.size(); j++) {
      // std::cout<<"vias "<<j<<std::endl;

      PnRDB::Via temp_via;
      ConvertToViaPnRDB_Placed_Origin(temp_via, net.seg[i].candis[net.seg[i].chosenCand].vias[j]);

      HierNode.interVias.push_back(temp_via);
    }
  }
  // std::cout<<"END par"<<std::endl;
};

void GlobalRouter::ConvertToContactPnRDB_Placed_Origin(PnRDB::contact& pnr_contact, RouterDB::contact& router_contact) {
  PnRDB::point temp_point;
  pnr_contact.metal = drc_info.Metal_info[router_contact.metal].name;
  pnr_contact.originBox.LL.x = router_contact.placedLL.x;
  pnr_contact.originBox.LL.y = router_contact.placedLL.y;
  pnr_contact.originBox.UR.x = router_contact.placedUR.x;
  pnr_contact.originBox.UR.y = router_contact.placedUR.y;
  pnr_contact.originCenter.x = router_contact.placedCenter.x;
  pnr_contact.originCenter.y = router_contact.placedCenter.y;
};

void GlobalRouter::ConvertToViaPnRDB_Placed_Origin(PnRDB::Via& temp_via, RouterDB::Via& router_via) {
  // wbxu: placed field -> origin field [fixed]
  PnRDB::point temp_point;
  temp_via.model_index = router_via.model_index;
  temp_via.originpos.x = router_via.position.x;
  temp_via.originpos.y = router_via.position.y;
  // viarect
  temp_via.ViaRect.metal = drc_info.Via_info[router_via.ViaRect.metal].name;
  temp_via.ViaRect.originBox.LL.x = router_via.ViaRect.placedLL.x;
  temp_via.ViaRect.originBox.LL.y = router_via.ViaRect.placedLL.y;
  temp_via.ViaRect.originBox.UR.x = router_via.ViaRect.placedUR.x;
  temp_via.ViaRect.originBox.UR.y = router_via.ViaRect.placedUR.y;
  temp_via.ViaRect.originCenter.x = router_via.ViaRect.placedCenter.x;
  temp_via.ViaRect.originCenter.y = router_via.ViaRect.placedCenter.y;

  // LowerMetalRect
  temp_via.LowerMetalRect.metal = drc_info.Metal_info[router_via.LowerMetalRect.metal].name;
  temp_via.LowerMetalRect.originBox.LL.x = router_via.LowerMetalRect.placedLL.x;
  temp_via.LowerMetalRect.originBox.LL.y = router_via.LowerMetalRect.placedLL.y;
  temp_via.LowerMetalRect.originBox.UR.x = router_via.LowerMetalRect.placedUR.x;
  temp_via.LowerMetalRect.originBox.UR.y = router_via.LowerMetalRect.placedUR.y;
  temp_via.LowerMetalRect.originCenter.x = router_via.LowerMetalRect.placedCenter.x;
  temp_via.LowerMetalRect.originCenter.y = router_via.LowerMetalRect.placedCenter.y;

  // UpperMetalRect
  temp_via.UpperMetalRect.metal = drc_info.Metal_info[router_via.UpperMetalRect.metal].name;
  temp_via.UpperMetalRect.originBox.LL.x = router_via.UpperMetalRect.placedLL.x;
  temp_via.UpperMetalRect.originBox.LL.y = router_via.UpperMetalRect.placedLL.y;
  temp_via.UpperMetalRect.originBox.UR.x = router_via.UpperMetalRect.placedUR.x;
  temp_via.UpperMetalRect.originBox.UR.y = router_via.UpperMetalRect.placedUR.y;
  temp_via.UpperMetalRect.originCenter.x = router_via.UpperMetalRect.placedCenter.x;
  temp_via.UpperMetalRect.originCenter.y = router_via.UpperMetalRect.placedCenter.y;
};

void GlobalRouter::ConvertToContactPnRDB_Placed_Placed(PnRDB::contact& pnr_contact, RouterDB::contact& router_contact) {
  PnRDB::point temp_point;
  pnr_contact.metal = drc_info.Metal_info[router_contact.metal].name;
  pnr_contact.placedBox.LL.x = router_contact.placedLL.x;
  pnr_contact.placedBox.LL.y = router_contact.placedLL.y;
  pnr_contact.placedBox.UR.x = router_contact.placedUR.x;
  pnr_contact.placedBox.UR.y = router_contact.placedUR.y;
  pnr_contact.placedCenter.x = router_contact.placedCenter.x;
  pnr_contact.placedCenter.y = router_contact.placedCenter.y;
};

void GlobalRouter::ConvertToViaPnRDB_Placed_Placed(PnRDB::Via& temp_via, RouterDB::Via& router_via) {
  // wbxu: placed field -> origin field [fixed]
  PnRDB::point temp_point;
  temp_via.model_index = router_via.model_index;
  temp_via.placedpos.x = router_via.position.x;
  temp_via.placedpos.y = router_via.position.y;
  // viarect
  temp_via.ViaRect.metal = drc_info.Via_info[router_via.ViaRect.metal].name;
  temp_via.ViaRect.placedBox.LL.x = router_via.ViaRect.placedLL.x;
  temp_via.ViaRect.placedBox.LL.y = router_via.ViaRect.placedLL.y;
  temp_via.ViaRect.placedBox.UR.x = router_via.ViaRect.placedUR.x;
  temp_via.ViaRect.placedBox.UR.y = router_via.ViaRect.placedUR.y;
  temp_via.ViaRect.placedCenter.x = router_via.ViaRect.placedCenter.x;
  temp_via.ViaRect.placedCenter.y = router_via.ViaRect.placedCenter.y;

  // LowerMetalRect
  temp_via.LowerMetalRect.metal = drc_info.Metal_info[router_via.LowerMetalRect.metal].name;
  temp_via.LowerMetalRect.placedBox.LL.x = router_via.LowerMetalRect.placedLL.x;
  temp_via.LowerMetalRect.placedBox.LL.y = router_via.LowerMetalRect.placedLL.y;
  temp_via.LowerMetalRect.placedBox.UR.x = router_via.LowerMetalRect.placedUR.x;
  temp_via.LowerMetalRect.placedBox.UR.y = router_via.LowerMetalRect.placedUR.y;
  temp_via.LowerMetalRect.placedCenter.x = router_via.LowerMetalRect.placedCenter.x;
  temp_via.LowerMetalRect.placedCenter.y = router_via.LowerMetalRect.placedCenter.y;

  // UpperMetalRect
  temp_via.UpperMetalRect.metal = drc_info.Metal_info[router_via.UpperMetalRect.metal].name;
  temp_via.UpperMetalRect.placedBox.LL.x = router_via.UpperMetalRect.placedLL.x;
  temp_via.UpperMetalRect.placedBox.LL.y = router_via.UpperMetalRect.placedLL.y;
  temp_via.UpperMetalRect.placedBox.UR.x = router_via.UpperMetalRect.placedUR.x;
  temp_via.UpperMetalRect.placedBox.UR.y = router_via.UpperMetalRect.placedUR.y;
  temp_via.UpperMetalRect.placedCenter.x = router_via.UpperMetalRect.placedCenter.x;
  temp_via.UpperMetalRect.placedCenter.y = router_via.UpperMetalRect.placedCenter.y;
};

void GlobalRouter::NetToNodeBlockPins(PnRDB::hierNode& HierNode, RouterDB::Net& net) {
  auto logger = spdlog::default_logger()->clone("router.GlobalRouter.NetToNodeBlockPins");

  // std::cout<<"Start NetToNodeBlockPins"<<std::endl;
  // wbxu: when update hierNode data, all the coordinates should be stored into
  // origin fields, NOT placed fields. Because the hierNode data will be checkin back to higher nodes [fixed]
  PnRDB::pin temp_pin;
  // PnRDB::point temp_point;
  // wbxu: the name should be the name of terminal, not the net name! [fixed]
  if (net.terminal_idx == -1) {
    logger->warn("Router-Warning: cannot found terminal conntecting to net");
    return;
  }
  temp_pin.name = Terminals.at(net.terminal_idx).name;

  // blockspin to intermetal
  for (unsigned int i = 0; i < net.connected.size(); i++) {
    if (net.connected[i].type == RouterDB::BLOCK) {
      for (unsigned int j = 0; j < Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts.size(); j++) {
        PnRDB::contact temp_contact;
        ConvertToContactPnRDB_Placed_Origin(temp_contact, Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts[j]);
        temp_pin.pinContacts.push_back(temp_contact);
      }
      for (unsigned int j = 0; j < Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias.size(); j++) {
        PnRDB::Via temp_via;
        ConvertToViaPnRDB_Placed_Origin(temp_via, Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias[j]);
        temp_pin.pinVias.push_back(temp_via);
      }
    }
  }

  for (unsigned int i = 0; i < net.seg.size(); i++) {
    // wbxu: need to check chosenCand to avoid exeption [fixed]
    if (net.seg[i].chosenCand == -1) {
      continue;
    }
    for (unsigned int j = 0; j < net.seg[i].candis[net.seg[i].chosenCand].metals.size(); j++) {
      // wbxu: placed field -> origin field [fixed]
      PnRDB::contact temp_contact;
      ConvertToContactPnRDB_Placed_Origin(temp_contact, net.seg[i].candis[net.seg[i].chosenCand].metals[j].MetalRect);
      temp_pin.pinContacts.push_back(temp_contact);
    }
    for (unsigned int j = 0; j < net.seg[i].candis[net.seg[i].chosenCand].vias.size(); j++) {
      // wbxu: placed field -> origin field [fixed]
      PnRDB::Via temp_via;
      ConvertToViaPnRDB_Placed_Origin(temp_via, net.seg[i].candis[net.seg[i].chosenCand].vias[j]);
      temp_pin.pinVias.push_back(temp_via);
    }
  }

  HierNode.blockPins.push_back(temp_pin);
  // std::cout<<"END NetToNodeBlockPins"<<std::endl;
};

void GlobalRouter::TerminalToNodeTerminal(PnRDB::hierNode& HierNode) {
  // including via
  // includeing blockpin also

  for (unsigned int i = 0; i < this->Terminals.size(); i++) {
    // pins
    // std::cout<<"Info:: update terminal "<<i<<std::endl;
    for (unsigned int j = 0; j < this->Terminals[i].termContacts.size(); j++) {
      PnRDB::contact temp_contact;
      ConvertToContactPnRDB_Placed_Placed(temp_contact, this->Terminals[i].termContacts[j]);

      HierNode.Terminals[i].termContacts.push_back(temp_contact);
    }
  }
};

void GlobalRouter::BlockInterMetalToNodeInterMetal(PnRDB::hierNode& HierNode) {
  // including via
  // includeing blockpin also

  for (unsigned int i = 0; i < Blocks.size(); i++) {
    /*
           //pins
           for(int j=0;j<Blocks[i].pins.size();j++){
               for(int k=0;k<Blocks[i].pins[j].pinContacts;k++){
                    //to internal metal

                 PnRDB::contact temp_contact;
    ConvertToContactPnRDB_Placed_Origin(temp_contact,Blocks[i].pins[j].pinContacts[k]);
                 HierNode.interMetals.push_back(temp_contact);

                  }
               for(int k=0;k<Blocks[i].pins[j].pinVias;k++){
                 //to internal via
                 PnRDB::Via temp_via;
                 ConvertToViaPnRDB_Placed_Origin(temp_via, Blocks[i].pins[j].pinVias[k]);

                 HierNode.interVias.push_back(temp_via);

                  }
              }
    */
    // InternalMetal
    for (unsigned int j = 0; j < Blocks[i].InternalMetal.size(); j++) {
      // to internal metal
      PnRDB::contact temp_contact;
      ConvertToContactPnRDB_Placed_Origin(temp_contact, Blocks[i].InternalMetal[j]);
      HierNode.interMetals.push_back(temp_contact);
    }
    // via
    for (unsigned int j = 0; j < Blocks[i].InternalVia.size(); j++) {
      // to interal via
      PnRDB::Via temp_via;
      ConvertToViaPnRDB_Placed_Origin(temp_via, Blocks[i].InternalVia[j]);
      HierNode.interVias.push_back(temp_via);
    }
  }
  // block pin also becomes internal metal
};

void GlobalRouter::AddConnectedContactToNodeNet(PnRDB::hierNode& HierNode, RouterDB::Net& net, int net_index) {
  // std::cout<<"AddConnectedContactToNodeNet net "<<net_index<<std::endl;
  HierNode.Nets.at(net_index).connectedContact.clear();
  HierNode.Nets.at(net_index).connectedContact.resize(HierNode.Nets.at(net_index).connected.size());
  int currM = 0;
  for (unsigned int i = 0; i < net.seg.size(); i++) {  // for each net segment
    // std::cout<<"seg "<<i<<std::endl;
    int sel = net.seg.at(i).chosenCand;
    if (sel == -1) {
      continue;
    }
    // 1. segment source
    RouterDB::NType stype = net.seg.at(i).sourceType.type;
    int siter = net.seg.at(i).sourceType.iter;
    int siter2 = net.seg.at(i).sourceType.iter2;
    int smetal = net.seg.at(i).candis.at(sel).metals.at(0).MetalIdx;
    int sx = net.seg.at(i).candis.at(sel).metals.at(0).LinePoint.at(0).x;
    int sy = net.seg.at(i).candis.at(sel).metals.at(0).LinePoint.at(0).y;
    // std::cout<<"\tsource type: "<<stype<<" iter: "<<siter<<" iter2: "<<siter2<<" metal: "<<smetal<<" x: "<<sx<<" y: "<<sy<<" current metal:
    // "<<currM<<std::endl;
    AddConnectedContactFunc(HierNode, net, net_index, stype, siter, siter2, smetal, sx, sy, currM);
    // 2. segment dest
    stype = net.seg.at(i).destType.type;
    siter = net.seg.at(i).destType.iter;
    siter2 = net.seg.at(i).destType.iter2;
    smetal = net.seg.at(i).candis.at(sel).metals.back().MetalIdx;
    sx = net.seg.at(i).candis.at(sel).metals.back().LinePoint.back().x;
    sy = net.seg.at(i).candis.at(sel).metals.back().LinePoint.back().y;
    currM += (net.seg.at(i).candis.at(sel).metals.size() - 1);
    // std::cout<<"\tdest type: "<<stype<<" iter: "<<siter<<" iter2: "<<siter2<<" metal: "<<smetal<<" x: "<<sx<<" y: "<<sy<<" current metal:
    // "<<currM<<std::endl;
    AddConnectedContactFunc(HierNode, net, net_index, stype, siter, siter2, smetal, sx, sy, currM);
    ++currM;
  }
}

void GlobalRouter::AddConnectedContactFunc(PnRDB::hierNode& HierNode, RouterDB::Net& net, int net_index, RouterDB::NType stype, int siter, int siter2,
                                           int smetal, int sx, int sy, int mIdx) {
  auto logger = spdlog::default_logger()->clone("router.GlobalRouter.AddConnectedContactFunc");

  PnRDB::globalContact tmpC;
  tmpC.metalIdx = mIdx;
  if (stype == RouterDB::BLOCK) {  // block pin
    int pos = -1;
    for (unsigned int k = 0; k < HierNode.Nets.at(net_index).connected.size(); ++k) {
      if (HierNode.Nets.at(net_index).connected.at(k).type == PnRDB::Block && HierNode.Nets.at(net_index).connected.at(k).iter == siter &&
          HierNode.Nets.at(net_index).connected.at(k).iter2 == siter2) {
        pos = k;
        break;
      }
    }
    if (pos != -1) {
      int dist = INT_MAX;
      bool mark = false;
      std::vector<PnRDB::contact>::iterator target =
          HierNode.Blocks.at(siter2).instance.at(HierNode.Blocks.at(siter2).selectedInstance).blockPins.at(siter).pinContacts.end();
      for (std::vector<PnRDB::contact>::iterator cit =
               HierNode.Blocks.at(siter2).instance.at(HierNode.Blocks.at(siter2).selectedInstance).blockPins.at(siter).pinContacts.begin();
           cit != HierNode.Blocks.at(siter2).instance.at(HierNode.Blocks.at(siter2).selectedInstance).blockPins.at(siter).pinContacts.end(); ++cit) {
        if (drc_info.Metalmap[cit->metal] != smetal) {
          continue;
        }
        if (sx >= cit->placedBox.LL.x && sx <= cit->placedBox.UR.x && sy >= cit->placedBox.LL.y && sy <= cit->placedBox.UR.y) {
          tmpC.conTact = (*cit);
          HierNode.Nets.at(net_index).connectedContact.at(pos) = tmpC;
          mark = true;
          break;
        } else {
          {
            auto cand = std::abs(sx - cit->placedBox.LL.x) + std::abs(sy - cit->placedBox.LL.y);
            if (dist > cand) {
              dist = cand;
              target = cit;
            }
          }
          {
            auto cand = std::abs(sx - cit->placedBox.UR.x) + std::abs(sy - cit->placedBox.UR.y);
            if (dist > cand) {
              dist = cand;
              target = cit;
            }
          }
          {
            auto cand = std::abs(sx - cit->placedBox.UR.x) + std::abs(sy - cit->placedBox.LL.y);
            if (dist > cand) {
              dist = cand;
              target = cit;
            }
          }
          {
            auto cand = std::abs(sx - cit->placedBox.LL.x) + std::abs(sy - cit->placedBox.UR.y);
            if (dist > cand) {
              dist = cand;
              target = cit;
            }
          }
        }
      }
      if (!mark && target != HierNode.Blocks.at(siter2).instance.at(HierNode.Blocks.at(siter2).selectedInstance).blockPins.at(siter).pinContacts.end()) {
        tmpC.conTact = (*target);
        HierNode.Nets.at(net_index).connectedContact.at(pos) = tmpC;
      }
    }
  } else if (stype == RouterDB::TERMINAL && this->isTop) {
    int pos = -1;
    for (unsigned int k = 0; k < HierNode.Nets.at(net_index).connected.size(); ++k) {
      if (HierNode.Nets.at(net_index).connected.at(k).type == PnRDB::Terminal && HierNode.Nets.at(net_index).connected.at(k).iter == siter &&
          HierNode.Nets.at(net_index).connected.at(k).iter2 == siter2) {
        pos = k;
        break;
      }
    }
    if (pos != -1) {
      int dist = INT_MAX;
      bool mark = false;
      std::vector<PnRDB::contact>::iterator target = HierNode.Terminals.at(siter).termContacts.end();
      for (std::vector<PnRDB::contact>::iterator cit = HierNode.Terminals.at(siter).termContacts.begin();
           cit != HierNode.Terminals.at(siter).termContacts.end(); ++cit) {
        if (drc_info.Metalmap[cit->metal] != smetal) {
          continue;
        }
        if (sx >= cit->placedBox.LL.x && sx <= cit->placedBox.UR.x && sy >= cit->placedBox.LL.y && sy <= cit->placedBox.UR.y) {
          tmpC.conTact = (*cit);
          HierNode.Nets.at(net_index).connectedContact.at(pos) = tmpC;
          mark = true;
          break;
        } else {
          {
            auto cand = std::abs(sx - cit->placedBox.LL.x) + std::abs(sy - cit->placedBox.LL.y);
            if (dist > cand) {
              dist = cand;
              target = cit;
            }
          }
          {
            auto cand = std::abs(sx - cit->placedBox.UR.x) + std::abs(sy - cit->placedBox.UR.y);
            if (dist > cand) {
              dist = cand;
              target = cit;
            }
          }
          {
            auto cand = std::abs(sx - cit->placedBox.UR.x) + std::abs(sy - cit->placedBox.LL.y);
            if (dist > cand) {
              dist = cand;
              target = cit;
            }
          }
          {
            auto cand = std::abs(sx - cit->placedBox.LL.x) + std::abs(sy - cit->placedBox.UR.y);
            if (dist > cand) {
              dist = cand;
              target = cit;
            }
          }
        }
      }
      if (!mark && target != HierNode.Terminals.at(siter).termContacts.end()) {
        tmpC.conTact = (*target);
        HierNode.Nets.at(net_index).connectedContact.at(pos) = tmpC;
      }
    }
  } else {
    logger->error("Router-Error: incorrect source type");
  }
}

void GlobalRouter::ReturnHierNode(PnRDB::hierNode& HierNode) {
  HierNode.blockPins.clear();
  HierNode.interMetals.clear();
  HierNode.interVias.clear();

  for (unsigned int i = 0; i < HierNode.Nets.size(); i++) {
    HierNode.Nets[i].path_metal.clear();
    HierNode.Nets[i].path_via.clear();
  }

  if (isTop == 1) {
    // return terminal to node terminal
    // std::cout<<"starting: terminal to node terminal"<<std::endl;
    TerminalToNodeTerminal(HierNode);
    // std::cout<<"starting: terminal to node terminal"<<std::endl;
  }
  // distinguish those two net
  // std::cout<<"Start ReturnHierNode"<<std::endl;
  for (unsigned int i = 0; i < Nets.size(); i++) {
    // std::cout<<i<<" ter? "<<Nets[i].isTerminal<<std::endl;
    if (Nets[i].isTerminal) {
      // wbxu: not only nets should be put into NodeBlockPins, but also those pins connected to nets
      // should be put into NodeBlockPins
      // return blockpins
      // std::cout<<"starting: Net to node Block pins"<<std::endl;
      NetToNodeBlockPins(HierNode, Nets[i]);
      // std::cout<<"end: Net to node Block pins"<<std::endl;

    } else {
      // wbxu: not only nets should be put into NodeInterMetal, but also those pins connected to nets
      // should be put into NodeInterMetal
      // HierNode.interMetals
      // std::cout<<"starting: Net to node internal metal"<<std::endl;
      NetToNodeInterMetal(HierNode, Nets[i]);
      // std::cout<<"end: Net to node internal metal"<<std::endl;
    }

    for (unsigned int j = 0; j < HierNode.Nets.size(); j++) {
      if (HierNode.Nets[j].name == Nets[i].netName) {
        HierNode.Nets.at(j).path_metal.clear();
        HierNode.Nets.at(j).path_via.clear();
        // std::cout<<"starting: Net to node net"<<std::endl;
        NetToNodeNet(HierNode, Nets[i], j);
        AddConnectedContactToNodeNet(HierNode, Nets.at(i), j);
        // std::cout<<"end: Net to node net"<<std::endl;
        break;
      }
    }
  }
  /*
  //internal metal via & power nets
    for(int i=0;i<PowerNets.size();i++){
        for(int j=0;j<HierNode.PowerNets.size();j++){
            if(HierNode.PowerNets[j].name == PowerNets[i].netName){
                 HierNode.Nets.at(j).path_metal.clear();
                 HierNode.Nets.at(j).path_via.clear();
                 PowerNetToNodePowerNet(HierNode, PowerNets[i], j);
                 break;
              }
           }
         PowerNetToNodeInterMetal(HierNode, PowerNets[i]);
       }

    PowerGridToNodeInterMetal(HierNode, Vdd_grid);
    PowerGridToNodeInterMetal(HierNode, Gnd_grid);
  */

  // std::cout<<"starting: block intermetal to block intermetal"<<std::endl;
  BlockInterMetalToNodeInterMetal(HierNode);
  // std::cout<<"end: block intermetal to block intermetal"<<std::endl;
  // std::cout<<"End ReturnHierNode"<<std::endl;
};
