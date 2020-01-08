#include "PnRdatabase.h"

#include <iostream>
#include <fstream>
#include <iomanip>
#include <algorithm>

using namespace nlohmann;

#include <gtest/gtest.h>

/*
static bool EndsWith( const string& str, const string& pat)
{
    return str.size() >= pat.size() && str.substr( str.size() - pat.size(), pat.size()) == pat;
}
*/
static bool EndsWith( const string& str, const string& pat)
{
  return std::mismatch( str.rbegin(), str.rend(), pat.rbegin(), pat.rend()).second == pat.rend();
}


TEST( EndsWithTest, Test1)
{
    EXPECT_TRUE( EndsWith( "", ""));
    EXPECT_TRUE( EndsWith( "a", ""));
    EXPECT_FALSE( EndsWith( "", "a"));
    EXPECT_TRUE( EndsWith( "Steve Burns", "Burns"));
    EXPECT_FALSE( EndsWith( "Steve Burns", "Treefrog Steve Burns"));
}


PnRdatabase::PnRdatabase(string path, string topcell, string vname, string lefname, string mapname, string drname) {
  unitScale=2000;
  maxNode=0;
  cout<<"PnRDB-Info: reading data from path "<<path<<endl;

  if( drname == "HardDesignRules") {
      this->HardDesignRule();
      cout<<"PnRDB-Info: default PDK"<<std::endl;
  } else if( EndsWith( drname, ".rul")) {
      this->ReadDesignRule(path+"/"+drname);
      std::cout<<"PnRDB-Info: read PDK via "<<drname<<std::endl;
  } else if( EndsWith( drname, ".json")) {
      this->ReadPDKJSON(path+"/"+drname);
      std::cout<<"PnRDB-Info: read PDK via "<<drname<<std::endl;
  } else {
      std::cout<<"PnRDB-Error: unknown name for read PDK (HardDesignRules, *.rul, *.json): "<<drname<<std::endl;
      assert(0);
  }

  this->ReadLEF(path+"/"+lefname);
  this->ReadMap(path, mapname);
  this->ReadVerilog(path, vname, topcell);

  cout<<"PnRDB-Info: complete reading"<<endl;
}

queue<int> PnRdatabase::TraverseHierTree() {
  queue<int> Q;
  vector<string> color(hierTree.size(), "white");
  TraverseDFS(Q, color, topidx);
  return Q;
}

void PnRdatabase::TraverseDFS(queue<int>& Q, vector<string>& color, int idx) {
  color[idx]="gray";
  for(vector<PnRDB::blockComplex>::iterator it=hierTree.at(idx).Blocks.begin();it!=hierTree.at(idx).Blocks.end();++it) {
    if( it->child!=-1 && color[it->child].compare("white")==0 ) {
      TraverseDFS(Q, color, it->child);
    }
  }
  color[idx]="black";
  Q.push(idx);
}

PnRDB::hierNode PnRdatabase::CheckoutHierNode(int nodeID) {
  return hierTree[nodeID];
}

std::vector<PnRDB::hierNode> PnRdatabase::CheckoutHierNodeVec(int nodeID){
  std::vector<PnRDB::hierNode> nodeVec(hierTree[nodeID].PnRAS.size());
  for (unsigned int lidx = 0; lidx < hierTree[nodeID].PnRAS.size(); lidx++)
  {
    PnRDB::hierNode current_node = hierTree[nodeID];
    current_node.gdsFile = current_node.PnRAS[lidx].gdsFile;
    current_node.width = current_node.PnRAS[lidx].width;
    current_node.height = current_node.PnRAS[lidx].height;
    current_node.Blocks = current_node.PnRAS[lidx].Blocks;
    current_node.Terminals = current_node.PnRAS[lidx].Terminals;
    current_node.Nets = current_node.PnRAS[lidx].Nets;
    nodeVec[lidx] = current_node;
    nodeVec[lidx].LL = current_node.PnRAS[lidx].LL;
    nodeVec[lidx].UR = current_node.PnRAS[lidx].UR;
  }
  return nodeVec;
}

bool PnRdatabase::ReadMap(string fpath, string mapname) {
  cout<<"PnRDB-Info: reading map file "<<fpath+"/"+mapname<<endl;
  ifstream fin;
  string def;
  string mapfile=fpath+"/"+mapname;
  vector<string> temp;
  fin.exceptions(ifstream::failbit | ifstream::badbit);
  try {
    fin.open(mapfile.c_str());
    while(fin.peek()!=EOF) {
      getline(fin, def);
      if(def.compare("")==0) {continue;}
      temp = split_by_spaces_yg(def);
      if(temp.size()>=2) {
        gdsData.insert( std::pair<string,string>(temp[0],fpath+"/"+temp[1]) );
      }
    }
    fin.close();
    return true; 
  } catch(ifstream::failure& e) {
    cerr<<"PnRDB-Error: fail to read map file "<<endl;
  }
  return false;
}

static void updateContact( PnRDB::contact& c)
{
    c.originBox = c.placedBox;
    c.originCenter =  c.placedCenter;           
}

// [RA] need confirmation - wbxu
void PnRdatabase::updatePowerPins(PnRDB::pin& temp_pin){
 
  for(unsigned int i=0;i<temp_pin.pinContacts.size();i++){
      updateContact( temp_pin.pinContacts[i]);
  }

  for(unsigned int i=0;i<temp_pin.pinVias.size();i++){
      temp_pin.pinVias[i].originpos = temp_pin.pinVias[i].placedpos;
      updateContact( temp_pin.pinVias[i].ViaRect);
      updateContact( temp_pin.pinVias[i].UpperMetalRect);
      updateContact( temp_pin.pinVias[i].LowerMetalRect);
  }

};

void PnRdatabase::TransformNode(PnRDB::hierNode& updatedNode){
  //this function transform all points and inside the node
  //according to LL and orient
  //it recursively call other transform functions
  PnRDB::point LL = updatedNode.LL;
  std::vector<PnRDB::blockComplex>::iterator bit;
  TransformBlockComplexs(updatedNode.Blocks, LL);
  TransformTerminals(updatedNode.Terminals, LL);
  TransformPins(updatedNode.blockPins, LL, 0, 0, PnRDB::Omark::N);
  TransformContacts(updatedNode.interMetals, LL, 0, 0, PnRDB::Omark::N);
  TransformVias(updatedNode.interVias, LL, 0, 0, PnRDB::Omark::N);
}

void PnRdatabase::TransformTerminal(PnRDB::terminal &terminal, PnRDB::point LL){
  for (std::vector<PnRDB::contact>::iterator cit = terminal.termContacts.begin(); cit != terminal.termContacts.end(); cit++)
  {
    cit->placedBox = cit->placedBox + LL;
    cit->placedCenter = cit->placedCenter + LL;
  }
}

void PnRdatabase::TransformTerminals(std::vector<PnRDB::terminal> &terminals, PnRDB::point LL){
  for (std::vector<PnRDB::terminal>::iterator tit = terminals.begin(); tit != terminals.end(); tit++)
  {
    TransformTerminal(*tit, LL);
  }
}

void PnRdatabase::TransformBlock(PnRDB::block &block, PnRDB::point LL){
  int width = block.width, height = block.height;
  PnRDB::Omark ort = block.orient;
  TransformBbox(block.placedBox, LL, width, height, ort);
  TransformPoint(block.placedCenter, LL, width, height, ort);
  TransformPins(block.blockPins, LL, width, height, ort);
  TransformContacts(block.interMetals, LL, width, height, ort);
  TransformVias(block.interVias, LL, width, height, ort);
  TransformPins(block.dummy_power_pin, LL, width, height, ort);
}

void PnRdatabase::TransformBlocks(std::vector<PnRDB::block> &blocks, PnRDB::point LL){
  for (std::vector<PnRDB::block>::iterator bit = blocks.begin(); bit != blocks.end();bit++){
    TransformBlock(*bit, LL);
  }
}

void PnRdatabase::TransformBlockComplexs(std::vector<PnRDB::blockComplex> &bcs, PnRDB::point LL){
  for (std::vector<PnRDB::blockComplex>::iterator bit = bcs.begin(); bit != bcs.end();bit++){
    TransformBlockComplex(*bit, LL);
  }
}

void PnRdatabase::TransformBlockComplex(PnRDB::blockComplex &bc, PnRDB::point LL){
  TransformBlocks(bc.instance, LL);
}

void PnRdatabase::TransformPins(std::vector<PnRDB::pin> &pins, PnRDB::point LL,int width, int height, PnRDB::Omark ort){
  for (std::vector<PnRDB::pin>::iterator pit = pins.begin(); pit != pins.end();pit++){
    TransformPin(*pit, LL, width, height, ort);
  }
}

void PnRdatabase::TransformPin(PnRDB::pin &pin, PnRDB::point LL,int width, int height, PnRDB::Omark ort){
  TransformContacts(pin.pinContacts, LL, width, height, ort);
  TransformVias(pin.pinVias, LL, width, height, ort);
}

void PnRdatabase::TransformVias(std::vector<PnRDB::Via> &vias, PnRDB::point LL, int width, int height, PnRDB::Omark ort){
  for (std::vector<PnRDB::Via>::iterator vit = vias.begin(); vit != vias.end();vit++){
    TransformVia(*vit, LL, width, height, ort);
  }
}

void PnRdatabase::TransformVia(PnRDB::Via &via, PnRDB::point LL,int width, int height, PnRDB::Omark ort){
  TransformPoint(via.placedpos, LL, width, height, ort);
  TransformContact(via.UpperMetalRect, LL, width, height, ort);
  TransformContact(via.LowerMetalRect, LL, width, height, ort);
  TransformContact(via.ViaRect, LL, width, height, ort);
}

void PnRdatabase::TransformContacts(std::vector<PnRDB::contact> &contacts, PnRDB::point LL,int width, int height, PnRDB::Omark ort){
  for (std::vector<PnRDB::contact>::iterator cit = contacts.begin(); cit != contacts.end();cit++){
    TransformContact(*cit, LL, width, height, ort);
  }
}

void PnRdatabase::TransformContact(PnRDB::contact &contact, PnRDB::point LL,int width, int height, PnRDB::Omark ort){
  TransformBbox(contact.placedBox, LL, width, height, ort);
  TransformPoint(contact.placedCenter, LL, width, height, ort);
}

void PnRdatabase::TransformBboxs(std::vector<PnRDB::bbox> &bboxs, PnRDB::point LL, int width, int height, PnRDB::Omark ort){
  for (std::vector<PnRDB::bbox>::iterator bit = bboxs.begin(); bit != bboxs.end();bit++){
    TransformBbox(*bit, LL, width, height, ort);
  }
}

void PnRdatabase::TransformBbox(PnRDB::bbox &box, PnRDB::point LL,int width, int height, PnRDB::Omark ort){
  TransformPoint(box.LL, LL, width, height, ort);
  TransformPoint(box.UR, LL, width, height, ort);
}

void PnRdatabase::TransformPoints(std::vector<PnRDB::point> &points, PnRDB::point LL, int width, int height, PnRDB::Omark ort){
  for (std::vector<PnRDB::point>::iterator pit = points.begin(); pit != points.end();pit++){
    TransformPoint(*pit, LL, width, height, ort);
  }
}

void PnRdatabase::TransformPoint(PnRDB::point &p, PnRDB::point LL,int width, int height, PnRDB::Omark ort) {
  int WW=width; int HH=height; int X=p.x; int Y=p.y;
  switch(ort) {
    case PnRDB::N: p.x=X;	p.y=Y;
            break;
    case PnRDB::S: p.x=WW-X;	p.y=HH-Y;
            break;
    case PnRDB::W: p.x=HH-Y;	p.y=X;
            break;
    case PnRDB::E: p.x=Y;	p.y=WW-X;
            break;
    case PnRDB::FN:p.x=WW-X;	p.y=Y; 
            break;
    case PnRDB::FS:p.x=X;	p.y=HH-Y;
            break;
    case PnRDB::FW:p.x=Y;	p.y=X;
            break;
    case PnRDB::FE:p.x=HH-Y;	p.y=WW-X;
            break;
    default:p.x=X;	p.y=Y;
            break;
  }
  p = p + LL;
}

// [RA] need further modification for hierarchical issue - wbxu
void PnRdatabase::CheckinHierNode(int nodeID, const PnRDB::hierNode& updatedNode){
  //In fact, the original node, do not need to be updated. Just update father node is fine.
  //update the original node
  std::cout<<"CheckinHierNode\n";
  PnRDB::layoutAS tmpL;
  tmpL.gdsFile=updatedNode.gdsFile;
  tmpL.width=updatedNode.width;
  tmpL.height=updatedNode.height;
  tmpL.Blocks=updatedNode.Blocks;
  tmpL.Terminals=updatedNode.Terminals;
  tmpL.Nets=updatedNode.Nets;
  tmpL.LL = updatedNode.LL;
  tmpL.UR = updatedNode.UR;
  hierTree[nodeID].PnRAS.push_back(tmpL);

  hierTree[nodeID].isCompleted = 1;
  hierTree[nodeID].gdsFile = updatedNode.gdsFile;
  //update current node information
  for(unsigned int i=0;i<hierTree[nodeID].Blocks.size();i++){
     int sel=updatedNode.Blocks[i].selectedInstance;
     std::cout<<"Block "<<i<<" select "<<sel<<std::endl;
     if(sel<0 or sel>=updatedNode.Blocks[i].instNum) {std::cout<<"PnRDB-Error: unselected block "<<i<<std::endl;continue;}
     //std::cout<<"dB "<<hierTree[nodeID].Blocks[i].instNum<<std::endl;
     if(hierTree[nodeID].Blocks[i].instNum<updatedNode.Blocks[i].instNum) { // for capacitor, new data in place and route
       hierTree[nodeID].Blocks[i].instance.clear();
       hierTree[nodeID].Blocks[i].instance=updatedNode.Blocks[i].instance;
       hierTree[nodeID].Blocks[i].instNum=updatedNode.Blocks[i].instNum;
     }
     hierTree[nodeID].Blocks[i].selectedInstance=sel;
     for(int w=0;w<updatedNode.Blocks[i].instNum;++w) {
	 auto& lhs = hierTree[nodeID].Blocks[i].instance.at(w);
	 auto& rhs = updatedNode.Blocks[i].instance.at(w);

     //std::cout<<"\tchoice "<<w<<std::endl;
     //lhs.name = rhs.name;
     lhs.orient = rhs.orient;

     lhs.placedBox = rhs.placedBox;

     lhs.placedCenter = rhs.placedCenter;

     for(unsigned int j=0;j<lhs.blockPins.size();j++){
        for(unsigned int k=0;k<lhs.blockPins[j].pinContacts.size();k++){
           lhs.blockPins[j].pinContacts[k]= rhs.blockPins[j].pinContacts[k];
           }
        for(unsigned int k=0;k<lhs.blockPins[j].pinVias.size();k++){
           lhs.blockPins[j].pinVias[k]= rhs.blockPins[j].pinVias[k];
           }  
        }

     for(unsigned int j=0;j<lhs.interMetals.size();j++){
           lhs.interMetals[j]= rhs.interMetals[j];
        }

     for(unsigned int j=0;j<lhs.interVias.size();j++){
           lhs.interVias[j]= rhs.interVias[j];
        }     
     }
	 
  }

  hierTree[nodeID].router_report = updatedNode.router_report; //update router information

  //update terminals information when the node is top level
    //if(updatedNode.isTop==1)
    if(1){	 
       for(unsigned int i=0;i<hierTree[nodeID].Terminals.size();i++){
            hierTree[nodeID].Terminals[i].termContacts.clear();
           for(unsigned int j=0;j<updatedNode.Terminals[i].termContacts.size();j++){ //this line $$$$yaguang$$$$$
               hierTree[nodeID].Terminals[i].termContacts.push_back( updatedNode.Terminals[i].termContacts[j]  );
               //hierTree[nodeID].Terminals[i].termContacts[j].placedBox= updatedNode.Terminals[i].termContacts[j].placedBox;
	       //hierTree[nodeID].Terminals[i].termContacts[j].placedCenter= updatedNode.Terminals[i].termContacts[j].placedCenter;
               }
         }
       }
  
    unordered_map<string,int> updatedNode_net_map;
    for(unsigned int j=0;j<updatedNode.Nets.size();j++){
	const auto& net = updatedNode.Nets[j];
	assert( updatedNode_net_map.find( net.name) == updatedNode_net_map.end());
	updatedNode_net_map[net.name] = j;
    }

    for(unsigned int i=0;i<hierTree[nodeID].Nets.size();i++){
	auto& net = hierTree[nodeID].Nets[i];
	unordered_map<string,int>::const_iterator cit = updatedNode_net_map.find( net.name);
	if ( cit != updatedNode_net_map.end()) {
	    auto& net2 = updatedNode.Nets[cit->second];
	    net.path_metal = net2.path_metal;
	    net.path_via = net2.path_via;
	}
    }

    /*
  //update net information//////
  for(int i=0;i<hierTree[nodeID].Nets.size();i++){
     for(int j=0;j<updatedNode.Nets.size();j++){
          if(hierTree[nodeID].Nets[i].name ==updatedNode.Nets[j].name){
               hierTree[nodeID].Nets[i].path_metal = updatedNode.Nets[j].path_metal;
               hierTree[nodeID].Nets[i].path_via = updatedNode.Nets[j].path_via;
               break;
            }
        }
     }
    */

  std::cout<<"update power net\n";
  //update PowerNet information//////
  std::cout<<"hierTree power net size "<<hierTree[nodeID].PowerNets.size()<<std::endl;
  std::cout<<"updatedNode power net size "<<updatedNode.PowerNets.size()<<std::endl;
  for(unsigned int i=0;i<hierTree[nodeID].PowerNets.size();i++){
     for(unsigned int j=0;j<updatedNode.PowerNets.size();j++){
         if(hierTree[nodeID].PowerNets[i].name == updatedNode.PowerNets[j].name){
               hierTree[nodeID].PowerNets[i].path_metal = updatedNode.PowerNets[j].path_metal;
               hierTree[nodeID].PowerNets[i].path_via = updatedNode.PowerNets[j].path_via;
               hierTree[nodeID].PowerNets[i].connected = updatedNode.PowerNets[j].connected;
               hierTree[nodeID].PowerNets[i].dummy_connected = updatedNode.PowerNets[j].dummy_connected;
               hierTree[nodeID].PowerNets[i].Pins = updatedNode.PowerNets[j].Pins;
               break;
           }
         }
     }
   std::cout<<"node ID "<<nodeID<<std::endl;
   std::cout<<"hierTree power net size "<<hierTree[nodeID].PowerNets.size()<<std::endl;
   std::cout<<"updatedNode power net size "<<updatedNode.PowerNets.size()<<std::endl;

   hierTree[nodeID].blockPins=updatedNode.blockPins;
   hierTree[nodeID].interMetals=updatedNode.interMetals;
   hierTree[nodeID].interVias=updatedNode.interVias;

  //update father imformation//////
    std::cout<<"Update parent\n";
    for(unsigned int i=0;i<hierTree[nodeID].parent.size();i++){

     std::cout<<"Start update blocks in parent"<<std::endl;
     //update father blocks information
     auto& parent_node = hierTree[hierTree[nodeID].parent[i]];

     //there will be a bug for multi-aspect ratio Yaguang 1/1/2020
     std::cout<<"Update router report for parent"<<std::endl;
     for(int j=0;j<updatedNode.router_report.size();j++){
          parent_node.router_report.push_back(updatedNode.router_report[j]);
        }
     std::cout<<"End Update router report for parent"<<std::endl;

     for(unsigned int j=0;j<parent_node.Blocks.size();j++){

	 auto& lhs = parent_node.Blocks[j];
	 auto& prelim_b = lhs.instance.back();

	 if( prelim_b.master == updatedNode.name) {
          if(lhs.instNum>0) {
	    lhs.instance.push_back( prelim_b);
          }

	  auto& b = lhs.instance.back();

          lhs.instNum++;
          b.gdsFile = updatedNode.gdsFile;
          //update terminal to pin information
          
          for(unsigned int p=0;p<b.blockPins.size();p++){
              for(unsigned int q=0;q<updatedNode.blockPins.size();q++){
                  if(b.blockPins[p].name == updatedNode.blockPins[q].name){                     
		    //		      b.blockPins[p].pinContacts.clear();
		      b.blockPins[p].pinContacts = updatedNode.blockPins[q].pinContacts;
		      //		      b.blockPins[p].pinVias.clear();
		      b.blockPins[p].pinVias = updatedNode.blockPins[q].pinVias;
		      break;     
		  }
	      }
          }
          
	  //          b.interMetals.clear();
          b.interMetals = updatedNode.interMetals;
          
	  //          b.interVias.clear();
          b.interVias = updatedNode.interVias;

          b.width=updatedNode.width;
          b.height=updatedNode.height;
          b.originCenter.x = updatedNode.width/2;
          b.originCenter.y = updatedNode.height/2;
          b.originBox.LL.x = 0;
          b.originBox.LL.y = 0;
          b.originBox.UR.x = updatedNode.width;
          b.originBox.UR.y = updatedNode.height;
          }
        }

    std::cout<<"Start Update power pin in parent"<<std::endl;
     //update power pin information

     for(unsigned int j=0;j<parent_node.Blocks.size();j++){
	 auto& lhs = parent_node.Blocks[j];
	 auto& b = lhs.instance.back();

          if(b.master.compare(updatedNode.name)==0){
             for(unsigned int k = 0; k<updatedNode.PowerNets.size();k++){
                  int found = 0;
                  
                  for(unsigned int l =0;l<parent_node.PowerNets.size();l++){
                       if(updatedNode.PowerNets[k].name == parent_node.PowerNets[l].name){
                            found = 1;

                            //parent_node.PowerNets[l].dummy_connected.clear();
                            //there will be a bug, if not clear() for multi aspect ratio *** BUG*** Yaguang, 1/1/2020

                            for(unsigned int p=0;p<updatedNode.PowerNets[k].Pins.size();p++){
                                  PnRDB::connectNode temp_connectNode;
                                  temp_connectNode.iter2 = j;
                                  temp_connectNode.iter = b.dummy_power_pin.size();
                                  parent_node.PowerNets[l].dummy_connected.push_back(temp_connectNode);
                                  PnRDB::pin temp_pin;
                                  temp_pin=updatedNode.PowerNets[k].Pins[p];
                                  
                                  updatePowerPins(temp_pin);

                                  b.dummy_power_pin.push_back(temp_pin);
                               }
                         }
                     }
                  if(found ==0){
                      PnRDB::PowerNet temp_PowerNet;
                      temp_PowerNet = updatedNode.PowerNets[k];
                      temp_PowerNet.connected.clear();
                      temp_PowerNet.dummy_connected.clear();
                      temp_PowerNet.Pins.clear();
                      
                      for(unsigned int p=0;p<updatedNode.PowerNets[k].Pins.size();p++){
                             PnRDB::pin temp_pin;
                             PnRDB::connectNode temp_connectNode;
                             temp_connectNode.iter2 = j;
                             temp_connectNode.iter = b.dummy_power_pin.size();
                             temp_pin = updatedNode.PowerNets[k].Pins[p];
                             updatePowerPins(temp_pin);
                             b.dummy_power_pin.push_back(temp_pin);
                             temp_PowerNet.dummy_connected.push_back(temp_connectNode);
                          }
                      
                      parent_node.PowerNets.push_back(temp_PowerNet);
                    }
                }             
            }
        }
     std::cout<<"End update power pin in parent"<<std::endl;
     }

  std::cout<<"End update blocks in parent"<<std::endl;
  


}

void PnRdatabase::WriteLef(const PnRDB::hierNode &node, const string& file, const string& opath) const {

  std::ofstream leffile;
  string leffile_name = opath + file;

  leffile.open(leffile_name);

  double time = 2000;
  
  leffile<<"MACRO "<<node.name<<std::endl;
  leffile<<"  ORIGIN 0 0 ;"<<std::endl;
  leffile<<"  FOREIGN "<<node.name<<" 0 0 ;"<<std::endl;
  leffile<<"  SIZE "<< (double) node.width/time<<" BY "<<(double) node.height/time <<" ;"<<std::endl;

  //pins
  for(unsigned int i=0;i<node.blockPins.size();i++){

      leffile<<"  PIN "<<node.blockPins[i].name<<std::endl;
      leffile<<"    DIRECTION INOUT ;"<<std::endl;
      leffile<<"    USE SIGNAL ;"<<std::endl;
      //leffile<<"    DIRECTION "<<node.blockPins[i].type<<" ;"<<std::endl;
      //leffile<<"    USE "<<node.blockPins[i].use<<" 0 0 ;"<<std::endl;
      leffile<<"    PORT "<<std::endl;

      for(unsigned int j=0;j<node.blockPins[i].pinContacts.size();j++){

         leffile<<"      LAYER "<<node.blockPins[i].pinContacts[j].metal<<" ;"<<std::endl;
         leffile<<"        RECT "<<(double) node.blockPins[i].pinContacts[j].originBox.LL.x/time<<" "<<(double) node.blockPins[i].pinContacts[j].originBox.LL.y/time<<" "<<(double) node.blockPins[i].pinContacts[j].originBox.UR.x/time<<" "<<(double) node.blockPins[i].pinContacts[j].originBox.UR.y/time<<" ;"<<std::endl;

         }
      
      leffile<<"    END"<<std::endl;
      leffile<<"  END "<<node.blockPins[i].name<<std::endl;  
      
 
     }

  leffile<<"  OBS "<<std::endl;
  for(unsigned int i=0;i<node.interMetals.size();i++){

     
     leffile<<"  LAYER "<<node.interMetals[i].metal<<" ;"<<std::endl;
     leffile<<"        RECT "<<(double) node.interMetals[i].originBox.LL.x/time<<" "<<(double) node.interMetals[i].originBox.LL.y/time<<" "<<(double) node.interMetals[i].originBox.UR.x/time<<" "<<(double) node.interMetals[i].originBox.UR.y/time<<" ;"<<std::endl;

     }
  leffile<<"  END "<<std::endl;

  leffile<<"END "<<node.name<<std::endl;
  
  leffile.close();
}

json PnRdatabase::WriteGcellGlobalRouteFile(const PnRDB::hierNode& node, const string& rofile, const string& opath,
                                            const int MetalIdx, const string net_name, const int width,
                                            const int first_tile_idx, const int last_tile_idx,
                                            std::vector<int>& tile_idxs, const int MetalDirection, const int net_id) const {
    //do output tiles (first_tile_idx, ..., last_tile_idx)
    std::cout << "output data " << std::endl;
    std::cout << "layer " << DRC_info.Metal_info.at(MetalIdx).name;
    std::cout << " net_name " << net_name;
    std::cout << " width " << width << std::endl;
    std::cout << " rect ";
    json jsonWire;
    jsonWire["layer"] = DRC_info.Metal_info.at(MetalIdx).name;
    jsonWire["net_name"] = net_name;
    jsonWire["width"] = width;

    {
      const auto& f = node.tiles_total.at(first_tile_idx);
      const auto& l = node.tiles_total.at(last_tile_idx);
#if 0
      std::cout << "ABS(" << f.x << ", " << f.y << ", " << l.x << ", " << l.y << ")" << std::endl;
      std::cout << "IDX(" << f.Xidx << ", " << f.Yidx << ", " << l.Xidx << ", " << l.Yidx << ")" << std::endl;
      int m1_p = 80*2;
      int m2_p = 84*2;
      std::cout << "MOD(" << f.x/m1_p << " " << f.x%m1_p
		<< ", "   << f.y/m2_p << " " << f.y%m2_p
	        << ", "   << l.x/m1_p << " " << l.x%m1_p
	        << ", "   << l.y/m2_p << " " << l.y%m2_p << std::endl;
#endif

      std::cout << " MetalDirection: " << MetalDirection << std::endl;
      json jsonRect =  json::array();
      jsonRect.push_back(f.x);
      jsonRect.push_back(f.y);
      jsonRect.push_back(l.x);
      jsonRect.push_back(l.y);
      jsonWire["rect"] = jsonRect;
    }

    std::cout << "connected pins: " << std::endl;
    PnRDB::net net = node.Nets.at(net_id);
    json jsonConnectedPins = json::array();
    std::cout << "tile_idx: ";
    for(vector<int>::const_iterator tile_idx = tile_idxs.begin(); tile_idx!=tile_idxs.end(); ++tile_idx){
        std::cout << *tile_idx << ", ";
        //search all the tiles in the consecutive tiles
        for(vector<std::vector<int>>::const_iterator i = net.connectedTile.begin(); i!=net.connectedTile.end();++i){
            int pin_id = i - net.connectedTile.begin();
            //pin_id is the index in net.connectedTile
            for(vector<int>::const_iterator j = i->begin(); j!=i->end();++j){
                if(*tile_idx != *j){continue;}
                //current tile index == pin_terminal
                json jsonConnectedPin;
                std::cout << "pin_id " << pin_id << std::endl;
                if (net.connected.at(pin_id).type==PnRDB::Block) {
                    int selectedInstance = node.Blocks.at(net.connected.at(pin_id).iter2).selectedInstance;
                    vector<PnRDB::contact> pinContacts = node.Blocks.at(net.connected.at(pin_id).iter2).instance.at(selectedInstance).blockPins.at(net.connected.at(pin_id).iter).pinContacts;
                    for(vector<PnRDB::contact>::const_iterator contact_it = pinContacts.begin(); contact_it != pinContacts.end(); ++contact_it){
                        string sink_name = node.Blocks.at(net.connected.at(pin_id).iter2).instance.at(selectedInstance).name + "/" + node.Blocks.at(net.connected.at(pin_id).iter2).instance.at(selectedInstance).blockPins.at(net.connected.at(pin_id).iter).name;
                        std::cout << "sink_name: " << sink_name;
                        jsonConnectedPin["sink_name"] = sink_name;

                        string layer = "";
                        layer = contact_it->metal;
                        jsonConnectedPin["layer"] = layer;
                        std::cout << " layer: " << layer << std::endl;

                        json jsonRect = json::array();
                        std::cout << "contacts size " << pinContacts.size() << std::endl;
                        PnRDB::bbox rect = contact_it->placedBox;
                        jsonRect.push_back(rect.LL.x);
                        jsonRect.push_back(rect.LL.y);
                        jsonRect.push_back(rect.UR.x);
                        jsonRect.push_back(rect.UR.y);
                        std::cout << "placedBox:" << rect.LL.x << ", " << rect.LL.y << ", ";
                        std::cout << rect.UR.x << ", " << rect.UR.y << std::endl;
                        jsonConnectedPin["rect"] = jsonRect;
                        jsonConnectedPins.push_back( jsonConnectedPin);
                    }
                } else if (node.Nets.at(net_id).connected.at(pin_id).type==PnRDB::Terminal){
                    vector<PnRDB::contact> termContacts = node.Terminals.at(net.connected.at(pin_id).iter).termContacts;
                    for(vector<PnRDB::contact>::const_iterator contact_it = termContacts.begin(); contact_it != termContacts.end(); ++contact_it){
                        string sink_name = node.Terminals.at(net.connected.at(pin_id).iter).name;
                        std::cout << "sink_name: " << sink_name;
                        jsonConnectedPin["sink_name"] = sink_name;

                        string layer = "";
                        layer = contact_it->metal;
                        jsonConnectedPin["layer"] = layer;
                        std::cout << " layer: " << layer << std::endl;

                        json jsonRect = json::array();
                        PnRDB::bbox rect = contact_it->placedBox;
                        jsonRect.push_back(rect.LL.x);
                        jsonRect.push_back(rect.LL.y);
                        jsonRect.push_back(rect.UR.x);
                        jsonRect.push_back(rect.UR.y);
                        std::cout << "#termcontact:" << rect.LL.x << ", " << rect.LL.y << ", ";
                        std::cout << rect.UR.x << ", " << rect.UR.y << std::endl;
                        jsonConnectedPin["rect"] = jsonRect;

                        jsonConnectedPins.push_back( jsonConnectedPin);
                    }
                }
                break;
            }
        }
    }
    jsonWire["connected_pins"] = jsonConnectedPins;
    tile_idxs.clear();
	return jsonWire;
    
}

void PnRdatabase::WriteGcellGlobalRoute(const PnRDB::hierNode& node, const string& rofile, const string& opath) const {
    //this function write gcell global router result into json for detail route use
    //combine consecutive tiles into one
    json jsonWiresArray = json::array();
    std::cout << "#Nets:" << node.Nets.size() << std::endl;
    //std::cout << "#Pin_terminals:" << node.Pin_terminals.size() <<std::endl;
    
    for(vector<PnRDB::net>::const_iterator it=node.Nets.begin(); it!=node.Nets.end(); ++it) {
        //std::cout << "Net degree:" << it->degree << std::endl;
        int MetalIdx = -1; // used to store metal_idx of the consecutive tiles with same tile_idx 
        int first_tile_idx = -1, last_tile_idx = -1; //first and last tile_idx of consecutive tiles in the same metal layers
        int width = 0; //width of consecutive tiles, not always the tile.width, 
                   //=tile.width in vertical metals(even layer), 
                   //=tile.height in horizontal metals(odd layer)
        std::vector<int> tile_idxs; //store tile idxs of consecutive tiles
        int net_id = it - node.Nets.begin(); 
        int MetalDirection = -1; //vertical metal in even layers, horizontal metal in odd layers
        for(vector<std::pair<int,int>>::const_iterator it2=it->GcellGlobalRouterPath.begin(); it2!=it->GcellGlobalRouterPath.end(); ++it2) {            
            int MetalIdx1 = 0, MetalIdx2 = 0; //metal id of the two tiles in the pair
            const int tile_idx1 = it2->first;
	    const int tile_idx2 = it2->second; //tile ids

	    const auto& tile1 = node.tiles_total.at(tile_idx1);
	    const auto& tile2 = node.tiles_total.at(tile_idx2);

            int x1 = tile1.x, y1 = tile1.y; //coordinate of first tile's center
            int x2 = tile2.x, y2 = tile2.y; //coordinate of sencond tile's center
            int w1 = tile1.width, h1 = tile1.height; //w/h of first tile
            int w2 = tile2.width, h2 = tile2.height; //w/h of second tile

            if( tile1.metal.size() != 1 || tile2.metal.size() != 1){
                std::cout << "ERROR: tile.metal.size != 1 !" << std::endl;
            }else{
                MetalIdx1 = tile1.metal.front();
                MetalIdx2 = tile2.metal.front();
            }
            std::cout << "tile indexs: " << tile_idx1 << " " << tile_idx2 << std::endl;
            std::cout << "tile layers: " << MetalIdx1 << " " << MetalIdx2 << endl;
            std::cout << "first tile x/y/width/height: " << x1 << " " << y1 << " " << w1 << " " << h1 << endl;
            std::cout << "second tile x/y/width/height: " << x2 << " " << y2 << " " << w2 << " " << h2 << endl;

            if(MetalIdx1 == MetalIdx2){
                MetalDirection = DRC_info.Metal_info.at(MetalIdx1).direct;
            }

            if(MetalIdx1 != MetalIdx2){
                //tiles in this pair belongs to different layers
                if(first_tile_idx != -1 && last_tile_idx != -1){
                    //do output tiles (first_tile_idx, ..., last_tile_idx)
		    vector<std::pair<int,int>>::const_iterator it3 = it2; //consider tile pairs whose pos same as last tile's
                    while(it3 != it->GcellGlobalRouterPath.end()){
                        if(it3->first != tile_idxs.back()){
                            if(node.tiles_total.at(it3->first).x == node.tiles_total.at(last_tile_idx).x &&\
                                node.tiles_total.at(it3->first).y == node.tiles_total.at(last_tile_idx).y){
                                tile_idxs.push_back(it3->first);
                            }else break;
                        }  
                        if(it3->second != tile_idxs.back()){
                            if(node.tiles_total.at(it3->second).x == node.tiles_total.at(last_tile_idx).x &&\
                                node.tiles_total.at(it3->second).y == node.tiles_total.at(last_tile_idx).y){
                                tile_idxs.push_back(it3->second);
                            }else break;
                        }  
                        ++it3;
                    }
                    json jsonWire = WriteGcellGlobalRouteFile(node, rofile, opath, MetalIdx, it->name, width,
                                                first_tile_idx, last_tile_idx, tile_idxs, MetalDirection, net_id);                   
                    jsonWiresArray.push_back( jsonWire);
                    first_tile_idx = -1;//reset consecutive tiles
                    last_tile_idx = -1;
                }
                continue;
            } 
            

            if(first_tile_idx == -1 && last_tile_idx == -1){
                if(MetalIdx1 == MetalIdx2){
                    first_tile_idx = tile_idx1;//start a new consecutive tiles
                    last_tile_idx = tile_idx2;
                    tile_idxs.push_back(first_tile_idx);
                    if(first_tile_idx != last_tile_idx)tile_idxs.push_back(last_tile_idx);//ignore same idx
                    MetalIdx = MetalIdx1;
                    if(MetalDirection == 0){
                        width = w1;
                    }else if(MetalDirection == 1){
                        width = h1;
                    }
                    vector<std::pair<int,int>>::const_iterator it3 = it2; //consider tile pairs whose pos same as first tile's
                    while(it3 - it->GcellGlobalRouterPath.begin() > 0){
                        --it3;
                        if(it3->second != tile_idxs.front()){
                            if(node.tiles_total.at(it3->second).x == node.tiles_total.at(first_tile_idx).x &&\
                                node.tiles_total.at(it3->second).y == node.tiles_total.at(first_tile_idx).y){
                                tile_idxs.insert(tile_idxs.begin(), it3->second);
                            }else break;
                        }
                        if(it3->first != tile_idxs.front()){
                            if(node.tiles_total.at(it3->first).x == node.tiles_total.at(first_tile_idx).x &&\
                                node.tiles_total.at(it3->first).y == node.tiles_total.at(first_tile_idx).y){
                                tile_idxs.insert(tile_idxs.begin(), it3->first);
                            }else break;
                        }  
                    }
                }
            }

            //current pair of tiles can be appended to (first_tile_idx, ..., last_tile_idx) only when
            //1.same metal id 
            //2.same width
            bool can_append = false; //True only if the above criteria are all satisfied
                                     //otherwise output data (first_tile_idx, ..., last_tile_idx)
            if(MetalIdx1 == MetalIdx){
                if(tile_idx1 == last_tile_idx){
                    if((MetalDirection == 0 && width == w1) || (MetalDirection == 1 && width == h1)){
                        can_append = true;
                    }
                }else if(first_tile_idx == tile_idx1 && last_tile_idx == tile_idx2){
                    can_append = true;
                }
            }

            std::cout << "MetalDirection: " <<MetalDirection << std::endl;
            std::cout << "can append: " << can_append << std::endl;

            if(can_append == false){
                //do output tiles (first_tile_idx, ..., last_tile_idx)
		vector<std::pair<int,int>>::const_iterator it3 = it2; //consider tile pairs whose pos same as last tile's
                while(it3 != it->GcellGlobalRouterPath.end()){
                    if(it3->first != tile_idxs.back()){
                        if(node.tiles_total.at(it3->first).x == node.tiles_total.at(last_tile_idx).x &&\
                            node.tiles_total.at(it3->first).y == node.tiles_total.at(last_tile_idx).y){
                            tile_idxs.push_back(it3->first);
                        }else break;
                    }  
                    if(it3->second != tile_idxs.back()){
                        if(node.tiles_total.at(it3->second).x == node.tiles_total.at(last_tile_idx).x &&\
                            node.tiles_total.at(it3->second).y == node.tiles_total.at(last_tile_idx).y){
                            tile_idxs.push_back(it3->second);
                        }else break;
                    }  
                    ++it3;
                }
                json jsonWire = WriteGcellGlobalRouteFile(node, rofile, opath, MetalIdx, it->name, width,
                                            first_tile_idx, last_tile_idx, tile_idxs, MetalDirection, net_id);
                jsonWiresArray.push_back( jsonWire);
                first_tile_idx = tile_idx1;//start a new consecutive tiles
                last_tile_idx = tile_idx2;
                tile_idxs.push_back(first_tile_idx);
                if(first_tile_idx != last_tile_idx)tile_idxs.push_back(last_tile_idx);//ignore same idx
                MetalIdx = MetalIdx1;
                if(MetalDirection == 0){
                    width = w1;
                }else if(MetalDirection == 1){
                    width = h1;
                }
		it3 = it2; //consider tile pairs whose pos same as first tile's
                while(it3 - it->GcellGlobalRouterPath.begin() > 0){
                    --it3;
                    if(it3->second != tile_idxs.front()){
                        if(node.tiles_total.at(it3->second).x == node.tiles_total.at(first_tile_idx).x &&\
                            node.tiles_total.at(it3->second).y == node.tiles_total.at(first_tile_idx).y){
                            tile_idxs.insert(tile_idxs.begin(), it3->second);
                        }else break;
                    }  
                    if(it3->first != tile_idxs.front()){
                        if(node.tiles_total.at(it3->first).x == node.tiles_total.at(first_tile_idx).x &&\
                            node.tiles_total.at(it3->first).y == node.tiles_total.at(first_tile_idx).y){
                            tile_idxs.insert(tile_idxs.begin(), it3->first);
                        }else break;
                    }  
                }
                if(it2 + 1 == it->GcellGlobalRouterPath.end()){
                    //do output tiles (first_tile_idx, ..., last_tile_idx)
                    json jsonWire = WriteGcellGlobalRouteFile(node, rofile, opath, MetalIdx, it->name, width,
                                                first_tile_idx, last_tile_idx, tile_idxs, MetalDirection, net_id);
                    jsonWiresArray.push_back( jsonWire);     
                }
            }else{
                if(tile_idx2 != last_tile_idx)tile_idxs.push_back(tile_idx2); //ignore same idx
                last_tile_idx = tile_idx2;//can append, set last tile to the second tile of current pair
                if(it2 + 1 == it->GcellGlobalRouterPath.end()){
                    //do output tiles (first_tile_idx, ..., last_tile_idx)
                    json jsonWire = WriteGcellGlobalRouteFile(node, rofile, opath, MetalIdx, it->name, width,
                                                first_tile_idx, last_tile_idx, tile_idxs, MetalDirection, net_id);   
                    jsonWiresArray.push_back(jsonWire);  
                }
            }
        }
        std::cout << std::endl;
    }

    json jsonTop;
    jsonTop["wires"] = jsonWiresArray;

    std::ofstream jsonStream(opath+rofile);
    if(jsonStream.fail()) {
	cout<< "PnRData-Error: cannot open file "<<opath+rofile<<" for writing"<<endl;
	return;
    }
    jsonStream << std::setw(4) << jsonTop;
    jsonStream.close();
    
}


void PnRdatabase::WriteGlobalRoute(const PnRDB::hierNode& node, const string& rofile, const string& opath) const {

    json jsonWiresArray = json::array();

    for(vector<PnRDB::net>::const_iterator it=node.Nets.begin(); it!=node.Nets.end(); ++it) {
	for(vector<PnRDB::Metal>::const_iterator it2=it->path_metal.begin(); it2!=it->path_metal.end(); ++it2) {

	    json jsonWire;
	    jsonWire["layer"] = DRC_info.Metal_info.at(it2->MetalIdx).name;
	    jsonWire["net_name"] = it->name;
	    jsonWire["width"] = it2->width;

	    json jsonRect = json::array();
	    jsonRect.push_back( it2->LinePoint.at(0).x);
	    jsonRect.push_back( it2->LinePoint.at(0).y);
	    jsonRect.push_back( it2->LinePoint.at(1).x);
	    jsonRect.push_back( it2->LinePoint.at(1).y);
	    jsonWire["rect"] = jsonRect;

	    json jsonConnectedPins = json::array();

	    int mIdx=it2-it->path_metal.begin();

	    for(unsigned int k=0;k<it->connectedContact.size();++k) {
		if(it->connectedContact.at(k).metalIdx!=mIdx) {continue;}
		if(it->connected.at(k).type==PnRDB::Block || (it->connected.at(k).type==PnRDB::Terminal and node.isTop)) {
		    json jsonConnectedPin;
		    if ( it->connected.at(k).type==PnRDB::Block) {
			jsonConnectedPin["sink_name"] = node.Blocks.at(it->connected.at(k).iter2).instance.back().name + "/" + node.Blocks.at(it->connected.at(k).iter2).instance.back().blockPins.at(it->connected.at(k).iter).name;
		    } else {
			jsonConnectedPin["sink_name"] = node.Terminals.at(it->connected.at(k).iter).name;
		    }
		    jsonConnectedPin["layer"] = it->connectedContact.at(k).conTact.metal;
		    json jsonRect = json::array();
		    jsonRect.push_back( it->connectedContact.at(k).conTact.placedBox.LL.x);
		    jsonRect.push_back( it->connectedContact.at(k).conTact.placedBox.LL.y);
		    jsonRect.push_back( it->connectedContact.at(k).conTact.placedBox.UR.x);
		    jsonRect.push_back( it->connectedContact.at(k).conTact.placedBox.UR.y);
		    jsonConnectedPin["rect"] = jsonRect;

		    jsonConnectedPins.push_back( jsonConnectedPin);
		}
	    }
	    jsonWire["connected_pins"] = jsonConnectedPins;
	    jsonWiresArray.push_back( jsonWire);
	}

    }

    json jsonTop;
    jsonTop["wires"] = jsonWiresArray;

    std::ofstream jsonStream(opath+rofile);
    if(jsonStream.fail()) {
	cout<< "PnRData-Error: cannot open file "<<opath+rofile<<" for writing"<<endl;
	return;
    }
    jsonStream << std::setw(4) << jsonTop;
    jsonStream.close();
}


/*
void PnRdatabase::WriteGlobalRoute(PnRDB::hierNode& node, string rofile, string opath) {

  std::ofstream OF2(opath+rofile);
  if(OF2.fail()) {
    cout<< "PnRData-Error: cannot open the file "<<rofile<<endl;
    return;
  }
  OF2<<"{"<<endl<<"  \"wires\": ["<<endl;
  int i=0;
  for(vector<PnRDB::net>::iterator it=node.Nets.begin(); it!=node.Nets.end(); ++it) {
    for(vector<PnRDB::Metal>::iterator it2=it->path_metal.begin(); it2!=it->path_metal.end(); ++it2) {
      //if(it2->LinePoint.at(0).x==it2->LinePoint.at(1).x and it2->LinePoint.at(0).y==it2->LinePoint.at(1).y) {continue;}
      if(i!=0) {OF2<<","<<std::endl;}
      i++;
      OF2<<"    { \"layer\": \""<<DRC_info.Metal_info.at(it2->MetalIdx).name;
      OF2<<"\", \"net_name\": \""<<it->name<<"\", \"width\": "<<it2->width;
      OF2<<", \"rect\": [ "<<it2->LinePoint.at(0).x<<", "<<it2->LinePoint.at(0).y<<", "<<it2->LinePoint.at(1).x<<", "<<it2->LinePoint.at(1).y<<"],"<<std::endl;
      OF2<<"      \"connected_pins\": ["<<std::endl;
      int mIdx=it2-it->path_metal.begin();
      int sinkCount=0;
      for(int k=0;k<it->connectedContact.size();++k) {
        if(it->connectedContact.at(k).metalIdx!=mIdx) {continue;}
        if(it->connected.at(k).type==PnRDB::Block) {
          if(sinkCount!=0) {OF2<<","<<std::endl;}
          OF2<<"          { "<<"\"sink_name\": \""<<node.Blocks.at(it->connected.at(k).iter2).instance.back().name<<"/"<<node.Blocks.at(it->connected.at(k).iter2).instance.back().blockPins.at(it->connected.at(k).iter).name<<"\"";
        } else if (it->connected.at(k).type==PnRDB::Terminal and node.isTop) {
          if(sinkCount!=0) {OF2<<","<<std::endl;}
          OF2<<"          { "<<"\"sink_name\": \""<<node.Terminals.at(it->connected.at(k).iter).name<<"\"";
        } else {continue;}
        ++sinkCount;
        OF2<<", \"layer\": \""<<it->connectedContact.at(k).conTact.metal<<"\", \"rect\": ["<<it->connectedContact.at(k).conTact.placedBox.LL.x<<", "<<it->connectedContact.at(k).conTact.placedBox.LL.y<<", "<<it->connectedContact.at(k).conTact.placedBox.UR.x<<", "<<it->connectedContact.at(k).conTact.placedBox.UR.y<<"] }";
      }
      if(sinkCount>0) {OF2<<std::endl;}
      OF2<<"      ]"<<std::endl;
      OF2<<"    }";
      //if(it!=node.Nets.end()-1 or it2!=it->segments.end()-1) {OF2<<",";}
      //OF2<<endl;
    }
  }
  OF2<<std::endl<<"  ]"<<endl;
  //OF2<<"  \"rects\": ["<<endl;
  //for(vector<PnRDB::net>::iterator it=node.Nets.begin(); it!=node.Nets.end(); ++it) {
  //  if(node.isTop) {
  //    if(it->connected.size()<=1) {continue;}
  //  } else {
  //    if(!it->sink2Terminal and it->connected.size()<=1) {continue;}
  //    if(it->sink2Terminal and it->connected.size()<=2) {continue;}
  //  }
  //  for(int k=0;k<it->connectedContact.size();++k) {
  //    if(it->connected.at(k).type==PnRDB::Block) {
  //      OF2<<"    { \"net_name\": \""<<it->name<<"\", \"sink_name\": \""<<node.Blocks.at(it->connected.at(k).iter2).instance.back().name<<"/"<<node.Blocks.at(it->connected.at(k).iter2).instance.back().blockPins.at(it->connected.at(k).iter).name<<"\"";
  //    } else if (it->connected.at(k).type==PnRDB::Terminal and node.isTop) {
  //      OF2<<"    { \"net_name\": \""<<it->name<<"\", \"sink_name\": \""<<node.Terminals.at(it->connected.at(k).iter).name<<"\"";
  //    } else {continue;}
  //    OF2<<", metalIdx: "<<it->connectedContact.at(k).metalIdx<<", \"layer\": \""<<it->connectedContact.at(k).conTact.metal<<"\", \"rect\": ["<<it->connectedContact.at(k).conTact.placedBox.LL.x<<", "<<it->connectedContact.at(k).conTact.placedBox.LL.y<<", "<<it->connectedContact.at(k).conTact.placedBox.UR.x<<", "<<it->connectedContact.at(k).conTact.placedBox.UR.y<<"] },"<<endl;
  //  }
  //}
  OF2<<endl<<"}";
  OF2.close();
}
*/

void PnRdatabase::WritePlaceRoute(PnRDB::hierNode& node, string pofile, string rofile) {
  std::ofstream OF(pofile);
  if(OF.fail()) {
    cout<< "PnRData-Error: cannot open the file "<<pofile<<endl;
    return;
  }
  int Xunit=-1,Yunit=-1;
  switch (DRC_info.Metal_info.at(0).direct) {
    case 1: // H -> Y axis
            Yunit=DRC_info.Metal_info.at(0).grid_unit_y; break;
    case 0: // V -> X axis
            Xunit=DRC_info.Metal_info.at(0).grid_unit_x; break;
    default:
            cout<<"PnRData-Error: incorrect routing direction"<<endl;
  }
  switch (DRC_info.Metal_info.at(1).direct) {
    case 1: // H -> Y axis
            Yunit=DRC_info.Metal_info.at(1).grid_unit_y; break;
    case 0: // V -> X axis
            Xunit=DRC_info.Metal_info.at(1).grid_unit_x; break;
    default:
            cout<<"PnRData-Error: incorrect routing direction"<<endl;
  }
  cout<<"Xunit "<<Xunit<<" ; Yunit "<<Yunit<<endl;
  OF<<"{"<<endl;
  // write current node name
  OF<<"  \"nm\": \""<<node.name<<"\","<<endl;
  OF<<"  \"bbox\": [ "<<0<<", "<<0<<", "<<node.width/Xunit<<", "<<node.height/Yunit<<"],"<<endl;
  //OF<<"  \"bbox\": [ "<<0<<", "<<0<<", "<<node.width<<", "<<node.height<<"],"<<endl;
  // write leaf master
  OF<<"  \"leaves\": ["<<endl;
  string endStr;
  endStr=(lefData.rbegin())->first;
  for( map<string, std::vector<PnRDB::lefMacro> >::iterator it=lefData.begin(); it!=lefData.end(); ++it) {
    string lefname;
    for(unsigned int w=0;w<node.Blocks.size();++w) {
      if(it->first.compare(node.Blocks.at(w).instance.back().master)==0) {
        lefname=node.Blocks.at(w).instance.at( node.Blocks.at(w).selectedInstance ).lefmaster;
        break;
      }
    }
    int sel=-1;
    for(unsigned int w=0;w<it->second.size();++w) {
      if(it->second.at(w).name.compare(lefname)==0) {sel=w;break;}
    }
    if ( sel == -1) {
      cout<<"PnRData-Error: sel == -1"<<endl;
      continue;
    }

    OF<<"    {"<<endl;
    OF<<"      \"template_name\": \""<<(it->second).at(sel).master<<"\","<<endl;
    OF<<"      \"bbox\": [ 0, 0, "<<(it->second).at(sel).width/Xunit<<", "<<(it->second).at(sel).height/Yunit<<"],"<<endl;
    OF<<"      \"terminales\": ["<<endl;
    for(vector<PnRDB::pin>::iterator it2=(it->second).at(sel).macroPins.begin(); it2!=(it->second).at(sel).macroPins.end(); ++it2) {
      for(vector<PnRDB::contact>::iterator it3=it2->pinContacts.begin(); it3!=it2->pinContacts.end(); ++it3) {
        //int metalUnit;
        //int metalIdx=DRC_info.Metalmap[it3->metal];
        //if (DRC_info.Metal_info.at(metalIdx).direct==0) { //V
        //  metalUnit=DRC_info.Metal_info.at(metalIdx).grid_unit_x;
        //  OF<<"        { \"net_name\": \""<<it2->name<<"\", \"layer\": \""<<it3->metal<<"\", \"rect\": [ "<<it3->originBox.LL.x<<", "<<it3->originBox.LL.y<<", "<<it3->originBox.UR.x<<", "<<it3->originBox.UR.y<<"]}";
        //} else if(DRC_info.Metal_info.at(metalIdx).direct==1) { // H
        //  metalUnit=DRC_info.Metal_info.at(metalIdx).grid_unit_y;
        //  OF<<"        { \"net_name\": \""<<it2->name<<"\", \"layer\": \""<<it3->metal<<"\", \"rect\": [ "<<it3->originBox.LL.x<<", "<<it3->originBox.LL.y<<", "<<it3->originBox.UR.x<<", "<<it3->originBox.UR.y<<"]}";
        //} else {
        //  cout<<"PnRDB-Error: undefined direction found"<<endl;
        //}
        OF<<"        { \"net_name\": \""<<it2->name<<"\", \"layer\": \""<<it3->metal<<"\", \"rect\": [ "<<it3->originBox.LL.x<<", "<<it3->originBox.LL.y<<", "<<it3->originBox.UR.x<<", "<<it3->originBox.UR.y<<"]}";
        if(!(it2==(it->second).at(sel).macroPins.end()-1 and it3==it2->pinContacts.end()-1)) {
          OF<<",";
        }
        OF<<endl;
      }
    }
    OF<<"      ]"<<endl<<"    }";
    if(it->first.compare(endStr)!=0) {OF<<",";}
    OF<<endl;
  }
  OF<<"  ],"<<endl;
  // write instances
  OF<<"  \"instances\": ["<<endl;
  for(vector<PnRDB::blockComplex>::iterator it=node.Blocks.begin(); it!=node.Blocks.end(); ++it) {
    int sel=it->selectedInstance;
    if(sel<0 or sel>=it->instNum) {std::cout<<"PnRDB-Error: unselected block\n";}
    OF<<"    {"<<endl;
    OF<<"      \"instance_name\": \""<<it->instance.at(sel).name<<"\","<<endl;
    OF<<"      \"template_name\": \""<<it->instance.at(sel).master<<"\","<<endl;
    OF<<"      \"transformation\": {"<<endl;
    if(it->instance.at(sel).orient==PnRDB::N) {
      OF<<"      \"oX\": "<<(it->instance.at(sel).placedCenter.x-(it->instance.at(sel).width/2))/Xunit<<",\n      \"oY\": "<<(it->instance.at(sel).placedCenter.y-(it->instance.at(sel).height/2))/Yunit<<",\n      \"sX\": "<<1<<",\n      \"sY\": "<<1<<"\n      },"<<endl;
    } else if (it->instance.at(sel).orient==PnRDB::S) {
      OF<<"      \"oX\": "<<(it->instance.at(sel).placedCenter.x+(it->instance.at(sel).width/2))/Xunit<<",\n      \"oY\": "<<(it->instance.at(sel).placedCenter.y+(it->instance.at(sel).height/2))/Yunit<<",\n      \"sX\": "<<-1<<",\n      \"sY\": "<<-1<<"\n      },"<<endl;
    } else if (it->instance.at(sel).orient==PnRDB::FN) {
      OF<<"      \"oX\": "<<(it->instance.at(sel).placedCenter.x+(it->instance.at(sel).width/2))/Xunit<<",\n      \"oY\": "<<(it->instance.at(sel).placedCenter.y-(it->instance.at(sel).height/2))/Yunit<<",\n      \"sX\": "<<-1<<",\n      \"sY\": "<<1<<"\n      },"<<endl;
    } else if (it->instance.at(sel).orient==PnRDB::FS) {
      OF<<"      \"oX\": "<<(it->instance.at(sel).placedCenter.x-(it->instance.at(sel).width/2))/Xunit<<",\n      \"oY\": "<<(it->instance.at(sel).placedCenter.y+(it->instance.at(sel).height/2))/Yunit<<",\n      \"sX\": "<<1<<",\n      \"sY\": "<<-1<<"\n      },"<<endl;
    } else {
      cout<<"PnRDB-Error: unsupported orientation!"<<endl;
    }
    OF<<"      \"formal_actual_map\": {"<<endl;
    int maxNo=0;
    for(vector<PnRDB::pin>::iterator it2=it->instance.at(sel).blockPins.begin(); it2!=it->instance.at(sel).blockPins.end(); ++it2) {
      if(it2->netIter!=-1) maxNo++;
    }
    for(vector<PnRDB::pin>::iterator it2=it->instance.at(sel).blockPins.begin(); it2!=it->instance.at(sel).blockPins.end(); ++it2) {
      int netID=it2->netIter;
      if(netID==-1) {continue;}
      maxNo--;
      OF<<"        \""<<it2->name<<"\": \""<<node.Nets.at(netID).name<<"\"";
      if(maxNo>0) {OF<<",";}
      OF<<endl;
    }
    OF<<"      }"<<endl<<"    }";
    if(it!=node.Blocks.end()-1) {OF<<",";}
    OF<<endl;
  }
  OF<<"  ]"<<endl;
  OF<<"}";
  OF.close();
/*
  std::ofstream OF2(rofile);
  if(OF2.fail()) {
    cout<< "PnRData-Error: cannot open the file "<<rofile<<endl;
    return;
  }
  OF2<<"{"<<endl<<"  \"wires\": ["<<endl;
  for(vector<PnRDB::net>::iterator it=node.Nets.begin(); it!=node.Nets.end(); ++it) {
    for(vector<PnRDB::route>::iterator it2=it->segments.begin(); it2!=it->segments.end(); ++it2) {
      int metalIdx=DRC_info.Metalmap[it2->metal];
      OF2<<"    { \"layer\": \""<<it2->metal<<"\", \"net_name\": \""<<it->name<<"\", \"width\": "<<DRC_info.Metal_info.at(metalIdx).width*10/2<<", \"rect\": [ "<<it2->src.x<<", "<<it2->src.y<<", "<<it2->dest.x<<", "<<it2->dest.y<<"]}";
      if(it!=node.Nets.end()-1 or it2!=it->segments.end()-1) {OF2<<",";}
      OF2<<endl;
    }
    OF2<<endl;
  }
  OF2<<"  ]"<<endl<<"}";
  OF2.close();
*/
}



// [RA] need confirmation -wbxu
void PnRdatabase::AddingPowerPins(PnRDB::hierNode &node){

  for(unsigned int i=0;i<node.PowerNets.size();i++){
       
       for(unsigned int j=0;j<node.PowerNets[i].dummy_connected.size();j++){
            int iter2 = node.PowerNets[i].dummy_connected[j].iter2;
            int iter = node.PowerNets[i].dummy_connected[j].iter;
            for(unsigned int k=0;k<node.Blocks[iter2].instance.size();k++){
                 PnRDB::pin temp_pin;
                 temp_pin = node.Blocks[iter2].instance[k].dummy_power_pin[iter];
                 temp_pin.netIter = -2;
                 node.PowerNets[i].dummy_connected[j].iter = node.Blocks[iter2].instance[k].blockPins.size();
                 node.Blocks[iter2].instance[k].blockPins.push_back(temp_pin);
               }
           
          }     
     }

   
};

// [RA] need confirmation -wbxu
void PnRdatabase::Extract_RemovePowerPins(PnRDB::hierNode &node){

//extract power pin information

  for(unsigned int i = 0;i<node.PowerNets.size();i++){

       node.PowerNets[i].Pins.clear();
      
       for(unsigned int j=0;j<node.PowerNets[i].connected.size();j++){
             PnRDB::pin temp_pin;
             int iter = node.PowerNets[i].connected[j].iter;
             int iter2 = node.PowerNets[i].connected[j].iter2;
             temp_pin = node.Blocks[iter2].instance[node.Blocks[iter2].selectedInstance].blockPins[iter];
             node.PowerNets[i].Pins.push_back(temp_pin);
           }

       for(unsigned int j=0;j<node.PowerNets[i].dummy_connected.size();j++){
             PnRDB::pin temp_pin;
             int iter = node.PowerNets[i].dummy_connected[j].iter;
             int iter2 = node.PowerNets[i].dummy_connected[j].iter2;
             temp_pin = node.Blocks[iter2].instance[node.Blocks[iter2].selectedInstance].blockPins[iter];
             node.PowerNets[i].Pins.push_back(temp_pin);
           }
     
     }

//remove power pins in blocks

  for(unsigned int i=0;i<node.Blocks.size();i++){
     
     for(unsigned int k=0;k<node.Blocks[i].instance.size();k++){
       std::vector<PnRDB::pin> temp_pins;
       for(unsigned int j=0;j<node.Blocks[i].instance[k].blockPins.size();j++){
            int netIter = node.Blocks[i].instance[k].blockPins[j].netIter;
            if(netIter!=-2){
                 temp_pins.push_back(node.Blocks[i].instance[k].blockPins[j]);
              }else{
                 break;
              }
          }
        node.Blocks[i].instance[k].blockPins.clear();
        node.Blocks[i].instance[k].blockPins = temp_pins;
        }
     }


};

void PnRdatabase::Write_Router_Report(PnRDB::hierNode &node, const string& opath){

  std::ofstream router_report;
  string report_path = opath+"Router_Report.txt";
  router_report.open(report_path);


  for(int i = 0;i < node.router_report.size();i++){

      router_report<<"Node "<<node.router_report[i].node_name<<std::endl;

      for(int j=0;j<node.router_report[i].routed_net.size();j++){
       
        router_report<<"  Net "<<node.router_report[i].routed_net[j].net_name<<std::endl;

        for(int k=0;k<node.router_report[i].routed_net[j].pin_name.size();k++){
           
           router_report<<"    Pin "<<node.router_report[i].routed_net[j].pin_name[k]<<" Find a path "<<node.router_report[i].routed_net[j].pin_access[k]<<std::endl;              

        }

      }
      
    }

  router_report.close();

};


