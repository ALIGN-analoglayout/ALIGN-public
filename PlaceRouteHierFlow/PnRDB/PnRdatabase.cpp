#include "PnRdatabase.h"

#include <iostream>
#include <fstream>
#include <iomanip>
#include <algorithm>

using namespace nlohmann;

#include "spdlog/spdlog.h"

static bool EndsWith( const string& str, const string& pat)
{
  return std::mismatch( str.rbegin(), str.rend(), pat.rbegin(), pat.rend()).second == pat.rend();
}

PnRdatabase::~PnRdatabase() {
  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.~PnRdatabase");
  logger->debug( "Deconstructing PnRdatabase");
}

deque<int> PnRdatabase::TraverseHierTree() {
  deque<int> Q;
  vector<string> color(hierTree.size(), "white");
  TraverseDFS(Q, color, topidx);
  return Q;
}

void PnRdatabase::Write_Current_Workload(PnRDB::hierNode &node, double total_current, int current_number, std::string outputfile){

  /*
  int llx = node.LL.x;
  int lly = node.LL.y;
  int urx = node.UR.x;
  int ury = node.UR.y;
  */

  int llx = 0;
  int lly = 0;
  int urx = node.width;
  int ury = node.height;

  std::ofstream currentfile;
  currentfile.open(outputfile);

  srand(time(0));

  vector<double> rand_current;

  for(int i =0;i<current_number;i++){
     rand_current.push_back(rand() % 3);
  }

  double sum=0;

  for(int i =0;i<current_number;i++){
     sum = sum + rand_current[i];
  }
  
  
  for(int i=0;i<current_number;i++){
    double x_num = rand() % 10 +1;
    double y_num = rand() % 10 +1;
    if(x_num==10) x_num-=1;
    if(y_num==10) y_num-=1;   
    double x = x_num/10*(urx-llx)+llx;
    double y = y_num/10*(ury-lly)+lly;
    //double current = 0.0005;//rand_current[i]*rand_current[i]/sum*total_current;
    double current = 0.0005/(rand() % 10 +1);//rand_current[i]*rand_current[i]/sum*total_current;
    currentfile<<x<<" "<<y<<" "<<x<<" "<<y<<" "<<current<<std::endl;
  }
  currentfile.close();

}

void PnRdatabase::Write_Power_Mesh_Conf(std::string outputfile){

  std::ofstream PMCfile;
  PMCfile.open(outputfile);

  for(unsigned int i=0;i<DRC_info.Metal_info.size();i++){
    PMCfile<<(double) /*(rand()%5+1)*/4/10<<" "; //power density change from 0.1 to 0.5
  }
  PMCfile<<std::endl;  

  for(unsigned int i=0;i<DRC_info.Via_info.size();i++){
    PMCfile<<1<<" ";
  }
  PMCfile<<std::endl;

  PMCfile.close();
}

void PnRdatabase::TraverseDFS(deque<int>& Q, vector<string>& color, int idx) {
  color[idx]="gray";
  for(vector<PnRDB::blockComplex>::iterator it=hierTree.at(idx).Blocks.begin();it!=hierTree.at(idx).Blocks.end();++it) {
    if( it->child!=-1 && color[it->child].compare("white")==0 ) {
      TraverseDFS(Q, color, it->child);
    }
  }
  color[idx]="black";
  Q.push_back(idx);
}

PnRDB::hierNode PnRdatabase::CheckoutHierNode(int nodeID, int sel) {
  auto& hN = hierTree.at(nodeID);
  if (sel >= 0 && hN.PnRAS.size() > 0) {
    const auto& p = hN.PnRAS[sel];
    hN.gdsFile = p.gdsFile;
    hN.width = p.width;
    hN.height = p.height;
    hN.HPWL = p.HPWL;
    hN.Blocks = p.Blocks;
    hN.Terminals = p.Terminals;
    hN.Nets = p.Nets;
    hN.LL = p.LL;
    hN.UR = p.UR;
    hN.PowerNets = p.PowerNets;
    hN.GuardRings = p.GuardRings;
  }
  return hN;
}

void PnRdatabase::AppendToHierTree(const PnRDB::hierNode& hN) {
  hierTree.push_back( hN);
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

}

void PnRdatabase::TransformNode(PnRDB::hierNode& updatedNode, PnRDB::point translate, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  /*
  this function transform all points and inside the node according to translate and orient,
  it recursively call other transform functions
  Inputs:
    updatedNode: node needs updating
    translate: translate vector
    ort: current_node absolute orientation
    transform_type: Forward (orientate and translate), Backward (undo orientate and translate)
  */
  PnRDB::point LL = updatedNode.LL, UR = updatedNode.UR;
  int width = 0, height = 0;  // here width and height are in updated node coordinate
  if (ort == PnRDB::N || ort == PnRDB::FN || ort == PnRDB::S || ort == PnRDB::FS) {
    width = UR.x - LL.x;
    height = UR.y - LL.y;
    updatedNode.width = width;
    updatedNode.height = height;
  } else if (ort == PnRDB::W || ort == PnRDB::FW || ort == PnRDB::E || ort == PnRDB::FE) {
    width = UR.y - LL.y; 
    height = UR.x - LL.x;
    updatedNode.width = width;
    updatedNode.height = height;
  }
  TransformBlockComplexs(updatedNode.Blocks, translate, width, height, ort, transform_type);
  TransformNets(updatedNode.Nets, translate, width, height, ort, transform_type);
  TransformTerminals(updatedNode.Terminals, translate, width, height, ort, transform_type);
  TransformPins(updatedNode.blockPins, translate, width, height, ort, transform_type);
  TransformContacts(updatedNode.interMetals, translate, width, height, ort, transform_type);
  TransformVias(updatedNode.interVias, translate, width, height, ort, transform_type);
  TransformGuardrings(updatedNode.GuardRings, translate, width, height, ort, transform_type);
}

void PnRdatabase::TransformTerminal(PnRDB::terminal& terminal, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  for (std::vector<PnRDB::contact>::iterator cit = terminal.termContacts.begin(); cit != terminal.termContacts.end(); ++cit) {
    TransformContacts(terminal.termContacts, translate, width, height, ort, transform_type);
  }
}

void PnRdatabase::TransformTerminals(std::vector<PnRDB::terminal>& terminals, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  for (std::vector<PnRDB::terminal>::iterator tit = terminals.begin(); tit != terminals.end(); ++tit) {
    TransformTerminal(*tit, translate, width, height, ort, transform_type);
  }
}

void PnRdatabase::TransformBlock(PnRDB::block& block, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  TransformBbox(block.placedBox, translate, width, height, ort, transform_type);
  TransformPoint(block.placedCenter, translate, width, height, ort, transform_type);
  TransformPins(block.blockPins, translate, width, height, ort, transform_type);
  TransformContacts(block.interMetals, translate, width, height, ort, transform_type);
  TransformVias(block.interVias, translate, width, height, ort, transform_type);
  TransformPins(block.dummy_power_pin, translate, width, height, ort, transform_type);
}

void PnRdatabase::TransformBlocks(std::vector<PnRDB::block>& blocks, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  for (std::vector<PnRDB::block>::iterator bit = blocks.begin(); bit != blocks.end(); ++bit) {
    TransformBlock(*bit, translate, width, height, ort, transform_type);
  }
}

void PnRdatabase::TransformBlockComplexs(std::vector<PnRDB::blockComplex>& bcs, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  for (std::vector<PnRDB::blockComplex>::iterator bit = bcs.begin(); bit != bcs.end(); ++bit) {
    TransformBlockComplex(*bit, translate, width, height, ort, transform_type);
  }
}

void PnRdatabase::TransformBlockComplex(PnRDB::blockComplex& bc, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  TransformBlocks(bc.instance, translate, width, height, ort, transform_type);
}

void PnRdatabase::TransformPins(std::vector<PnRDB::pin>& pins, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  for (std::vector<PnRDB::pin>::iterator pit = pins.begin(); pit != pins.end(); ++pit) {
    TransformPin(*pit, translate, width, height, ort, transform_type);
  }
}

void PnRdatabase::TransformPin(PnRDB::pin& pin, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  TransformContacts(pin.pinContacts, translate, width, height, ort, transform_type);
  TransformVias(pin.pinVias, translate, width, height, ort, transform_type);
}

void PnRdatabase::TransformGuardrings(std::vector<PnRDB::GuardRing>& guardrings, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  for (std::vector<PnRDB::GuardRing>::iterator git = guardrings.begin(); git != guardrings.end(); ++git) {
    TransformGuardring(*git, translate, width, height, ort, transform_type);
  }
}

void PnRdatabase::TransformGuardring(PnRDB::GuardRing& guardring, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  TransformPoint(guardring.LL, translate, width, height, ort, transform_type);
  TransformPoint(guardring.UR, translate, width, height, ort, transform_type);
  TransformPoint(guardring.center, translate, width, height, ort, transform_type);
  TransformPins(guardring.blockPins, translate, width, height, ort, transform_type);
  TransformContacts(guardring.interMetals, translate, width, height, ort, transform_type);
  TransformVias(guardring.interVias, translate, width, height, ort, transform_type);
}

void PnRdatabase::TransformVias(std::vector<PnRDB::Via>& vias, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  for (std::vector<PnRDB::Via>::iterator vit = vias.begin(); vit != vias.end(); ++vit) {
    TransformVia(*vit, translate, width, height, ort, transform_type);
  }
}

void PnRdatabase::TransformVia(PnRDB::Via& via, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  TransformPoint(via.placedpos, translate, width, height, ort, transform_type);
  TransformPoint(via.originpos, translate, width, height, ort, transform_type);
  TransformContact(via.UpperMetalRect, translate, width, height, ort, transform_type);
  TransformContact(via.LowerMetalRect, translate, width, height, ort, transform_type);
  TransformContact(via.ViaRect, translate, width, height, ort, transform_type);
}

void PnRdatabase::TransformContacts(std::vector<PnRDB::contact>& contacts, PnRDB::point translate, int width, int height,
                                    PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  for (std::vector<PnRDB::contact>::iterator cit = contacts.begin(); cit != contacts.end(); ++cit) {
    TransformContact(*cit, translate, width, height, ort, transform_type);
  }
}

void PnRdatabase::TransformContact(PnRDB::contact& contact, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  TransformBbox(contact.placedBox, translate, width, height, ort, transform_type);
  TransformBbox(contact.originBox, translate, width, height, ort, transform_type);
  TransformPoint(contact.placedCenter, translate, width, height, ort, transform_type);
  TransformPoint(contact.originCenter, translate, width, height, ort, transform_type);
}

void PnRdatabase::TransformBboxs(std::vector<PnRDB::bbox>& bboxs, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  for (std::vector<PnRDB::bbox>::iterator bit = bboxs.begin(); bit != bboxs.end(); ++bit) {
    TransformBbox(*bit, translate, width, height, ort, transform_type);
  }
}

void PnRdatabase::TransformBbox(PnRDB::bbox& box, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  int WW = width;
  int HH = height;
  if (transform_type == PnRDB::TransformType::Forward) {
    PnRDB::point tempLL = box.LL, tempUR = box.UR;
    switch (ort) {
      case PnRDB::N:  // keep same
        box.LL = tempLL;
        box.UR = tempUR;
        break;
      case PnRDB::S:  // rotate 180 degree
        box.LL.x = WW - tempUR.x;
        box.LL.y = HH - tempUR.y;
        box.UR.x = WW - tempLL.x;
        box.UR.y = HH - tempLL.y;
        break;
      case PnRDB::W:  // rotate 90 degree counter clockwise
        box.LL.x = HH - tempUR.y;
        box.LL.y = tempLL.x;
        box.UR.x = HH - tempLL.y;
        box.UR.y = tempUR.x;
        break;
      case PnRDB::E:  // rotate 90 degree clockwise
        box.LL.x = tempLL.y;
        box.LL.y = WW - tempUR.x;
        box.UR.x = tempUR.y;
        box.UR.y = WW - tempLL.x;
        break;
      case PnRDB::FN:  // flip horizontally
        box.LL.x = WW - tempUR.x;
        box.UR.x = WW - tempLL.x;
        break;
      case PnRDB::FS:  // flip vertically
        box.LL.y = HH - tempUR.y;
        box.UR.y = HH - tempLL.y;
        break;
      case PnRDB::FW:  // flip along 45 degree axis
        box.LL.x = tempLL.y;
        box.LL.y = tempLL.x;
        box.UR.x = tempUR.y;
        box.UR.y = tempUR.x;
        break;
      case PnRDB::FE:  //flip along 135 degree axis
        box.LL.x = HH - tempUR.y;
        box.LL.y = WW - tempUR.x;
        box.UR.x = HH - tempLL.y;
        box.UR.y = WW - tempLL.x;
        break;
      default:
        box.LL = tempLL;
        box.UR = tempUR;
        break;
    }
    box.LL = box.LL + translate;
    box.UR = box.UR + translate;
  }else if(transform_type==PnRDB::TransformType::Backward){
    box.LL = box.LL - translate;
    box.UR = box.UR - translate;
    PnRDB::point tempLL = box.LL, tempUR = box.UR;
    switch (ort) {
      case PnRDB::N:  // keep same
        box.LL = tempLL;
        box.UR = tempUR;
        break;
      case PnRDB::S:  // rotate 180 degree
        box.LL.x = WW - tempUR.x;
        box.LL.y = HH - tempUR.y;
        box.UR.x = WW - tempLL.x;
        box.UR.y = HH - tempLL.y;
        break;
      case PnRDB::W:  // rotate 90 degree counter clockwise
        box.LL.x = tempLL.y;
        box.LL.y = HH - tempUR.x;
        box.UR.x = tempUR.y;
        box.UR.y = HH - tempLL.x;
        break;
      case PnRDB::E:  // rotate 90 degree clockwise
        box.LL.x = WW - tempUR.y;
        box.LL.y = tempLL.x;
        box.UR.x = WW - tempLL.y;
        box.UR.y = tempUR.x;
        break;
      case PnRDB::FN:  // flip horizontally
        box.LL.x = WW - tempUR.x;
        box.UR.x = WW - tempLL.x;
        break;
      case PnRDB::FS:  // flip vertically
        box.LL.y = HH - tempUR.y;
        box.UR.y = HH - tempLL.y;
        break;
      case PnRDB::FW:  // flip along 45 degree axis
        box.LL.x = tempLL.y;
        box.LL.y = tempLL.x;
        box.UR.x = tempUR.y;
        box.UR.y = tempUR.x;
        break;
      case PnRDB::FE:  //flip along 135 degree axis
        box.LL.x = WW - tempUR.y;
        box.LL.y = HH - tempUR.x;
        box.UR.x = WW - tempLL.y;
        box.UR.y = HH - tempLL.x;
        break;
      default:
        box.LL = tempLL;
        box.UR = tempUR;
        break;
    }
  }
}

void PnRdatabase::TransformPoints(std::vector<PnRDB::point>& points, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  for (std::vector<PnRDB::point>::iterator pit = points.begin(); pit != points.end(); ++pit) {
    TransformPoint(*pit, translate, width, height, ort, transform_type);
  }
}

void PnRdatabase::TransformPoint(PnRDB::point& p, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  int WW = width;
  int HH = height;
  if (transform_type == PnRDB::TransformType::Forward) {
    int X = p.x, Y = p.y;
    switch (ort) {
      case PnRDB::N:
        p.x = X;
        p.y = Y;
        break;
      case PnRDB::S:
        p.x = WW - X;
        p.y = HH - Y;
        break;
      case PnRDB::W:
        p.x = HH - Y;
        p.y = X;
        break;
      case PnRDB::E:
        p.x = Y;
        p.y = WW - X;
        break;
      case PnRDB::FN:// flip horizontally
        p.x = WW - X;
        p.y = Y;
        break;
      case PnRDB::FS:// flip vertically
        p.x = X;
        p.y = HH - Y;
        break;
      case PnRDB::FW:// flip along 45 degree axis
        p.x = Y;
        p.y = X;
        break;
      case PnRDB::FE:// flip along 135 degree axis
        p.x = HH - Y;
        p.y = WW - X;
        break;
      default:
        p.x = X;
        p.y = Y;
        break;
    }
    p = p + translate;
  } else if (transform_type == PnRDB::TransformType::Backward) {
    p = p - translate;
    int X = p.x, Y = p.y;
    switch (ort) {
      case PnRDB::N:
        p.x = X;
        p.y = Y;
        break;
      case PnRDB::S:
        p.x = WW - X;
        p.y = HH - Y;
        break;
      case PnRDB::W:
        p.x = Y;
        p.y = HH - X;
        break;
      case PnRDB::E:
        p.x = WW - Y;
        p.y = X;
        break;
      case PnRDB::FN:// flip horizontally
        p.x = WW - X;
        p.y = Y;
        break;
      case PnRDB::FS:// flip vertically
        p.x = X;
        p.y = HH - Y;
        break;
      case PnRDB::FW:// flip along 45 degree axis
        p.x = Y;
        p.y = X;
        break;
      case PnRDB::FE:// flip along 135 degree axis
        p.x = WW - Y;
        p.y = HH - X;
        break;
      default:
        p.x = X;
        p.y = Y;
        break;
    }
  }
}

void PnRdatabase::TransformMetal(PnRDB::Metal& metal, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type){
  TransformPoints(metal.LinePoint, translate, width, height, ort, transform_type);
  TransformContact(metal.MetalRect, translate, width, height, ort, transform_type);
}

void PnRdatabase::TransformMetals(std::vector<PnRDB::Metal>& metals, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type){
  for (std::vector<PnRDB::Metal>::iterator mit = metals.begin(); mit != metals.end(); ++mit) {
    TransformMetal(*mit, translate, width, height, ort, transform_type);
  }
}

void PnRdatabase::TransformNet(PnRDB::net& net, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  TransformMetals(net.path_metal, translate, width, height, ort, transform_type);
  TransformVias(net.path_via, translate, width, height, ort, transform_type);
}

void PnRdatabase::TransformNets(std::vector<PnRDB::net>& nets, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType transform_type) {
  for (std::vector<PnRDB::net>::iterator nit = nets.begin(); nit != nets.end(); ++nit) {
    TransformNet(*nit, translate, width, height, ort, transform_type);
  }
}

void PnRdatabase::TranslateNode(PnRDB::hierNode& updatedNode, PnRDB::point translate) { 
  /*
  Inputs:
    updatedNode: node needs updating
    translate: translate reference point, all points will be subtracted by this point
  */
  PnRDB::point LL = updatedNode.LL, UR = updatedNode.UR;
  int width = UR.x - LL.x, height = UR.y - LL.y;
  TransformBlockComplexs(updatedNode.Blocks, translate, width, height, PnRDB::Omark::N, PnRDB::Backward);
  TransformTerminals(updatedNode.Terminals, translate, width, height, PnRDB::Omark::N, PnRDB::Backward);
  TransformPins(updatedNode.blockPins, translate, width, height, PnRDB::Omark::N, PnRDB::Backward);
  TransformContacts(updatedNode.interMetals, translate, width, height, PnRDB::Omark::N, PnRDB::Backward);
  TransformVias(updatedNode.interVias, translate, width, height, PnRDB::Omark::N, PnRDB::Backward);
  TransformNets(updatedNode.Nets, translate, width, height, PnRDB::Omark::N, PnRDB::Backward);
  TransformPoint(updatedNode.LL, translate, width, height, PnRDB::Omark::N, PnRDB::Backward);
  TransformPoint(updatedNode.UR, translate, width, height, PnRDB::Omark::N, PnRDB::Backward);
}

PnRDB::Omark PnRdatabase::RelOrt2AbsOrt(PnRDB::Omark current_node_ort, PnRDB::Omark childnode_ort) {
  /*
  Inputs:
    current_node_ort: current_node's absolute orientation in topnode
    childnode_ort: childnode's relative orientation in current_node
  Outputs:
    childnode's absolute orientation in topnode

  coordinate definition: Z = X × Y
  Y
  ↑
  ⊙Z →X
  transform matrix:
  N:  1  0  0
      0  1  0 
      0  0  1
  S: -1  0  0
      0 -1  0
      0  0  1
  W:  0 -1  0
      1  0  0
      0  0  1
  E:  0  1  0
     -1  0  0
      0  0  1
  F: -1  0  0
      0  1  0
      0  0 -1
  FN: F × N = F
    =-1  0  0
      0  1  0
      0  0 -1
  FS: F × S 
    = 1  0  0
      0 -1  0
      0  0 -1
  FW: F × W
      0  1  0
      1  0  0
      0  0 -1
  FE: F × E
      0 -1  0
     -1  0  0
      0  0 -1
  */
  const PnRDB::Omark TransformTable[8][8] = {{PnRDB::N, PnRDB::S, PnRDB::W, PnRDB::E, PnRDB::FN, PnRDB::FS, PnRDB::FW, PnRDB::FE},
                                             {PnRDB::S, PnRDB::N, PnRDB::E, PnRDB::W, PnRDB::FS, PnRDB::FN, PnRDB::FE, PnRDB::FW},
                                             {PnRDB::W, PnRDB::E, PnRDB::S, PnRDB::N, PnRDB::FE, PnRDB::FW, PnRDB::FN, PnRDB::FS},
                                             {PnRDB::E, PnRDB::W, PnRDB::N, PnRDB::S, PnRDB::FW, PnRDB::FE, PnRDB::FS, PnRDB::FN},
                                             {PnRDB::FN, PnRDB::FS, PnRDB::FW, PnRDB::FE, PnRDB::N, PnRDB::S, PnRDB::W, PnRDB::E},
                                             {PnRDB::FS, PnRDB::FN, PnRDB::FE, PnRDB::FW, PnRDB::S, PnRDB::N, PnRDB::E, PnRDB::W},
                                             {PnRDB::FW, PnRDB::FE, PnRDB::FS, PnRDB::FN, PnRDB::E, PnRDB::W, PnRDB::N, PnRDB::S},
                                             {PnRDB::FE, PnRDB::FW, PnRDB::FN, PnRDB::FS, PnRDB::W, PnRDB::E, PnRDB::S, PnRDB::N}};
  return TransformTable[current_node_ort][childnode_ort];
}

void PnRdatabase::TransformBlockPinsOriginToPlaced(std::vector<PnRDB::pin>& blockPins, PnRDB::point translate, int width, int height,
                                                   PnRDB::Omark ort) {
  /*
  this function transforms original pose into placed pose
  Inputs:
    blockPins: blockpins to be transformed
    translate: translate vector
    ort: orientation
  */
  TransformPins(blockPins, translate, width, height, ort, PnRDB::TransformType::Forward);
  std::vector<PnRDB::pin> blockPins_copy = blockPins;
  TransformPins(blockPins, translate, width, height, ort, PnRDB::TransformType::Backward);
  for (unsigned int pit = 0; pit < blockPins.size(); pit++) {
    for (unsigned int cit = 0; cit < blockPins[pit].pinContacts.size(); cit++) {
      blockPins[pit].pinContacts[cit].placedBox = blockPins_copy[pit].pinContacts[cit].originBox;
      blockPins[pit].pinContacts[cit].placedCenter = blockPins_copy[pit].pinContacts[cit].originCenter;
    }
    for (unsigned int vit = 0; vit < blockPins[pit].pinVias.size(); vit++){
      blockPins[pit].pinVias[vit].placedpos = blockPins_copy[pit].pinVias[vit].originpos;
      blockPins[pit].pinVias[vit].UpperMetalRect.placedBox = blockPins_copy[pit].pinVias[vit].UpperMetalRect.originBox;
      blockPins[pit].pinVias[vit].UpperMetalRect.placedCenter = blockPins_copy[pit].pinVias[vit].UpperMetalRect.originCenter;
      blockPins[pit].pinVias[vit].LowerMetalRect.placedBox = blockPins_copy[pit].pinVias[vit].LowerMetalRect.originBox;
      blockPins[pit].pinVias[vit].LowerMetalRect.placedCenter = blockPins_copy[pit].pinVias[vit].LowerMetalRect.originCenter;
      blockPins[pit].pinVias[vit].ViaRect.placedBox = blockPins_copy[pit].pinVias[vit].ViaRect.originBox;
      blockPins[pit].pinVias[vit].ViaRect.placedCenter = blockPins_copy[pit].pinVias[vit].ViaRect.originCenter;
    }
  }
}

void PnRdatabase::TransformIntermetalsOriginToPlaced(std::vector<PnRDB::contact>& interMetals, PnRDB::point translate, int width, int height,
                                                   PnRDB::Omark ort) {
  /*
  this function transforms original pose into placed pose
  Inputs:
    interMetals: intermetals to be transformed
    translate: translate vector
    ort: orientation
  */
  TransformContacts(interMetals, translate, width, height, ort, PnRDB::TransformType::Forward);
  std::vector<PnRDB::contact> interMetals_copy = interMetals;
  TransformContacts(interMetals, translate, width, height, ort, PnRDB::TransformType::Backward);
  for (unsigned int mit = 0; mit < interMetals.size(); mit++) {
    interMetals[mit].placedBox = interMetals_copy[mit].originBox;
    interMetals[mit].placedCenter = interMetals_copy[mit].originCenter;
  }
}

void PnRdatabase::TransformInterviasOriginToPlaced(std::vector<PnRDB::Via>& interVias, PnRDB::point translate, int width, int height,
                                                   PnRDB::Omark ort) {
  /*
  this function transforms original pose into placed pose
  Inputs:
    interVias: intervias to be transformed
    translate: translate vector
    ort: orientation
  */
  TransformVias(interVias, translate, width, height, ort, PnRDB::TransformType::Forward);
  std::vector<PnRDB::Via> interVias_copy = interVias;
  TransformVias(interVias, translate, width, height, ort, PnRDB::TransformType::Backward);
  for (unsigned int vit = 0; vit < interVias.size(); vit++){
      interVias[vit].placedpos = interVias_copy[vit].originpos;
      interVias[vit].UpperMetalRect.placedBox = interVias_copy[vit].UpperMetalRect.originBox;
      interVias[vit].UpperMetalRect.placedCenter = interVias_copy[vit].UpperMetalRect.originCenter;
      interVias[vit].LowerMetalRect.placedBox = interVias_copy[vit].LowerMetalRect.originBox;
      interVias[vit].LowerMetalRect.placedCenter = interVias_copy[vit].LowerMetalRect.originCenter;
      interVias[vit].ViaRect.placedBox = interVias_copy[vit].ViaRect.originBox;
      interVias[vit].ViaRect.placedCenter = interVias_copy[vit].ViaRect.originCenter;
    }
}

std::vector<int> PnRdatabase::UsedInstancesIdx(int nodeID) {
  std::vector<int> ret;
  for (unsigned int i = 0; i < hierTree[nodeID].PnRAS.size(); i++) {
    bool found = false;
    for (auto p : hierTree[nodeID].parent) {
      for (auto b : hierTree[p].Blocks) {
        if (b.instance[b.selectedInstance].master == hierTree[nodeID].name && b.selectedInstance == i) {
          //if the instance is used in any parent node
          ret.push_back(i);
          found = true;
          break;
        }
      }
      if (found) break;
    }
  }
  return ret;
}

void PnRdatabase::CheckinChildnodetoBlock(PnRDB::hierNode& parent, int blockID, const PnRDB::hierNode& child, PnRDB::Omark ort) {
  // update child into parent.blocks[blockID]
  // update (child.intermetal,intervia,blockpins) into blocks[blockid]
  //PnRDB::Omark ort = child.abs_orient;
  int width = child.UR.x - child.LL.x;
  int height = child.UR.y - child.LL.y;

  auto& pi = parent.Blocks[blockID].instance[parent.Blocks[blockID].selectedInstance];

  PnRDB::point translate = pi.placedBox.LL;
  pi.gdsFile = child.gdsFile;

  // transform child blockpins orginals into placed in parent coordinate
  std::vector<PnRDB::pin> blockPins = child.blockPins;
  TransformBlockPinsOriginToPlaced(blockPins, translate, width, height, ort);
  for (unsigned int p = 0; p < pi.blockPins.size(); p++) {
    for (unsigned int q = 0; q < child.blockPins.size(); q++) {
      if (pi.blockPins[p].name == blockPins[q].name) {
        pi.blockPins[p].pinContacts = blockPins[q].pinContacts;
        pi.blockPins[p].pinVias = blockPins[q].pinVias;
        break;
      }
    }
  }

  //transform child intermetals originals into placed in parent coordinate
  std::vector<PnRDB::contact> interMetals = child.interMetals;
  TransformIntermetalsOriginToPlaced(interMetals, translate, width, height, ort);
  pi.interMetals = interMetals;

  //transform child intervias originals into placed in parent coordinate
  std::vector<PnRDB::Via> interVias = child.interVias;
  TransformInterviasOriginToPlaced(interVias, translate, width, height, ort);
  pi.interVias = interVias;

  //checkin childnode router report
  for (unsigned int i = 0; i < child.router_report.size();++i){
    parent.router_report.push_back(child.router_report[i]);
  }
}

void PnRdatabase::ExtractPinsToPowerPins(PnRDB::hierNode& updatedNode) {
  for (unsigned int i = 0; i < updatedNode.PowerNets.size(); i++) {
    for (unsigned int j = 0; j < updatedNode.PowerNets[i].connected.size(); j++) {
      PnRDB::pin temp_pin;
      int iter = updatedNode.PowerNets[i].connected[j].iter;
      int iter2 = updatedNode.PowerNets[i].connected[j].iter2;
      temp_pin = updatedNode.Blocks[iter2].instance[updatedNode.Blocks[iter2].selectedInstance].blockPins[iter];
      updatedNode.PowerNets[i].Pins[j] = temp_pin;
    }
  }
}

// [RA] need further modification for hierarchical issue - wbxu
void PnRdatabase::CheckinHierNode(int nodeID, const PnRDB::hierNode& updatedNode){

  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.CheckinHierNode");

  //In fact, the original node, do not need to be updated. Just update father node is fine.
  //update the original node
  logger->info("CheckinHierNode");
  PnRDB::layoutAS tmpL;
  tmpL.gdsFile=updatedNode.gdsFile;
  tmpL.width=updatedNode.width;
  tmpL.height=updatedNode.height;
  tmpL.HPWL = updatedNode.HPWL;
  tmpL.Blocks = updatedNode.Blocks;
  tmpL.Terminals=updatedNode.Terminals;
  tmpL.Nets=updatedNode.Nets;
  tmpL.LL = updatedNode.LL;
  tmpL.UR = updatedNode.UR;
  tmpL.GuardRings = updatedNode.GuardRings;
  hierTree[nodeID].PnRAS.push_back(tmpL);

  hierTree[nodeID].isCompleted = 1;
  hierTree[nodeID].gdsFile = updatedNode.gdsFile;
  hierTree[nodeID].GuardRings = updatedNode.GuardRings;
  // update current node information
  for(unsigned int i=0;i<hierTree[nodeID].Blocks.size();i++){
     int sel=updatedNode.Blocks[i].selectedInstance;
     logger->debug("Block {0} select {1} ",i,sel);
     if(sel<0 || sel>=updatedNode.Blocks[i].instNum) {logger->error("PnRDB-Error: unselected block {0}",i);continue;}
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
      net.axis_coor = net2.axis_coor;
  }
    }

    /*
  //update net information//////
  for(unsigned int i=0;i<hierTree[nodeID].Nets.size();i++){
     for(unsigned int j=0;j<updatedNode.Nets.size();j++){
          if(hierTree[nodeID].Nets[i].name ==updatedNode.Nets[j].name){
               hierTree[nodeID].Nets[i].path_metal = updatedNode.Nets[j].path_metal;
               hierTree[nodeID].Nets[i].path_via = updatedNode.Nets[j].path_via;
               break;
            }
        }
     }
    */

  logger->debug("update power net");
  //update PowerNet information//////
  logger->debug("hierTree power net size {0}",hierTree[nodeID].PowerNets.size());
  logger->debug("updatedNode power net size {0}",updatedNode.PowerNets.size());
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
   hierTree[nodeID].PnRAS.back().PowerNets=updatedNode.PowerNets;
   logger->debug("node ID {0}",nodeID);
   logger->debug("hierTree power net size {0}",hierTree[nodeID].PowerNets.size());
   logger->debug("updatedNode power net size {0}",updatedNode.PowerNets.size());

   hierTree[nodeID].blockPins=updatedNode.blockPins;
   hierTree[nodeID].interMetals=updatedNode.interMetals;
   hierTree[nodeID].interVias=updatedNode.interVias;

  //update father imformation//////
    logger->debug("Update parent");
    for(unsigned int i=0;i<hierTree[nodeID].parent.size();i++){

     logger->debug("Start update blocks in parent");
     //update father blocks information
     auto& parent_node = hierTree[hierTree[nodeID].parent[i]];

     //there will be a bug for multi-aspect ratio Yaguang 1/1/2020
     logger->debug("Update router report for parent");
     for(unsigned int j=0;j<updatedNode.router_report.size();j++){
          parent_node.router_report.push_back(updatedNode.router_report[j]);
        }
     logger->debug("End Update router report for parent");

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

/*
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
*/

    logger->debug("Start Update power pin in parent");
     //update power pin information

    for(unsigned int j=0;j<parent_node.Blocks.size();j++){
       auto& lhs = parent_node.Blocks[j];
       auto& b = lhs.instance.back();
       if(b.master.compare(updatedNode.name)==0){
         b.dummy_power_pin.clear();          
          for(unsigned int k = 0; k<updatedNode.PowerNets.size();k++){
            int found = 0;
            for(unsigned int l =0;l<b.PowerNets.size();l++){
               if(updatedNode.PowerNets[k].name == b.PowerNets[l].name){
                 found = 1;
                 b.PowerNets[l].dummy_connected.clear();
                 for(unsigned int p=0;p<updatedNode.PowerNets[k].Pins.size();p++){
                   PnRDB::connectNode temp_connectNode;
                   temp_connectNode.iter2 = j;
                   temp_connectNode.iter = b.dummy_power_pin.size();
                   //here is the problem
                   b.PowerNets[l].dummy_connected.push_back(temp_connectNode);
                   //parent_node.PowerNets[l].dummy_connected.push_back(temp_connectNode);
                   //need move the dummy_connected into block level
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
                   //here is the problem too
                   temp_PowerNet.dummy_connected.push_back(temp_connectNode);
                   //temp_PowerNet.dummy_connected.push_back(temp_connectNode);
                   //here is the problem too
                   }                     
                b.PowerNets.push_back(temp_PowerNet);
               }                      
           }
         }
      }

      logger->debug("Extract dummy power connection into parent");

      for(unsigned int k = 0; k<parent_node.PowerNets.size();k++){
         parent_node.PowerNets[k].dummy_connected.clear();
      }

      for(unsigned int j=0;j<parent_node.Blocks.size();j++){
         auto& lhs = parent_node.Blocks[j];
         auto& b = lhs.instance.back();
         for(unsigned int l =0;l<b.PowerNets.size();l++){
            int found = 0;
            for(unsigned int k = 0; k<parent_node.PowerNets.size();k++){
               if(b.PowerNets[l].name==parent_node.PowerNets[k].name){
                  found = 1;
                  for(unsigned int h = 0;h < b.PowerNets[l].dummy_connected.size();h++){
                      parent_node.PowerNets[k].dummy_connected.push_back(b.PowerNets[l].dummy_connected[h]);
                     }
                 }
            }
            if(found ==0){
               PnRDB::PowerNet temp_PowerNet;
               temp_PowerNet = b.PowerNets[l];
               temp_PowerNet.connected.clear();
               //temp_PowerNet.dummy_connected.clear();
               temp_PowerNet.Pins.clear();
               parent_node.PowerNets.push_back(temp_PowerNet);
            }
         }
      }
      
      logger->debug("End update power pin in parent");


     }

  logger->debug("End update blocks in parent");
  


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

    auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.WriteGcellGlobalRouteFile");

    //do output tiles (first_tile_idx, ..., last_tile_idx)
    logger->debug( "output data " );
    logger->debug( "layer {0}" ,DRC_info.Metal_info.at(MetalIdx).name);
    logger->debug( " net_name {0}" ,net_name);
    logger->debug( " width {0}" , width );
    logger->debug( " rect ");
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

      logger->debug( " MetalDirection: {0}" , MetalDirection );
      json jsonRect =  json::array();
      jsonRect.push_back(f.x);
      jsonRect.push_back(f.y);
      jsonRect.push_back(l.x);
      jsonRect.push_back(l.y);
      jsonWire["rect"] = jsonRect;
    }

    logger->debug( "connected pins: " );
    PnRDB::net net = node.Nets.at(net_id);
    json jsonConnectedPins = json::array();
    logger->debug( "tile_idx: ");
    for(vector<int>::const_iterator tile_idx = tile_idxs.begin(); tile_idx!=tile_idxs.end(); ++tile_idx){
        logger->debug("{0}, " ,*tile_idx);
        //search all the tiles in the consecutive tiles
        for(vector<std::vector<int>>::const_iterator i = net.connectedTile.begin(); i!=net.connectedTile.end();++i){
            int pin_id = i - net.connectedTile.begin();
            //pin_id is the index in net.connectedTile
            for(vector<int>::const_iterator j = i->begin(); j!=i->end();++j){
                if(*tile_idx != *j){continue;}
                //current tile index == pin_terminal
                json jsonConnectedPin;
                logger->debug("pin_id {0}" , pin_id );
                if (net.connected.at(pin_id).type==PnRDB::Block) {
                    int selectedInstance = node.Blocks.at(net.connected.at(pin_id).iter2).selectedInstance;
                    vector<PnRDB::contact> pinContacts = node.Blocks.at(net.connected.at(pin_id).iter2).instance.at(selectedInstance).blockPins.at(net.connected.at(pin_id).iter).pinContacts;
                    for(vector<PnRDB::contact>::const_iterator contact_it = pinContacts.begin(); contact_it != pinContacts.end(); ++contact_it){
                        string sink_name = node.Blocks.at(net.connected.at(pin_id).iter2).instance.at(selectedInstance).name + "/" + node.Blocks.at(net.connected.at(pin_id).iter2).instance.at(selectedInstance).blockPins.at(net.connected.at(pin_id).iter).name;
                        logger->debug( "sink_name: {0} " ,sink_name);
                        jsonConnectedPin["sink_name"] = sink_name;

                        string layer = "";
                        layer = contact_it->metal;
                        jsonConnectedPin["layer"] = layer;
                        logger->debug( " layer: {0}" , layer);

                        json jsonRect = json::array();
                        logger->debug( "contacts size {0}" , pinContacts.size() );
                        PnRDB::bbox rect = contact_it->placedBox;
                        jsonRect.push_back(rect.LL.x);
                        jsonRect.push_back(rect.LL.y);
                        jsonRect.push_back(rect.UR.x);
                        jsonRect.push_back(rect.UR.y);
                        logger->debug( "placedBox: {0}, {1}, " , rect.LL.x ,rect.LL.y );
                        logger->debug( "{0}, {1} ",rect.UR.x,rect.UR.y );
                        jsonConnectedPin["rect"] = jsonRect;
                        jsonConnectedPins.push_back( jsonConnectedPin);
                    }
                } else if (node.Nets.at(net_id).connected.at(pin_id).type==PnRDB::Terminal){
                    vector<PnRDB::contact> termContacts = node.Terminals.at(net.connected.at(pin_id).iter).termContacts;
                    for(vector<PnRDB::contact>::const_iterator contact_it = termContacts.begin(); contact_it != termContacts.end(); ++contact_it){
                        string sink_name = node.Terminals.at(net.connected.at(pin_id).iter).name;
                        logger->debug( "sink_name: {0}", sink_name);
                        jsonConnectedPin["sink_name"] = sink_name;

                        string layer = "";
                        layer = contact_it->metal;
                        jsonConnectedPin["layer"] = layer;
                        logger->debug( " layer: {0}", layer);

                        json jsonRect = json::array();
                        PnRDB::bbox rect = contact_it->placedBox;
                        jsonRect.push_back(rect.LL.x);
                        jsonRect.push_back(rect.LL.y);
                        jsonRect.push_back(rect.UR.x);
                        jsonRect.push_back(rect.UR.y);
                        logger->debug( "#termcontact: {0}, {1} " , rect.LL.x , rect.LL.y );
                        logger->debug( "{0}, {1} ",rect.UR.x , rect.UR.y);
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

    auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.WriteGcellGlobalRoute");

    //this function write gcell global router result into json for detail route use
    //combine consecutive tiles into one
    json jsonWiresArray = json::array();
    logger->debug("#Nets: {0}" , node.Nets.size() );
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

            if( int(tile1.metal.size()) != 1 || int(tile2.metal.size()) != 1){
                logger->error( "ERROR: tile.metal.size != 1 !" );
            }else{
                MetalIdx1 = tile1.metal.front();
                MetalIdx2 = tile2.metal.front();
            }
            logger->debug("tile indexs: {0} {1} " , tile_idx1 , tile_idx2);
            logger->debug("tile layers: {0} {1} " ,MetalIdx1 , MetalIdx2 );
            logger->debug("first tile x/y/width/height: {0} {1} {2} {3}" , x1 , y1 , w1 , h1);
            logger->debug("second tile x/y/width/height: {0} {1} {2} {3} " , x2, y2 , w2 , h2 );

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

            logger->debug( "MetalDirection: {0}" ,MetalDirection );
            logger->debug( "can append: {0}" ,can_append );

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
        //std::cout << std::endl;
    }

    json jsonTop;
    jsonTop["wires"] = jsonWiresArray;

    std::ofstream jsonStream(opath+rofile);
    if (jsonStream.fail()) {
      logger->error("PnRData-Error: cannot open file {0} for writing", opath + rofile);
      return;
    }
    jsonStream << std::setw(4) << jsonTop;
    jsonStream.close();
    
}

void PnRdatabase::WriteGcellDetailRoute(const PnRDB::hierNode& node, const string& rofile, const string& opath) const {

    auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.WriteGcellDetailRoute");

    json jsonWiresArray = json::array();
    for(unsigned int i=0;i<node.Nets.size();++i){

      json jsonNet;
      jsonNet["name"] = node.Nets[i].name;
      json jsonpath = json::array();
      for(unsigned int j=0;j<node.Nets[i].path_metal.size();++j){

         json jsonRect =  json::array();
         jsonRect.push_back(node.Nets[i].path_metal[j].LinePoint[0].x);
         jsonRect.push_back(node.Nets[i].path_metal[j].LinePoint[0].y);
         jsonRect.push_back(node.Nets[i].path_metal[j].LinePoint[1].x);
         jsonRect.push_back(node.Nets[i].path_metal[j].LinePoint[1].y);
         jsonpath.push_back(jsonRect);

      }
      jsonNet["path"] = jsonpath;

      json connections = json::array();

      for(unsigned int j=0;j<node.Nets[i].connected.size();++j){

         json connection =  json::array();
         if(node.Nets[i].connected[j].iter2>=0){
           connection.push_back(node.Nets[i].connected[j].iter2);
           connection.push_back(node.Nets[i].connected[j].iter);
           connections.push_back(connection);
         }

      }
      jsonNet["path"] = jsonpath;
      jsonNet["connection"] = connections;

      
      jsonWiresArray.push_back(jsonNet);

    }

    json jsonBlocks = json::array();
    for(unsigned int i=0;i<node.Blocks.size();++i){
      int selected_index = node.Blocks[i].selectedInstance;
      json jsonblock;
      jsonblock["name"] = node.Blocks[i].instance[selected_index].name;
      json blockposition = json::array();
      blockposition.push_back(node.Blocks[i].instance[selected_index].placedBox.LL.x);
      blockposition.push_back(node.Blocks[i].instance[selected_index].placedBox.LL.y);
      blockposition.push_back(node.Blocks[i].instance[selected_index].placedBox.UR.x);
      blockposition.push_back(node.Blocks[i].instance[selected_index].placedBox.UR.y);
      jsonblock["position"] = blockposition;
      json blockpins = json::array();
      for(unsigned int j=0;j<node.Blocks[i].instance[selected_index].blockPins.size();++j){
        json blockpin;
        blockpin["name"] = node.Blocks[i].instance[selected_index].blockPins[j].name;
        json blockpincontacts = json::array();
        for(unsigned int k=0;k<node.Blocks[i].instance[selected_index].blockPins[j].pinContacts.size();++k){
           json blockpincontact = json::array();
           blockpincontact.push_back(node.Blocks[i].instance[selected_index].blockPins[j].pinContacts[k].placedBox.LL.x);
           blockpincontact.push_back(node.Blocks[i].instance[selected_index].blockPins[j].pinContacts[k].placedBox.LL.y);
           blockpincontact.push_back(node.Blocks[i].instance[selected_index].blockPins[j].pinContacts[k].placedBox.UR.x);
           blockpincontact.push_back(node.Blocks[i].instance[selected_index].blockPins[j].pinContacts[k].placedBox.UR.y);
           blockpincontacts.push_back(blockpincontact);
        }
        blockpin["contact"] = blockpincontacts;
        blockpins.push_back(blockpin);
      }
      jsonblock["pin"] = blockpins;
      jsonBlocks.push_back(jsonblock);
    }
    

    json jsonTop;
    jsonTop["wires"] = jsonWiresArray;
    jsonTop["blocks"] = jsonBlocks;

    std::ofstream jsonStream(opath+rofile);
    if (jsonStream.fail()) {
      logger->error("PnRData-Error: cannot open file {0} for writing", opath + rofile);
      return;
    }
    jsonStream << std::setw(4) << jsonTop;
    jsonStream.close();
    
}


void PnRdatabase::WriteGlobalRoute(const PnRDB::hierNode& node, const string& rofile, const string& opath) const {

	auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.WriteGlobalRoute");

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
		if(it->connected.at(k).type==PnRDB::Block || (it->connected.at(k).type==PnRDB::Terminal && node.isTop)) {
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
	logger->error("PnRData-Error: cannot open file {0} for writing ",opath+rofile);
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
      //if(it2->LinePoint.at(0).x==it2->LinePoint.at(1).x && it2->LinePoint.at(0).y==it2->LinePoint.at(1).y) {continue;}
      if(i!=0) {OF2<<","<<std::endl;}
      i++;
      OF2<<"    { \"layer\": \""<<DRC_info.Metal_info.at(it2->MetalIdx).name;
      OF2<<"\", \"net_name\": \""<<it->name<<"\", \"width\": "<<it2->width;
      OF2<<", \"rect\": [ "<<it2->LinePoint.at(0).x<<", "<<it2->LinePoint.at(0).y<<", "<<it2->LinePoint.at(1).x<<", "<<it2->LinePoint.at(1).y<<"],"<<std::endl;
      OF2<<"      \"connected_pins\": ["<<std::endl;
      int mIdx=it2-it->path_metal.begin();
      int sinkCount=0;
      for(unsigned int k=0;k<it->connectedContact.size();++k) {
        if(it->connectedContact.at(k).metalIdx!=mIdx) {continue;}
        if(it->connected.at(k).type==PnRDB::Block) {
          if(sinkCount!=0) {OF2<<","<<std::endl;}
          OF2<<"          { "<<"\"sink_name\": \""<<node.Blocks.at(it->connected.at(k).iter2).instance.back().name<<"/"<<node.Blocks.at(it->connected.at(k).iter2).instance.back().blockPins.at(it->connected.at(k).iter).name<<"\"";
        } else if (it->connected.at(k).type==PnRDB::Terminal && node.isTop) {
          if(sinkCount!=0) {OF2<<","<<std::endl;}
          OF2<<"          { "<<"\"sink_name\": \""<<node.Terminals.at(it->connected.at(k).iter).name<<"\"";
        } else {continue;}
        ++sinkCount;
        OF2<<", \"layer\": \""<<it->connectedContact.at(k).conTact.metal<<"\", \"rect\": ["<<it->connectedContact.at(k).conTact.placedBox.LL.x<<", "<<it->connectedContact.at(k).conTact.placedBox.LL.y<<", "<<it->connectedContact.at(k).conTact.placedBox.UR.x<<", "<<it->connectedContact.at(k).conTact.placedBox.UR.y<<"] }";
      }
      if(sinkCount>0) {OF2<<std::endl;}
      OF2<<"      ]"<<std::endl;
      OF2<<"    }";
      //if(it!=node.Nets.end()-1 || it2!=it->segments.end()-1) {OF2<<",";}
      //OF2<<endl;
    }
  }
  OF2<<std::endl<<"  ]"<<endl;
  //OF2<<"  \"rects\": ["<<endl;
  //for(vector<PnRDB::net>::iterator it=node.Nets.begin(); it!=node.Nets.end(); ++it) {
  //  if(node.isTop) {
  //    if(it->connected.size()<=1) {continue;}
  //  } else {
  //    if(!it->sink2Terminal && it->connected.size()<=1) {continue;}
  //    if(it->sink2Terminal && it->connected.size()<=2) {continue;}
  //  }
  //  for(int k=0;k<it->connectedContact.size();++k) {
  //    if(it->connected.at(k).type==PnRDB::Block) {
  //      OF2<<"    { \"net_name\": \""<<it->name<<"\", \"sink_name\": \""<<node.Blocks.at(it->connected.at(k).iter2).instance.back().name<<"/"<<node.Blocks.at(it->connected.at(k).iter2).instance.back().blockPins.at(it->connected.at(k).iter).name<<"\"";
  //    } else if (it->connected.at(k).type==PnRDB::Terminal && node.isTop) {
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

  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.WritePlaceRoute");

  std::ofstream OF(pofile);
  if(OF.fail()) {
    logger->error("PnRData-Error: cannot open the file ",pofile);
    return;
  }
  int Xunit=-1,Yunit=-1;
  switch (DRC_info.Metal_info.at(0).direct) {
    case 1: // H -> Y axis
            Yunit=DRC_info.Metal_info.at(0).grid_unit_y; break;
    case 0: // V -> X axis
            Xunit=DRC_info.Metal_info.at(0).grid_unit_x; break;
    default:
            logger->error("PnRData-Error: incorrect routing direction");
  }
  switch (DRC_info.Metal_info.at(1).direct) {
    case 1: // H -> Y axis
            Yunit=DRC_info.Metal_info.at(1).grid_unit_y; break;
    case 0: // V -> X axis
            Xunit=DRC_info.Metal_info.at(1).grid_unit_x; break;
    default:
            logger->error("PnRData-Error: incorrect routing direction");
  }
  logger->debug("Xunit {0} ; Yunit {1}",Xunit,Yunit);
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
      logger->error("PnRData-Error: sel == -1");
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
        if(!(it2==(it->second).at(sel).macroPins.end()-1 && it3==it2->pinContacts.end()-1)) {
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
    if(sel<0 || sel>=it->instNum) {logger->error("PnRDB-Error: unselected block");}
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
      logger->error("PnRDB-Error: unsupported orientation!");
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
      if(it!=node.Nets.end()-1 || it2!=it->segments.end()-1) {OF2<<",";}
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
	    assert ( 0 <= iter2 && iter2 < node.Blocks.size());

            int iter = node.PowerNets[i].dummy_connected[j].iter;

            for(unsigned int k=0;k<node.Blocks[iter2].instance.size();k++){
                 PnRDB::pin temp_pin;
		 assert( 0 <= iter && iter < node.Blocks[iter2].instance[k].dummy_power_pin.size());
                 temp_pin = node.Blocks[iter2].instance[k].dummy_power_pin[iter];
                 temp_pin.netIter = -2;
                 node.PowerNets[i].dummy_connected[j].iter = int(node.Blocks[iter2].instance[k].blockPins.size());
                 node.Blocks[iter2].instance[k].blockPins.push_back(temp_pin);
               }
           
          }     
     }

   
}

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
             //std::cout<<"dummy power pin flag1"<<std::endl;
             if(iter<int(node.Blocks[iter2].instance[node.Blocks[iter2].selectedInstance].blockPins.size()))
             temp_pin = node.Blocks[iter2].instance[node.Blocks[iter2].selectedInstance].blockPins[iter];
             //std::cout<<"dummy power pin flag2"<<std::endl;
             node.PowerNets[i].Pins.push_back(temp_pin);
           }
     
     }

//extract power pin inside guard ring
  PnRDB::pin temp_pin;
  for(unsigned int i=0;i<node.GuardRings.size();i++){
     for(unsigned int j=0;j<node.GuardRings[i].blockPins.size();j++){
        temp_pin.name = node.GuardRings[i].blockPins[j].name;
        for(unsigned int k=0;k<node.GuardRings[i].blockPins[j].pinContacts.size();k++){
            temp_pin.pinContacts.push_back(node.GuardRings[i].blockPins[j].pinContacts[k]);
            break;
        }
        break;
     }
     break;
  }
  if(int(temp_pin.pinContacts.size())>0){
    for(unsigned int i=0;i<node.PowerNets.size();i++){
       if(node.PowerNets[i].power==0){
         node.PowerNets[i].Pins.push_back(temp_pin);
         break;
       }
    }
  }


//remove power pins in blocks

  for(unsigned int i=0;i<node.Blocks.size();i++){
     
     for(unsigned int k=0;k<node.Blocks[i].instance.size();k++){
       std::vector<PnRDB::pin> temp_pins;
       for(unsigned int j=0;j<node.Blocks[i].instance[k].blockPins.size();j++){

           PnRDB::pin each_pin =  node.Blocks[i].instance[k].blockPins[j];

           for(unsigned int h=0;h<each_pin.pinContacts.size();h++){
              node.Blocks[i].instance[k].interMetals.push_back(each_pin.pinContacts[h]);
           }
            
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


}

void PnRdatabase::Write_Router_Report(PnRDB::hierNode &node, const string& opath){

  std::ofstream router_report;
  string report_path = opath+"Router_Report.txt";
  router_report.open(report_path);


  for(unsigned int i = 0;i < node.router_report.size();i++){

      router_report<<"Node "<<node.router_report[i].node_name<<std::endl;

      for(unsigned int j=0;j<node.router_report[i].routed_net.size();j++){
       
        router_report<<"  Net "<<node.router_report[i].routed_net[j].net_name<<std::endl;

        for(unsigned int k=0;k<node.router_report[i].routed_net[j].pin_name.size();k++){
           
           router_report<<"    Pin "<<node.router_report[i].routed_net[j].pin_name[k]<<" Find a path "<<node.router_report[i].routed_net[j].pin_access[k]<<std::endl;              

        }

      }
      
    }

  router_report.close();

}

void PnRdatabase::semantic0( const string& topcell)
{
  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.semantic0");
    //update hier tree here for the class Nodes.
    //initialize
    for(unsigned int i=0;i<hierTree.size();i++){
        for(unsigned int j=0;j<hierTree[i].Blocks.size();j++){
            hierTree[i].Blocks[j].child = -1;
	}
    }
		
    //update hier tree here for the class Nodes.
    for(unsigned int i=0;i<hierTree.size();i++){
        for(unsigned int j=0;j<hierTree.size();j++){
            for(unsigned int k=0;k<hierTree[j].Blocks.size();k++)
                if(hierTree[j].Blocks[k].instance.back().master.compare(hierTree[i].name)==0){
                   hierTree[j].Blocks[k].child = i;
                   int parent_found = 0;
                   for(unsigned int p=0;p<hierTree[i].parent.size();p++){
		     if(hierTree[i].parent[p] == (int)j){parent_found=1;} 
		   }
                   if(parent_found==0){hierTree[i].parent.push_back(j);}                   
                  }
            }
        if(hierTree[i].name.compare(topcell)==0){
           topidx =i;
           hierTree[i].isTop = 1;
          }
                //update terminal information
        for(unsigned int l=0;l<hierTree[i].Nets.size();l++){
            for(unsigned int m=0;m<hierTree[i].Terminals.size();m++){
                if(hierTree[i].Nets[l].name.compare(hierTree[i].Terminals[m].name)==0){
                   hierTree[i].Nets[l].degree++;
		   {
		       PnRDB::connectNode temp_connectNode;
		       temp_connectNode.type = PnRDB::Terminal;
		       temp_connectNode.iter = m;
		       temp_connectNode.iter2 = -1;
		       hierTree[i].Nets[l].connected.push_back(temp_connectNode);
		   }
                   hierTree[i].Nets[l].sink2Terminal = 1;
                   hierTree[i].Terminals[m].netIter = l;
                   }
                }
            }
      }
		
    for(unsigned int i=0;i<hierTree.size();i++){
        for(unsigned int j=0;j<hierTree[i].Blocks.size();j++){
            if(hierTree[i].Blocks[j].child==-1){
               hierTree[i].Blocks[j].instance.back().isLeaf=1;
               }
        else{
             hierTree[i].Blocks[j].instance.back().isLeaf=0;
             }
           }
       }

  logger->debug("Middle");
    //mergeLEFandGDS
    for(unsigned int i=0;i<hierTree.size();i++){
    //cout<<"hierTree node "<<i<<endl;
    if(!MergeLEFMapData(hierTree[i])){logger->error("Failed to mergeLEFMapData of module {0}",hierTree[i].name);
      }else{
      logger->debug("Finished merge lef data");
      }
      }

}


void PnRdatabase::semantic1( const vector<tuple<string,string,string> >& global_signals)
{
  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.semantic1");


  // wbxu: following lines need modifications to reflect changes of block instance vector
  //update powernets information
  logger->debug("Middle");

  const std::string supply_node_name = "global_power";

  for(auto p = global_signals.begin(); p != global_signals.end(); ++p) {
    std::string supply_name = std::get<2>(*p);
    std::string supply_name_full = std::get<0>(*p) + "." + supply_name;

    int power;
    if        (std::get<1>(*p) == "supply0"){
      power = 0;
    } else if (std::get<1>(*p) == "supply1"){
      power = 1;
    } else {
      assert(0);
    }
    for(unsigned int j=0;j<hierTree.size();j++){
      std::vector<PnRDB::net> temp_net;
      bool powernet_found = 0;
      for(unsigned int k=0;k<hierTree[j].Nets.size();k++){
	if(hierTree[j].Nets[k].name == supply_name_full || hierTree[j].Nets[k].name == supply_name){
	  powernet_found = 1;
	  PnRDB::PowerNet temp_PowerNet;
	  temp_PowerNet.name = hierTree[j].Nets[k].name;
	  temp_PowerNet.power = power;
	  temp_PowerNet.connected = hierTree[j].Nets[k].connected;
	  hierTree[j].PowerNets.push_back(temp_PowerNet);
	}else{
	  temp_net.push_back(hierTree[j].Nets[k]);
	}
      }

      if(powernet_found==0){
	PnRDB::PowerNet temp_PowerNet;
	temp_PowerNet.name = supply_name;
	temp_PowerNet.power = power;
	hierTree[j].PowerNets.push_back(temp_PowerNet);
      }

      hierTree[j].Nets = temp_net;
    }
  }

}


void PnRdatabase::semantic2()
{
    auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.semantic2");

  //update pins & terminal connection iternet
  for(unsigned int i=0;i<hierTree.size();i++){
      for(unsigned int j=0;j<hierTree[i].Nets.size();j++){
           for(unsigned int k=0;k<hierTree[i].Nets[j].connected.size();k++){
                if(hierTree[i].Nets[j].connected[k].type == PnRDB::Block){
                        for(unsigned int m=0;m<hierTree[i].Blocks[hierTree[i].Nets[j].connected[k].iter2].instance.size();++m) {
                            hierTree[i].Blocks[hierTree[i].Nets[j].connected[k].iter2].instance.at(m).blockPins[hierTree[i].Nets[j].connected[k].iter].netIter = j;
                        } // [RA] need confirmation -wbxu
                  }else{
hierTree[i].Terminals[hierTree[i].Nets[j].connected[k].iter].netIter = j;
                  }
              }
         }
       
      for(unsigned int j=0;j<hierTree[i].PowerNets.size();j++){

           for(unsigned int k=0;k<hierTree[i].PowerNets[j].connected.size();k++){
                if(hierTree[i].PowerNets[j].connected[k].type == PnRDB::Block){
                    for(unsigned int m=0;m<hierTree[i].Blocks[hierTree[i].PowerNets[j].connected[k].iter2].instance.size();++m) {
                    hierTree[i].Blocks[hierTree[i].PowerNets[j].connected[k].iter2].instance.at(m).blockPins[hierTree[i].PowerNets[j].connected[k].iter].netIter = -1; 
                    }  // [RA] need confirmation - wbxu
                    hierTree[i].PowerNets[j].Pins.push_back(hierTree[i].Blocks[hierTree[i].PowerNets[j].connected[k].iter2].instance.back().blockPins[hierTree[i].PowerNets[j].connected[k].iter]); // [AR] need modification -wbxu
                  }else{
                    hierTree[i].Terminals[hierTree[i].PowerNets[j].connected[k].iter].netIter = -1;
                    PnRDB::pin temp_pin;
                    temp_pin.name = hierTree[i].Terminals[hierTree[i].PowerNets[j].connected[k].iter].name;
                    temp_pin.netIter = -1;
                    temp_pin.pinContacts = hierTree[i].Terminals[hierTree[i].PowerNets[j].connected[k].iter].termContacts;
                    hierTree[i].PowerNets[j].Pins.push_back(temp_pin);
                  }
              }

      }

  //adjust symmetry net iter

  for(unsigned int i=0;i<hierTree.size();i++){
     for(unsigned int j=0;j<hierTree[i].SNets.size();j++){
        int iter1=-1;
        int iter2=-1;
        for(unsigned int k=0;k<hierTree[i].Nets.size();k++){
           if(hierTree[i].Nets[k].name==hierTree[i].SNets[j].net1.name){
               iter1 = k;
               break;
             }
        }
        for(unsigned int k=0;k<hierTree[i].Nets.size();k++){
           if(hierTree[i].Nets[k].name==hierTree[i].SNets[j].net2.name){
               iter2 = k;
               break;
             }
        }
        hierTree[i].Nets[iter1].symCounterpart=iter2;
        hierTree[i].Nets[iter2].symCounterpart=iter1; 
     }
  }

//Add LinearConst here

      for(unsigned int j=0;j<hierTree[i].L_Constraints.size();j++){

        PnRDB::LinearConst temp_LinearConst = hierTree[i].L_Constraints[j];

        for(unsigned int k=0;k<hierTree[i].Nets.size();k++){
           if(hierTree[i].Nets[k].name == temp_LinearConst.net_name){
             hierTree[i].Nets[k].upperBound = temp_LinearConst.upperBound;
             for(unsigned int h=0;h<hierTree[i].Nets[k].connected.size();h++){
                logger->debug("Connected {0} {1} {2}",hierTree[i].Nets[k].connected[h].type,hierTree[i].Nets[k].connected[h].iter,hierTree[i].Nets[k].connected[h].iter2);
                for(unsigned int l=0;l<temp_LinearConst.pins.size();l++){
                  logger->debug("LinearConst cont {0} {1} {2}",temp_LinearConst.pins[l].first,temp_LinearConst.pins[l].second,temp_LinearConst.alpha[l]);
                  if(hierTree[i].Nets[k].connected[h].type == PnRDB::Block && hierTree[i].Nets[k].connected[h].iter2 == temp_LinearConst.pins[l].first && hierTree[i].Nets[k].connected[h].iter == temp_LinearConst.pins[l].second){
                    logger->debug("LinearConst alpha {0}",temp_LinearConst.alpha[l]);
                    hierTree[i].Nets[k].connected[h].alpha = temp_LinearConst.alpha[l];
                  }else if(hierTree[i].Nets[k].connected[h].type == PnRDB::Terminal && temp_LinearConst.pins[l].first==-1 && hierTree[i].Nets[k].connected[h].iter == temp_LinearConst.pins[l].second){
                    hierTree[i].Nets[k].connected[h].alpha = temp_LinearConst.alpha[l];
                    logger->debug("LinearConst alpha {0}",temp_LinearConst.alpha[l]);
                  }
                 }
             }
           }
        }
      }

      for(unsigned int j=0;j<hierTree[i].L_Constraints.size();j++){

          for(unsigned int k=0;k<hierTree[i].L_Constraints[j].alpha.size();k++){
              logger->debug("LinearConst info {0} {1} ",hierTree[i].L_Constraints[j].net_name,hierTree[i].L_Constraints[j].alpha[k]);
           }

      }

      for(unsigned int j=0;j<hierTree[i].Nets.size();j++){
         for(unsigned int k =0;k<hierTree[i].Nets[j].connected.size();k++){
            logger->debug("Assign Linear {0} {1} ",hierTree[i].Nets[j].upperBound,hierTree[i].Nets[j].connected[k].alpha);
         }
      }

      

  }
}


static string stem(const string& s) {

  unsigned int start = 0;
  unsigned int slash = s.find_last_of( '/');
  if ( slash != string::npos) {
    start = slash + 1;
  }

  unsigned int end = s.size();
  unsigned int dot = s.find_last_of( '.');
  if ( dot != string::npos) {
    end = dot;
  }

  // xx/y.d
  //   ^ ^
  // 012345

  return s.substr( start, end-start);
}

bool PnRdatabase::MergeLEFMapData(PnRDB::hierNode& node){

  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.MergeLEFMapData");

  bool missing_lef_file = 0;

  logger->info("merge LEF/map data on node {0}", node.name);  
  for (unsigned int i = 0; i < node.Blocks.size(); i++) {
    const string abstract_template_name = node.Blocks[i].instance.front().master;

    if (gdsData2.find(abstract_template_name) == gdsData2.end()) {
      if (abstract_template_name.find("Cap") != std::string::npos || abstract_template_name.find("cap") != std::string::npos || !node.Blocks[i].instance.back().isLeaf) continue;
      logger->error("The key does not exist in map: {0}", abstract_template_name);
    }

    unsigned int variants_count = gdsData2[abstract_template_name].size();
    node.Blocks[i].instance.resize(variants_count);
    for (unsigned int j = 1; j < variants_count; j++) node.Blocks[i].instance[j] = node.Blocks[i].instance[0];
    node.Blocks[i].instNum = variants_count;
    for (unsigned int j = 0; j < variants_count; j++) {
      auto& b = node.Blocks[i].instance[j];
      b.gdsFile = gdsData2[abstract_template_name][j];
      string a_concrete_template_name = stem(b.gdsFile);
      if (lefData.find(a_concrete_template_name) == lefData.end()) {
        logger->error("No LEF file for a_concrete_template_name {0}", a_concrete_template_name);
        missing_lef_file = 1;
        continue;
      }
      auto& lef = lefData.at(a_concrete_template_name).front();
      b.interMetals = lef.interMetals;
      b.interVias = lef.interVias;
      // node.Blocks[i].instNum++;
      b.width = lef.width;
      b.height = lef.height;
      b.lefmaster = lef.name;
      b.originBox.LL.x = 0;
      b.originBox.LL.y = 0;
      b.originBox.UR.x = lef.width;
      b.originBox.UR.y = lef.height;
      b.originCenter.x = lef.width / 2;
      b.originCenter.y = lef.height / 2;

      for (unsigned int k = 0; k < b.blockPins.size(); k++) {
        bool found = 0;
        for (unsigned int m = 0; m < lef.macroPins.size(); m++) {
          if (lef.macroPins[m].name.compare(b.blockPins[k].name) == 0) {
            b.blockPins[k].type = lef.macroPins[m].type;
            b.blockPins[k].pinContacts = lef.macroPins[m].pinContacts;
            b.blockPins[k].pinVias = lef.macroPins[m].pinVias;
            b.blockPins[k].use = lef.macroPins[m].use;
            found = 1;
            break;
          }
        }
        if (found == 0) logger->error("Block {0} pin {1} not found in lef file", b.name, b.blockPins[k].name);
      }
    }
    assert(!missing_lef_file);
  }

  return 1;
}
