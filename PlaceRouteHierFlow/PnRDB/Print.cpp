#include <fstream>
#include <iomanip>
#include <iostream>

#include "PnRdatabase.h"
#include "spdlog/spdlog.h"

void PnRdatabase::PrintHierTree() {}

void PnRdatabase::PrintLEFData() {
  // cout<<"PnRDB-Info: PrintLEFData"<<endl;
  for (map<string, std::vector<PnRDB::lefMacro> >::iterator it = lefData.begin(); it != lefData.end(); ++it) {
    // cout<<"\nMacro: "<<it->first<<endl;
    for (int w = 0; w < (int)it->second.size(); ++w) {
      // std::cout<<"Choice "<<w<<std::endl;
      // cout<<"Content: name "<<(it->second).at(w).name<<"; width "<<(it->second).at(w).width<<"; height "<<(it->second).at(w).height<<endl;
      // cout<<"Macro pins"<<endl;
      for (vector<PnRDB::pin>::iterator it2 = it->second.at(w).macroPins.begin(); it2 != it->second.at(w).macroPins.end(); ++it2) {
        // cout<<"\tpin name: "<<it2->name<<"; type: "<<it2->type;
        for (vector<PnRDB::contact>::iterator it4 = it2->pinContacts.begin(); it4 != it2->pinContacts.end(); it4++) {
          // cout<<"\n\tmetal: "<<it4->metal<<"; orginBox: ";
          // cout<<" LL-{"<<it4->originBox.LL.x<<","<<it4->originBox.LL.y<<"}";
          // cout<<" UR-{"<<it4->originBox.UR.x<<","<<it4->originBox.UR.y<<"}";
          // cout<<" center-{"<<it4->originCenter.x<<","<<it4->originCenter.y<<"}";
        }
        // cout<<endl;
      }
      // cout<<"Internal metals"<<endl;
      for (vector<PnRDB::contact>::iterator it4 = it->second.at(w).interMetals.begin(); it4 != it->second.at(w).interMetals.end(); ++it4) {
        // cout<<"\tmetal: "<<it4->metal<<"; orginBox: ";
        // cout<<" LL-{"<<it4->originBox.LL.x<<","<<it4->originBox.LL.y<<"}";
        // cout<<" UR-{"<<it4->originBox.UR.x<<","<<it4->originBox.UR.y<<"}";
        // cout<<" center-{"<<it4->originCenter.x<<","<<it4->originCenter.y<<"}";
        // cout<<endl;
      }
    }
  }
}

void PnRdatabase::PrintDesignRuleData() {
  // cout<<"=== Design Rule Data ==="<<endl;
  for (map<string, int>::iterator it = drData.MinWidth.begin(); it != drData.MinWidth.end(); ++it) {
    // cout<<it->first<<" width "<<it->second<<endl;
  }
  for (map<string, int>::iterator it = drData.MaxSpace.begin(); it != drData.MaxSpace.end(); ++it) {
    // cout<<it->first<<" space "<<it->second<<endl;
  }
  for (map<string, int>::iterator it = drData.EnMax.begin(); it != drData.EnMax.end(); ++it) {
    // cout<<it->first<<" enclose "<<it->second<<endl;
  }
  for (map<string, int>::iterator it = drData.TrkSpacing.begin(); it != drData.TrkSpacing.end(); ++it) {
    // cout<<it->first<<" trackspace "<<it->second<<endl;
  }
  for (map<string, int>::iterator it = drData.grid_unit_x.begin(); it != drData.grid_unit_x.end(); ++it) {
    // cout<<it->first<<" grid x "<<it->second<<endl;
  }
  for (map<string, int>::iterator it = drData.grid_unit_y.begin(); it != drData.grid_unit_y.end(); ++it) {
    // cout<<it->first<<" grid y "<<it->second<<endl;
  }
}

void PnRdatabase::PrintHierNode(PnRDB::hierNode& node) {
  // std::cout<<"Hier Node Printing"<<std::endl;
  // std::cout<<"Name: "<<node.name<<" ; isTop: "<<node.isTop<<" ; isCompeted: "<<node.isCompleted<<" ; width: "<<node.width<<" ; height: "<<node.height<<" ;
  // gdsFile: "<<node.gdsFile<<" ; parent: ";
  for (vector<int>::iterator it = node.parent.begin(); it != node.parent.end(); ++it) {
    // std::cout<<*it;
  }
  // std::cout<<std::endl<<"Blocks"<<std::endl;
  for (vector<PnRDB::blockComplex>::iterator it = node.Blocks.begin(); it != node.Blocks.end(); ++it) {
    PrintBlock(*it);
  }
  // std::cout<<std::endl<<"Nets"<<std::endl;
  for (vector<PnRDB::net>::iterator it = node.Nets.begin(); it != node.Nets.end(); ++it) {
    PrintNet(*it);
  }
  // std::cout<<std::endl<<"Terminals"<<std::endl;
  for (vector<PnRDB::terminal>::iterator it = node.Terminals.begin(); it != node.Terminals.end(); ++it) {
    PrintTerminal(*it);
  }
  // std::cout<<std::endl<<"Node blockpins"<<std::endl;
  for (vector<PnRDB::pin>::iterator it = node.blockPins.begin(); it != node.blockPins.end(); ++it) {
    PrintBlockPin(*it);
  }
  // std::cout<<std::endl<<"Node internal metals"<<std::endl;
  for (vector<PnRDB::contact>::iterator it = node.interMetals.begin(); it != node.interMetals.end(); ++it) {
    PrintContact(*it);
  }
  // std::cout<<std::endl<<"Node internal vias"<<std::endl;
  for (vector<PnRDB::Via>::iterator it = node.interVias.begin(); it != node.interVias.end(); ++it) {
    PrintVia(*it);
  }
  // std::cout<<std::endl<<"Node symmetry nets"<<std::endl;
  for (std::vector<PnRDB::SymmNet>::iterator it = node.SNets.begin(); it != node.SNets.end(); ++it) {
    PrintSymmNet(*it);
  }
}

void PnRdatabase::PrintSymmNet(PnRDB::SymmNet& t) {
  // std::cout<<"@Symmetry net"<<std::endl;
  // std::cout<<" net1:"<<t.net1.name<<" ; iter: "<<t.iter1<<std::endl;
  for (std::vector<PnRDB::connectNode>::iterator it = t.net1.connected.begin(); it != t.net1.connected.end(); ++it) {
    // std::cout<<" {"<<it->type<<":"<<it->iter<<","<<it->iter2<<"}";
  }
  // std::cout<<endl;
  // std::cout<<" net2:"<<t.net2.name<<" ; iter: "<<t.iter2<<std::endl;
  for (std::vector<PnRDB::connectNode>::iterator it = t.net2.connected.begin(); it != t.net2.connected.end(); ++it) {
    // std::cout<<" {"<<it->type<<":"<<it->iter<<","<<it->iter2<<"}";
  }
  // std::cout<<endl;
}

void PnRdatabase::PrintTerminal(PnRDB::terminal& t) {
  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.PrintTerminal");

  logger->debug("@Terminal");
  logger->debug(" name: {0} ; type {1} ; netiter {2} ", t.name, t.type, t.netIter);
  for (vector<PnRDB::contact>::iterator it = t.termContacts.begin(); it != t.termContacts.end(); ++it) {
    PrintContact(*it);
  }
}

void PnRdatabase::PrintNet(PnRDB::net& n) {
  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.PrintNet");

  logger->debug("@Net");
  logger->debug(
      "name: {0} ; shielding: {1}; sin2Terminal: {2} ; degree: {3}; symCounterpart: {4}; iter2SNetLsit: {5}; priority: {6} ; symmetry axis direction: {7} ; "
      "symmetry axis coor: {8}",
      n.name, n.shielding, n.sink2Terminal, n.degree, n.symCounterpart, n.iter2SNetLsit, n.priority, n.axis_dir, n.axis_coor);
  // std::cout<<"connected ";
  for (vector<PnRDB::connectNode>::iterator it = n.connected.begin(); it != n.connected.end(); ++it) {
    // std::cout<<" {"<<it->type<<","<<it->iter<<","<<it->iter2<<"} ";
  }
  // std::cout<<std::endl;
  for (vector<PnRDB::Metal>::iterator it = n.path_metal.begin(); it != n.path_metal.end(); ++it) {
    PrintMetal(*it);
  }
  for (vector<PnRDB::Via>::iterator it = n.path_via.begin(); it != n.path_via.end(); ++it) {
    PrintVia(*it);
  }
}

void PnRdatabase::PrintBlock(PnRDB::blockComplex& bc) {
  PnRDB::blockComplex* it = &bc;
  // std::cout<<"@Block"<<std::endl;
  // std::cout<<"Child: "<<it->child<<" ; instNum: "<<it->instNum<<" ; selectedInstance: "<<it->selectedInstance<<std::endl;
  for (unsigned int w = 0; w < bc.instance.size(); ++w) {
    // std::cout<<"Choice "<<w<<" -> name: "<<it->instance.at(w).name<<" ; master: "<<it->instance.at(w).master<<" ; type: "<<it->instance.at(w).type<<" ;
    // width: "<<it->instance.at(w).width<<" ; height: "<<it->instance.at(w).height<<" ; isLeaf: "<<it->instance.at(w).isLeaf<<" ; gds:
    // "<<it->instance.at(w).gdsFile<<" ; orient: "<<it->instance.at(w).orient<<" ; originCenter:
    // {"<<it->instance.at(w).originCenter.x<<","<<it->instance.at(w).originCenter.y<<"}; placedCenter:
    // {"<<it->instance.at(w).placedCenter.x<<","<<it->instance.at(w).placedCenter.y<<"}"<<std::endl; std::cout<<"originBox:
    // LL"<<it->instance.at(w).originBox.LL.x<<","<<it->instance.at(w).originBox.LL.y<<"
    // UR"<<it->instance.at(w).originBox.UR.x<<","<<it->instance.at(w).originBox.UR.y<<std::endl; std::cout<<"placedBox:
    // LL"<<it->instance.at(w).placedBox.LL.x<<","<<it->instance.at(w).placedBox.LL.y<<"
    // UR"<<it->instance.at(w).placedBox.UR.x<<","<<it->instance.at(w).placedBox.UR.y<<std::endl; std::cout<<"Blockpins"<<std::endl;
    for (vector<PnRDB::pin>::iterator it2 = it->instance.at(w).blockPins.begin(); it2 != it->instance.at(w).blockPins.end(); it2++) {
      // std::cout<<"name: "<<it2->name<<" ; type: "<<it2->type<<" ; use: "<<it2->use<<" ; netIter: "<<it2->netIter<<std::endl;
      // std::cout<<"pinContact "<<std::endl;
      for (vector<PnRDB::contact>::iterator it3 = it2->pinContacts.begin(); it3 != it2->pinContacts.end(); ++it3) {
        PrintContact(*it3);
      }
      for (vector<PnRDB::Via>::iterator it3 = it2->pinVias.begin(); it3 != it2->pinVias.end(); ++it3) {
        PrintVia(*it3);
      }
    }
    // std::cout<<"Internal Metals"<<std::endl;
    for (vector<PnRDB::contact>::iterator it2 = it->instance.at(w).interMetals.begin(); it2 != it->instance.at(w).interMetals.end(); ++it2) {
      PrintContact(*it2);
    }
    // std::cout<<"Internal Vias"<<std::endl;
    for (vector<PnRDB::Via>::iterator it2 = it->instance.at(w).interVias.begin(); it2 != it->instance.at(w).interVias.end(); it2++) {
      PrintVia(*it2);
    }
  }
}

void PnRdatabase::PrintBlockPin(PnRDB::pin& p) {
  PnRDB::pin* it2 = &p;
  // std::cout<<"@Blockpin"<<std::endl;
  // std::cout<<"name: "<<it2->name<<" ; type: "<<it2->type<<" ; use: "<<it2->use<<" ; netIter: "<<it2->netIter<<std::endl;
  // std::cout<<"pinContact "<<std::endl;
  for (vector<PnRDB::contact>::iterator it3 = it2->pinContacts.begin(); it3 != it2->pinContacts.end(); ++it3) {
    PrintContact(*it3);
  }
  for (vector<PnRDB::Via>::iterator it3 = it2->pinVias.begin(); it3 != it2->pinVias.end(); ++it3) {
    PrintVia(*it3);
  }
}

void PnRdatabase::PrintMetal(PnRDB::Metal& m) {
  // std::cout<<"@Metal index: "<<m.MetalIdx<<" ; wdith:"<<m.width<<std::endl;
  for (vector<PnRDB::point>::iterator it = m.LinePoint.begin(); it != m.LinePoint.end(); ++it) {
    // std::cout<<" {"<<it->x<<","<<it->y<<"} ";
  }
  // std::cout<<std::endl;
  PrintContact(m.MetalRect);
}

void PnRdatabase::PrintVia(PnRDB::Via& v) {
  // std::cout<<"@Via ";
  // std::cout<<" model:"<<v.model_index<<" ; originpos: {"<<v.originpos.x<<","<<v.originpos.y<<"}; placedpos:
  // {"<<v.placedpos.x<<","<<v.placedpos.y<<"}"<<std::endl;
  PrintContact(v.UpperMetalRect);
  PrintContact(v.LowerMetalRect);
  PrintContact(v.ViaRect);
}

void PnRdatabase::PrintContact(PnRDB::contact& cont) {
  // std::cout<<"@Contact ";
  // PnRDB::contact *it3=&cont;
  // std::cout<<" metal: "<<it3->metal<<" ; originCenter: {"<<it3->originCenter.x<<","<<it3->originCenter.y<<"} ; placedCenter:
  // {"<<it3->placedCenter.x<<","<<it3->placedCenter.y<<"}"<<std::endl; std::cout<<"originBox: LL"<<it3->originBox.LL.x<<","<<it3->originBox.LL.y<<"
  // UR"<<it3->originBox.UR.x<<","<<it3->originBox.UR.y<<std::endl; std::cout<<"placedBox: LL"<<it3->placedBox.LL.x<<","<<it3->placedBox.LL.y<<"
  // UR"<<it3->placedBox.UR.x<<","<<it3->placedBox.UR.y<<std::endl;
}
// Local Variables:
// c-basic-offset: 4
// End:

std::map<string, PnRDB::lefMacro> PnRdatabase::checkoutSingleLEF() {
  std::map<string, PnRDB::lefMacro> mm;
  for (std::map<string, std::vector<PnRDB::lefMacro> >::iterator it = this->lefData.begin(); it != this->lefData.end(); ++it) {
    mm[it->first] = it->second.back();
  }
  return mm;
}
