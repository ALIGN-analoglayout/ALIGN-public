#include <gtest/gtest.h>
#include "PnRdatabase.h"

using namespace nlohmann;

namespace PnRDB {
  
  void to_json(json& j, const point& v) {
    j["x"] = v.x;
    j["y"] = v.y;
  }

  void from_json(const json& j, point& v) {
    j["x"].get_to(v.x);
    j["y"].get_to(v.y);
  }

  void to_json(json& j, const bbox& v) {
    j["polygon"] = json(v.polygon);
    j["LL"] = json(v.LL);
    j["LR"] = json(v.LR);
    j["UL"] = json(v.UL);
    j["UR"] = json(v.UR);
  }

  void from_json(const json& j, bbox& v) {
    j["polygon"].get_to( v.polygon);
    j["LL"].get_to( v.LL);
    j["LR"].get_to( v.LR);
    j["UL"].get_to( v.UL);
    j["UR"].get_to( v.UR);
  }

  void to_json(json& j, const contact& v) {
    j["metal"] = v.metal;
    j["originBox"] = v.originBox;
    j["placedBox"] = v.placedBox;
    j["originCenter"] = v.originCenter;
    j["placedCenter"] = v.placedCenter;
  }

  void from_json(const json& j, contact& v) {
    j["metal"].get_to( v.metal);
    j["originBox"].get_to( v.originBox);
    j["placedBox"].get_to( v.placedBox);
    j["originCenter"].get_to( v.originCenter);
    j["placedCenter"].get_to( v.placedCenter);
  }

  void to_json(json& j, const connectNode& v) {
    j["type"] = json(v.type);
    j["iter"] = v.iter;
    j["iter2"] = v.iter2;
  }

  void from_json(const json& j, connectNode& v) {
    j["type"].get_to(v.type);
    j["iter"].get_to(v.iter);
    j["iter2"].get_to(v.iter2);
  }

  void to_json(json& j, const globalContact& v) {
    j["contact"] = json(v.conTact);
    j["metalIdx"] = json(v.metalIdx);
  }

  void from_json(const json& j, globalContact& v) {
    j["contact"].get_to( v.conTact);
    j["metalIdx"].get_to( v.metalIdx);
  }

  void to_json(json& j, const Metal& v) {
    j["MetalIdx"] = v.MetalIdx;
    j["LinePoint"] = json(v.LinePoint);
    j["width"] = v.width;
    j["MetalRect"] = v.MetalRect;
  }

  void from_json(const json& j, Metal& v) {
    j["MetalIdx"].get_to( v.MetalIdx);
    j["LinePoint"].get_to( v.LinePoint);
    j["width"].get_to( v.width);
    j["MetalRect"].get_to( v.MetalRect);
  }

  void to_json(json& j, const Via& v) {
    j["model_index"] = v.model_index;
    j["originpos"] = v.originpos;
    j["placedpos"] = v.placedpos;
    j["UpperMetalRect"] = v.UpperMetalRect;
    j["LowerMetalRect"] = v.LowerMetalRect;
    j["ViaRect"] = v.ViaRect;
  }

  void from_json(const json& j, Via& v) {
    j["model_index"].get_to( v.model_index);
    j["originpos"].get_to( v.originpos);
    j["placedpos"].get_to( v.placedpos);
    j["UpperMetalRect"].get_to( v.UpperMetalRect);
    j["LowerMetalRect"].get_to( v.LowerMetalRect);
    j["ViaRect"].get_to( v.ViaRect);
  }

  void to_json(json& j, const Smark& v) {
    if ( v == V) {
      j = "V";
    } else if ( v == H) {
      j = "H";
    } /* else null (default) */
  }

  void from_json(const json& j, Smark& v) {
    if ( j == "V") {
      v = V;
    } else if ( j == "H") {
      v = H;
    }       // TODO: what if not match?
  }

  void to_json(json& j, const NType& v) {
    if ( v == Block) {
      j = "Block";
    } else if ( v == Terminal) {
      j = "Terminal";
    } // TODO: what if not match?
  }

  void from_json(const json& j, NType& v) {
    if ( j == "Block") {
      v = Block;
    } else if ( j == "Terminal") {
      v = Terminal;
    } // TODO: what if not match?
  }

  void to_json(json& j, const Omark& v) {
    if        ( v == N) {
      j = "N";
    } else if ( v == S) {
      j = "S";
    } else if ( v == W) {
      j = "W";
    } else if ( v == E) {
      j = "E";
    } else if ( v == FN) {
      j = "FN";
    } else if ( v == FS) {
      j = "FS";
    } else if ( v == FW) {
      j = "FW";
    } else if ( v == FE) {
      j = "FE";
    } /* else null (default) */
  }

  void from_json(const json& j, Omark& v) {
    if ( j == "N") {
      v = N;
    } else if ( j == "S") {
      v = S;
    } else if ( j == "W") {
      v = W;
    } else if ( j == "E") {
      v = E;
    } else if ( j == "FN") {
      v = FN;
    } else if ( j == "FS") {
      v = FS;
    } else if ( j == "FW") {
      v = FW;
    } else if ( j == "FE") {
      v = FE;
    } // TODO: what if not match?
  }

  void to_json(json& j, const Bmark& v) {
    if        ( v == TL) {
      j = "TL";
    } else if ( v == TC) {
      j = "TC";
    } else if ( v == TR) {
      j = "TR";
    } else if ( v == RT) {
      j = "RT";
    } else if ( v == RC) {
      j = "RC";
    } else if ( v == RB) {
      j = "RB";
    } else if ( v == BR) {
      j = "BR";
    } else if ( v == BC) {
      j = "BC";
    } else if ( v == BL) {
      j = "BL";
    } else if ( v == LB) {
      j = "LB";
    } else if ( v == LC) {
      j = "LC";
    } else if ( v == LT) {
      j = "LT";
    } /* else null (default) */
  }

  void from_json(const json& j, Bmark& v) {
    if        ( j == "TL") {
      v = TL;
    } else if ( j == "TC") {
      v = TC;
    } else if ( j == "TR") {
      v = TR;
    } else if ( j == "RT") {
      v = RT;
    } else if ( j == "RC") {
      v = RC;
    } else if ( j == "RB") {
      v = RB;
    } else if ( j == "BR") {
      v = BR;
    } else if ( j == "BC") {
      v = BC;
    } else if ( j == "BL") {
      v = BL;
    } else if ( j == "LB") {
      v = LB;
    } else if ( j == "LC") {
      v = LC;
    } else if ( j == "LT") {
      v = LT;
    } // TODO: what if not match?
  }

  void to_json(json& j, const net& v) {
    j["name"] = v.name;
    j["shielding"] = v.shielding;
    j["sink2Terminal"] = v.sink2Terminal;
    j["degree"] = v.degree;
    j["symCounterpart"] = v.symCounterpart;
    j["iter2SNetLsit"] = v.iter2SNetLsit;
    j["connected"] = json(v.connected);
    j["priority"] = v.priority;
    j["segments"] = json(v.segments);
    j["interVias"] = json(v.interVias);
    j["path_metal"] = json(v.path_metal);
    j["path_via"] = json(v.path_via);
    j["connectedContact"] = json(v.connectedContact);
    j["axis_dir"] = json(v.axis_dir);
    j["axis_coor"] = json(v.axis_coor);
  }

  void from_json(const json& j, net& v) {
    j["name"].get_to( v.name);
    j["shielding"].get_to( v.shielding);
    j["sink2Terminal"].get_to( v.sink2Terminal);
    j["degree"].get_to( v.degree);
    j["symCounterpart"].get_to( v.symCounterpart);
    j["iter2SNetLsit"].get_to( v.iter2SNetLsit);
    j["connected"].get_to( v.connected);
    j["priority"].get_to( v.priority);
    j["segments"].get_to( v.segments);
    j["interVias"].get_to( v.interVias);
    j["path_metal"].get_to( v.path_metal);
    j["path_via"].get_to( v.path_via);
    j["connectedContact"].get_to( v.connectedContact);
    j["axis_dir"].get_to( v.axis_dir);
    j["axis_coor"].get_to( v.axis_coor);
  }

  void to_json(json& j, const pin& v) {
    j["name"] = v.name;
    j["type"] = v.type;
    j["use"] = v.use;
    j["netIter"] = v.netIter;
    j["pinContacts"] = v.pinContacts;
    j["pinVias"] = v.pinVias;
  }

  void from_json(const json& j, pin& v) {
    j["name"].get_to( v.name);
    j["type"].get_to( v.type);
    j["use"].get_to( v.use);
    j["netIter"].get_to( v.netIter);
    j["pinContacts"].get_to( v.pinContacts);
    j["pinVias"].get_to( v.pinVias);
  }

  void to_json(json& j, const block& v) {
    j["name"] = v.name;
    j["master"] = v.master;
    j["lefmaster"] = v.lefmaster;
    j["type"] = v.type;
    j["width"] = v.width;
    j["height"] = v.height;
    j["isLeaf"] = v.isLeaf;
    j["originBox"] = json(v.originBox);
    j["originCenter"] = json(v.originCenter);
    j["gdsFile"] = v.gdsFile;
    j["orient"] = json(v.orient);
    j["placedBox"] = json(v.placedBox);
    j["placedCenter"] = json(v.placedCenter);
    j["blockPins"] = json(v.blockPins);
    j["interMetals"] = json(v.interMetals);
    j["interVias"] = json(v.interVias);
    j["dummy_power_pin"] = json(v.dummy_power_pin);
  }

  void from_json(const json& j, block& v) {
    j["name"].get_to( v.name);
    j["master"].get_to( v.master);
    j["lefmaster"].get_to( v.lefmaster);
    j["type"].get_to( v.type);
    j["width"].get_to( v.width);
    j["height"].get_to( v.height);
    j["isLeaf"].get_to( v.isLeaf);
    j["originBox"].get_to( v.originBox);
    j["originCenter"].get_to( v.originCenter);
    j["gdsFile"].get_to( v.gdsFile);
    j["orient"].get_to( v.orient);
    j["placedBox"].get_to( v.placedBox);
    j["placedCenter"].get_to( v.placedCenter);
    j["blockPins"].get_to( v.blockPins);
    j["interMetals"].get_to( v.interMetals);
    j["interVias"].get_to( v.interVias);
    j["dummy_power_pin"].get_to( v.dummy_power_pin);
  }

  void to_json(json& j, const terminal& v) {
    j["name"] = v.name;
    j["type"] = v.type;
    j["netIter"] = v.netIter;
    j["termContacts"] = v.termContacts;
  }

  void from_json(const json& j, terminal& v) {
    j["name"].get_to( v.name);
    j["type"].get_to( v.type);
    j["netIter"].get_to( v.netIter);
    j["termContacts"].get_to( v.termContacts);
  }

  void to_json(json& j, const blockComplex& v) {
    j["instance"] = json(v.instance);
    j["selectedInstance"] = v.selectedInstance;
    j["child"] = v.child;
    j["instNum"] = v.instNum;
  }

  void from_json(const json& j, blockComplex& v) {
    j["instance"].get_to( v.instance);
    j["selectedInstance"].get_to( v.selectedInstance);
    j["child"].get_to( v.child);
    j["instNum"].get_to( v.instNum);
  }

  void to_json(json& j, const PowerGrid& v) {
    j["metals"] = json(v.metals);
    j["vias"] = json(v.vias);
    j["power"] = v.power;
  }

  void from_json(const json& j, PowerGrid& v) {
    j["metals"].get_to( v.metals);
    j["vias"].get_to( v.vias);
    j["power"].get_to( v.power);
  }

  void to_json(json& j, const PowerNet& v) {
    j["name"] = v.name;
    j["power"] = v.power;
    j["Pins"] = json(v.Pins);
    j["connected"] = json(v.connected);
    j["dummy_connected"] = json(v.dummy_connected);
    j["path_metal"] = json(v.path_metal);
    j["path_via"] = json(v.path_via);
  }

  void from_json(const json& j, PowerNet& v) {
    j["name"].get_to( v.name);
    j["power"].get_to( v.power);
    j["Pins"].get_to( v.Pins);
    j["connected"].get_to( v.connected);
    j["dummy_connected"].get_to( v.dummy_connected);
    j["path_metal"].get_to( v.path_metal);
    j["path_via"].get_to( v.path_via);
  }

  void to_json(json& j, const layoutAS& v) {
    j["width"] = v.width;
    j["height"] = v.height;
    j["gdsFile"] = v.gdsFile;
    j["Blocks"] = json(v.Blocks);
    j["Nets"] = json(v.Nets);
    j["Terminals"] = json(v.Terminals);
  }

  void from_json(const json& j, layoutAS& v) {
    j["width"].get_to( v.width);
    j["height"].get_to( v.height);
    j["gdsFile"].get_to( v.gdsFile);
    j["Blocks"].get_to( v.Blocks);
    j["Nets"].get_to( v.Nets);
    j["Terminals"].get_to( v.Terminals);
  }

  void to_json(json& j, const SymmNet& v) {
    j["net1"] = json(v.net1);
    j["net2"] = json(v.net2);
    j["iter1"] = v.iter1;
    j["iter2"] = v.iter2;
  }

  void from_json(const json& j, SymmNet& v) {
    j["net1"].get_to( v.net1);
    j["net2"].get_to( v.net2);
    j["iter1"].get_to( v.iter1);
    j["iter2"].get_to( v.iter2);
  }

  void to_json(json& j, const SymmPairBlock& v) {
    j["sympair"] = json(v.sympair);
    j["selfsym"] = json(v.selfsym);
  }

  void from_json(const json& j, SymmPairBlock& v) {
    j["sympair"].get_to( v.sympair);
    j["selfsym"].get_to( v.selfsym);
  }

  void to_json(json& j, const Preplace& v) {
    j["blockid1"] = v.blockid1;
    j["blockid2"] = v.blockid2;
    j["conner"] = v.conner;
    j["distance"] = v.distance;
    j["horizon"] = v.horizon;
  }

  void from_json(const json& j, Preplace& v) {
    j["blockid1"].get_to( v.blockid1);
    j["blockid2"].get_to( v.blockid2);
    j["conner"].get_to( v.conner);
    j["distance"].get_to( v.distance);
    j["horizon"].get_to( v.horizon);
  }

  void to_json(json& j, const Alignment& v) {
    j["blockid1"] = v.blockid1;
    j["blockid2"] = v.blockid2;
    j["distance"] = v.distance;
    j["horizon"] = v.horizon;
  }

  void from_json(const json& j, Alignment& v) {
    j["blockid1"].get_to( v.blockid1);
    j["blockid2"].get_to( v.blockid2);
    j["distance"].get_to( v.distance);
    j["horizon"].get_to( v.horizon);
  }

  void to_json(json& j, const Abument& v) {
    j["blockid1"] = v.blockid1;
    j["blockid2"] = v.blockid2;
    j["distance"] = v.distance;
    j["horizon"] = v.horizon;
  }

  void from_json(const json& j, Abument& v) {
    j["blockid1"].get_to( v.blockid1);
    j["blockid2"].get_to( v.blockid2);
    j["distance"].get_to( v.distance);
    j["horizon"].get_to( v.horizon);
  }

  void to_json(json& j, const MatchBlock& v) {
    j["blockid1"] = v.blockid1;
    j["blockid2"] = v.blockid2;
  }

  void from_json(const json& j, MatchBlock& v) {
    j["blockid1"].get_to( v.blockid1);
    j["blockid2"].get_to( v.blockid2);
  }

  void to_json(json& j, const AlignBlock& v) {
    j["blocks"] = json(v.blocks);
    j["horizon"] = v.horizon;
  }

  void from_json(const json& j, AlignBlock& v) {
    j["blocks"].get_to( v.blocks);
    j["horizon"].get_to( v.horizon);
  }

  void to_json(json& j, const PortPos& v) {
    j["tid"] = v.tid;
    j["pos"] = json(v.pos);
  }

  void from_json(const json& j, PortPos& v) {
    j["tid"].get_to( v.tid);
    j["pos"].get_to( v.pos);
  }

  void to_json(json& j, const CCCap& v) {
    j["size"] = json(v.size);
    j["CCCap_name"] = v.CCCap_name;
    j["Unit_capacitor"] = v.Unit_capacitor;
    j["cap_ratio"] = v.cap_ratio;
    j["cap_r"] = v.cap_r;
    j["cap_s"] = v.cap_s;
  }

  void from_json(const json& j, CCCap& v) {
    j["size"].get_to( v.size);
    j["CCCap_name"].get_to( v.CCCap_name);
    j["Unit_capacitor"].get_to( v.Unit_capacitor);
    j["cap_ratio"].get_to( v.cap_ratio);
    j["cap_r"].get_to( v.cap_r);
    j["cap_s"] .get_to( v.cap_s);
  }

  void to_json(json& j, const hierNode& v) {
    j["isCompleted"] = v.isCompleted;
    j["isTop"] = v.isTop;
    j["width"] = v.width;
    j["height"] = v.height;
    j["name"] = v.name;
    j["gdsFile"] = v.gdsFile;
    j["parent"] = json(v.parent);
    j["Blocks"] = json(v.Blocks);
    j["Nets"] = json(v.Nets);
    j["Terminals"] = json(v.Terminals);
    j["Vdd"] = json(v.Vdd);
    j["Gnd"] = json(v.Gnd);
    j["PowerNets"] = json(v.PowerNets);
    j["blockPins"] = json(v.blockPins);
    j["interMetals"] = json(v.interMetals);
    j["interVias"] = json(v.interVias);

    j["PnRAS"] = json(v.PnRAS);
    j["SNets"] = json(v.SNets);
    j["SPBlocks"] = json(v.SPBlocks);

    j["Preplace_blocks"] = json(v.Preplace_blocks);
    j["Alignment_blocks"] = json(v.Alignment_blocks);
    j["Align_blocks"] = json(v.Align_blocks);
    j["Abument_blocks"] = json(v.Abument_blocks);
    j["Match_blocks"] = json(v.Match_blocks);
    j["CC_Caps"] = json(v.CC_Caps);
    j["Port_Location"] = json(v.Port_Location);
    j["bias_Hgraph"] = json(v.bias_Hgraph);
    j["bias_Vgraph"] = json(v.bias_Vgraph);
  }

  void from_json(const json& j, hierNode& v) {
    j["isCompleted"].get_to( v.isCompleted);
    j["isTop"].get_to( v.isTop);
    j["width"].get_to( v.width);
    j["height"].get_to( v.height);
    j["name"].get_to( v.name);
    j["gdsFile"].get_to( v.gdsFile);
    j["parent"].get_to( v.parent);
    j["Blocks"].get_to( v.Blocks);
    j["Nets"].get_to( v.Nets);
    j["Terminals"].get_to( v.Terminals);
    j["Vdd"].get_to( v.Vdd);
    j["Gnd"].get_to( v.Gnd);
    j["PowerNets"].get_to( v.PowerNets);
    j["blockPins"].get_to( v.blockPins);
    j["interMetals"].get_to( v.interMetals);
    j["interVias"].get_to( v.interVias);

    j["PnRAS"].get_to( v.PnRAS);
    j["SNets"].get_to( v.SNets);
    j["SPBlocks"].get_to( v.SPBlocks);

    j["Preplace_blocks"].get_to( v.Preplace_blocks);
    j["Alignment_blocks"].get_to( v.Alignment_blocks);
    j["Align_blocks"].get_to( v.Align_blocks);
    j["Abument_blocks"].get_to( v.Abument_blocks);
    j["Match_blocks"].get_to( v.Match_blocks);
    j["CC_Caps"].get_to( v.CC_Caps);
    j["Port_Location"].get_to( v.Port_Location);
    j["bias_Hgraph"].get_to( v.bias_Hgraph);
    j["bias_Vgraph"].get_to( v.bias_Vgraph);
  }

};

TEST( hierNodeTest, TestA)
{
  PnRDB::hierNode hN;
  hN.name = "hierNodeName";

  json json_hN(hN);

  EXPECT_EQ( json_hN["name"], "hierNodeName");

  {
    std::ofstream jsonStream( "__json");
    if(jsonStream.fail()) {
      cout<< "Cannot open file "<< "__json" <<" for writing"<<endl;
      return;
    }
    jsonStream << std::setw(4) << json_hN;
    jsonStream.close();
  }

}

TEST( hierNodeTest, TestInOut)
{
  std::ifstream ifs( "telescopic_ota-freeze.json");
  json j = json::parse( ifs);

  PnRDB::hierNode hN;

  j.get_to( hN);

  json json_hN(hN);

  EXPECT_EQ( j, json_hN);

}

void PnRdatabase::WriteDBJSON( const PnRDB::hierNode& hN, const string& filename)
{
  std::ofstream jsonStream( filename);
  if(jsonStream.fail()) {
    cout<< "Cannot open file " << filename << " for writing" << endl;
    return;
  }
  jsonStream << json(hN);
}

void PnRdatabase::ReadDBJSON( PnRDB::hierNode& hN, const string& filename)
{
  std::ifstream ifs( filename);
  if(ifs.fail()) {
    cout<< "Cannot open file " << filename << " for reading." << endl;
    return;
  }
  json::parse(ifs).get_to( hN);
}
