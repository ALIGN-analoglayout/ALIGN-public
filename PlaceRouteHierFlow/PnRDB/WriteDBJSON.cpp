#include <gtest/gtest.h>
#include "PnRdatabase.h"

using namespace nlohmann;

namespace PnRDB {
  
  void to_json(json& j, const point& v) {
    j["x"] = v.x;
    j["y"] = v.y;
  }

  void to_json(json& j, const bbox& v) {
    j["polygon"] = json(v.polygon);
    j["LL"] = json(v.LL);
    j["LR"] = json(v.LR);
    j["UL"] = json(v.UL);
    j["UR"] = json(v.UR);
  }

  void to_json(json& j, const contact& v) {
    j["metal"] = v.metal;
    j["originBox"] = v.originBox;
    j["placedBox"] = v.placedBox;
    j["originCenter"] = v.originCenter;
    j["placedCenter"] = v.placedCenter;
  }

  void to_json(json& j, const connectNode& v) {
    j["type"] = json(v.type);
    j["iter"] = v.iter;
    j["iter2"] = v.iter2;
  }

  void to_json(json& j, const globalContact& v) {
    j["contact"] = json(v.conTact);
    j["metalIdx"] = json(v.metalIdx);
  }

  void to_json(json& j, const Metal& v) {
    j["MetalIdx"] = v.MetalIdx;
    j["LinePoint"] = json(v.LinePoint);
    j["width"] = v.width;
    j["MetalRect"] = v.MetalRect;
  }

  void to_json(json& j, const Via& v) {
    j["model_index"] = v.model_index;
    j["originpos"] = v.originpos;
    j["placedpos"] = v.placedpos;
    j["UpperMetalRect"] = v.UpperMetalRect;
    j["LowerMetalRect"] = v.LowerMetalRect;
    j["ViaRect"] = v.ViaRect;
  }


  void to_json(json& j, const Smark& v) {
    if ( v == V) {
      j = "V";
    } else if ( v == H) {
      j = "H";
    } /* else null (default) */
  }

  void to_json(json& j, const NType& v) {
    if ( v == Block) {
      j = "Block";
    } else if ( v == Terminal) {
      j = "Terminal";
    } /* else null (default) */
  }

  void to_json(json& j, const Omark& v) {
    if ( v == N) {
      j = "N";
    } else if ( v == S) {
      j = "S";
    } else if ( v == W) {
      j = "S";
    } else if ( v == E) {
      j = "S";
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

  void to_json(json& j, const Bmark& v) {
    if ( v == TL) {
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

  void to_json(json& j, const net& v) {
    j["name"] = v.name;
    j["shielding"] = v.shielding;
    j["sink2Terminal"] = v.sink2Terminal;
    j["degree"] = v.degree;
    j["symCounterpart"] = v.symCounterpart;
    j["iter2SNetLsit"] = v.iter2SNetLsit;
    j["connectNode>"] = json(v.connected);
    j["priority"] = v.priority;
    j["segments"] = json(v.segments);
    j["interVias"] = json(v.interVias);
    j["path_metal"] = json(v.path_metal);
    j["path_via"] = json(v.path_via);
    j["connectedContact"] = json(v.connectedContact);
    j["axis_dir"] = json(v.axis_dir);
    j["axis_coor"] = json(v.axis_coor);
  }

  void to_json(json& j, const pin& v) {
    j["name"] = v.name;
    j["type"] = v.type;
    j["use"] = v.use;
    j["netIter"] = v.netIter;
    j["pinContacts"] = v.pinContacts;
    j["pinVias"] = v.pinVias;
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

  void to_json(json& j, const terminal& v) {
    j["name"] = v.name;
    j["type"] = v.type;
    j["netIter"] = v.netIter;
    j["termContacts"] = v.termContacts;
  }

  void to_json(json& j, const blockComplex& v) {
    j["instance"] = json(v.instance);
    j["selectedInstance"] = v.selectedInstance;
    j["child"] = v.child;
    j["instNum"] = v.instNum;
  }

  void to_json(json& j, const PowerGrid& v) {
    j["metals"] = json(v.metals);
    j["vias"] = json(v.vias);
    j["power"] = v.power;
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

  void to_json(json& j, const layoutAS& v) {
    j["width"] = v.width;
    j["height"] = v.height;
    j["gdsFile"] = v.gdsFile;
    j["Blocks"] = json(v.Blocks);
    j["Nets"] = json(v.Nets);
    j["Terminals"] = json(v.Terminals);
  }

  void to_json(json& j, const SymmNet& v) {
    j["net1"] = json(v.net1);
    j["net2"] = json(v.net2);
    j["iter1"] = v.iter1;
    j["iter2"] = v.iter2;
  }

  void to_json(json& j, const SymmPairBlock& v) {
    j["sympair"] = json(v.sympair);
    j["selfsym"] = json(v.selfsym);
  }

  void to_json(json& j, const Preplace& v) {
    j["blockid1"] = v.blockid1;
    j["blockid2"] = v.blockid2;
    j["conner"] = v.conner;
    j["distance"] = v.distance;
    j["horizon"] = v.horizon;
  }

  void to_json(json& j, const Alignment& v) {
    j["blockid1"] = v.blockid1;
    j["blockid2"] = v.blockid2;
    j["distance"] = v.distance;
    j["horizon"] = v.horizon;
  }

  void to_json(json& j, const Abument& v) {
    j["blockid1"] = v.blockid1;
    j["blockid2"] = v.blockid2;
    j["distance"] = v.distance;
    j["horizon"] = v.horizon;
  }

  void to_json(json& j, const MatchBlock& v) {
    j["blockid1"] = v.blockid1;
    j["blockid2"] = v.blockid2;
  }

  void to_json(json& j, const AlignBlock& v) {
    j["blocks"] = json(v.blocks);
    j["horizon"] = v.horizon;
  }

  void to_json(json& j, const PortPos& v) {
    j["tid"] = v.tid;
    j["pos"] = json(v.pos);
  }

  void to_json(json& j, const CCCap& v) {
    j["size"] = json(v.size);
    j["CCCap_name"] = v.CCCap_name;
    j["Unit_capacitor"] = v.Unit_capacitor;
    j["cap_ratio"] = v.cap_ratio;
    j["cap_r"] = v.cap_r;
    j["cap_s"] = v.cap_s;
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

void PnRdatabase::WriteDBJSON( const PnRDB::hierNode& hN, const string& filename)
{
  std::ofstream jsonStream( filename);
  if(jsonStream.fail()) {
    cout<< "Cannot open file " << filename << " for writing" << endl;
    return;
  }
  jsonStream << json(hN);
}
