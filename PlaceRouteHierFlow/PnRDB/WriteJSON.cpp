#include <time.h>

#include <cassert>
#include <fstream>
#include <iomanip>
#include <iostream>

#include "PnRdatabase.h"

using namespace nlohmann;

static int via2int(const PnRDB::Drc_info& drc_info, const string& via) { return stoi(drc_info.MaskID_Via.at(drc_info.Viamap.at(via))); }

static int metal2int(const PnRDB::Drc_info& drc_info, const string& metal) { return stoi(drc_info.MaskID_Metal.at(drc_info.Metalmap.at(metal))); }

unsigned short JSON_Presentation(int font, int vp, int hp) {
  if (font < 0 || font > 3) font = 0;
  if (vp < 0 || vp > 2) vp = 0;
  if (hp < 0 || hp > 2) hp = 0;
  return font * 16 + vp * 4 + hp;
}

unsigned short JSON_STrans(bool reflect, bool abs_angle, bool abs_mag) { return 32768 * reflect + 2 * abs_mag + abs_angle; }

json JSON_TimeTime() {
  static short int year, month;
  time_t* now = (time_t*)malloc(sizeof(time_t));
  time(now);
  struct tm* date;
  date = localtime(now);

  year = 1900 + date->tm_year;
  month = 1 + date->tm_mon;
  json timeTime = {year, month, date->tm_mday, date->tm_hour, date->tm_min, date->tm_sec,
                   year, month, date->tm_mday, date->tm_hour, date->tm_min, date->tm_sec};
  free(now);
  return timeTime;
}

void JSONExtractUit(string GDSData, double& unit) {
  auto logger = spdlog::default_logger()->clone("PnRDB.JSONExtractUit");

  std::string jsonFileName = GDSData + ".json";
  // std::cout << "GDS JSON FILE=" << jsonFileName << std::endl;
  json jsonStrAry;
  ifstream jsonFile(jsonFileName);
  if (jsonFile.is_open()) {
    json jedb = json::parse(jsonFile);
    if (jedb["header"].is_number()) {
      json libAry = jedb["bgnlib"];
      for (json::iterator lit = libAry.begin(); lit != libAry.end(); ++lit) {
        json lib = *lit;
        json strAry = lib["units"];
        if (strAry.is_array()) {
          logger->debug("Unit {0} ", to_string(strAry));
          json::iterator xyI = strAry.begin();
          double xyU = *xyI;
          unit = 0.5 * 0.000000001 / xyU;
          return;
        }
      }
    }
  }
}

void JSONReaderWrite_subcells(string GDSData, long int& rndnum, vector<string>& strBlocks, vector<int>& llx, vector<int>& lly, vector<int>& urx,
                              vector<int>& ury, json& mjsonStrAry) {
  auto logger = spdlog::default_logger()->clone("PnRDB.JSONReaderWrite_subcells");

  rndnum++;

  std::string jsonFileName = GDSData + ".json";
  logger->debug("GDS JSON FILE={0}", jsonFileName);

  int TJ_llx = INT_MAX;
  int TJ_lly = INT_MAX;
  int TJ_urx = -1 * INT_MAX;
  int TJ_ury = -1 * INT_MAX;

  json jsonStrAry;
  ifstream jsonFile(jsonFileName);
  if (jsonFile.is_open()) {
    json jedb = json::parse(jsonFile);
    if (jedb["header"].is_number()) {
      json libAry = jedb["bgnlib"];
      for (json::iterator lit = libAry.begin(); lit != libAry.end(); ++lit) {
        json lib = *lit;
        json strAry = lib["bgnstr"];
        for (json::iterator sit = strAry.begin(); sit != strAry.end(); ++sit) {
          json str = *sit;
          string nm = str["strname"];
          string strname = nm + "_" + std::to_string(rndnum);
          // json elements = str["elements"];
          for (json::iterator elmI = str["elements"].begin(); elmI != str["elements"].end(); ++elmI) {
            TJ_llx = INT_MAX;
            TJ_lly = INT_MAX;
            TJ_urx = INT_MIN;
            TJ_ury = INT_MIN;
            json elm = *elmI;
            if (elm["xy"].is_array()) {
              json xyAry = elm["xy"];
              int pos = 0;
              for (json::iterator xyI = xyAry.begin(); xyI != xyAry.end(); ++xyI, pos++) {
                if (pos % 2) {
                  if (*xyI > TJ_ury) TJ_ury = *xyI;
                  if (*xyI < TJ_lly) TJ_lly = *xyI;
                } else {
                  if (*xyI > TJ_urx) TJ_urx = *xyI;
                  if (*xyI < TJ_llx) TJ_llx = *xyI;
                }
              }
            }
            if (elm["sname"].is_string()) {
              string sn = elm["sname"];
              (*elmI)["sname"] = sn + "_" + std::to_string(rndnum);
            }
          }
          strBlocks.push_back(strname);
          str["strname"] = strname;
          mjsonStrAry.push_back(str);
        }
      }
    } else
      logger->error("NOT a VALID JSON FILE: {0}", jsonFileName);
  } else {
    logger->error("NO JSON FILE: {0}", jsonFileName);
    // DAK: This means we will have a missing subcell!
    // DAK: Should error here
  }
  llx.push_back(TJ_llx);
  lly.push_back(TJ_lly);
  urx.push_back(TJ_urx);
  ury.push_back(TJ_ury);
};

/**
static void
JSONLabelTerminals(PnRDB::hierNode& node, const PnRDB::Drc_info& drc_info, json& elmAry, double unit)
{

    auto logger = spdlog::default_logger()->clone("PnRDB.JSONLabelTerminals");

    elmAry = json::array();

    //cout<<"Top: "<<node.isTop<<endl;
    //cout<<"#terminals print"<<endl;
    //cout<<"#size: "<<node.Terminals.size()<<endl;
    for(unsigned int i=0;i<node.Terminals.size();i++){
        //cout<<"#name: "<<node.Terminals[i].name<<endl;
        //cout<<"#type: "<<node.Terminals[i].type<<endl;
        //cout<<"#netIter: "<<node.Terminals[i].netIter<<endl;
        //cout<<"#termContact size: "<<node.Terminals[i].termContacts.size()<<endl;
        for(unsigned int j=0;j<node.Terminals[i].termContacts.size();j++){
            //cout<<"#contact-metal: "<<node.Terminals[i].termContacts[j].metal<<endl;
            //cout<<"#contact-placedCenter(x,y): "<<node.Terminals[i].termContacts[j].placedCenter.x<<" "
                //<<node.Terminals[i].termContacts[j].placedCenter.y<<endl;
        }
    }
    int test_font=1,test_vp=1,test_hp=1;
    const int test_texttype=32;//pin purpose
    double test_mag=0.03;
    int center_x[1],center_y[1];

    if (node.isTop == 1) {
        for (unsigned int i = 0; i < node.Terminals.size(); i++) {
            int write = 0;
            for (unsigned int j = 0; j < node.Terminals[i].termContacts.size(); j++) {
                PnRDB::contact con = node.Terminals[i].termContacts[j];

                //cout<<"#test metal string: \""<<con.metal<<"\""<<endl;
                if (! con.metal.empty()) {
                    if (write == 0) {
                      center_x[0] = unit * con.placedCenter.x;
                      center_y[0] = unit * con.placedCenter.y;
              logger->debug("Terminal name {0} center {1} {2}",node.Terminals[i].name,center_x[0],center_y[0]);
                      json elm;
                      elm["type"] = "text";
                      elm["layer"] = metal2int( drc_info, con.metal);
                      elm["texttype"] = test_texttype;
                      elm["presentation"] = JSON_Presentation (test_font, test_vp, test_hp);

                      elm["strans"] = 0;
                      elm["mag"] = test_mag;
                      json xy = json::array();
                      xy.push_back (center_x[0]);
                      xy.push_back (center_y[0]);
                      elm["xy"] = xy;
                      elm["string"] = node.Terminals[i].name;
                      elmAry.push_back (elm);

                      write = 1;
                    }
                }
            }
        }
    }
}**/

void assignBoxPoints(int* x, int* y, struct PnRDB::bbox b, double unit) {
  x[0] = unit * b.LL.x;
  x[1] = unit * b.LL.x;
  x[2] = unit * b.UR.x;
  x[3] = unit * b.UR.x;
  x[4] = x[0];
  y[0] = unit * b.LL.y;
  y[1] = unit * b.UR.y;
  y[2] = unit * b.UR.y;
  y[3] = unit * b.LL.y;
  y[4] = y[0];
}

void addTextElements(json& jsonElements, int cenX, int cenY, int layer, const PnRDB::Drc_info& drc_info, int layer_index, const string& text) {
  int test_font = 1, test_vp = 1, test_hp = 1;
  // const int test_texttype=3; //draw 0, label 2, pin 3, blockage 4
  double test_mag = 3e-8;
  json element;
  element["type"] = "text";
  element["layer"] = layer;
  element["texttype"] = drc_info.Metal_info.at(layer_index).gds_datatype.Label;
  // std::cout << "add Text Elements Test" << layer_index << layer << element["texttype"] << std::endl;
  // reminder, layer_index is not metal layer number. It is the index of metal in drc_info.Metal_info
  element["presentation"] = JSON_Presentation(test_font, test_vp, test_hp);

  element["width"] = -1;
  element["strans"] = 0;
  element["mag"] = test_mag;
  json xy = json::array();
  xy.push_back(cenX);
  xy.push_back(cenY);
  element["xy"] = xy;
  element["string"] = text;
  jsonElements.push_back(element);
}

static bool addMetalBoundaries(json& jsonElements, struct PnRDB::Metal& metal, const PnRDB::Drc_info& drc_info, double unit) {
  int x[5], y[5];
  assignBoxPoints(x, y, metal.MetalRect.placedBox, unit);

  if (metal.LinePoint[0].x != metal.LinePoint[1].x || metal.LinePoint[0].y != metal.LinePoint[1].y) {
    json bound0;
    bound0["type"] = "boundary";
    bound0["layer"] = metal2int(drc_info, metal.MetalRect.metal);
    bound0["datatype"] = 0;
    json xy = json::array();
    for (size_t i = 0; i < 5; i++) {
      xy.push_back(x[i]);
      xy.push_back(y[i]);
    }
    bound0["xy"] = xy;
    jsonElements.push_back(bound0);
    return true;
  }
  return false;
}

static void addContactBoundaries(json& jsonElements, struct PnRDB::contact& Contact, const PnRDB::Drc_info& drc_info, int unit) {
  int x[5], y[5];
  assignBoxPoints(x, y, Contact.placedBox, unit);
  json bound0;
  bound0["type"] = "boundary";
  bound0["layer"] = metal2int(drc_info, Contact.metal);
  bound0["datatype"] = 0;
  json xy = json::array();
  for (size_t i = 0; i < 5; i++) {
    xy.push_back(x[i]);
    xy.push_back(y[i]);
  }
  bound0["xy"] = xy;
  jsonElements.push_back(bound0);
}

void addOABoundaries(json& jsonElements, int width, int height) {
  int x[5], y[5];
  x[0] = y[0] = x[1] = y[3] = x[4] = y[4] = 0;
  x[2] = x[3] = width;
  y[1] = y[2] = height;
  json bound1;
  bound1["type"] = "boundary";
  bound1["layer"] = 235;
  bound1["datatype"] = 5;
  json xy = json::array();
  for (size_t i = 0; i < 5; i++) {
    xy.push_back(x[i]);
    xy.push_back(y[i]);
  }
  bound1["xy"] = xy;
  bound1["propattr"] = 126;
  bound1["propvalue"] = "oaBoundary:pr";
  jsonElements.push_back(bound1);
  //   boundary
  //       layer 235
  //       datatype 5
  //       xy   5   0 0   0 1608   8640 1608   8640 0
  //                0 0
  //       propattr 126
  //       propvalue "oaBoundary:pr"
  //       endel
}

void addTop_OABoundaries(json& jsonElements, int width, int height, const PnRDB::Drc_info& drc_info, double unitScale) {
  int off_set = unitScale * drc_info.Metal_info.back().width;
  int x[5], y[5];
  x[0] = y[0] = x[1] = y[3] = x[4] = y[4] = 0 - off_set;
  x[2] = x[3] = width + off_set;
  y[1] = y[2] = height + off_set;
  json bound1;
  bound1["type"] = "boundary";
  bound1["layer"] = drc_info.top_boundary.layerNo;
  bound1["datatype"] = drc_info.top_boundary.gds_datatype.Draw;
  json xy = json::array();
  for (size_t i = 0; i < 5; i++) {
    xy.push_back(x[i]);
    xy.push_back(y[i]);
  }
  bound1["xy"] = xy;
  bound1["propattr"] = 126;
  bound1["propvalue"] = "oaBoundary:pr";
  jsonElements.push_back(bound1);
  //   boundary
  //       layer 235
  //       datatype 5
  //       xy   5   0 0   0 1608   8640 1608   8640 0
  //                0 0
  //       propattr 126
  //       propvalue "oaBoundary:pr"
  //       endel
}

static void addViaBoundaries(json& jsonElements, struct PnRDB::Via& via, const PnRDB::Drc_info& drc_info, double unit) {
  int x[5], y[5];
  assignBoxPoints(x, y, via.ViaRect.placedBox, unit);

  json bound0;
  bound0["type"] = "boundary";
  bound0["layer"] = via2int(drc_info, via.ViaRect.metal);
  bound0["datatype"] = 0;
  json xy = json::array();
  for (size_t i = 0; i < 5; i++) {
    xy.push_back(x[i]);
    xy.push_back(y[i]);
  }
  bound0["xy"] = xy;
  jsonElements.push_back(bound0);

  // LowerMetalRect
  assignBoxPoints(x, y, via.LowerMetalRect.placedBox, unit);

  json bound1;
  bound1["type"] = "boundary";
  bound1["layer"] = metal2int(drc_info, via.LowerMetalRect.metal);
  bound1["datatype"] = 0;
  xy = json::array();
  for (size_t i = 0; i < 5; i++) {
    xy.push_back(x[i]);
    xy.push_back(y[i]);
  }
  bound1["xy"] = xy;
  jsonElements.push_back(bound1);

  // UpperMetalRect
  assignBoxPoints(x, y, via.UpperMetalRect.placedBox, unit);

  json bound2;
  bound2["type"] = "boundary";
  bound2["layer"] = metal2int(drc_info, via.UpperMetalRect.metal);
  bound2["datatype"] = 0;
  xy = json::array();
  for (size_t i = 0; i < 5; i++) {
    xy.push_back(x[i]);
    xy.push_back(y[i]);
  }
  bound2["xy"] = xy;
  jsonElements.push_back(bound2);
}

std::string PnRdatabase::WriteJSON(PnRDB::hierNode& node, bool includeBlock, bool includeNet, bool includePowerNet, bool includePowerGrid,
                                   const std::string& gdsName, const PnRDB::Drc_info& drc_info, const string& opath) {
  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.WriteJSON");

  logger->debug("JSON WRITE CELL {0} ", gdsName);
  node.gdsFile = opath + gdsName + ".gds";
  string TopCellName = gdsName;
  std::set<string> uniGDSset;
  double unitScale = 0.5;
  for (unsigned int i = 0; i < node.Blocks.size(); i++) uniGDSset.insert(node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).gdsFile);

  for (std::set<string>::iterator it = uniGDSset.begin(); it != uniGDSset.end(); ++it) {
    JSONExtractUit(*it, unitScale);
  }
  logger->debug("unitScale {0} ", unitScale);
  uniGDSset.clear();

  std::ofstream jsonStream;
  jsonStream.open(node.gdsFile + ".json");
  json jsonTop;
  json jsonLibAry = json::array();
  jsonTop["header"] = 600;
  json jsonLib;
  jsonLib["time"] = JSON_TimeTime();
  double dbUnitUser = 0.5 * 0.000000001 / unitScale;
  double dbUnitMeter = dbUnitUser;
  /// 1e6;
  jsonLib["units"] = {dbUnitUser, dbUnitMeter};
  // jsonLib["units"] = {0.00025, 2.5e-10};
  jsonLib["libname"] = "test";
  json jsonStrAry = json::array();

  vector<string> strBlocks;
  std::map<string, int> gdsMap2strBlock;
  vector<string> strBlocks_Top;
  vector<int> llx, lly, urx, ury;
  long int rndnum = static_cast<long int>(time(NULL));

  int idx = 0;
  if (includeBlock) {
    for (unsigned int i = 0; i < node.Blocks.size(); i++) uniGDSset.insert(node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).gdsFile);
    for (unsigned int i = 0; i < node.GuardRings.size(); i++) uniGDSset.insert(node.GuardRings[i].gdsFile);

    // cout<<"start wrting sub-blocks"<<endl;
    for (std::set<string>::iterator it = uniGDSset.begin(); it != uniGDSset.end(); ++it) {
      json j;
      JSONReaderWrite_subcells(*it, rndnum, strBlocks, llx, lly, urx, ury, j);
      for (json::iterator str = j.begin(); str != j.end(); ++str) jsonStrAry.push_back(*str);
      strBlocks_Top.push_back(strBlocks.back());
      gdsMap2strBlock.insert(std::make_pair(*it, idx));
      idx++;
    }
  }

  json jsonStr;
  jsonStr["time"] = JSON_TimeTime();
  // DAK: Hack to match time for repeated runs
  jsonStr["time"] = {2019, 4, 24, 9, 46, 15, 2019, 4, 24, 9, 46, 15};
  jsonStr["strname"] = TopCellName;
  json jsonElements = json::array();

  int x[5], y[5];
  int write_blockPins_name = 1;
  if (write_blockPins_name && node.isTop == 1) {
    for (unsigned int i = 0; i < node.blockPins.size(); i++) {
      int write = 0;
      logger->debug("Write blockPins info {0}", node.blockPins[i].name);
      logger->debug("blockPins contact size {0}", node.blockPins[i].pinContacts.size());
      for (unsigned int j = 0; j < node.blockPins[i].pinContacts.size(); j++) {
        if (write == 0) {
          PnRDB::contact con = node.blockPins[i].pinContacts[j];
          logger->debug("contact info {0} {1} {2} {3}", con.originBox.LL.x, con.originBox.LL.y, con.originBox.UR.x, con.originBox.UR.y);
          con.placedBox = con.originBox;
          addContactBoundaries(jsonElements, con, drc_info, unitScale);
          assignBoxPoints(x, y, con.originBox, unitScale);
          addTextElements(jsonElements, (x[0] + x[2]) / 2, (y[0] + y[2]) / 2, metal2int(drc_info, con.metal), drc_info, drc_info.Metalmap.at(con.metal),
                          node.blockPins[i].name);
          write = 1;  // added by yg
        }
      }
    }
  }

  // write out extend pins
  int write_extend_pins = 1;
  if (write_extend_pins) {
    for (unsigned int i = 0; i < node.Blocks.size(); i++) {
      int selected_block_index = node.Blocks[i].selectedInstance;
      for (unsigned int j = 0; j < node.Blocks[i].instance[selected_block_index].blockPins.size(); j++) {
        for (unsigned int k = 0; k < node.Blocks[i].instance[selected_block_index].blockPins[j].pinContacts.size(); k++) {
          PnRDB::contact con = node.Blocks[i].instance[selected_block_index].blockPins[j].pinContacts[k];
          // con.placedBox = con.originBox;
          addContactBoundaries(jsonElements, con, drc_info, unitScale);
        }
      }
    }
  }

  /*
      int write_blockPins = 1;
      if (write_blockPins){
          for (unsigned int i = 0; i < node.blockPins.size(); i++) {
              int write = 1;
              for (unsigned int j = 0; j < node.blockPins[i].pinContacts.size(); j++) {
                  PnRDB::contact con = node.blockPins[i].pinContacts[j];
                  con.placedBox = con.originBox;
                  addContactBoundaries (jsonElements, con, drc_info, unitScale);
                  if (write == 0) {
                      PnRDB::contact con = node.blockPins[i].pinContacts[j];
                      std::cout<<"contact info "<<con.originBox.LL.x<<" "<<con.originBox.LL.y<<" "<<con.originBox.UR.x<<" "<<con.originBox.UR.y<<std::endl;
                      con.placedBox = con.originBox;
                      addContactBoundaries (jsonElements, con, drc_info, unitScale);
                      assignBoxPoints (x, y, con.originBox, unitScale);
                      addTextElements (jsonElements, (x[0]+x[2])/2, (y[0]+y[2])/2,
                                       metal2int( drc_info, con.metal),
                      drc_info, drc_info.Metalmap.at(con.metal),
                      node.blockPins[i].name);
                      write = 0;	// added by yg
                  }
              }
          }
      }
  */
  if (includeNet) {
    // cout<<"start writing nets"<<endl;
    for (unsigned int i = 0; i < node.Nets.size(); i++) {
      // path_metal
      int write = 1;
      for (unsigned int j = 0; j < node.Nets[i].path_metal.size(); j++) {
        PnRDB::Metal metal = node.Nets[i].path_metal[j];
        if (addMetalBoundaries(jsonElements, metal, drc_info, unitScale)) {
          if (write == 0) {
            assignBoxPoints(x, y, metal.MetalRect.placedBox, unitScale);
            addTextElements(jsonElements, (x[0] + x[2]) / 2, (y[0] + y[2]) / 2, metal2int(drc_info, metal.MetalRect.metal), drc_info,
                            drc_info.Metalmap.at(metal.MetalRect.metal), node.Nets[i].name);
            write = 1;  // added by yg
          }
        }
      }
      // path_via
      for (unsigned int j = 0; j < node.Nets[i].path_via.size(); j++) addViaBoundaries(jsonElements, node.Nets[i].path_via[j], drc_info, unitScale);
    }
  }
  json j;
  // JSONLabelTerminals(node, drc_info, j, unitScale);
  for (json::iterator elm = j.begin(); elm != j.end(); ++elm) jsonElements.push_back(*elm);

  if (includePowerNet) {
    for (unsigned int i = 0; i < node.PowerNets.size(); i++) {
      // path_metal
      int write = 0;
      for (unsigned int j = 0; j < node.PowerNets[i].path_metal.size(); j++) {
        PnRDB::Metal metal = node.PowerNets[i].path_metal[j];
        if (addMetalBoundaries(jsonElements, metal, drc_info, unitScale)) {
          if (write == 0) {
            assignBoxPoints(x, y, metal.MetalRect.placedBox, unitScale);
            addTextElements(jsonElements, (x[0] + x[2]) / 2, (y[0] + y[2]) / 2, metal2int(drc_info, metal.MetalRect.metal), drc_info,
                            drc_info.Metalmap.at(metal.MetalRect.metal), node.PowerNets[i].name);
            write = 1;  // added by yg
          }
        }
        //add power label in the top middle
        metal = Find_Top_Middle_Metal(node, drc_info, i);
	assignBoxPoints (x, y, metal.MetalRect.placedBox, unitScale);
        addTextElements (jsonElements, (x[0]+x[2])/2, (y[0]+y[2])/2, metal2int(drc_info, metal.MetalRect.metal), drc_info, drc_info.Metalmap.at(metal.MetalRect.metal), node.PowerNets[i].name);        
      }
      // path_via
      for (unsigned int j = 0; j < node.PowerNets[i].path_via.size(); j++) addViaBoundaries(jsonElements, node.PowerNets[i].path_via[j], drc_info, unitScale);
    }
  }

  if (includePowerGrid) {
    const int vdd = 1;
    const int gnd = 1;
    if (vdd == 1) {
      for (unsigned int i = 0; i < node.Vdd.metals.size(); i++) addMetalBoundaries(jsonElements, node.Vdd.metals[i], drc_info, unitScale);

      for (unsigned int i = 0; i < node.Vdd.vias.size(); i++) addViaBoundaries(jsonElements, node.Vdd.vias[i], drc_info, unitScale);
    }
    if (gnd == 1) {
      for (unsigned int i = 0; i < node.Gnd.metals.size(); i++) addMetalBoundaries(jsonElements, node.Gnd.metals[i], drc_info, unitScale);

      for (unsigned int i = 0; i < node.Gnd.vias.size(); i++) addViaBoundaries(jsonElements, node.Gnd.vias[i], drc_info, unitScale);
    }
  }

  if (includeBlock) {
    int bOrient;

    // for(int i = 0;i < node.Blocks.size(); i++){
    //    //int index=gdsMap2strBlock[node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).gdsFile];
    //    for( int j=0;j<node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).interMetals.size();j++){
    //         addContactBoundaries(jsonElements, node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).interMetals[j], drc_info, unitScale);
    //       }
    //   }

    for (unsigned int i = 0; i < node.GuardRings.size(); i++) {
      json sref;
      sref["type"] = "sref";
      sref["sname"] = strBlocks_Top[gdsMap2strBlock[node.GuardRings[i].gdsFile]];
      sref["strans"] = 0;
      json xy = json::array();
      xy.push_back(int(unitScale * node.GuardRings[i].LL.x));
      xy.push_back(int(unitScale * node.GuardRings[i].LL.y));
      sref["xy"] = xy;
      jsonElements.push_back(sref);
    }

    for (unsigned int i = 0; i < node.Blocks.size(); i++) {
      int index = gdsMap2strBlock[node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).gdsFile];

      json sref;
      sref["type"] = "sref";
      sref["sname"] = strBlocks_Top[index];
      sref["angle"] = 0.0;

      switch (node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).orient) {
        case PnRDB::N:
          bOrient = 0;
          break;
        case PnRDB::S:
          bOrient = 1;
          break;
        case PnRDB::E:
          bOrient = 2;
          break;
        case PnRDB::W:
          bOrient = 3;
          break;
        case PnRDB::FN:
          bOrient = 4;
          break;
        case PnRDB::FS:
          bOrient = 5;
          break;
        case PnRDB::FE:
          bOrient = 6;
          break;
        case PnRDB::FW:
          bOrient = 7;
          break;
        default:
          bOrient = 8;
      }

      PnRDB::bbox box = node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).placedBox;
      switch (bOrient) {
        case 0:
          sref["strans"] = 0;
          sref["angle"] = 0.0;
          x[0] = unitScale * box.LL.x;
          y[0] = unitScale * box.LL.y;
          break;
        case 1:
          sref["strans"] = 0;
          sref["angle"] = 180.0;
          x[0] = unitScale * box.UR.x + llx[index];
          y[0] = unitScale * box.UR.y + lly[index];
          break;
        case 2:
          assert(0);
          break;
        case 3:
          assert(0);
          break;
        case 4:
          sref["strans"] = 32768;  // DAK: HACK
          sref["angle"] = 180.0;
          x[0] = unitScale * box.UR.x + llx[index];
          y[0] = unitScale * box.LL.y - lly[index];
          break;
        case 5:
          sref["strans"] = 32768;  // DAK: HACK
          sref["angle"] = 0.0;
          x[0] = unitScale * box.LL.x - llx[index];
          y[0] = unitScale * box.UR.y + lly[index];
          break;
        case 6:
          assert(0);
          break;
        case 7:
          assert(0);
          break;
        default:
          sref["strans"] = 0;  // DAK: HACK
          sref["angle"] = 0.0;
          x[0] = unitScale * box.LL.x;
          y[0] = unitScale * box.LL.y;
      }
      json xy = json::array();
      for (size_t i = 0; i < 1; i++) {
        xy.push_back(x[i]);
        xy.push_back(y[i]);
      }
      sref["xy"] = xy;
      jsonElements.push_back(sref);
    }
  }

  addOABoundaries(jsonElements, unitScale * node.width, unitScale * node.height);
  if (node.isTop) {
    addTop_OABoundaries(jsonElements, unitScale * node.width, unitScale * node.height, drc_info, unitScale);
  }
  jsonStr["elements"] = jsonElements;
  jsonStrAry.push_back(jsonStr);
  jsonLib["bgnstr"] = jsonStrAry;

  jsonLibAry.push_back(jsonLib);
  jsonTop["bgnlib"] = jsonLibAry;
  jsonStream << std::setw(4) << jsonTop;
  jsonStream.close();
  logger->debug(" JSON FINALIZE {0} ", gdsName);
  return node.gdsFile;
}

PnRDB::Metal PnRdatabase::Find_Top_Middle_Metal(PnRDB::hierNode& node, const PnRDB::Drc_info& drc_info, int index){

  std::vector<PnRDB::Metal> Metals;

  if(node.PowerNets[index].name==node.Vdd.name){
     Metals = node.Vdd.metals;
  }else if(node.PowerNets[index].name==node.Gnd.name){
     Metals = node.Gnd.metals;
  }

  PnRDB::point chip_centor = node.LL + node.UR;
  chip_centor.x = chip_centor.x/2;
  chip_centor.y = chip_centor.y/2;

  int top_power_routing_metal = drc_info.Design_info.power_routing_metal_u;
  int Metal_index = 0;
  int distance = INT_MAX;
  for(unsigned int i=0;i<Metals.size();++i){
     if(Metals[i].MetalIdx==top_power_routing_metal){
       int temp_dis = abs(Metals[i].MetalRect.placedCenter.x-chip_centor.x)+abs(Metals[i].MetalRect.placedCenter.y-chip_centor.y);
       if(temp_dis<distance){
          distance = temp_dis;
          Metal_index = i;
       }
     }
  }
  return Metals[Metal_index];
  
}

// added by yg 2019-10-26
void AddContact(PnRDB::contact& temp_contact, json& temp_json_Contact, int unit) {
  json temp_json_contact;
  temp_json_contact["Physical Layer"] = temp_contact.metal;
  temp_json_contact["LLx"] = temp_contact.placedBox.LL.x * unit;
  temp_json_contact["LLy"] = temp_contact.placedBox.LL.y * unit;
  temp_json_contact["URx"] = temp_contact.placedBox.UR.x * unit;
  temp_json_contact["URy"] = temp_contact.placedBox.UR.y * unit;

  temp_json_Contact.push_back(temp_json_contact);
}

void AddContacts(std::vector<PnRDB::contact>& temp_contact, json& temp_json_Contact, int unit) {
  for (unsigned int i = 0; i < temp_contact.size(); i++) {
    AddContact(temp_contact[i], temp_json_Contact, unit);
  }
}

void AddContacts_Metal(std::vector<PnRDB::Metal>& temp_metal, json& temp_json_Contact, int unit) {
  for (unsigned int i = 0; i < temp_metal.size(); i++) {
    AddContact(temp_metal[i].MetalRect, temp_json_Contact, unit);
  }
}

void AddVia(PnRDB::Via& temp_via, json& temp_json_Contact, json& temp_json_Via, int unit) {
  AddContact(temp_via.ViaRect, temp_json_Via, unit);
  AddContact(temp_via.LowerMetalRect, temp_json_Contact, unit);
  AddContact(temp_via.UpperMetalRect, temp_json_Contact, unit);
}

void AddVias(std::vector<PnRDB::Via>& temp_via, json& temp_json_Contact, json& temp_json_Via, int unit) {
  for (unsigned int i = 0; i < temp_via.size(); i++) {
    AddVia(temp_via[i], temp_json_Contact, temp_json_Via, unit);
  }
}

void PnRdatabase::WriteJSON_Routability_Analysis(PnRDB::hierNode& node, const string& opath, PnRDB::Drc_info& drc_info) {
  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.WriteJSON_Routability_Analysis");

  logger->debug("JSON WRITE Routability Analysis {0}", node.name);
  std::ofstream jsonStream;
  jsonStream.open(opath + node.name + ".json");
  json jsonTop;
  jsonTop["Cell Name"] = node.name;
  jsonTop["Units"] = "0.5nm";
  jsonTop["Istop"] = node.isTop;
  int unit = 1;

  json temp_box;
  temp_box["Physical Layer"] = "null";
  temp_box["LLx"] = 0 * unit;
  temp_box["LLy"] = 0 * unit;
  temp_box["URx"] = node.width * unit;
  temp_box["URy"] = node.height * unit;
  jsonTop["Cell box"] = temp_box;

  if (drc_info.Metal_info[0].direct == 1) {  // H

    jsonTop["x pitches"] = drc_info.Metal_info[1].grid_unit_x * unit;
    jsonTop["y pitches"] = drc_info.Metal_info[0].grid_unit_y * unit;

  } else {  // V

    jsonTop["x pitches"] = drc_info.Metal_info[0].grid_unit_x * unit;
    jsonTop["y pitches"] = drc_info.Metal_info[1].grid_unit_y * unit;
  }

  // Node terminals
  json jsonTerminals = json::array();

  for (unsigned int i = 0; i < node.Terminals.size(); i++) {
    json tempjsonTerminal;
    tempjsonTerminal["Name"] = node.Terminals[i].name;
    json temp_Contact = json::array();
    AddContacts(node.Terminals[i].termContacts, temp_Contact, unit);
    tempjsonTerminal["Internal Metal"] = temp_Contact;
    jsonTerminals.push_back(tempjsonTerminal);
  }

  jsonTop["Terminals"] = jsonTerminals;

  // node Blocks
  json jsonBlocks = json::array();
  for (unsigned int i = 0; i < node.Blocks.size(); i++) {
    int index = node.Blocks[i].selectedInstance;
    json temp_block;
    temp_block["Name"] = node.Blocks[i].instance.at(index).name;
    temp_block["Height"] = node.Blocks[i].instance.at(index).height;
    temp_block["Width"] = node.Blocks[i].instance.at(index).width;
    json box;
    box["Physical Layer"] = "null";
    box["LLx"] = node.Blocks[i].instance.at(index).placedBox.LL.x * unit;
    box["LLy"] = node.Blocks[i].instance.at(index).placedBox.LL.y * unit;
    box["URx"] = node.Blocks[i].instance.at(index).placedBox.UR.x * unit;
    box["URy"] = node.Blocks[i].instance.at(index).placedBox.UR.y * unit;
    temp_block["Box"] = box;

    // pins
    json block_pins = json::array();
    for (unsigned j = 0; j < node.Blocks[i].instance.at(index).blockPins.size(); j++) {
      json temp_pin;
      temp_pin["Name"] = node.Blocks[i].instance.at(index).blockPins[j].name;
      json temp_Contacts = json::array();
      json temp_Vias = json::array();
      AddContacts(node.Blocks[i].instance.at(index).blockPins[j].pinContacts, temp_Contacts, unit);
      AddVias(node.Blocks[i].instance.at(index).blockPins[j].pinVias, temp_Contacts, temp_Vias, unit);
      temp_pin["Internal Metal"] = temp_Contacts;
      temp_pin["Internal Via"] = temp_Vias;
      block_pins.push_back(temp_pin);
    }

    temp_block["Pins"] = block_pins;

    // internal metals
    // internal vias
    json internal_metal = json::array();
    json internal_via = json::array();
    AddContacts(node.Blocks[i].instance.at(index).interMetals, internal_metal, unit);
    AddVias(node.Blocks[i].instance.at(index).interVias, internal_metal, internal_via, unit);
    temp_block["Internal Metal"] = internal_metal;
    temp_block["Internal Via"] = internal_via;
    jsonBlocks.push_back(temp_block);
  }

  jsonTop["Blocks"] = jsonBlocks;

  // Nets
  json jsonNets = json::array();

  for (unsigned int i = 0; i < node.Nets.size(); i++) {
    json json_temp_net;
    json_temp_net["Name"] = node.Nets[i].name;
    // connected
    json json_connected = json::array();

    for (unsigned int j = 0; j < node.Nets[i].connected.size(); j++) {
      json temp_connected;
      if (node.Nets[i].connected[j].type == PnRDB::Block) {
        temp_connected["Type"] = "Block";
        int select_block_index = node.Blocks[node.Nets[i].connected[j].iter2].selectedInstance;
        int block_index = node.Nets[i].connected[j].iter2;
        int pin_index = node.Nets[i].connected[j].iter;
        temp_connected["Block name"] = node.Blocks[block_index].instance.at(select_block_index).name;
        temp_connected["Pin name"] = node.Blocks[block_index].instance.at(select_block_index).blockPins[pin_index].name;
      } else {
        temp_connected["Type"] = "Terminal";
        temp_connected["Block name"] = "Null";
        temp_connected["Pin name"] = node.Terminals[node.Nets[i].connected[j].iter].name;
      }
      json_connected.push_back(temp_connected);
    }

    json_temp_net["Connected"] = json_connected;
    // internal metal
    // internal via
    json internal_metals = json::array();
    json internal_vias = json::array();
    AddContacts_Metal(node.Nets[i].path_metal, internal_metals, unit);
    AddVias(node.Nets[i].path_via, internal_metals, internal_vias, unit);
    json_temp_net["Internal Metal"] = internal_metals;
    json_temp_net["Internal Via"] = internal_vias;

    jsonNets.push_back(json_temp_net);
  }

  jsonTop["Nets"] = jsonNets;

  jsonStream << std::setw(4) << jsonTop;
  jsonStream.close();
  logger->debug(" JSON FINALIZE {0}", node.name);
}
