#include <assert.h>

#include <cmath>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <sstream>

#include "PnRdatabase.h"

using std::map;
static double parse_and_scale(const std::string& s, double unitScale) {
  auto logger = spdlog::default_logger()->clone("PnRDB.parse_and_scale");

  double scaled = stod(s) * unitScale;
  double result = round(scaled);
  if (fabs(scaled - result) > 0.001) {
    logger->error( "ERROR: parse_and_scale {0} {1} Rounded result differs too much from unrounded result ( {2} {3} )" , s , unitScale , result
              , scaled );
  }
  return result;
}

//create bbox of vias to create rows or taps and actives
void MergeVias(vector<PnRDB::bbox>& boxes)
{
  map<pair<int, int>, PnRDB::bbox> rowBBox;
  for (auto& b : boxes) {
    auto ypair = std::make_pair(b.LL.y, b.UR.y);
    auto it = rowBBox.find(ypair);
    if (it == rowBBox.end()) {
      rowBBox[ypair] = b; 
    } else {
      rowBBox[ypair].merge(b);
    }
  }
  boxes.clear();
  for (auto& it : rowBBox) {
    boxes.push_back(it.second);
  }
}


bool PnRdatabase::ReadLEF(const string& leffile, bool wtap) {

  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.ReadLEF");

  ifstream fin;
  fin.exceptions(ifstream::failbit | ifstream::badbit);
  try {
    fin.open(leffile.c_str());
    _ReadLEF( fin, leffile, wtap);
    fin.close();
    return true;
  } catch (ifstream::failure& e) {
    logger->error("PnRDB-Error: fail to read LEF file ");
  }
  return false;
}

bool PnRdatabase::ReadLEFFromString(const string& lefStr, const bool wtap) {
  std::istringstream is(lefStr);
  _ReadLEF( is, "<string>", wtap);
  return true;
}

void PnRdatabase::_ReadLEF(istream& fin, const string& leffile, const bool wtap) {

  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase._ReadLEF");

  logger->info( "PnRDB-Info: reading LEF file {0}" , leffile);
  string def;
  size_t found;
  vector<string> temp;
  int* p;
  int p_temp = 0;
  p = &p_temp;
  string macroName;
  string portEnd = "END";
  string obsEnd = "END";
  string pinEnd;
  string macroEnd;
  string unitsEnd;
  double units = 2.0;
  int width = -1, height = -1;
  vector<PnRDB::pin> macroPins;
  vector<PnRDB::contact> interMetals;  // metal within each MACRO
  vector<PnRDB::Via> interVias; //via within each MACRO
  vector<PnRDB::bbox> tapVias, activeVias;
  bool Metal_Flag, tapVia(false), activeVia(false), pmosDevice(false);
  {
    int stage = 0;
    bool skip_the_rest_of_stage_4 = false;
    while (fin.peek() != EOF) {
      getline(fin, def);
      // cout<<def<<endl;
      // [wbxu] This function needs to be updated to support internal metals, currently we're lack of data
      if (stage == 0) {  // idle mode
        logger->debug( "stage0.def: {0}" , def );
        if ((found = def.find("MACRO")) != string::npos) {
          temp = get_true_word(found, def, 0, ';', p);
          macroName = temp[1];
          macroEnd = "END " + temp[1];
          // cout<<"Stage "<<stage<<" @ "<<macroName<<" ~~ "<<macroEnd<<endl;
          width = 0;
          height = 0;
          macroPins.clear();
          interMetals.clear();
          interVias.clear();
          tapVias.clear();
          activeVias.clear();
          stage = 1;
          pmosDevice = false;
        }
      } else if (stage == 5) {  // within UNITS
        if ((found = def.find(unitsEnd)) != string::npos) {
          stage = 1;
        } else if ((found = def.find("DATABASE")) != string::npos) {
          temp = get_true_word(found, def, 0, ';', p);
          units = unitScale / stod(temp[3]);
        }
      } else if (stage == 1) {  // within MACRO
        if ((found = def.find("SIZE")) != string::npos) {
          temp = get_true_word(found, def, 0, ';', p);
          width = parse_and_scale(temp[1], units);
          height = parse_and_scale(temp[3], units);
          // cout<<"Stage "<<stage<<" @ W "<<width<<"; H "<<height<<endl;
        } else if ((found = def.find("UNITS")) != string::npos) {
          stage = 5;
          unitsEnd = "END UNITS";
        } else if ((found = def.find("PIN")) != string::npos) {
          temp = get_true_word(found, def, 0, ';', p);
          macroPins.resize(macroPins.size() + 1);
          macroPins.back().name = temp[1];
          pinEnd = "END " + temp[1];
          // cout<<"Stage "<<stage<<" @ pin "<<macroPins.back().name<<"; end "<<pinEnd<<endl;
          stage = 2;
        } else if ((found = def.find("OBS")) != string::npos) {
          // interMetals.resize(interMetals.size()+1);
          stage = 4;
        } else if ((found = def.find(macroEnd)) != string::npos) {
          PnRDB::lefMacro macroIns;
          macroIns.width = width;
          macroIns.height = height;
          macroIns.name = macroName;
          macroIns.macroPins = macroPins;
          macroIns.interMetals = interMetals;
          macroIns.interVias = interVias;
          MergeVias(tapVias);
          MergeVias(activeVias);
          //logger->info("name : {0} {1} {2}", macroName, tapVias.size(), activeVias.size());
          if (pmosDevice) {
            macroIns._taVias = std::make_shared<PnRDB::taVias>(tapVias, activeVias, false);
          } else {
            macroIns._taVias = std::make_shared<PnRDB::taVias>(tapVias, activeVias, true);
          }

          string key = "_AspectRatio";
          std::size_t found = macroIns.name.find(key);
          if (found != std::string::npos) {  // different aspect ratio exists
            macroIns.master = macroIns.name.substr(0, found);
          } else {  // different aspect ratio does not exist
            macroIns.master = macroIns.name;
          }
          //for (auto& v : macroIns._tapVias) {
          //  logger->debug("{0} tap row : {1} {2} {3} {4}", macroIns.master, v.LL.x, v.LL.y, v.UR.x, v.UR.y);
          //}
          //for (auto& v : macroIns._activeVias) {
          //  logger->debug("active row : {0} {1} {2} {3} {4}", v.LL.x, v.LL.y, v.UR.x, v.UR.y, macroIns.master);
          //}
          auto& lefD = wtap ? lefData : _lefDataWoTap;
          if (lefD.find(macroIns.master) == lefD.end()) {
            std::vector<PnRDB::lefMacro> lefV;
            lefV.push_back(macroIns);
            lefD.insert(std::pair<string, std::vector<PnRDB::lefMacro> >(macroIns.master, lefV));
            // lefD.insert( std::pair<string,PnRDB::lefMacro>(macroName,macroIns) );
          } else {
            lefD[macroIns.master].push_back(macroIns);
          }
          // cout<<"Stage "<<stage<<" @ insert macro data"<<endl;
          stage = 0;
        }
      } else if (stage == 4) {  // within OBS
        logger->debug("stage4.Def: {0}", def);
        if ((found = def.find("LAYER")) != string::npos) {
          skip_the_rest_of_stage_4 = false;
          temp = get_true_word(found, def, 0, ';', p);
          if (temp[1].front() == 'M') {
            interMetals.resize(interMetals.size() + 1);
            interMetals.back().metal = temp[1];
          } else if (temp[1].front() == 'V' && temp[1].back()!='0') {
            tapVia = (temp[1].find("tap") != std::string::npos);
            activeVia = (temp[1].find("active") != std::string::npos);
            if (!tapVia && !activeVia) {
              interVias.resize(interVias.size() + 1);
              interVias.back().model_index = DRC_info.Viamap[temp[1]];
              interVias.back().ViaRect.metal = temp[1];
            }
          } else {
            if (!pmosDevice) pmosDevice = (temp[1].find("Nwell") != std::string::npos);
            skip_the_rest_of_stage_4 = true;
          }
          //logger->info("device : {0} {1} {2}", macroName, temp[1], pmosDevice);
        } else if ((found = def.find("RECT")) != string::npos) {
          char rect_type = temp[1].front();
          temp = get_true_word(found, def, 0, ';', p);
          int LLx = parse_and_scale(temp[1], units);
          int LLy = parse_and_scale(temp[2], units);
          int URx = parse_and_scale(temp[3], units);
          int URy = parse_and_scale(temp[4], units);
          PnRDB::bbox oBox;
          PnRDB::point tp;
          tp.x = LLx;
          tp.y = LLy;
          oBox.LL = tp;
          tp.x = URx;
          tp.y = URy;
          oBox.UR = tp;
          if (!skip_the_rest_of_stage_4) {
            if (rect_type == 'M') {
              assert(interMetals.size() > 0);
              interMetals.back().originBox = oBox;
              interMetals.back().originCenter.x = (LLx + URx) / 2;
              interMetals.back().originCenter.y = (LLy + URy) / 2;
            } else if (rect_type == 'V') {
              if (!tapVia && !activeVia) {
                assert(interVias.size() > 0);
                PnRDB::point center((LLx + URx) / 2, (LLy + URy) / 2);
                PnRDB::ViaModel via_model = DRC_info.Via_model[interVias.back().model_index];
                interVias.back().originpos = center;
                interVias.back().ViaRect.originCenter = center;
                interVias.back().ViaRect.originBox.LL = via_model.ViaRect[0] + center;
                interVias.back().ViaRect.originBox.UR = via_model.ViaRect[1] + center;
                interVias.back().ViaRect.metal = via_model.name;
                interVias.back().LowerMetalRect.originCenter = center;
                interVias.back().LowerMetalRect.originBox.LL = via_model.LowerRect[0] + center;
                interVias.back().LowerMetalRect.originBox.UR = via_model.LowerRect[1] + center;
                interVias.back().LowerMetalRect.metal = DRC_info.Metal_info[via_model.LowerIdx].name;
                interVias.back().UpperMetalRect.originCenter = center;
                interVias.back().UpperMetalRect.originBox.LL = via_model.UpperRect[0] + center;
                interVias.back().UpperMetalRect.originBox.UR = via_model.UpperRect[1] + center;
                interVias.back().UpperMetalRect.metal = DRC_info.Metal_info[via_model.UpperIdx].name;
              } else if (tapVia) {
                tapVias.push_back(oBox);
                tapVia = false;
              } else if (activeVia) {
                activeVias.push_back(oBox);
                activeVia = false;
              }
            }
          }
        } else if ((found = def.find(obsEnd)) != string::npos) {
          // cout<<"Stage "<<stage<<" @ port end "<<portEnd<<endl;
          stage = 1;
        }
      } else if (stage == 2) {  // within PIN
        if ((found = def.find("USE")) != string::npos) {
          temp = get_true_word(found, def, 0, ';', p);
          macroPins.back().use = temp[1];
        } else if ((found = def.find("DIRECTION")) != string::npos) {
          temp = get_true_word(found, def, 0, ';', p);
          macroPins.back().type = temp[1];
          // cout<<"Stage "<<stage<<" @ pin type"<<macroPins.back().type<<endl;
        } else if ((found = def.find("PORT")) != string::npos) {
          temp = get_true_word(found, def, 0, ';', p);
          // macroPins.back().pinContacts.resize( macroPins.back().pinContacts.size()+1 );
          // cout<<"Stage "<<stage<<" @ new contact for pin"<<endl;
          stage = 3;
        } else if ((found = def.find(pinEnd)) != string::npos) {
          // cout<<"Stage" << stage<<" @ pin end "<<pinEnd<<endl;
          stage = 1;
        }
      } else if (stage == 3) {  // within PORT
        if ((found = def.find("LAYER")) != string::npos) {
          // Metal_Flag = true;
          temp = get_true_word(found, def, 0, ';', p);
          char rect_type = temp[1].front();
          if(rect_type=='M'){
            Metal_Flag = true;
            macroPins.back().pinContacts.resize(macroPins.back().pinContacts.size() + 1);
            macroPins.back().pinContacts.back().metal = temp[1];
          }else{
            Metal_Flag = false;
          }
          // cout<<"Stage "<<stage<<" @ contact layer "<<macroPins.back().pinContacts.back().metal<<endl;
        } else if ((found = def.find("RECT")) != string::npos && Metal_Flag) {
          // Metal_Flag = true;
          temp = get_true_word(found, def, 0, ';', p);
          int LLx = parse_and_scale(temp[1], units);
          int LLy = parse_and_scale(temp[2], units);
          int URx = parse_and_scale(temp[3], units);
          int URy = parse_and_scale(temp[4], units);
          PnRDB::bbox oBox;
          PnRDB::point tp;
          tp.x = LLx;
          tp.y = LLy;
          oBox.LL = tp;
          tp.x = URx;
          tp.y = URy;
          oBox.UR = tp;
          macroPins.back().pinContacts.back().originBox = oBox;
          macroPins.back().pinContacts.back().originCenter.x = (LLx + URx) / 2;
          macroPins.back().pinContacts.back().originCenter.y = (LLy + URy) / 2;
          // cout<<"Stage "<<stage<<" @ bbox ";
          // for(vector<PnRDB::point>::iterator
          // it=macroPins.back().pinContacts.back().originBox.polygon.begin();it!=macroPins.back().pinContacts.back().originBox.polygon.end();++it)
          // {
          //  cout<<" {"<<it->x<<","<<it->y<<"}";
          //}
          // cout<<endl<<"Stage "<<stage<<" @ center
          // "<<macroPins.back().pinContacts.back().originCenter.x<<","<<macroPins.back().pinContacts.back().originCenter.y<<endl;
        } else if ((found = def.find(portEnd)) != string::npos) {
          // cout<<"Stage "<<stage<<" @ port end "<<portEnd<<endl;
          if (macroPins.back().pinContacts.size() == 0 || macroPins.back().pinContacts.back().metal == "") {
            logger->error("Error: LEF Physical Pin information Missing" );
            assert(0);
          }
          stage = 2;
        }
      }
    }
  }
}
