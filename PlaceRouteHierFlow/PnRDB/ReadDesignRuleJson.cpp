#include <time.h>

#include <fstream>
#include <iomanip>
#include <iostream>

#include "PnRdatabase.h"

using namespace nlohmann;
#define FinFET_MOCK_PDK
// uncomment the above line when using layer.json from FinFET_MOCK_PDK

void PnRdatabase::ReadPDKJSON(std::string drfile) {
  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.ReadPDKJSON");

  int times = 2;
  json jsonStrAry;
  ifstream jsonFile(drfile);
  if (jsonFile.is_open()) {
    json jedb = json::parse(jsonFile);
    json layerAry = jedb["Abstraction"];
    ScaleFactor = jedb["ScaleFactor"];
    DRC_info.ScaleFactor = ScaleFactor;
    // times *= ScaleFactor;
    std::map<int, PnRDB::metal_info> metalSet;
    std::map<int, PnRDB::via_info> viaSet;
    std::unordered_map<string, int> name2ViaLayerMap;
    // 1. Extract metal info
    int metal_index = 0;
    for (json::iterator lit = layerAry.begin(); lit != layerAry.end(); ++lit) {
      json layer = *lit;
      std::string lname = layer["Layer"];
      if (lname.front() == 'M') {
        metal_index = metal_index + 1;
        // metal layer
        metal_index = metal_index + 1;
#ifdef FinFET_MOCK_PDK
        // logger->debug("Reading Json PDK on {0}", lname);
        // logger->debug("Reading Json PDK on GdsLayerNo");
        int lnum = layer["GdsLayerNo"];
        int Drawnum = layer["GdsDatatype"]["Draw"];
        int Pinnum = layer["GdsDatatype"]["Pin"];
        int Labelnum = layer["GdsDatatype"]["Label"];
        int Blockagenum = layer["GdsDatatype"]["Blockage"];
#else
        int lnum = layer["LayerNo"];
#endif
        std::string ldir = layer["Direction"];
        int offset = layer["Offset"];
        int lpitch = -1;
        // logger->debug("Reading Json PDK on Pitch");
        json pdata = layer["Pitch"];
        if (pdata.is_array()) {
          json::iterator pit = pdata.begin();
          lpitch = (*pit);
        } else if (pdata.is_number()) {
          lpitch = pdata;
        }
        int lwidth = -1;
        // logger->debug("Reading Json PDK on Width");
        json wdata = layer["Width"];
        if (wdata.is_array()) {
          json::iterator wit = wdata.begin();
          lwidth = (*wit);
        } else if (wdata.is_number()) {
          lwidth = wdata;
        }
        // logger->debug("Reading Json PDK on MinL");
        int lminL = layer["MinL"];
        // int lmaxL=layer["MaxL"];
        // logger->debug("Reading Json PDK on EndToEnd");
        int le2e = layer["EndToEnd"];

        double unit_C = 0;
        double unit_CC = 0;
        double unit_R = 0;
        // logger->debug("Reading Json PDK on Units, C, CC, R");
#ifdef FinFET_MOCK_PDK
        if (layer["UnitC"]["Mean"].is_number()) {
          unit_C = layer["UnitC"]["Mean"];
        }
        if (layer["UnitCC"]["Mean"].is_number()) {
          unit_CC = layer["UnitCC"]["Mean"];
        }
        if (layer["UnitR"]["Mean"].is_number()) {
          unit_R = layer["UnitR"]["Mean"];
        }
#else
        if (layer["UnitC"].is_number()) {
          unit_C = layer["UnitC"];
        }
        if (layer["UnitR"].is_number()) {
          unit_R = layer["UnitR"];
        }
#endif

        PnRDB::metal_info tmp_metal;
        tmp_metal.name = lname;
        tmp_metal.layerNo = lnum;
#ifdef FinFET_MOCK_PDK
        tmp_metal.gds_datatype.Draw = Drawnum;
        tmp_metal.gds_datatype.Pin = Pinnum;
        tmp_metal.gds_datatype.Label = Labelnum;
        tmp_metal.gds_datatype.Blockage = Blockagenum;
#endif
        if (ldir.compare("V") == 0) {
          tmp_metal.direct = 0;
          tmp_metal.grid_unit_x = times * lpitch / ScaleFactor;
          tmp_metal.grid_unit_y = -1;
        } else if (ldir.compare("H") == 0) {
          tmp_metal.direct = 1;
          tmp_metal.grid_unit_y = times * lpitch / ScaleFactor;
          tmp_metal.grid_unit_x = -1;
        } else {
          logger->error("PnR-Error: incorrect metal direction");
        }
        tmp_metal.width = times * lwidth / ScaleFactor;
        tmp_metal.dist_ss = times * (lpitch - lwidth) / ScaleFactor;
        tmp_metal.minL = times * lminL / ScaleFactor;
        tmp_metal.dist_ee = times * le2e / ScaleFactor;
        tmp_metal.offset = times * offset / ScaleFactor;
        double rc_scale = 0.0005;
        tmp_metal.unit_R = unit_R * rc_scale;
        tmp_metal.unit_C = unit_C * rc_scale;
        tmp_metal.unit_CC = unit_CC * rc_scale;
        metalSet.insert(std::pair<int, PnRDB::metal_info>(metal_index, tmp_metal));
      }
    }
    for (std::map<int, PnRDB::metal_info>::iterator it = metalSet.begin(); it != metalSet.end(); ++it) {
      DRC_info.Metal_info.push_back(it->second);
      //cout << "Assign the metalmap[" << it->second.name << "] = " << DRC_info.Metal_info.size()-1 << endl;
      DRC_info.Metalmap[it->second.name] = DRC_info.Metal_info.size() - 1;
    }
    DRC_info.MaxLayer = DRC_info.Metal_info.size() - 1;

    // add Boundary
    for (json::iterator lit = layerAry.begin(); lit != layerAry.end(); ++lit) {
      json layer = *lit;
      std::string lname = layer["Layer"];
      if (lname.compare("Outline") == 0) {  //
        PnRDB::Boundary temp_boundary;
        temp_boundary.layerNo = layer["GdsLayerNo"];
        temp_boundary.gds_datatype.Draw = layer["GdsDatatype"]["Draw"];
        // temp_boundary.gds_datatype.Pin=layer["GdsDatatype"]["Pin"];
        // temp_boundary.gds_datatype.Label=layer["GdsDatatype"]["Label"];
        // temp_boundary.gds_datatype.Blockage=layer["GdsDatatype"]["Blockage"];
        DRC_info.top_boundary = temp_boundary;
      }
    }

    // std::cout<<"Boundary test "<<DRC_info.top_boundary.name<<" "<<DRC_info.top_boundary.layerNo<<" "<<DRC_info.top_boundary.gds_datatype.Draw<<std::endl;

    // 2. Extract via info
    int via_index = 0;
    for (json::iterator lit = layerAry.begin(); lit != layerAry.end(); ++lit) {
      json layer = *lit;
      std::string lname = layer["Layer"];
      if (lname.front() == 'V') {
        via_index = via_index + 1;
        // via layer
        via_index = via_index + 1;
        // logger->debug("Reading Json PDK on {0}", lname);
#ifdef FinFET_MOCK_PDK
        // logger->debug("Reading Json PDK on GdsLayerNo");
        int lnum = layer["GdsLayerNo"];
        int Drawnum = layer["GdsDatatype"]["Draw"];
#else
        int lnum = layer["LayerNo"];
#endif
        // std::cout<<"Reading Json PDK on "<<"Stack"<<std::endl;
        json stackAry = layer["Stack"];
        // std::cout<<"Reading Json PDK on "<<"WidthX"<<std::endl;
        int lwidthx = layer["WidthX"];
        // std::cout<<"Reading Json PDK on "<<"WidthY"<<std::endl;
        int lwidthy = layer["WidthY"];
        // std::cout<<"Reading Json PDK on "<<"SpaceX"<<std::endl;
        int lspacex = layer["SpaceX"];
        // std::cout<<"Reading Json PDK on "<<"SpaceY"<<std::endl;
        int lspacey = layer["SpaceY"];
        // std::cout<<"Reading Json PDK on "<<"VencA_L"<<std::endl;
        int lvencal = layer["VencA_L"];
        // std::cout<<"Reading Json PDK on "<<"VencA_H"<<std::endl;
        int lvencah = layer["VencA_H"];
        // std::cout<<"Reading Json PDK on "<<"VencP_L"<<std::endl;
        int lvencpl = layer["VencP_L"];
        // std::cout<<"Reading Json PDK on "<<"VencP_H"<<std::endl;
        int lvencph = layer["VencP_H"];

        double R = 0;
#ifdef FinFET_MOCK_PDK
        if (layer["R"]["Mean"].is_number()) {
          R = layer["R"]["Mean"];
        }
#else
        if (layer["R"].is_number()) {
          R = layer["R"];
        }
#endif

        PnRDB::via_info tmp_via;
        tmp_via.name = lname;
        tmp_via.layerNo = lnum;
#ifdef FinFET_MOCK_PDK
        tmp_via.gds_datatype.Draw = Drawnum;
#endif
        tmp_via.width = times * lwidthx / ScaleFactor;
        tmp_via.width_y = times * lwidthy / ScaleFactor;
        tmp_via.cover_l = times * lvencal / ScaleFactor;
        tmp_via.cover_l_P = times * lvencpl / ScaleFactor;
        tmp_via.cover_u = times * lvencah / ScaleFactor;
        tmp_via.cover_u_P = times * lvencph / ScaleFactor;
        tmp_via.dist_ss = times * lspacex / ScaleFactor;
        tmp_via.dist_ss_y = times * lspacey / ScaleFactor;
        tmp_via.R = R;
        {
          assert(stackAry.size() == 2);

          std::vector<int> metal_stack_indices(2, -1);  // size=2, default=-1

          for (unsigned int i = 0; i < 2; ++i) {
            auto& s = stackAry[i];
            if (s.is_string()) {
              metal_stack_indices[i] = DRC_info.Metalmap[s];  // get via's upper and lower metal name by via's Stack
            } else {
              // cout << "Null metal for via " << tmp_via.name << " pos " << i << endl;
            }
          }

          if (metal_stack_indices[0] != -1 && metal_stack_indices[1] != -1) {
            tmp_via.lower_metal_index = metal_stack_indices[0];
            tmp_via.upper_metal_index = metal_stack_indices[1];
            assert(viaSet.find(lnum) == viaSet.end());
            viaSet.insert(std::pair<int, PnRDB::via_info>(via_index, tmp_via));
            assert(name2ViaLayerMap.find(tmp_via.name) == name2ViaLayerMap.end());
            name2ViaLayerMap[tmp_via.name] = via_index;
          }
        }
      }
    }

    for (std::map<int, PnRDB::via_info>::iterator it = viaSet.begin(); it != viaSet.end(); ++it) {
      DRC_info.Via_info.push_back(it->second);
      //cout << "Assign the Viamap[" << it->second.name << "] = " << DRC_info.Via_info.size()-1 << endl;
      DRC_info.Viamap[it->second.name] = DRC_info.Via_info.size() - 1;
    }

    // extract information for guard ring
    for (json::iterator lit = layerAry.begin(); lit != layerAry.end(); ++lit) {
      json layer = *lit;
      std::string lname = layer["Layer"];
      if (lname.compare("GuardRing") == 0) {  //
        PnRDB::guardring_info temp_guardring_info;
        // temp_boundary.layerNo = layer["GdsLayerNo"];
        // temp_guardring_info.gds_datatype.Draw=layer["GdsDatatype"]["Draw"];
        // temp_boundary.gds_datatype.Pin=layer["GdsDatatype"]["Pin"];
        // temp_boundary.gds_datatype.Label=layer["GdsDatatype"]["Label"];
        // temp_boundary.gds_datatype.Blockage=layer["GdsDatatype"]["Blockage"];
        temp_guardring_info.xspace = layer["XSpace"];
        temp_guardring_info.yspace = layer["YSpace"];
        temp_guardring_info.xspace *= times;
        temp_guardring_info.xspace /= ScaleFactor;
        temp_guardring_info.yspace *= times;
        temp_guardring_info.yspace /= ScaleFactor;
        DRC_info.Guardring_info = temp_guardring_info;
      }
    }

    // 3. Add metal weight
    // add
    for (unsigned int i = 0; i < DRC_info.Metal_info.size(); i++) {
      DRC_info.metal_weight.push_back(1);
    }
    // 4. Add Via model
    for (unsigned int i = 0; i < DRC_info.Via_info.size(); i++) {
      PnRDB::ViaModel temp_viamodel;

      temp_viamodel.name = DRC_info.Via_info[i].name;
      const auto& vs = viaSet[name2ViaLayerMap[temp_viamodel.name]];

      temp_viamodel.ViaIdx = i;
      temp_viamodel.LowerIdx = vs.lower_metal_index;
      temp_viamodel.UpperIdx = vs.upper_metal_index;

      // const string& lm_name = DRC_info.Metal_info.at(temp_viamodel.LowerIdx).name;
      // const string& um_name = DRC_info.Metal_info.at(temp_viamodel.UpperIdx).name;

      // cout << "Via " << temp_viamodel.name << " ViaIndex " << temp_viamodel.ViaIdx << " LowerIdx " << temp_viamodel.LowerIdx << " (" << lm_name << ")
      // UpperIdx " << temp_viamodel.UpperIdx << " (" << um_name << ")" << endl;

      PnRDB::point temp_point;
      auto& vi = DRC_info.Via_info[temp_viamodel.ViaIdx];
      // LL
      temp_point.x = 0 - vi.width / 2;
      temp_point.y = 0 - vi.width_y / 2;
      temp_viamodel.ViaRect.push_back(temp_point);
      // UR
      temp_point.x = 0 + vi.width / 2;
      temp_point.y = 0 + vi.width_y / 2;
      temp_viamodel.ViaRect.push_back(temp_point);
      temp_viamodel.R = vi.R;
      /*
                   {
                     auto& mi = DRC_info.Metal_info[temp_viamodel.LowerIdx];
                     //LL LowerRect
                     if(mi.direct==0){
                       temp_point.x = 0-mi.width/2-vi.cover_l_P;
                       temp_point.y = 0-mi.width/2-vi.cover_l;
                       temp_viamodel.LowerRect.push_back(temp_point);
                       //UR
                       temp_point.x = 0+mi.width/2+vi.cover_l_P;
                       temp_point.y = 0+mi.width/2+vi.cover_l;
                       temp_viamodel.LowerRect.push_back(temp_point);
                     }else{
                       temp_point.y = 0-mi.width/2-vi.cover_l_P;
                       temp_point.x = 0-mi.width/2-vi.cover_l;
                       temp_viamodel.LowerRect.push_back(temp_point);
                       //UR
                       temp_point.y = 0+mi.width/2+vi.cover_l_P;
                       temp_point.x = 0+mi.width/2+vi.cover_l;
                       temp_viamodel.LowerRect.push_back(temp_point);
                     }
                   }

                   {
                     auto& mi = DRC_info.Metal_info[temp_viamodel.UpperIdx];

                     //LL UpperRect
                     if(mi.direct==0){
                       temp_point.x = 0-mi.width/2-vi.cover_u_P;
                       temp_point.y = 0-mi.width/2-vi.cover_u;
                       temp_viamodel.UpperRect.push_back(temp_point);
                       //UR
                       temp_point.x = 0+mi.width/2+vi.cover_u_P;
                       temp_point.y = 0+mi.width/2+vi.cover_u;
                       temp_viamodel.UpperRect.push_back(temp_point);
                     }else{
                       temp_point.y = 0-mi.width/2-vi.cover_u_P;
                       temp_point.x = 0-mi.width/2-vi.cover_u;
                       temp_viamodel.UpperRect.push_back(temp_point);
                       //UR
                       temp_point.y = 0+mi.width/2+vi.cover_u_P;
                       temp_point.x = 0+mi.width/2+vi.cover_u;
                       temp_viamodel.UpperRect.push_back(temp_point);
                     }
                     DRC_info.Via_model.push_back(temp_viamodel);
                   }
      */
      {
        auto& mi = DRC_info.Metal_info[temp_viamodel.LowerIdx];
        int width = mi.width;
        // LL LowerRect
        if (mi.direct == 0) {  // Vertical metal
          temp_point.x = std::min(0 - vi.width / 2 - vi.cover_l_P, -width / 2);
          temp_point.y = 0 - vi.width_y / 2 - vi.cover_l;
          temp_viamodel.LowerRect.push_back(temp_point);
          // UR
          temp_point.x = std::max(0 + vi.width / 2 + vi.cover_l_P, width / 2);
          temp_point.y = 0 + vi.width_y / 2 + vi.cover_l;
          temp_viamodel.LowerRect.push_back(temp_point);
        } else {  // Horizontal metal
          temp_point.y = std::min(0 - vi.width_y / 2 - vi.cover_l_P, -width / 2);
          temp_point.x = 0 - vi.width / 2 - vi.cover_l;
          temp_viamodel.LowerRect.push_back(temp_point);
          // UR
          temp_point.y = std::max(0 + vi.width_y / 2 + vi.cover_l_P, width / 2);
          temp_point.x = 0 + vi.width / 2 + vi.cover_l;
          temp_viamodel.LowerRect.push_back(temp_point);
        }
      }

      {
        auto& mi = DRC_info.Metal_info[temp_viamodel.UpperIdx];
        int width = mi.width;
        // LL UpperRect
        if (mi.direct == 0) {
          temp_point.x = std::min(0 - vi.width / 2 - vi.cover_u_P, -width / 2);
          temp_point.y = 0 - vi.width_y / 2 - vi.cover_u;
          temp_viamodel.UpperRect.push_back(temp_point);
          // UR
          temp_point.x = std::max(0 + vi.width / 2 + vi.cover_u_P, width / 2);
          temp_point.y = 0 + vi.width_y / 2 + vi.cover_u;
          temp_viamodel.UpperRect.push_back(temp_point);
        } else {
          temp_point.y = std::min(0 - vi.width_y / 2 - vi.cover_u_P, -width / 2);
          temp_point.x = 0 - vi.width / 2 - vi.cover_u;
          temp_viamodel.UpperRect.push_back(temp_point);
          // UR
          temp_point.y = std::max(0 + vi.width_y / 2 + vi.cover_u_P, width / 2);
          temp_point.x = 0 + vi.width / 2 + vi.cover_u;
          temp_viamodel.UpperRect.push_back(temp_point);
        }
        DRC_info.Via_model.push_back(temp_viamodel);
      }
    }
    // 6. Add mask ID
    // added by wbxu
    for (unsigned int i = 0; i < DRC_info.Metal_info.size(); ++i) {
      DRC_info.MaskID_Metal.push_back(std::to_string(DRC_info.Metal_info.at(i).layerNo));
    }
    for (unsigned int i = 0; i < DRC_info.Via_info.size(); ++i) {
      DRC_info.MaskID_Via.push_back(std::to_string(DRC_info.Via_info.at(i).layerNo));
    }

    // 7. read design info
    // first init hspace and vspace
    if (DRC_info.Metal_info[0].direct == 1) {  // horizontal
      DRC_info.Design_info.Vspace = DRC_info.Metal_info[0].grid_unit_y;
    } else {
      DRC_info.Design_info.Hspace = DRC_info.Metal_info[0].grid_unit_x;
    }
    if (DRC_info.Metal_info[1].direct == 1) {  // horizontal
      DRC_info.Design_info.Vspace = DRC_info.Metal_info[1].grid_unit_y;
    } else {
      DRC_info.Design_info.Hspace = DRC_info.Metal_info[1].grid_unit_x;
    }
    // then read them
    if (jedb.contains("design_info")) {
      json design_info = jedb["design_info"];
      DRC_info.Design_info.Hspace = design_info["Hspace"];
      DRC_info.Design_info.Vspace = design_info["Vspace"];
      DRC_info.Design_info.Hspace *= times;
      DRC_info.Design_info.Hspace /= ScaleFactor;
      DRC_info.Design_info.Vspace *= times;
      DRC_info.Design_info.Vspace /= ScaleFactor;
      DRC_info.Design_info.signal_routing_metal_l = DRC_info.Metalmap[design_info["bottom_signal_routing_layer"]];
      DRC_info.Design_info.signal_routing_metal_u = DRC_info.Metalmap[design_info["top_signal_routing_layer"]];
      DRC_info.Design_info.power_routing_metal_l = DRC_info.Metalmap[design_info["bottom_power_routing_layer"]];
      DRC_info.Design_info.power_routing_metal_u = DRC_info.Metalmap[design_info["top_power_routing_layer"]];

      DRC_info.Design_info.h_skip_factor = 7;
      DRC_info.Design_info.v_skip_factor = 8;
      if (design_info.contains("h_skip_factor")) {
        DRC_info.Design_info.h_skip_factor = design_info["h_skip_factor"];
      }
      if (design_info.contains("v_skip_factor")) {
        DRC_info.Design_info.v_skip_factor = design_info["v_skip_factor"];
      }
      if (design_info.contains("compact_placement")) {
        DRC_info.Design_info.compact_style = design_info["compact_placement"];
      }

      DRC_info.Design_info.power_grid_metal_l = DRC_info.Metalmap[design_info["top_power_routing_layer"]] - 1;
      DRC_info.Design_info.power_grid_metal_u = DRC_info.Metalmap[design_info["top_power_routing_layer"]];
      if (design_info.contains("bottom_power_grid_layer")) {
        DRC_info.Design_info.power_grid_metal_l = DRC_info.Metalmap[design_info["bottom_power_grid_layer"]];
      }
      if (design_info.contains("top_power_grid_layer")) {
        DRC_info.Design_info.power_grid_metal_u = DRC_info.Metalmap[design_info["top_power_grid_layer"]];
      }

      // std::cout<<"design info "<<DRC_info.Design_info.signal_routing_metal_l<<" "<<DRC_info.Design_info.signal_routing_metal_u<<"
      // "<<DRC_info.Design_info.power_grid_metal_l<<" "<<DRC_info.Design_info.power_grid_metal_u<<" "<<DRC_info.Design_info.power_routing_metal_l<<"
      // "<<DRC_info.Design_info.power_routing_metal_u<<std::endl;
    }
  }
}
