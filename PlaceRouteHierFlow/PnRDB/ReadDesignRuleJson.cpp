#include "PnRdatabase.h"

#include <iostream>
#include <fstream>
#include <iomanip>
#include <time.h>

using namespace nlohmann;


void PnRdatabase::ReadPDKJSON(std::string drfile) {
    int times=2;
    json jsonStrAry;
    ifstream jsonFile (drfile);
    if (jsonFile.is_open()) {
	json jedb = json::parse (jsonFile);
        json layerAry = jedb["Abstraction"];
        std::map<int, PnRDB::metal_info> metalSet;
        std::map<int, PnRDB::via_info> viaSet;
        std::unordered_map<string, int> name2ViaLayerMap;
        // 1. Extract metal info
        for(json::iterator lit = layerAry.begin(); lit != layerAry.end(); ++lit) {
          json layer = *lit;
          std::string lname=layer["Layer"];
          if(lname.front()=='M') {
            // metal layer
            int lnum=layer["LayerNo"];
            std::string ldir=layer["Direction"];
            int lpitch=-1;
            json pdata=layer["Pitch"];
            if(pdata.is_array()) {
              json::iterator pit=pdata.begin();
              lpitch=(*pit);
            } else if (pdata.is_number()) {
              lpitch=pdata;
            }
            int lwidth=-1;
            json wdata=layer["Width"];
            if(wdata.is_array()) {
              json::iterator wit=wdata.begin();
              lwidth=(*wit);
            } else if (wdata.is_number()) {
              lwidth=wdata;
            }
            int lminL=layer["MinL"];
            //int lmaxL=layer["MaxL"];
            int le2e=layer["EndToEnd"];

            double unit_C = 0;
            if(layer["UnitC"].is_number()){unit_C=layer["UnitC"];}
            double unit_R = 0;
            if(layer["UnitR"].is_number()){unit_R=layer["UnitR"];}

            PnRDB::metal_info tmp_metal;
            tmp_metal.name=lname;
            tmp_metal.layerNo=lnum;
            if(ldir.compare("V")==0) { tmp_metal.direct=0; tmp_metal.grid_unit_x=times*lpitch; tmp_metal.grid_unit_y=-1;
            } else if (ldir.compare("H")==0) { tmp_metal.direct=1; tmp_metal.grid_unit_y=times*lpitch; tmp_metal.grid_unit_x=-1;
            } else {std::cout<<"PnR-Error: incorrect metal direction\n";}
            tmp_metal.width=times*lwidth;
            tmp_metal.dist_ss=times*(lpitch-lwidth);
            tmp_metal.minL=times*lminL;
            tmp_metal.dist_ee=times*le2e;
            double rc_scale = 0.0005;
            tmp_metal.unit_R = unit_R*rc_scale;
            tmp_metal.unit_C = unit_C*rc_scale;
            metalSet.insert( std::pair<int, PnRDB::metal_info>(lnum, tmp_metal) );
            }
        }
        for(std::map<int, PnRDB::metal_info>::iterator it=metalSet.begin(); it!=metalSet.end(); ++it) {
          DRC_info.Metal_info.push_back(it->second);
	  cout << "Assign the metalmap[" << it->second.name << "] = " << DRC_info.Metal_info.size()-1 << endl;
          DRC_info.Metalmap[it->second.name] = DRC_info.Metal_info.size()-1;
        }
        DRC_info.MaxLayer = DRC_info.Metal_info.size()-1;
        // 2. Extract via info
        for(json::iterator lit = layerAry.begin(); lit != layerAry.end(); ++lit) {
          json layer = *lit;
          std::string lname=layer["Layer"];
          if(lname.front()=='V') {
            // via layer
            int lnum=layer["LayerNo"];
            json stackAry = layer["Stack"];
            int lwidthx= layer["WidthX"];
            int lwidthy= layer["WidthY"];
            int lspacex= layer["SpaceX"];
            int lspacey= layer["SpaceY"];
            int lvencal= layer["VencA_L"];
            int lvencah= layer["VencA_H"];
            int lvencpl= layer["VencP_L"];
            int lvencph= layer["VencP_H"];

            double R = 0;
            if(layer["R"].is_number()){R=layer["R"];}
            
            PnRDB::via_info tmp_via;
            tmp_via.name=lname;
            tmp_via.layerNo=lnum;
            tmp_via.width=times*lwidthx;
            tmp_via.width_y=times*lwidthy;
            tmp_via.cover_l=times*lvencal;
            tmp_via.cover_l_P=times*lvencpl;
            tmp_via.cover_u=times*lvencah;
            tmp_via.cover_u_P=times*lvencph;
            tmp_via.dist_ss=times*lspacex;
            tmp_via.dist_ss_y=times*lspacey;
            tmp_via.R = R;
	    {
	      assert( stackAry.size() == 2);

	      std::vector<int> metal_stack_indices(2,-1); // size=2, default=-1

	      for (unsigned int i=0; i<2; ++i) {
		auto& s = stackAry[i];
		if(s.is_string()) {
		  metal_stack_indices[i] = DRC_info.Metalmap[s];
		} else {
		  cout << "Null metal for via " << tmp_via.name << " pos " << i << endl;
		}
	      }

	      if ( metal_stack_indices[0] != -1 &&
		   metal_stack_indices[1] != -1) {
		tmp_via.lower_metal_index = metal_stack_indices[0];
		tmp_via.upper_metal_index = metal_stack_indices[1];
		assert( viaSet.find( lnum) == viaSet.end());
		viaSet.insert( std::pair<int, PnRDB::via_info>(lnum, tmp_via) );
		assert( name2ViaLayerMap.find( tmp_via.name) == name2ViaLayerMap.end());
		name2ViaLayerMap[tmp_via.name] = lnum;
	      }
	    }
          }
        }
        for(std::map<int, PnRDB::via_info>::iterator it=viaSet.begin(); it!=viaSet.end(); ++it) {
          DRC_info.Via_info.push_back(it->second);
          DRC_info.Viamap[it->second.name] = DRC_info.Via_info.size()-1;
        }

        // 3. Add metal weight
        //add
        for(unsigned int i=0;i<DRC_info.Metal_info.size();i++){
             DRC_info.metal_weight.push_back(1);
        }
        // 4. Add Via model
        for(unsigned int i=0;i<DRC_info.Via_info.size();i++){
             PnRDB::ViaModel temp_viamodel;

             temp_viamodel.name = DRC_info.Via_info[i].name;
	     const auto &vs = viaSet[name2ViaLayerMap[temp_viamodel.name]];

             temp_viamodel.ViaIdx = i;
             temp_viamodel.LowerIdx = vs.lower_metal_index;
             temp_viamodel.UpperIdx = vs.upper_metal_index;

	     const string& lm_name = DRC_info.Metal_info.at(temp_viamodel.LowerIdx).name;
	     const string& um_name = DRC_info.Metal_info.at(temp_viamodel.UpperIdx).name;

	     cout << "Via " << temp_viamodel.name << " ViaIndex " << temp_viamodel.ViaIdx << " LowerIdx " << temp_viamodel.LowerIdx << " (" << lm_name << ") UpperIdx " << temp_viamodel.UpperIdx << " (" << um_name << ")" << endl;

             PnRDB::point temp_point;
	     auto& vi = DRC_info.Via_info[temp_viamodel.ViaIdx];
             //LL
             temp_point.x = 0-vi.width/2;
             temp_point.y = 0-vi.width_y/2;
             temp_viamodel.ViaRect.push_back(temp_point);
             //UR
             temp_point.x = 0+vi.width/2;
             temp_point.y = 0+vi.width_y/2;
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
	       //LL LowerRect
	       if(mi.direct==0){
		 temp_point.x = 0-vi.width/2-vi.cover_l_P;
		 temp_point.y = 0-vi.width_y/2-vi.cover_l;
		 temp_viamodel.LowerRect.push_back(temp_point);
		 //UR
		 temp_point.x = 0+vi.width/2+vi.cover_l_P;
		 temp_point.y = 0+vi.width_y/2+vi.cover_l;
		 temp_viamodel.LowerRect.push_back(temp_point);
	       }else{
		 temp_point.y = 0-vi.width_y/2-vi.cover_l_P;
		 temp_point.x = 0-vi.width/2-vi.cover_l;
		 temp_viamodel.LowerRect.push_back(temp_point);
		 //UR
		 temp_point.y = 0+vi.width_y/2+vi.cover_l_P;
		 temp_point.x = 0+vi.width/2+vi.cover_l;
		 temp_viamodel.LowerRect.push_back(temp_point);
	       } 
	     }
             
	     {
	       auto& mi = DRC_info.Metal_info[temp_viamodel.UpperIdx];

	       //LL UpperRect
	       if(mi.direct==0){
		 temp_point.x = 0-vi.width/2-vi.cover_u_P;
		 temp_point.y = 0-vi.width_y/2-vi.cover_u;
		 temp_viamodel.UpperRect.push_back(temp_point);
		 //UR
		 temp_point.x = 0+vi.width/2+vi.cover_u_P;
		 temp_point.y = 0+vi.width_y/2+vi.cover_u;
		 temp_viamodel.UpperRect.push_back(temp_point);
	       }else{
		 temp_point.y = 0-vi.width_y/2-vi.cover_u_P;
		 temp_point.x = 0-vi.width/2-vi.cover_u;
		 temp_viamodel.UpperRect.push_back(temp_point);
		 //UR
		 temp_point.y = 0+vi.width_y/2+vi.cover_u_P;
		 temp_point.x = 0+vi.width/2+vi.cover_u;
		 temp_viamodel.UpperRect.push_back(temp_point);
	       } 
	       DRC_info.Via_model.push_back(temp_viamodel);
	     }
	}
        // 6. Add mask ID
        //added by wbxu
        for(unsigned int i=0;i<DRC_info.Metal_info.size();++i) {
          DRC_info.MaskID_Metal.push_back(std::to_string( DRC_info.Metal_info.at(i).layerNo ));
        }
        for(unsigned int i=0;i<DRC_info.Via_info.size();++i) {
          DRC_info.MaskID_Via.push_back(std::to_string( DRC_info.Via_info.at(i).layerNo ));
        }
    }
}
