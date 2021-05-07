#include "capplacer.h"
#include <iomanip>
#include <nlohmann/json.hpp>
#include <cassert>
#include <utility>
#include "spdlog/spdlog.h"
#include <algorithm>
#include <unordered_set>

using namespace std;
using namespace nlohmann;

ostream & operator<< (ostream& os, const PnRDB::point& p) {
    os << "(" << p.x << ", " << p.y << ")";
    return os;
}
ostream & operator<< (ostream& os, const PnRDB::bbox& p) {
    os << "[" << p.LL << ", " << p.UR << "]";
    return os;
}
ostream & operator<< (ostream& os, int vec[5]) {
    os << "[";
    for (unsigned i = 0; i < 5; i++) {
	if (i > 0) os << ", ";
	os << vec[i];
    }
    os << "]";
    return os;
}

json
ToJsonAry (const PnRDB::bbox& box) {
    json xy = json::array();
    xy.push_back (box.LL.x);    xy.push_back (box.LL.y);
    xy.push_back (box.LL.x);    xy.push_back (box.UR.y);
    xy.push_back (box.UR.x);    xy.push_back (box.UR.y);
    xy.push_back (box.UR.x);    xy.push_back (box.LL.y);
    xy.push_back (box.LL.x);    xy.push_back (box.LL.y);
    return xy;
}

json
ToJsonAry (const PnRDB::point& p0, const PnRDB::point& p1) {
    json xy = json::array();
    xy.push_back (p0.x);    xy.push_back (p0.y);
    xy.push_back (p1.x);    xy.push_back (p1.y);
    return xy;
}
    
// These are in PnRDB
extern unsigned short JSON_Presentation (int font, int vp, int hp);
extern unsigned short JSON_STrans (bool reflect, bool abs_angle, bool abs_mag);
extern json JSON_TimeTime ();

Placer_Router_Cap::Placer_Router_Cap(const string& opath, const string& fpath, PnRDB::hierNode & current_node,
				     PnRDB::Drc_info &drc_info,
				     const map<string, PnRDB::lefMacro> &lefData,
				     bool aspect_ratio, int num_aspect){

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.Placer_Router_Cap");

    logger->debug("Begin CC Capacitor Placement and Router");
    Common_centroid_capacitor_aspect_ratio(opath, fpath, current_node, drc_info, lefData, aspect_ratio, num_aspect);
    logger->debug("End CC Capacitor Placement and Router");
}

void Placer_Router_Cap::Placer_Router_Cap_clean(){

    CheckOutBlock = PnRDB::block();

    metal_width.clear();

    metal_direct.clear();

    metal_distance_ss.clear();

    //  via_width_x.clear();

    //  via_width_y.clear();

    //  via_cover_l.clear();

    //  via_cover_u.clear();

    Caps.clear();

    cap_pair_sequence.clear();

    net_sequence.clear();

    num_router_net_v.clear();

    num_router_net_h.clear();

    Nets_pos.clear();

    Nets_neg.clear();
}


void
Placer_Router_Cap::Placer_Router_Cap_function (vector<int> & ki, vector<pair<string, string> > &cap_pin,
					       const string& fpath, const string& unit_capacitor,
					       const string& final_gds,
					       bool cap_ratio, int cap_r, int cap_s,
					       const PnRDB::Drc_info& drc_info,
					       const map<string, PnRDB::lefMacro>& lefData,
					       bool dummy_flag, const string& opath) {

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.Placer_Router_Cap_function");

    //dummy_flag is 1, dummy capacitor is added; Else, dummy capacitor do not exist.
    //not added, needed to be added 

    //initial DRC router

    //from lef file readin cap demension
    logger->debug("CC Capacitor Debug flag step1");
    string H_metal;
    int H_metal_index=-1;
    string V_metal;
    int V_metal_index=-1;

    string HV_via_metal;
    int HV_via_metal_index=-1;

    vector<string> obs;

    unordered_set<string> obs_map;
    logger->debug("CC Capacitor Debug flag step2");
    logger->debug("Unit cap name {0}",unit_capacitor);
    if(lefData.find(unit_capacitor)==lefData.end()){
      logger->error("Unit cap error, check unit cap in lef, gds, and const file");
      assert(0);
     }
    const auto &uc = lefData.at(unit_capacitor);
    
    for(unsigned int i=0;i<uc.interMetals.size();i++){
	obs_map.insert( uc.interMetals[i].metal);
	if( std::find( obs.begin(), obs.end(), uc.interMetals[i].metal) == obs.end()) {
	    obs.push_back(uc.interMetals[i].metal);
	}
    }
    logger->debug("CC Capacitor Debug flag step2");
    assert( obs_map.size() == obs.size());

    unit_cap_dim = PnRDB::point (uc.width, uc.height);
    std::cout<<"uc.width "<<uc.width<<"uc.height "<<uc.height<<std::endl;

    PnRDB::point pin_min (INT_MAX, INT_MAX);
    string pin_metal;
    logger->debug("CC Capacitor Debug flag step3");
    /*
     * SMB: This does something weird
     * it updates the LL if both the x && y coords are less than the previous best
     * So not necessarily the smallest x or the smallest y
     */
    
    for(unsigned int i=0;i<uc.macroPins.size();i++){
	for(unsigned int j=0;j<uc.macroPins[i].pinContacts.size();j++){
	    const auto& pc = uc.macroPins[i].pinContacts[j];
	    const auto& r = pc.originBox.LL;
            logger->debug("Cand {0} {1}", r.x, r.y);
	    if(r.x<=pin_min.x && r.y<=pin_min.y){
		pin_min = r;
		pin_metal = pc.metal;
	    }
	}
    }
    logger->debug("Found pin_minx {0} pin_miny {1}", pin_min.x, pin_min.y);
	  
    //determine which three layer are used for routing metal
	  
    const auto& mm = drc_info.Metalmap.at(pin_metal);

    auto setup = [&]( auto& this_metal, auto& this_metal_idx, auto& other_metal, auto& other_metal_idx) {
	this_metal = pin_metal;
	this_metal_idx = mm;
	if(mm>0){ // metal pin has metal - 1 and
	    other_metal_idx = mm-1;
	}else{
	    other_metal_idx = mm+1;
	}
	other_metal = drc_info.Metal_info.at(other_metal_idx).name;
    };


    if(drc_info.Metal_info.at(mm).direct == 1){ // metal pin is H
	setup( H_metal, H_metal_index, V_metal, V_metal_index);
    }else{
	setup( V_metal, V_metal_index, H_metal, H_metal_index);
    }
	  
    if(H_metal_index>V_metal_index){
	HV_via_metal = V_metal;
	HV_via_metal_index = V_metal_index;
    }else{
	HV_via_metal = H_metal;
	HV_via_metal_index = H_metal_index;
    }

#if 0
    // Experimental; has fixed bugs in the past
    //round up to grid size
    // DAK:  Use SnapUp()
    auto roundup = []( int& v, int pitch) {
	v = pitch*((v+pitch-1)/pitch);
    };

    //  roundup( unit_cap_demension.first, drc_info.Metal_info.at(V_metal_index).grid_unit_x);
    //  roundup( unit_cap_demension.second, drc_info.Metal_info.at(H_metal_index).grid_unit_y);
#endif

    assert (unit_cap_dim.x % 2 == 0);
    assert (unit_cap_dim.y % 2 == 0);

    const auto& mv = drc_info.Metalmap.at(HV_via_metal);
    const auto& mvm = drc_info.Via_model.at(mv);
    if(mvm.LowerIdx==mm){
	shifting = pin_min - mvm.LowerRect[0];;
    }else if(mvm.UpperIdx==mm){
	shifting = pin_min - mvm.UpperRect[0];
    }
    logger->debug("pin_minx {0} pin_miny {1} shifting_x {2} shifting_y {3} H_metal {4} V_metal {5} HV_via_metal {6}", pin_min.x, pin_min.y, shifting.x, shifting.y, H_metal, V_metal, HV_via_metal);

    offset = PnRDB::point (0, 0);
  
    for(unsigned int i=0;i<drc_info.Metal_info.size();i++){
	metal_width.push_back(drc_info.Metal_info.at(i).width); //change 
	metal_width[i] = metal_width[i] / 2;
	metal_distance_ss.push_back(drc_info.Metal_info.at(i).dist_ss); //change //72
	metal_distance_ss[i] = metal_distance_ss[i]/2;
	metal_direct.push_back(drc_info.Metal_info.at(i).direct);
    }


    min_dis = PnRDB::point ((drc_info.Metal_info.at(V_metal_index).width
			     + drc_info.Metal_info.at(V_metal_index).dist_ss),
			    (drc_info.Metal_info.at(H_metal_index).width
			     + drc_info.Metal_info.at(H_metal_index).dist_ss)) * 2;


    span_dist = min_dis;
    span_dist.scale (1, 3); // m1 distance

    logger->debug("span_dist {0} {1}", span_dist.x, span_dist.y);

    //initial cap information

    double r;
    double s;

    if(cap_ratio==1){ //cap_ratio = 1, pass the ratio by user otherwise calculate it by the code
	r = cap_r;
	s = cap_s;
    } else { // compute r and making it as square as possible
	double sum = std::accumulate( ki.begin(), ki.end(), 0);
	r = ceil(sqrt(sum));
	s = ceil(sum/r);
    }

    //for dummy caps
    if(dummy_flag){
	r += 2;
	s += 2;
    }


    for(int i=0;i<(int) r;i++){
	for(int j=0;j<(int) s;j++){
	    cap temp_cap;
	    temp_cap.index_x=(double) i;
	    temp_cap.index_y=(double) j;
	    PnRDB::point cap_dim = unit_cap_dim + span_dist;
	    temp_cap.pos = PnRDB::bbox(unit_cap_dim).center() + cap_dim.scale(i, j);
	    temp_cap.net_index = -1;
	    temp_cap.access = 0;
	    Caps.push_back(temp_cap);
	}
    }

    //initial cap_pair_sequence
    double Cx = (r-1)/2;
    double Cy = (s-1)/2;
    vector<double> dis;
    vector<int> index;
    for(unsigned int i=0;i<Caps.size();i++){
        double distance = sqrt((Caps[i].index_x-Cx)*(Caps[i].index_x-Cx)+(Caps[i].index_y-Cy)*(Caps[i].index_y-Cy));
        dis.push_back(distance);
        index.push_back(i);
    }
    //sort the distance
    for(unsigned int i=0;i<dis.size();i++){
	for(unsigned int j=i+1;j<dis.size();j++){
	    if(dis[index[i]]>dis[index[j]]){
		std::swap( index[i], index[j]);
	    }
	}
    }
    // this doesn't replace the above
    //  std::stable_sort( index.begin(), index.end(), [&](int i, int j) { return dis[i] < dis[j]; });

    //generate the cap pair sequence

    if (index.size()==1) {
	cap_pair_sequence.push_back(make_pair( index[0], -1));
    } else {
    
	int start_index=0;
	if(dis[index[0]]<dis[index[1]]){
	    cap_pair_sequence.push_back(make_pair( index[0], -1));
	    start_index = 1;
	}

	//inital the rest pair sequence based on counterclockwise
	for(unsigned int i=start_index;i<dis.size();i++){
	    for(unsigned int j=i+1;j<dis.size();j++){
		if(dis[index[i]]!=dis[index[j]]){
		    break;
		}
		if (Caps[index[i]].index_x+Caps[index[j]].index_x==2*Cx &&
		    Caps[index[i]].index_y+Caps[index[j]].index_y==2*Cy) {
		    cap_pair_sequence.push_back(make_pair( min( index[i], index[j]), max( index[i], index[j])));
		    break;
		}
	    }
	}
    }

    
    if(dummy_flag){
	auto not_on_border = [&]( const auto& c) {
	    return c.index_x!=0 && c.index_x!=r-1 && c.index_y!=0 && c.index_y!=s-1;
	};

	vector<pair<int,int> > temp_cap_pair_sequence;
	for(unsigned int i=0;i<cap_pair_sequence.size();i++){
	    int fi = cap_pair_sequence[i].first;
	    if( not_on_border(Caps[fi])) {
		int si = cap_pair_sequence[i].second;
		if(si==-1 || not_on_border( Caps[si])) {
		    temp_cap_pair_sequence.push_back(cap_pair_sequence[i]);
		}
	    }
	}

	cap_pair_sequence = temp_cap_pair_sequence;
    }

    // to be continued here.
    logger->debug("CC Capacitor Debug flag step4");
    initial_net_pair_sequence(ki,cap_pin);
    logger->debug("CC Capacitor Debug flag step5");
    string outfile=opath+final_gds+".plt";
    logger->debug("CC Capacitor Debug flag step6");
    Router_Cap(ki,cap_pin, dummy_flag, cap_ratio, cap_r, cap_s);
    logger->debug("CC Capacitor Debug flag step7");
    GetPhysicalInfo_router( H_metal, H_metal_index, V_metal, V_metal_index, drc_info);
    logger->debug("CC Capacitor Debug flag step8");
    cal_offset(drc_info, H_metal_index, V_metal_index, HV_via_metal_index);
    logger->debug("CC Capacitor Debug flag step9");
    ExtractData(fpath ,unit_capacitor, final_gds, uc, drc_info, H_metal_index, V_metal_index, HV_via_metal_index, opath);
    logger->debug("CC Capacitor Debug flag step10");
    WriteGDSJSON (fpath ,unit_capacitor, final_gds, drc_info, opath);
    logger->debug("CC Capacitor Debug flag step11");
    WriteViewerJSON (fpath ,unit_capacitor, final_gds, drc_info, opath);
    logger->debug("CC Capacitor Debug flag step12");
    PrintPlacer_Router_Cap(outfile);
    logger->debug("CC Capacitor Debug flag step13");
}

static int
getLayerMask (const std::string & layer, const PnRDB::Drc_info & drc_info) {
    int index = drc_info.Metalmap.at(layer);
    int mask = stoi(drc_info.MaskID_Metal.at(index));
    return mask;
}

static int
getLayerViaMask (const std::string & layer, const PnRDB::Drc_info & drc_info) {
    int index = drc_info.Metalmap.at(layer);
    int mask = stoi(drc_info.MaskID_Via.at(index));
    return mask;
}

void
fillContact (PnRDB::contact& con, const PnRDB::bbox& box) {
    con.originBox.LL = box.LL;
    con.originBox.UR = box.UR;
    con.originCenter = box.center();
}

class MinMax : public PnRDB::bbox {
public:
    MinMax () : bbox (INT_MAX, INT_MAX, INT_MIN, INT_MIN){}
    explicit MinMax (const PnRDB::bbox &b) : bbox (b) {}
    explicit MinMax (const MinMax &m) : bbox (m) {}
    void update (const PnRDB::bbox& obox) { *this = MinMax(unionBox(obox)); }
};

void
Placer_Router_Cap::ExtractData (const string& fpath, const string& unit_capacitor, const string& final_gds, const PnRDB::lefMacro &uc, const PnRDB::Drc_info & drc_info, int H_metal, int V_metal, int HV_via_index, const string& opath) {

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.ExtractData");

    string topGDS_loc = opath+final_gds+".gds";
    //    int gds_unit = 20;
    //writing metals
    MinMax minmax;

    /// common for both Nets_pos and Nets_neg
    auto extract_data_1_2 = [&]( auto& n_array) {
	for (unsigned int i = 0; i < n_array.size(); i++) {//for each net
	    PnRDB::pin temp_Pins;
	    for (unsigned int j = 0; j < n_array[i].start_connection_pos.size(); j++) { //for segment

		int width = drc_info.Metal_info.at(drc_info.Metalmap.at(n_array[i].metal[j])).width/2;

		PnRDB::bbox box = fillPathBBox (n_array[i].start_connection_pos[j],
						n_array[i].end_connection_pos[j], width);
		minmax.update (box);
		PnRDB::contact mtemp_contact;
		fillContact (mtemp_contact, box);
		mtemp_contact.metal = n_array[i].metal[j];
		if (n_array[i].Is_pin[j] == 1) {
		    temp_Pins.name = n_array[i].name;
		    temp_Pins.pinContacts.push_back(mtemp_contact);
		}
		CheckOutBlock.interMetals.push_back(mtemp_contact);
	    }   
	    CheckOutBlock.blockPins.push_back(temp_Pins);
	}
    };


    //for positive nets
    logger->debug("Extract Data Step 1");
    extract_data_1_2( Nets_pos);

    logger->debug("Extract Data Step 2");
    extract_data_1_2( Nets_neg);


    auto extract_data_3_4 = [&]( auto& n_array) {

	for (unsigned int i = 0; i < n_array.size(); i++) {
	    for (unsigned int j = 0; j < n_array[i].via_pos.size(); j++) {//the size of via needs to be modified according to different PDK
		auto& viaRect = drc_info.Via_model.at(drc_info.Metalmap.at(n_array[i].via_metal[j])).ViaRect;
		PnRDB::bbox viaBox (viaRect[0], viaRect[1]);
		viaBox = viaBox + offset + n_array[i].via_pos[j];;
		minmax.update (viaBox);
	    
		PnRDB::contact temp_contact;
		fillContact (temp_contact, viaBox);
		//this part needs modify 2019/6/3
		
		PnRDB::Via temp_via;
		PnRDB::contact upper_contact;
		PnRDB::contact lower_contact;
		upper_contact.placedCenter = temp_contact.placedCenter;
		lower_contact.placedCenter = temp_contact.placedCenter;

		int via_model_index = drc_info.Metalmap.at(n_array[i].via_metal[j]);
		const auto& vm = drc_info.Via_model.at(via_model_index);

		temp_contact.metal = vm.name;

		PnRDB::contact h_contact;
		h_contact.originBox = PnRDB::bbox (vm.UpperRect[0], vm.UpperRect[1]) + temp_contact.placedCenter;

		PnRDB::contact v_contact;
		v_contact.originBox = PnRDB::bbox (vm.LowerRect[0], vm.LowerRect[1]) + temp_contact.placedCenter;
	    
		lower_contact.metal = drc_info.Metal_info.at(vm.LowerIdx).name;
		upper_contact.metal = drc_info.Metal_info.at(vm.UpperIdx).name;
		lower_contact.originBox = v_contact.originBox;
		upper_contact.originBox = h_contact.originBox;
		temp_via.model_index = via_model_index;
		
		temp_via.placedpos = temp_contact.originCenter;
		temp_via.ViaRect = temp_contact;
		temp_via.LowerMetalRect = lower_contact;
		temp_via.UpperMetalRect = upper_contact;
		CheckOutBlock.interVias.push_back(temp_via);
	    }
	}
    };

    logger->debug("Extract Data Step 3");
    extract_data_3_4( Nets_pos);

    logger->debug("Extract Data Step 4");
    extract_data_3_4( Nets_neg);


    CheckOutBlock.orient = PnRDB::Omark(0); //need modify
    logger->debug("Extract Data Step 5");

    std::set<std::string> internal_metal_layer;
    std::vector<std::string> internal_metal;
    
    for (unsigned int i = 0; i < uc.interMetals.size(); i++)
	internal_metal_layer.insert(uc.interMetals[i].metal);
    
    for (auto it = internal_metal_layer.begin(); it != internal_metal_layer.end(); it++)
	internal_metal.push_back(*it);
    
    for(unsigned int i=0;i < Caps.size(); i++){                                     
	PnRDB::bbox cap_rect = PnRDB::bbox (unit_cap_dim) + (Caps[i].pos - unit_cap_dim / 2 + offset);
	minmax.update (cap_rect);
                                                                                   
	for(unsigned int j=0;j<internal_metal.size();j++){                           
	    PnRDB::contact temp_contact;
	    temp_contact.metal = internal_metal[j];
	    fillContact (temp_contact, cap_rect);
	    CheckOutBlock.interMetals.push_back(temp_contact);
	}
    }
   
    logger->debug("Extract Data Step 6");

    const auto& vm = drc_info.Via_model.at(HV_via_index);
    PnRDB::point cp2;
    if(drc_info.Via_model[HV_via_index].LowerIdx == V_metal){
	cp2 = PnRDB::point (vm.UpperRect[0].x, vm.LowerRect[0].y);
    }else{
	cp2 = PnRDB::point (vm.LowerRect[0].x, vm.UpperRect[0].y);
    }
    PnRDB::point cp = vm.ViaRect[0] - cp2;
    PnRDB::point gp (drc_info.Metal_info.at(V_metal).grid_unit_x,  drc_info.Metal_info.at(H_metal).grid_unit_y);
    PnRDB::point mw (drc_info.Metal_info.at(V_metal).width, drc_info.Metal_info.at(H_metal).width);

    PnRDB::point delta = gp - mw / 2 - cp;

    PnRDB::bbox bl = minmax.bloat(delta.x, delta.y);

    bl.LL.x = floor((double) bl.LL.x/drc_info.Metal_info.at(V_metal).grid_unit_x)*drc_info.Metal_info.at(V_metal).grid_unit_x;
    bl.LL.y = floor((double) bl.LL.y/drc_info.Metal_info.at(H_metal).grid_unit_y)*drc_info.Metal_info.at(H_metal).grid_unit_y;

    bl.UR.x = ceil((double) bl.UR.x/drc_info.Metal_info.at(V_metal).grid_unit_x)*drc_info.Metal_info.at(V_metal).grid_unit_x;
    bl.UR.y = ceil((double) bl.UR.y/drc_info.Metal_info.at(H_metal).grid_unit_y)*drc_info.Metal_info.at(H_metal).grid_unit_y;

    CheckOutBlock.gdsFile = topGDS_loc;
    PnRDB::point temp_point;
    CheckOutBlock.originBox.LL = bl.LL;
    logger->debug("cap LL {0} {1}",bl.LL.x,bl.LL.y);
    CheckOutBlock.originBox.UR = bl.UR;
    logger->debug("cap UR {0} {1}",bl.UR.x,bl.UR.y);
    CheckOutBlock.width = CheckOutBlock.originBox.width();
    CheckOutBlock.height = CheckOutBlock.originBox.height();
    CheckOutBlock.originCenter = CheckOutBlock.originBox.center();
}

void
Placer_Router_Cap::cal_offset(const PnRDB::Drc_info &drc_info, int H_metal, int V_metal, int HV_via_index) {

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.cal_offset");

    MinMax minmax;

    //for positive nets
  
    for (unsigned int i = 0; i< Nets_pos.size(); i++) {//for each net
	for (unsigned int j = 0; j< Nets_pos[i].start_connection_pos.size();j++) { //for segment
            int width = drc_info.Metal_info.at(drc_info.Metalmap.at(Nets_pos[i].metal[j])).width/2;
	    minmax.update (fillPathBBox(Nets_pos[i].start_connection_pos[j],
					Nets_pos[i].end_connection_pos[j], width));
        }
    }
  
    //for neg nets
    for (unsigned int i = 0; i <  Nets_neg.size(); i++) {//for each net
	for (unsigned int j = 0; j <  Nets_neg[i].start_connection_pos.size();j++) { //for segment
            int width = drc_info.Metal_info.at(drc_info.Metalmap.at(Nets_neg[i].metal[j])).width/2;
	    minmax.update (fillPathBBox(Nets_neg[i].start_connection_pos[j],
					Nets_neg[i].end_connection_pos[j], width));
        }
    }
  
    //wirting vias
    //for positive net

    auto update_mm = [&](const auto& n_array) {
	for (unsigned int i = 0; i < n_array.size(); i++) {
	    for (unsigned int j = 0; j < n_array[i].via_pos.size(); j++) {//the size of via needs to be modified according to different PDK

		const auto& vm = n_array[i].via_metal[j];
		const auto& viaRect = drc_info.Via_model.at(drc_info.Metalmap.at(vm)).ViaRect;
		const auto& viaPos = n_array[i].via_pos[j];
		minmax.update (PnRDB::bbox(viaRect[0], viaRect[1]) + viaPos);
	    }
	}
    };
    update_mm( Nets_pos);
    update_mm( Nets_neg);
  
    for (unsigned int i = 0; i < Caps.size(); i++) {
	minmax.update (PnRDB::bbox (unit_cap_dim) + (Caps[i].pos - (unit_cap_dim / 2)));
    }

    const auto& vm = drc_info.Via_model[HV_via_index];
    PnRDB::point covPnt = vm.ViaRect[0];;

    PnRDB::point cp2;
    if(vm.LowerIdx == V_metal){
	cp2 = PnRDB::point (vm.UpperRect[0].x, vm.LowerRect[0].y);
    }else{
	cp2 = PnRDB::point (vm.LowerRect[0].x, vm.UpperRect[0].y);
    }
    covPnt -= cp2;
    const auto& vmv = drc_info.Metal_info[V_metal];
    const auto& vmh = drc_info.Metal_info[H_metal];

    auto gp = PnRDB::point (vmv.grid_unit_x, vmh.grid_unit_y);
    auto wp = PnRDB::point (vmv.width, vmh.width) / 2;
    auto mp = minmax.LL;
    offset = gp - wp - covPnt - mp;
    logger->debug("offset {0} {1}",offset.x,offset.y);
    if(offset.x%gp.x!=0 || offset.y%gp.y!=0){//why offset is not correct, might have some bug here? Yaguang - 4/12/2020
      logger->debug("gp {0} {1}",gp.x,gp.y);
      logger->debug("offset.x%gp.x {0} offset.y%gp.y {1}",offset.x%gp.x,offset.y%gp.y);
      offset.x = ceil((double) offset.x/gp.x)*gp.x;
      offset.y = ceil((double) offset.y/gp.y)*gp.y;
      logger->debug("offset {0} {1}",offset.x,offset.y);
      logger->debug("offset.x%gp.x {0} offset.y%gp.y {1}",offset.x%gp.x,offset.y%gp.y);
      //assert(0);
    }

}

void
Placer_Router_Cap::initial_net_pair_sequence(vector<int> & ki, vector<pair<string, string> > & cap_pin) {

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.initial_net_pair_sequence");

    //initial net pair sequence
    logger->debug("initial_net_pair_sequence test1");
    vector<pair<int,int> > S_unique;
    vector<pair<int,int> > S_unit_unit;
    vector<pair<int,int> > S_unit_odd;
    vector<pair<int,int> > S_odd_odd;
    vector<pair<int,int> > S;
    pair<int,int> temp_pair;
    vector<int> C_unit;
    vector<int> C_odd;
    vector<int> C_even;
    for(unsigned int i=0;i<ki.size();i++){
	if(ki[i]==1){
	    C_unit.push_back(i);
	}else if(ki[i]%2==1){
	    C_odd.push_back(i);
	}else{
	    C_even.push_back(i);
	}
    }
    //initial net pair sequence for pair
    logger->debug("initial_net_pair_sequence test2");
    auto genS = [&]( const auto& C) {
	for(unsigned int i=0;i<C.size();i++){
	    for( int size=ki[C[i]]; size>1; size -= 2){
		S.push_back(make_pair( C[i], C[i]));
	    }
	}
    };
    genS( C_even);
    genS( C_odd);

    logger->debug("initial_net_pair_sequence test3");
    //initial net pair sequence for odd 
    int num_unit = C_unit.size();
    int num_odd = C_odd.size();
    while(num_odd>1){
	temp_pair.first = C_odd[num_odd-1];
	temp_pair.second = C_odd[num_odd-2];
	C_odd.pop_back();
	C_odd.pop_back();
	num_odd = num_odd -2;
	S_odd_odd.push_back(temp_pair);
    }
    if(num_odd==1 && num_unit>0){
	temp_pair.first = C_odd[num_odd-1];
	temp_pair.second = C_unit[num_unit-1];
	C_unit.pop_back();
	num_unit = num_unit -1;
	num_odd = num_odd -1;
	S_unit_odd.push_back(temp_pair);
    }else if(num_odd==1 && num_unit ==0){
	temp_pair.first = C_odd[num_odd-1];
	temp_pair.second = -1;
	num_odd = num_odd -1;
	S_unique.push_back(temp_pair);
    }
    ////initial net pair sequence for unit
    while(num_unit>1){
	temp_pair.first = C_unit[num_unit-1];
	temp_pair.second = C_unit[num_unit-2];
	C_unit.pop_back();
	C_unit.pop_back();
	num_unit = num_unit -2;
	S_unit_unit.push_back(temp_pair);
    }
    if(num_unit==1){
	temp_pair.first = C_unit[num_unit-1];
	temp_pair.second = -1;
	num_unit = num_unit -1;
	S_unique.push_back(temp_pair);
    }
    if(S_unique.size()>1){
        logger->error("Error in S_unique");
    }
    for(unsigned int i=0;i<S_unique.size();i++){
	net_sequence.push_back(S_unique[i]);
    }
    for(unsigned int i=0;i<S_unit_unit.size();i++){
	net_sequence.push_back(S_unit_unit[i]);
    }
    for(unsigned int i=0;i<S_unit_odd.size();i++){
	net_sequence.push_back(S_unit_odd[i]);
    }
    for(unsigned int i=0;i<S_odd_odd.size();i++){
	net_sequence.push_back(S_odd_odd[i]);
    }
    for(unsigned int i=0;i<S.size();i++){
	net_sequence.push_back(S[i]);
    }
    logger->debug("initial_net_pair_sequence test4");
    net temp_net;

    for(unsigned int i=0;i<ki.size()+1;i++){
	if(i<ki.size()){
	    //temp_net.name = cap_pin[i].first;
            temp_net.name = cap_pin[i].second;
	}else{
	    temp_net.name = "dummy_gnd_PLUS";
	}
	Nets_pos.push_back(temp_net);
    }

    logger->debug("initial_net_pair_sequence test5");
    int start_index=0;
    for(unsigned int i=0;i<net_sequence.size();i++){
	if(net_sequence[i].second==-1){
	    Nets_pos[net_sequence[i].first].cap_index.push_back(cap_pair_sequence[start_index].first);
	    Caps[cap_pair_sequence[start_index].first].net_index = net_sequence[i].first;
	    start_index = start_index+1;
	}else if(net_sequence[i].second!=-1 && cap_pair_sequence[start_index].second == -1){
	    start_index = start_index+1;
	    Nets_pos[net_sequence[i].first].cap_index.push_back(cap_pair_sequence[start_index].first);
	    Nets_pos[net_sequence[i].second].cap_index.push_back(cap_pair_sequence[start_index].second);
	    Caps[cap_pair_sequence[start_index].first].net_index = net_sequence[i].first;
	    Caps[cap_pair_sequence[start_index].second].net_index = net_sequence[i].second;
	    start_index = start_index+1;
	}else if(net_sequence[i].second!=-1 && cap_pair_sequence[start_index].second != -1){
	    Nets_pos[net_sequence[i].first].cap_index.push_back(cap_pair_sequence[start_index].first);
	    Nets_pos[net_sequence[i].second].cap_index.push_back(cap_pair_sequence[start_index].second);
	    Caps[cap_pair_sequence[start_index].first].net_index = net_sequence[i].first;
	    Caps[cap_pair_sequence[start_index].second].net_index = net_sequence[i].second;
	    start_index = start_index+1;
	}
    }
    //add a net for dummy capacitor


    // a dummy net is added for dummy capacitor
    logger->debug("initial_net_pair_sequence test6");

    int dummy_cap = Nets_pos.size();
    for(unsigned int i=0;i<Caps.size();i++){
	if(Caps[i].net_index==-1){
	    Nets_pos[dummy_cap-1].cap_index.push_back(i);
        }
    }
}

void Placer_Router_Cap::Router_Cap(vector<int> & ki, vector<pair<string, string> > &cap_pin, bool dummy_flag, bool cap_ratio, int cap_r, int cap_s){

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.Router_Cap");

    logger->debug("broken down 1");
    //route for cap
    for(unsigned int i=0;i<Nets_pos.size();i++){ // for each net
	for(unsigned int j=0;j<Nets_pos[i].cap_index.size();j++){ //for each unaccessed cap
	    if(Caps[Nets_pos[i].cap_index[j]].access==0){
		connection_set temp_set;
		temp_set.cap_index.push_back(Nets_pos[i].cap_index[j]); //new set & marked accessed
		Caps[Nets_pos[i].cap_index[j]].access = 1;
		//found its neighbor recursively
		found_neighbor(j,Nets_pos[i],temp_set);
		Nets_pos[i].Set.push_back(temp_set);
	    }
	} 
    }

    logger->debug("broken down 2");
    double sum = 0;
    for(unsigned int i=0;i<ki.size();i++){
	sum += ki[i];
    }

    logger->debug("broken down 3");
    double r = ceil(sqrt(sum));
    double s = ceil(sum/r);

    if(cap_ratio){
	r = cap_r;
	s = cap_s;
    }

    if(dummy_flag){
	r += 2;
	s += 2;
    }

    double Cx = r/2; //note this is different
    double Cy = s/2; //note this is different
    //create router line for each net (cap) vertical 

    logger->debug("broken down 1");
    for(unsigned int i=0;i<Nets_pos.size();i++){
	for(unsigned int j=0;j<Nets_pos[i].Set.size();j++){
	    connection_set temp_router_line;
	    //initial temp_router_line
	    for(int k=0;k<=r;k++){
		temp_router_line.cap_index.push_back(0);
	    }
	    for(unsigned int l=0;l<Nets_pos[i].Set[j].cap_index.size();l++){
		temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_x]=1;
		temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_x+1]=1;
		temp_router_line.cap_index[2*Cx-Caps[Nets_pos[i].Set[j].cap_index[l]].index_x]=1;
		temp_router_line.cap_index[2*Cx-Caps[Nets_pos[i].Set[j].cap_index[l]].index_x-1]=1;//-1
	    }
	    Nets_pos[i].router_line_v.push_back(temp_router_line);
	}
    }
  
    logger->debug("broken down 4");
    //common overlap checking vertical
    for(unsigned int i=0;i<Nets_pos.size();i++){
	for(int j=0;j<=r;j++){
	    Nets_pos[i].routable_line_v.push_back(1);
	}
	for(unsigned int k=0;k<Nets_pos[i].router_line_v.size();k++){
	    for(unsigned int l=0;l<Nets_pos[i].router_line_v[k].cap_index.size();l++){
		Nets_pos[i].routable_line_v[l] =(int) Nets_pos[i].routable_line_v[l] && Nets_pos[i].router_line_v[k].cap_index[l];
	    }
	}
    }

    logger->debug("broken down 5");
    //create router line for each net (cap) horizontal
    for(unsigned int i=0;i<Nets_pos.size();i++){
	for(unsigned int j=0;j<Nets_pos[i].Set.size();j++){
	    connection_set temp_router_line;
	    //initial temp_router_line
	    for(int k=0;k<=s;k++){
		temp_router_line.cap_index.push_back(0);
	    }
	    for(unsigned int l=0;l<Nets_pos[i].Set[j].cap_index.size();l++){
		temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_y]=1;
		temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_y+1]=1;
		temp_router_line.cap_index[2*Cy-Caps[Nets_pos[i].Set[j].cap_index[l]].index_y]=1;
		temp_router_line.cap_index[2*Cy-Caps[Nets_pos[i].Set[j].cap_index[l]].index_y-1]=1;//-1
	    }
	    Nets_pos[i].router_line_h.push_back(temp_router_line);
	}
    }

    logger->debug("broken down 6");
    //common overlap checking horizontal
    for(unsigned int i=0;i<Nets_pos.size();i++){
	for(int j=0;j<=s;j++){
	    Nets_pos[i].routable_line_h.push_back(1);
	}
	for(unsigned int k=0;k<Nets_pos[i].router_line_h.size();k++){
	    for(unsigned int l=0;l<Nets_pos[i].router_line_h[k].cap_index.size();l++){
		Nets_pos[i].routable_line_h[l] = Nets_pos[i].routable_line_h[l] && Nets_pos[i].router_line_h[k].cap_index[l];
	    }
	}
    }


    logger->debug("broken down 7");
    //create router line for each net (cap) half vertical 
    for(unsigned int i=0;i<Nets_pos.size();i++){
	for(unsigned int j=0;j<Nets_pos[i].Set.size();j++){
	    connection_set temp_router_line;
	    //initial temp_router_line
	    for(int k=0;k<=r;k++){
		temp_router_line.cap_index.push_back(0);
	    }
	    for(unsigned int l=0;l<Nets_pos[i].Set[j].cap_index.size();l++){
		temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_x]=1;
		temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_x+1]=1;
	    }
	    Nets_pos[i].half_router_line_v.push_back(temp_router_line);
	}
    }

    logger->debug("broken down 8");
    //create router line for each net (cap) half horizontal
    for(unsigned int i=0;i<Nets_pos.size();i++){
	for(unsigned int j=0;j<Nets_pos[i].Set.size();j++){
	    auto& ci = Nets_pos[i].Set[j].cap_index;
	    connection_set temp_router_line;
	    //initial temp_router_line
	    for(int k=0;k<=s;k++){
		temp_router_line.cap_index.push_back(0);
	    }
	    for(unsigned int l=0;l<ci.size();l++){
		auto& Ci = temp_router_line.cap_index;
		Ci[Caps[ci[l]].index_y]=1;
		Ci[Caps[ci[l]].index_y+1]=1;
	    }
	    Nets_pos[i].half_router_line_h.push_back(temp_router_line);
	}
    }
  

    logger->debug("broken down 9");
    //initialize num_router_net_v and num_router_net_h
    for(int i=0;i<=r;i++){num_router_net_v.push_back(0);}
    for(int i=0;i<=s;i++){num_router_net_h.push_back(0);}
  
    Nets_neg = Nets_pos;
    for(unsigned int i=0;i<Nets_pos.size();i++){
	if(i!=Nets_pos.size()-1){
	    //Nets_neg[i].name = cap_pin[i].second;
            Nets_neg[i].name = cap_pin[i].first;
	}else{
	    Nets_neg[i].name = "dummy_gnd_MINUS";
	}
    }
  

    auto router_cap_10_11 = [&]( auto& n_array, int sign) {

	for(unsigned int i=0;i<n_array.size();i++){
	    for(int k=0;k<=r;k++){n_array[i].line_v.push_back(0);}
	  
	    const auto& rlv = n_array[i].routable_line_v;
	    int sum=std::accumulate( rlv.begin(), rlv.end(), 0);
	    if(sum>0){
		//use the information of routable_line_v
		int router_num=n_array.size();
		if ( sign == -1) {
		    router_num = 2*n_array.size();
		}
		int choosen_route=-1;
		for(int j=0;j<=Cx;j++){
		    if(rlv[j]==1){
			if(num_router_net_v[j]<=router_num){
			    choosen_route=j;
			    router_num = num_router_net_v[j];
			}
		    }
		}
		n_array[i].line_v[choosen_route]=1;
		n_array[i].line_v[2*Cx-choosen_route]=1;
		num_router_net_v[choosen_route]=num_router_net_v[choosen_route]+1;
		num_router_net_v[2*Cx-choosen_route]=num_router_net_v[2*Cx-choosen_route]+1;
             
	    }else{
		//use the information of half_routable_line_v
		const auto& hrlv = n_array[i].half_router_line_v;

		for(unsigned int l=0;l<hrlv.size();l++){
		    const auto& ci = hrlv[l].cap_index;
		    const auto& lv = n_array[i].line_v;

		    assert( ci.size() == lv.size());
		    int found = std::inner_product( ci.begin(), ci.end(), lv.begin(), false,
						    []( bool a, bool b) { return a || b; },
						    []( int a, int b) { return a==1 && b==1; });
		    if(found ==0){
			int router_num=n_array.size();
			int choosen_route=-1;
			for(unsigned int k=0;k<ci.size();k++){
			    if(ci[k]==1){
				if(num_router_net_v[k]<=router_num){
				    choosen_route=k;
				    router_num = num_router_net_v[k];
				}
			    }
			}
			assert( choosen_route != -1);
			n_array[i].line_v[choosen_route] = 1;
			num_router_net_v[choosen_route] += 1;
		    }
		}
	    }
	}
    };
    logger->debug("broken down 10");
    router_cap_10_11( Nets_pos, 1);

    logger->debug("broken down 11");
    router_cap_10_11( Nets_neg, -1);

    logger->debug("broken down 12");
    vector<int> num_line( Nets_pos[0].line_v.size(), 0);
    for(unsigned int i=0;i<Nets_pos.size();i++){
	assert( Nets_pos[i].line_v.size() == Nets_neg[i].line_v.size());
	assert( Nets_pos[i].line_v.size() == num_line.size());
	for(unsigned int j=0;j<Nets_pos[i].line_v.size();j++){
	    num_line[j] += Nets_pos[i].line_v[j]+Nets_neg[i].line_v[j];
	}
    }

    logger->debug("broken down 13");
    int max_num_ =0;
    for(unsigned int i=0;i<num_line.size();i++){
	max_num_ = max(max_num_, num_line[i]);
    }

    span_dist = PnRDB::point((max_num_ + 1) * min_dis.x, span_dist.y);

    for(unsigned int i=0;i<Caps.size();i++){
	PnRDB::point cap_dim = unit_cap_dim + span_dist;
	PnRDB::point cap_pos = PnRDB::bbox(unit_cap_dim).center() + cap_dim.scale(Caps[i].index_x, Caps[i].index_x);
	Caps[i].pos.x = cap_pos.x;
    }

}

void Placer_Router_Cap::found_neighbor(int j, net& pos, connection_set& temp_set){
    const auto& pcj = Caps[pos.cap_index[j]];
    for(unsigned int i=0;i<pos.cap_index.size();i++){
	auto& pci = Caps[pos.cap_index[i]];
	if(pci.access==0){
	    int adiffx = abs(pci.index_x -pcj.index_x);
	    int adiffy = abs(pci.index_y -pcj.index_y);
	    if((adiffx == 0 && adiffy==1) || (adiffy == 0 && adiffx==1)) {
		pci.access = 1;
		temp_set.cap_index.push_back(pos.cap_index[i]);
		found_neighbor(i, pos, temp_set);
	    }
	}
    } 
}

void Placer_Router_Cap::addVia(net &temp_net,
			       PnRDB::point &coord_pos,
			       const PnRDB::Drc_info &drc_info,
			       const string& HV_via_metal,
			       int HV_via_metal_index,
			       int isPin) {
    const auto& vm = drc_info.Via_model.at(HV_via_metal_index);

    temp_net.via_pos.push_back (coord_pos); // DAK: Replace .via with .via_pos throughout
    temp_net.via_metal.push_back(HV_via_metal);

    auto apply_aux_pt = [&]( PnRDB::point p0, PnRDB::point p1, int idx) {
	PnRDB::point start_pos = p0;
	start_pos = start_pos + coord_pos;
	temp_net.start_connection_pos.push_back (start_pos);
	temp_net.Is_pin.push_back(isPin);
	temp_net.metal.push_back(drc_info.Metal_info[idx].name);
	PnRDB::point end_pos = p1;
	end_pos = end_pos + coord_pos;
	temp_net.end_connection_pos.push_back (end_pos);
    };
    auto apply_viax = [&]( const auto& ra, int idx) {
	apply_aux_pt( PnRDB::point(ra[0].x, 0), PnRDB::point(ra[1].x, 0), idx);
    };

    auto apply_viay = [&]( const auto& ra, int idx) {
	apply_aux_pt( PnRDB::point(0, ra[0].y), PnRDB::point(0, ra[1].y), idx);
    };

    if(drc_info.Metal_info.at(vm.LowerIdx).direct==1){
	apply_viax( vm.LowerRect, vm.LowerIdx); // use the LL.x and the UR.x with y = 0 for LoweRect
	apply_viay( vm.UpperRect, vm.UpperIdx); // Use the LL.y and the UR.y with x = 0 for UpperRect
    }else{
	apply_viay( vm.LowerRect, vm.LowerIdx); // 
	apply_viax( vm.UpperRect, vm.UpperIdx);
    }
}

void Placer_Router_Cap::check_grid( const net& n) const
{

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.check_grid");

    assert( n.start_connection_pos.size() == n.end_connection_pos.size());
    for( unsigned int i=0; i<n.start_connection_pos.size(); ++i) {
	const auto& s = n.start_connection_pos[i];
	const auto& e = n.end_connection_pos[i];
	//const auto& m = n.metal[i];
	//const auto& p = n.Is_pin[i];
	if ( s.x == e.x) {
	    // Vertical wi
	    int x = s.x;
            logger->debug(" V {0}",x % 80);
	} else {
	    int y = s.x;
	    logger->debug(" H {0}",y % 84);
	}
    }
}


class MinMaxBox {
    int best=0; // initialization not required except to satisfy -Wall 
    int best_cap_index=-1;
    int left_right = 0;
    int sign;
public:
    MinMaxBox( int s) : sign(s) {}

    void update( int value, int idx, int lr) {
	if( best_cap_index == -1 || (lr == 0 && sign*value>=sign*best) || (lr == 1 && sign*value>sign*best)){
	    best=value;
	    best_cap_index = idx;
	    left_right = lr;
	}
    }    

    int get_best_cap_index() const {
	return best_cap_index;
    }

    int get_left_right() const {
	return left_right;
    }

};

void Placer_Router_Cap::GetPhysicalInfo_merged_net(
						   vector<net>& n_array,
						   vector<int>& trails,
						   const PnRDB::Drc_info& drc_info,
						   const string& H_metal,
						   const string& V_metal,
						   const string& HV_via_metal,
						   int HV_via_metal_index,
						   int grid_offset,
						   int sign)
{

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.GetPhysicalInfo_merged_net");

    //  pair<double,double> coord;
    PnRDB::point coordP;

    for(unsigned int i=0;i<Caps.size();i++){
	Caps[i].access = 0;
    }

    int routed_trail=0;

    for(unsigned int i=0;i<n_array.size();i++){
	auto& n = n_array[i];

	// DAK: We should use points not these double pairs
	if(n.cap_index.size()==0){continue;}
	routed_trail += 1;
	PnRDB::point first_coordP;
	PnRDB::point end_coordP;
	int first_lock=0;
	int end_close=0;
	for(unsigned int l=0;l<n.line_v.size();l++){
	    if(n.line_v[l]==1){
		trails[l] += 1;
		//connect to connection set and found the end point
		MinMaxBox mb(sign);
		int found = 0;
		PnRDB::point opt;
		for(unsigned int k=0;k<n.cap_index.size();k++){
		    if ( Caps[n.cap_index[k]].access != 0) continue;

		    int lr = l-Caps[n.cap_index[k]].index_x;

		    if(lr!=0 && lr!=1) continue;

		    found = 1;
		    PnRDB::point half_cap_dim = unit_cap_dim / 2;
		    PnRDB::point shift = half_cap_dim - shifting;
		    PnRDB::point shift_final = shift.scale(sign, -sign);
		    coordP = Caps[n.cap_index[k]].pos + shift_final;
		  
		    addVia(n,coordP,drc_info,HV_via_metal,HV_via_metal_index,0);

		    shift = half_cap_dim - shifting + min_dis;
		    shift_final = shift.scale(sign, -sign);
		    PnRDB::point pt2 = Caps[n.cap_index[k]].pos + shift_final;
		  
		    if( lr == 1) {
			n.start_connection_pos.push_back (coordP);
			coordP.y = pt2.y;
			n.end_connection_pos.push_back (coordP);
			n.Is_pin.push_back(0);
			n.metal.push_back(V_metal);
			addVia(n,coordP,drc_info,HV_via_metal,HV_via_metal_index,0);
		    }
		    n.start_connection_pos.push_back (coordP);
		    if( lr == 0){ 
			opt =  Caps[n.cap_index[k]].pos - half_cap_dim - (span_dist - min_dis * trails[l]);
			coordP.x = opt.x;
		    }else if( lr == 1) {
			opt = Caps[n.cap_index[k]].pos + half_cap_dim + min_dis * trails[l];
			coordP.x = opt.x;
		    }
		    n.end_connection_pos.push_back (coordP);
		    n.Is_pin.push_back(0);
		    n.metal.push_back(H_metal);

		    addVia(n,coordP,drc_info,HV_via_metal,HV_via_metal_index,0);
		    mb.update( Caps[n.cap_index[k]].index_y, n.cap_index[k], lr);

		    Caps[n.cap_index[k]].access = 1;
		}
                if(0){
		//if(found == 0){
		    for(unsigned int k=0;k<n.cap_index.size();k++){
			int lr = l-Caps[n.cap_index[k]].index_x;
			if(lr==1){
			    PnRDB::point half_cap_dim = unit_cap_dim / 2;
			    PnRDB::point shift = half_cap_dim - shifting;
			    PnRDB::point shift_final = shift.scale(sign, -sign);
		  
			    opt = Caps[n.cap_index[k]].pos + shift_final;
		  
			    coordP = opt;
			    addVia(n,coordP,drc_info,HV_via_metal,HV_via_metal_index,0);

			    n.start_connection_pos.push_back (coordP);

			    shift = half_cap_dim - shifting + min_dis;
			    shift_final = shift.scale(sign, -sign);
			    PnRDB::point pt = Caps[n.cap_index[k]].pos + shift_final;
			    coordP.y = pt.y;
			    n.end_connection_pos.push_back (coordP);
			    n.Is_pin.push_back(0);
			    n.metal.push_back(V_metal);
			    addVia(n,coordP,drc_info,HV_via_metal,HV_via_metal_index,0);
			    n.start_connection_pos.push_back (coordP);
			    shift = half_cap_dim + min_dis * trails[1];
			    PnRDB::point pt2 = Caps[n.cap_index[k]].pos + shift;
			    opt = pt2;
			    coordP.x = pt2.x;
			    n.end_connection_pos.push_back (coordP);
			    n.Is_pin.push_back(0);
			    n.metal.push_back(H_metal);
			    addVia(n,coordP,drc_info,HV_via_metal,HV_via_metal_index,0);
			    Caps[n.cap_index[k]].access = 1;
			    mb.update( Caps[n.cap_index[k]].index_y, n.cap_index[k], lr);
			}
		    }
		}
		PnRDB::point half_cap_dim = unit_cap_dim / 2;
		PnRDB::point shift = min_dis * (routed_trail +2) + PnRDB::point(grid_offset, grid_offset);
		PnRDB::point shift_final = shift.scale(sign, sign);
		  
		PnRDB::point pt = Caps.back().pos + half_cap_dim;
		if (sign == 1)  pt = PnRDB::point(0,0);
		pt = pt - shift_final;
		coordP.y = pt.y;
		addVia(n,coordP,drc_info,HV_via_metal,HV_via_metal_index,1);
                 
		n.start_connection_pos.push_back (coordP);

		shift = min_dis * 2 - shifting;
		shift_final = shift.scale (sign, -sign);
	      
		PnRDB::point pt2 = Caps.back().pos + half_cap_dim;
		if (sign == 1)  pt2 = PnRDB::point(0,0);
		pt2 = pt2 + shift_final;

		coordP.y = pt2.y;
		n.end_connection_pos.push_back (coordP);
		n.Is_pin.push_back(0);
		n.metal.push_back(V_metal);
		n.start_connection_pos.push_back (coordP);

		PnRDB::point lr (mb.get_left_right(), mb.get_left_right());
		PnRDB::point nsh = half_cap_dim + lr.scale (min_dis.x, min_dis.y) -shifting;
		PnRDB::point nsh_final = nsh.scale(sign, sign);
	      
		PnRDB::point npt = Caps[mb.get_best_cap_index()].pos - nsh_final;

		coordP.y = npt.y;
		n.end_connection_pos.push_back (coordP);
		n.Is_pin.push_back(0);

		n.metal.push_back(V_metal);
		  
		if(first_lock==0 && found==1){
		    first_coordP.x = opt.x;
		    first_coordP.y = pt.y;
		    first_lock=1;

		    end_close=1;
		    end_coordP.x = opt.x;
		    end_coordP.y = pt.y;

		}else if(found==1){
		    end_close=1;
		    end_coordP.x = opt.x;
		    end_coordP.y = pt.y;
		}
	    }
	}
	//connect to each trail
	if(first_lock==1 && end_close==1){

            if(drc_info.Metalmap.find(H_metal)==drc_info.Metalmap.end()){
               logger->error("H_metal error");
               assert(0);
            }
            auto metal_index = drc_info.Metalmap.at(H_metal);
            int minL = drc_info.Metal_info.at(metal_index).minL;
            if(end_coordP.x - first_coordP.x < minL){
               end_coordP.x = first_coordP.x + minL;
            }

	    n.start_connection_pos.push_back (first_coordP);
	    n.end_connection_pos.push_back (end_coordP);
	    n.Is_pin.push_back(1);
	    n.metal.push_back(H_metal);
	}    

	check_grid(n);

    }

}

void Placer_Router_Cap::GetPhysicalInfo_common_net ( vector<net>& n_array,
						     vector<int>& trails,
						     const PnRDB::Drc_info& drc_info,
						     const string& H_metal,
						     const string& V_metal,
						     const string& HV_via_metal,
						     int HV_via_metal_index,
						     int grid_offset,
						     int sign)
{
    //  pair<double,double> coord;
    PnRDB::point coordP;

    for(unsigned int i=0;i<n_array.size();i++){
	auto& n = n_array[i];
	//connection for each connection set
	for(unsigned int j=0;j<n.Set.size();j++){
	    unsigned int end_flag = n.Set[j].cap_index.size();
	    unsigned int index = 0;
	    while(index<end_flag){
		if(Caps[n.Set[j].cap_index[index]].access==1){
		    int found=0;
		    for(unsigned int k=0;k<end_flag;k++){
			if (Caps[n.Set[j].cap_index[k]].access) continue;
			    
			int absx = abs(Caps[n.Set[j].cap_index[k]].index_x-Caps[n.Set[j].cap_index[index]].index_x);
			int absy = abs(Caps[n.Set[j].cap_index[k]].index_y-Caps[n.Set[j].cap_index[index]].index_y);

			if( !((absy == 0 && absx == 1) || (absx == 0 && absy == 1))) continue;

			PnRDB::point half_cap_dim = unit_cap_dim / 2;
			PnRDB::point shift = half_cap_dim - shifting;
			PnRDB::point shift_final = shift.scale(sign, -sign);
			coordP = Caps[n.Set[j].cap_index[k]].pos + shift_final;
			addVia(n,coordP,drc_info,HV_via_metal,HV_via_metal_index,0);
			n.start_connection_pos.push_back (coordP);
			coordP = Caps[n.Set[j].cap_index[index]].pos + shift_final;
			n.end_connection_pos.push_back (coordP);
		      
			n.Is_pin.push_back(0);

			if( absy==0 && absx==1) {
			    n.metal.push_back(H_metal);
			}else if( absx == 0 && absy ==1) {
			    n.metal.push_back(V_metal);
			}
			addVia (n,coordP,drc_info,HV_via_metal,HV_via_metal_index,0);
                   
			Caps[n.Set[j].cap_index[k]].access=1;
			index = 0;
			found = 1;
		    }
		    if(found==0){
			index += 1;
		    }
		}else{
		    index += 1;
		}
	    }
	}
    }
}   

int SnapDown (int pos, int wid) { return (pos / wid) * wid; }
int SnapUp (int pos, int wid) { return SnapDown (pos + wid - 1, wid); }

void Placer_Router_Cap::GetPhysicalInfo_router(
					       const string& H_metal, int H_metal_index,
					       const string& V_metal, int V_metal_index,
					       const PnRDB::Drc_info &drc_info){

    const auto& mH = drc_info.Metal_info.at(H_metal_index);
    int grid_offset;
    {
	// DAK: HACK
	int height_cap = INT_MIN;
	for(unsigned int i=0;i<Caps.size();i++){
	    height_cap = max (height_cap, (Caps[i].pos + unit_cap_dim/2).y);
	}
	int near_grid = SnapUp (height_cap, mH.grid_unit_y);
	assert( near_grid % 2 == 0);
	assert( height_cap % 2 == 0);

	grid_offset = (near_grid - height_cap)/2;
    }


    string HV_via_metal;
    int HV_via_metal_index;

    if(H_metal_index>V_metal_index){
	HV_via_metal = V_metal;
	HV_via_metal_index = V_metal_index;
    }else{
	HV_via_metal = H_metal;
	HV_via_metal_index = H_metal_index;
    }

   
    //connection for trails
    vector<int> trails;
    for(unsigned int i=0;i<Nets_pos[0].line_v.size();i++){trails.push_back(0);}

    assert( Nets_pos[0].line_v.size() == Nets_neg[0].line_v.size());

    GetPhysicalInfo_merged_net( Nets_pos, trails, drc_info,
				H_metal, V_metal, HV_via_metal, HV_via_metal_index, grid_offset,  1);

    GetPhysicalInfo_common_net( Nets_pos, trails, drc_info,
				H_metal, V_metal, HV_via_metal, HV_via_metal_index, grid_offset,  1);

    GetPhysicalInfo_merged_net( Nets_neg, trails, drc_info,
				H_metal, V_metal, HV_via_metal, HV_via_metal_index, grid_offset, -1);

    GetPhysicalInfo_common_net( Nets_neg, trails, drc_info,
				H_metal, V_metal, HV_via_metal, HV_via_metal_index, grid_offset, -1);

}

extern
void JSONReaderWrite_subcells (string GDSData, long int& rndnum,
			       vector<string>& strBlocks, vector<int>& llx, vector<int>& lly,
			       vector<int>& urx, vector<int>& ury, json& mjsonStrAry);

extern
void JSONExtractUit (string GDSData, double& unit);

extern 
void addOABoundaries (json& jsonElements, int width, int height);

PnRDB::bbox
Placer_Router_Cap::fillPathBBox (const PnRDB::point &start,
				 const PnRDB::point &end,
				 int half_width) {
    PnRDB::bbox box;
    if (start.x == end.x) { // Vertical
	int sy = start.y < end.y ? start.y : end.y;
	int ey = start.y > end.y ? start.y : end.y;
	box.LL = PnRDB::point (start.x - half_width, sy);
	box.UR = PnRDB::point (end.x + half_width, ey);
    } else {		    // Horizontal
	int sx = start.x < end.x ? start.x : end.x;
	int ex = start.x > end.x ? start.x : end.x;
	box.LL = PnRDB::point (sx, start.y  - half_width);
	box.UR = PnRDB::point (ex, end.y + half_width);
    }
    return box + offset;
}

void
Placer_Router_Cap::WriteGDSJSON (const string& fpath, const string& unit_capacitor, const string& final_gds, const PnRDB::Drc_info & drc_info, const string& opath) {

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.WriteGDSJSON");

    //begin to write JSON file from unit capacitor to final capacitor file
    string gds_unit_capacitor = fpath+"/"+unit_capacitor+".gds";
    string topGDS_loc = opath+final_gds+".gds";
    string TopCellName = final_gds;
    double unitScale=0.5;
    JSONExtractUit (gds_unit_capacitor, unitScale);
    logger->debug("Cap unitScale {0}",unitScale);

    std::ofstream jsonStream;
    jsonStream.open (topGDS_loc + ".json");
    json jsonTop;

    jsonTop["header"] = 600;
    json jsonLibAry = json::array();
    json jsonLib;
    jsonLib["time"] = JSON_TimeTime();
    // DAK Overwrite to match
    jsonLib["time"] = {2019, 4, 24, 9, 46, 15, 2019, 4, 24, 9, 46, 15};
    double dbUnitUser=2*0.00025/unitScale;
    double dbUnitMeter=dbUnitUser/1e6;
    jsonLib["units"] = {dbUnitUser, dbUnitMeter};
    jsonLib["libname"] = "test";

    //what is this
    vector<string> uniGDS;
    for(unsigned int i=0;i<1;i++){
	uniGDS.push_back(gds_unit_capacitor);
    }

    json jsonStrAry = json::array();

    vector<string> strBlocks;
    vector<int> llx, lly, urx, ury;
    map<string,int> gdsMap2strBlock;
    long int rndnum=111;
    vector<string> strBlocks_Top;
    int idx=0;
    //writing unit capacitors??? confirm with jinhyun
    logger->debug("GDS CAP SUBCELL read of {0}",gds_unit_capacitor);
    for(unsigned int i=0;i<uniGDS.size();i++) {
	json js;
        logger->debug("CAP GDS: Using JSON for subcells for now");
	JSONReaderWrite_subcells (gds_unit_capacitor, rndnum, strBlocks, llx,lly,urx,ury, js);
	for (json::iterator str = js.begin(); str != js.end(); ++str) {
	    jsonStrAry.push_back (*str);
	}
 
	if (strBlocks.size())
	    strBlocks_Top.push_back(strBlocks.back());
	else
            logger->error("ERROR: NO blocks returned from parsing {0}",gds_unit_capacitor);
	gdsMap2strBlock.insert(make_pair(gds_unit_capacitor,idx));
	idx++;
    }
    //writing metals

    json jsonStr;
    jsonLib["time"] = JSON_TimeTime();
    // DAK: Hack to match
    jsonStr["time"] = {2019, 4, 24, 9, 46, 15, 2019, 4, 24, 9, 46, 15};
    jsonStr["strname"] = TopCellName.c_str();
    json jsonElements = json::array();

    vector<vector<net>*> twoItems = { &Nets_pos, &Nets_neg};

    auto doit0 = [&](const auto& n_array) {
	for(unsigned int i=0; i< n_array.size(); i++){//for each net
	    const auto& n = n_array[i];
	    for(unsigned int j=0; j< n.start_connection_pos.size();j++){ //for segment

		const auto& mi = drc_info.Metal_info.at(drc_info.Metalmap.at(n.metal[j]));
		int width = mi.width/2;
		auto box = fillPathBBox (n.start_connection_pos[j],
					 n.end_connection_pos[j], width) * unitScale;
		//		box = box * unitScale;
 		json bound;
		bound["type"] = "boundary";
		bound["datatype"] = 0;
		json z = ToJsonAry(box);
		bound["xy"] = z;
		bound["layer"] = getLayerMask (n.metal[j], drc_info);
		jsonElements.push_back (bound);
	    }   
	}
    };
    doit0( Nets_pos);
    doit0( Nets_neg);
  
    auto doit1 = [&](const auto& n_array) {
	for (unsigned int i = 0; i < n_array.size(); i++) {
	    const auto& n = n_array[i];
	    for (unsigned int j = 0; j < n.via_pos.size(); j++) {//the size of via needs to be modified according to different PDK
		const auto& viaRect = drc_info.Via_model.at(drc_info.Metalmap.at(n.via_metal[j])).ViaRect;
		auto viaBox = PnRDB::bbox (viaRect[0], viaRect[1]) + (n.via_pos[j] + offset);;

		json bound;
		bound["type"] = "boundary";
		bound["datatype"] = 0;
		json z = ToJsonAry (viaBox * unitScale);
		bound["xy"] = z;
		bound["layer"] = getLayerViaMask (n.via_metal[j], drc_info);
		jsonElements.push_back (bound);
	    }
	}
    };
    doit1( Nets_pos);
    doit1( Nets_neg);

    //write orientation for each cap
    for (unsigned int i = 0; i < Caps.size(); i++) {
	json sref;
	sref["type"] = "sref";
	if (strBlocks_Top.size())
	    sref["sname"] = strBlocks_Top[0].c_str();
	else
            logger->error("ERROR: no block found to output from subcells");
	sref["strans"] = 0;
	sref["angle"] = 0.0;
	PnRDB::point half_cap_dim = unit_cap_dim / 2;
	auto pt = Caps[i].pos;

	pt = (pt - half_cap_dim + offset) * unitScale;
	json xy = json::array();
	xy.push_back(pt.x);
	xy.push_back(pt.y);
	sref["xy"] = xy;
	jsonElements.push_back (sref);
    }

    addOABoundaries(jsonElements, unitScale * CheckOutBlock.width, unitScale * CheckOutBlock.height);
    jsonStr["elements"] = jsonElements;
    jsonStrAry.push_back (jsonStr);
    jsonLib["bgnstr"] = jsonStrAry;

    jsonLibAry.push_back(jsonLib);
    jsonTop["bgnlib"] = jsonLibAry;
    jsonStream << std::setw(4) << jsonTop;
    jsonStream.close();
    logger->debug("CAP GDS JSON FINALIZE {0}",unit_capacitor);
}

void
Placer_Router_Cap::WriteViewerJSON (const string& fpath, const string& unit_capacitor, const string& top_name, const PnRDB::Drc_info & drc_info, const string& opath) {

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.WriteViewerJSON");

    // write Viewer JSON file for capacitor array

    int unitScale = 2; /* PnRDB units to angstroms */

    json jsonTop;

    json bbox = json::array();
    bbox.push_back( 0);
    bbox.push_back( 0);
    bbox.push_back( CheckOutBlock.width/unitScale);
    bbox.push_back( CheckOutBlock.height/unitScale);

    jsonTop["bbox"] = bbox;

    jsonTop["globalRoutes"] = json::array();
    jsonTop["globalRouteGrid"] = json::array();

    json terminals = json::array();

    //writing metals
    
    auto doit0 = [&](const auto& n_array) {
	for(unsigned int i=0; i< n_array.size(); i++){//for each net
	    const auto& n = n_array[i];
	    for(unsigned int j=0; j< n.start_connection_pos.size();j++){ //for segment

		const auto& mi = drc_info.Metal_info.at(drc_info.Metalmap.at(n.metal[j]));
		int width = mi.width/2;
		auto box = fillPathBBox (n.start_connection_pos[j],
					 n.end_connection_pos[j], width) / unitScale;
		json term;
		term["netName"] = n.name;
		term["layer"] = n.name; //drc_info.Via_model.at(drc_info.Metalmap.at(n.via_metal[j])).name;
		term["layer"] = mi.name;
		term["rect"] = ToJsonAry(box.LL, box.UR);

		terminals.push_back( term);
	    }   
	}
    };
    doit0( Nets_pos);
    doit0( Nets_neg);
  
    auto doit1 = [&](const auto& n_array) {
	for (unsigned int i = 0; i < n_array.size(); i++) {
	    const auto& n = n_array[i];
	    for (unsigned int j = 0; j < n.via_pos.size(); j++) {//the size of via needs to be modified according to different PDK
		const auto& viaRect = drc_info.Via_model.at(drc_info.Metalmap.at(n.via_metal[j])).ViaRect;
		json term;
		term["netName"] = n.name;
		term["layer"] = drc_info.Via_model.at(drc_info.Metalmap.at(n.via_metal[j])).name;

		auto viaBox = (PnRDB::bbox (viaRect[0], viaRect[1]) + (n.via_pos[j] + offset)) / unitScale;
		term["rect"] = ToJsonAry (viaBox.LL, viaBox.UR);

		terminals.push_back( term);
	    }
	}
    };
    doit1( Nets_pos);
    doit1( Nets_neg);

       
    json jsonUnit;
    {
	std::ifstream jsonStream;
	jsonStream.open( fpath+"/"+unit_capacitor+".json");
	// DAKSwap this out for below when we merge with latest
	string fn = fpath + "/" + unit_capacitor + ".json";
        logger->debug("Reading JSON for unit capacitor {0}", fn);
	jsonStream.open(fn);
	jsonStream >> jsonUnit;
    jsonStream.close();
    }


    for (unsigned int i = 0; i < Caps.size(); i++) {
	PnRDB::point half_cap_dim = unit_cap_dim / 2;
	auto pt = Caps[i].pos;

	pt = (pt - half_cap_dim + offset) / unitScale;
	
	int ni = Caps[i].net_index;

	json unitTerminals = jsonUnit["terminals"];
	for (unsigned int j = 0; j < jsonUnit["terminals"].size(); ++j) {
	    const json& term0 = jsonUnit["terminals"][j];
	    	
	    //bool addNetName = true;

	    json term1;
/*
	    if ( ni == -1) {
		if ( term0["netName"] == "PLUS") {
		    term1["netName"] = "dummy_gnd_PLUS";
		} else if ( term0["netName"] == "MINUS") {
		    term1["netName"] = "dummy_gnd_MINUS";
		} else {
		    continue;
		}
	    } else if ( Nets_pos.size() == 2) {
		assert( Nets_neg.size() == 2);
		assert( ni == 0);
		if ( term0["netName"] == "PLUS") {
		} else if ( term0["netName"] == "MINUS") {
		} else {
		    continue;
		}
		if ( addNetName) {
		    term1["netName"] = term0["netName"];
		}
	    } else {
		if ( term0["netName"] == "PLUS") {
		    ostringstream os;
		    os << "PLUS" << 1+ni;
                    std::cout<<"Cap Bug test "<<1+ni<<" "<<os.str()<<" "<<term0["netName"]<<std::endl;
		    if ( addNetName) {
			term1["netName"] = os.str();
		    }
		} else if ( term0["netName"] == "MINUS") {
		    ostringstream os;
		    os << "MINUS" << 1+ni;
                    std::cout<<"Cap Bug test "<<1+ni<<" "<<os.str()<<" "<<term0["netName"]<<std::endl;
		    if ( addNetName) {
			term1["netName"] = os.str();
		    }
		} else {
		    continue;
		}
	    }
*/
	    if ( ni == -1) {
		if ( term0["netName"] == "PLUS") {
		    term1["netName"] = "dummy_gnd_PLUS";
		} else if ( term0["netName"] == "MINUS") {
		    term1["netName"] = "dummy_gnd_MINUS";
		} else {
		    continue;
		}
	    } else {
		if ( term0["netName"] == "PLUS") {
                     term1["netName"] = Nets_pos[ni].name ;
                     logger->debug("Cap Bug test {0} {1}",1+ni,term1["netName"]);
		} else if ( term0["netName"] == "MINUS") {
                     term1["netName"] = Nets_neg[ni].name ;
                     logger->debug("Cap Bug test {0} {1}",1+ni,term1["netName"]);
		} else {
                    continue;
                }

	    }

	    term1["layer"] = term0["layer"];
	    json r0 = term0["rect"];
	    json r1 = json::array();
	    PnRDB::point p0 (r0[0].get<int>(), r0[1].get<int>());
	    PnRDB::point p1 (r0[2].get<int>(), r0[3].get<int>());

	    json z = ToJsonAry (pt + p0, pt + p1);
	    term1["rect"] = z;
	    terminals.push_back( term1);
	}
    }

    jsonTop["terminals"] = terminals;

    {
	std::ofstream jsonStream;
	std::string fn = opath + top_name + ".json";
        logger->debug("Writing JSON for cap array {0}", fn);
	jsonStream.open( fn);
	jsonStream << std::setw(4) << jsonTop;
	jsonStream.close();
    }
}

void Placer_Router_Cap::Common_centroid_capacitor_aspect_ratio(const string& opath, const string& fpath, PnRDB::hierNode& current_node, PnRDB::Drc_info & drc_info, const map<string, PnRDB::lefMacro>& lefData, bool aspect_ratio, int num_aspect){ //if aspect_ratio 1, then do CC with different aspect_ratio; Else not.

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.Common_centroid_capacitor_aspect_ratio");

    for(unsigned int i = 0;i<current_node.Blocks.size();i++){

	//const auto& b = current_node.Blocks[i].instance.back();
	PnRDB::block b = current_node.Blocks[i].instance[current_node.Blocks[i].instance.size()-1];

	if(b.isLeaf == 1 && b.gdsFile ==""){
	    logger->info("CC Capacitor Placement and Router : {0} {1}", current_node.name, b.name);

	    //this block must be CC
	    vector<int> ki;
	    vector<pair<string, string> > pin_names;
	    string unit_capacitor;
            string final_gds;
            pair<string, string> pins;
            for(unsigned int j=0;j<current_node.CC_Caps.size();j++){
                logger->debug("CC debug flag 1");
		if(current_node.CC_Caps[j].CCCap_name == b.name){
                    logger->debug("CC debug flag 2");
		    ki = current_node.CC_Caps[j].size;
                    bool dummy_flag = current_node.CC_Caps[j].dummy_flag;
                    //bool dummy_flag = 1;
		    unit_capacitor = current_node.CC_Caps[j].Unit_capacitor;
		    final_gds = b.master;
                    logger->debug("CC debug flag 3");
		    assert( b.blockPins.size() % 2 == 0);

                    for(unsigned int pin_index=0; pin_index <b.blockPins.size(); pin_index++){
                        int position_minus = b.blockPins[pin_index].name.find("MINUS");
                        if(position_minus!=string::npos){
                           pins.first = b.blockPins[pin_index].name;
                           for(unsigned int pin_index_p=0; pin_index_p <b.blockPins.size(); pin_index_p++){
                              int position_plus = b.blockPins[pin_index_p].name.find("PLUS");
                              std::string first_name_index (pins.first,5);
                              //std::cout<<"first_name_index "<<first_name_index<<" pin name" <<b.blockPins[pin_index].name<<std::endl;
                              if(position_plus!=string::npos){
                                 std::string second_name_index (b.blockPins[pin_index_p].name,4);
                                 //std::cout<<"second_name_index "<<second_name_index<<" pin name" <<b.blockPins[pin_index_p].name<<std::endl;
                                 if(first_name_index==second_name_index){
                                   pins.second = b.blockPins[pin_index_p].name;
                                   //std::cout<<pins.first<<" "<<pins.second<<std::endl;
                                   //std::cout<<"first_name_index "<<first_name_index<<" second_name_index "<<second_name_index<<" found"<<std::endl;
                                   //assert(0);
                                   pin_names.push_back(pins);
                                   break;
                                 }
                                }
                           }
                         }
                    }

                    /*
		    for(unsigned int pin_index=0; pin_index <b.blockPins.size(); pin_index+=2){
			pins.first = b.blockPins[pin_index].name;
			pins.second = b.blockPins[pin_index+1].name;
			pin_names.push_back(pins);
		    }
                    logger->debug("CC debug flag 4");
                    */

		    //std::cout<<"core dump 2"<<std::endl;
		    bool cap_ratio = current_node.CC_Caps[j].cap_ratio;
                    logger->debug("CC debug flag 5");
		    vector<int> cap_r;
		    vector<int> cap_s;
		    if(cap_ratio){                        
			cap_r.push_back(current_node.CC_Caps[j].cap_r);
			cap_s.push_back(current_node.CC_Caps[j].cap_s);
		    }

                    logger->debug("CC debug flag 6");
		    if(aspect_ratio){
			int sum = std::accumulate( ki.begin(), ki.end(), 0);
			double temp_r = ceil(sqrt(sum));
			double temp_s = ceil(sum/temp_r);
			int aspect_num = num_aspect;
			while(aspect_num > 0 && temp_r > 0){

                            if(temp_r*ceil(sum/temp_r)!=sum && ceil(sum/temp_s)*temp_s!=sum){   
			      cap_r.push_back(temp_r);
			      cap_s.push_back(ceil(sum/temp_r));
			      cap_r.push_back(ceil(sum/temp_s));
			      cap_s.push_back(temp_s);
                              aspect_num = aspect_num - 2;
                            }
			    temp_r = temp_r - 1;
			    temp_s = temp_s + 1;

			}

                        if(cap_r.size()==0){
			  temp_r = ceil(sqrt(sum));
			  temp_s = ceil(sum/temp_r);
                          aspect_num = num_aspect;
			  while(aspect_num > 0 && temp_r > 0){

                              if(temp_r*ceil(sum/temp_r)==sum && ceil(sum/temp_s)*temp_s==sum){   
			        cap_r.push_back(temp_r);
			        cap_s.push_back(ceil(sum/temp_r));
			        cap_r.push_back(ceil(sum/temp_s));
			        cap_s.push_back(temp_s);
                                aspect_num = aspect_num - 2;
                              }
			      temp_r = temp_r - 1;
			      temp_s = temp_s + 1;

			  }
                       }
                                                  
		    }
		    //increase other aspect ratio
                    logger->debug("CC debug flag 7");

		    //std::cout<<"New CC 4 "<<j<<std::endl;
		    //std::cout<<"cap_r size "<<cap_r.size()<<std::endl;
                    bool insert_dummy_connection = 0;
		    for(unsigned int q=0;q<cap_r.size();q++){
                        logger->debug("CC debug flag 8");

                        std::string cc_gds_file = final_gds+"_AspectRatio_"+to_string(cap_r[q])+"x"+to_string(cap_s[q]);
   
                        Placer_Router_Cap_clean();

                        Placer_Router_Cap_function(ki, pin_names, fpath, unit_capacitor, cc_gds_file, cap_ratio || aspect_ratio, cap_r[q], cap_s[q], drc_info, lefData, dummy_flag, opath);
                        PnRDB::block temp_block=CheckoutData();

                        if(q!=0){
                            current_node.Blocks[i].instance.push_back(current_node.Blocks[i].instance[0]);
			}
			assert( (int)q == current_node.Blocks[i].instNum);
			current_node.Blocks[i].instNum++;
                        //feedback data
			auto& va = current_node.Blocks[i].instance.at(q);
                        logger->debug("CC Start feed blocks");
			va.width = temp_block.width;
			va.height = temp_block.height;
			va.originBox = temp_block.originBox;
			va.originCenter = temp_block.originCenter;
			va.gdsFile = temp_block.gdsFile;
			va.orient = temp_block.orient;
			va.interMetals = temp_block.interMetals;
			va.interVias = temp_block.interVias;
                        /*
                        for(unsigned int l=0;l<va.blockPins.size();l++){
                          va.blockPins[l].pinContacts.clear();
                        }
                        */
                        for(unsigned int l=0;l<temp_block.blockPins.size();l++){
                           bool found = 0;
                           
                           for(unsigned int k=0;k<va.blockPins.size();k++){

				if(va.blockPins[k].name == temp_block.blockPins[l].name){    
                                    found = 1;
				    va.blockPins[k].pinContacts.clear();
				    for(unsigned int p=0;p<temp_block.blockPins[l].pinContacts.size();p++){
					va.blockPins[k].pinContacts.push_back(temp_block.blockPins[l].pinContacts[p]);
				    }
                                  
				}

                            }
                            //if not found then insert this pin as a power pin and add a dummy pin in 
                            if(!found && !temp_block.blockPins[l].name.empty()){
                            //if(!found){
                                   //create dummy connection and insert power pin
                                   PnRDB::connectNode temp_connectNode;
                                   temp_connectNode.iter2 = i;
                                   temp_connectNode.iter = va.blockPins.size();
                                   temp_block.blockPins[l].netIter = -2;
                                   va.blockPins.push_back(temp_block.blockPins[l]);
                                   //insert the dummy connection power power net
                                     //if power net does not exist, then create a power net
                                   for(unsigned powernet_index = 0;powernet_index<current_node.PowerNets.size();powernet_index++){
                                         if(current_node.PowerNets[powernet_index].power==0 && !insert_dummy_connection){
                                            current_node.PowerNets[powernet_index].dummy_connected.push_back(temp_connectNode);
                                            break;
                                           }
                                      }
                              }
                        }

                        insert_dummy_connection = 1;

			WriteLef(va, cc_gds_file+".lef", opath);
                        logger->debug("CC End feed blocks");
			continue;
		    } 
		}
	    }
	}
    }
}



void Placer_Router_Cap::PrintPlacer_Router_Cap(string outfile){

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.PrintPlacer_Router_Cap");

    logger->debug("Placer-Router-Cap-Info: create gnuplot file");
    ofstream fout;
    fout.open(outfile.c_str());

    //set title
    fout<<"#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)"<<endl;
    fout<<"\nset title\" #capacitors= "<<Caps.size()<<" \""<<endl;
    fout<<"\nset nokey"<<endl;
    fout<<"#   Uncomment these two lines starting with \"set\""<<endl;
    fout<<"#   to save an EPS file for inclusion into a latex document"<<endl;
    fout<<"# set terminal postscript eps color solid 20"<<endl;
    fout<<"# set output \"result.eps\""<<endl<<endl;
    fout<<"#   Uncomment these two lines starting with \"set\""<<endl;
    fout<<"#   to save a PS file for printing"<<endl;
    fout<<"set term jpeg"<<endl;
    fout<<"set output \"result.jpg\""<<endl<<endl;

    //set range
    fout<<"\nset xrange ["<<CheckOutBlock.originBox.LL.x-5000<<":"<<CheckOutBlock.originBox.UR.x+5000<<"]"<<endl;
    fout<<"\nset yrange ["<<CheckOutBlock.originBox.LL.y-5000<<":"<<CheckOutBlock.originBox.UR.y+5000<<"]"<<endl;

  
    //set label for capacitors
    for(unsigned int i=0;i<Caps.size();i++){
	if(Caps[i].net_index!=-1){
	    stringstream ss;
	    ss<<Caps[i].net_index;
	    string cap_name = "C_" + ss.str();;
	    fout<<"\nset label \""<<cap_name<<"\" at "<<Caps[i].pos.x<<" , "<<Caps[i].pos.y<<" center "<<endl;
	}else{
	    string cap_name = "C_d";
	    fout<<"\nset label \""<<cap_name<<"\" at "<<Caps[i].pos.x<<" , "<<Caps[i].pos.y<<" center "<<endl;
	}
	auto pnt = Caps[i].pos - unit_cap_dim / 2;
	fout<<"\nset label \""<<i<<"\" at "<< pnt.x <<" , "<< pnt.y<<" center "<<endl;
    }

    // plot capacitors
    fout<<"\nplot[:][:] \'-\' with lines linestyle 1,";
    for(unsigned int i=0;i<Nets_pos.size();i++){
	fout<<" \'-\' with lines linestyle "<<i+2<<",";
    }
    for(unsigned int i=0;i<Nets_neg.size();i++){
	fout<<" \'-\' with lines linestyle "<<i+2<<",";
    }
    fout<<endl<<endl;

    for(unsigned int i=0;i<Caps.size();i++){
	std::vector<PnRDB::point> signs = { PnRDB::point (-1, -1), PnRDB::point (-1, +1),
					    PnRDB::point (+1, +1), PnRDB::point (+1, -1),
					    PnRDB::point (-1, -1) };
	for (unsigned j = 0; j < signs.size(); j++) {
	    const PnRDB::point half_cap_dim (unit_cap_dim / 2);
	    auto corner = Caps[i].pos + half_cap_dim.scale(signs[j]);
	    fout << "\t" << corner.x << "\t" << corner.y << endl;
	}
	fout<<endl;
    }
    if (Caps.size() > 0) fout<<"\nEOF"<<endl;
    
    // plot connections
    auto plot_nets = [&] (auto& nets) {
	for (unsigned int i = 0; i < nets.size(); i++) {
	    for (unsigned int j = 0; j < nets[i].start_connection_pos.size(); j++) {
		auto spos = nets[i].start_connection_pos[j];
		auto epos = nets[i].end_connection_pos[j];
		fout << "\t" << spos.x << "\t" << spos.y << endl;
		fout << "\t" << epos.x << "\t" << epos.y << endl;
		fout << "\t" << spos.x << "\t" << spos.y << endl;
		fout << endl;
	    }
	    if (nets.size() > 0) fout << "\nEOF" << endl;
	}
    };

    plot_nets (Nets_pos);
    plot_nets (Nets_neg);
    fout.close();
}

void Placer_Router_Cap::WriteLef(const PnRDB::block &temp_block, const string& file, const string& opath){

	auto logger = spdlog::default_logger()->clone("cap_placer.Placer_Router_Cap.WriteLef");

    std::ofstream leffile;
    string leffile_name = opath + file;

    leffile.open(leffile_name);

    auto s = [](int v) {
	return (double) v/2000.0;
    };

    auto p_rect = [&](auto& p,const string& sp) {
	leffile<<sp<<"  LAYER "<< p.metal<<" ;"<<std::endl;
	const auto& b = p.originBox;
	leffile << "        RECT "
	<< s(b.LL.x)<<" "
	<< s(b.LL.y)<<" "
	<< s(b.UR.x)<<" "
	<< s(b.UR.y)<<" ;"<<std::endl;
    };

    leffile<<"MACRO "<<temp_block.master<<std::endl;
    leffile<<"  ORIGIN 0 0 ;"<<std::endl;
    leffile<<"  FOREIGN "<<temp_block.master<<" 0 0 ;"<<std::endl;
    leffile<<"  SIZE "<< s(temp_block.width)<<" BY "<< s(temp_block.height) <<" ;"<<std::endl;

    {
	int m1_pitch = 80;
	if ( temp_block.width % m1_pitch != 0) {
            logger->debug("WriteLef: block boundary off M1 grid (default PDK): {0} {1}",temp_block.width,temp_block.width % m1_pitch);
	}
    }
    {
	int m2_pitch = 84;
	if ( temp_block.height % m2_pitch != 0) {
            logger->debug("WriteLef: block boundary off M2 grid (default PDK): {0} {1}",temp_block.height,temp_block.height % m2_pitch);
	}
    }

    //pins
    for(unsigned int i=0;i<temp_block.blockPins.size();i++){

	leffile<<"  PIN "<<temp_block.blockPins[i].name<<std::endl;
	leffile<<"    DIRECTION INOUT ;"<<std::endl;
	leffile<<"    USE SIGNAL ;"<<std::endl;
	leffile<<"    PORT "<<std::endl;

	for(unsigned int j=0;j<temp_block.blockPins[i].pinContacts.size();j++){
	    const auto& p = temp_block.blockPins[i].pinContacts[j];
	    p_rect( p, "    ");
	    const auto& b = p.originBox;
	    if ( p.metal == "M1") {
		int c = b.center().x;
                logger->debug("M1 LEF PIN {0}",c % 80);
	    }
	    if ( p.metal == "M2") {
		int c = b.center().y;
                logger->debug("M2 LEF PIN {0}",c % 84);
		if ( c % 84 != 0) {
                    logger->debug("WriteLef: M2 LEF PIN off grid: {0} {1}",c,c % 84);
		}
	    }
	}
      
	leffile<<"    END"<<std::endl;
	leffile<<"  END "<<temp_block.blockPins[i].name<<std::endl;
    }

    leffile<<"  OBS "<<std::endl;
    for(unsigned int i=0;i<temp_block.interMetals.size();i++){
	p_rect( temp_block.interMetals[i], "");
    }
    leffile<<"  END "<<std::endl;

    leffile<<"END "<<temp_block.master<<std::endl;
  
    leffile.close();
}
// Local Variables:
// c-basic-offset: 4
// End:
