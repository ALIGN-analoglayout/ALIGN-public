#include "RawRouter.h"

RawRouter::RawRouter():topName("defaultDesign") {
  //this->topName="defaultDesign";
  this->width=0;
  this->height=0;
  this->isTop=false;
  this->grid_scale=1;
  this->lowest_metal=0;
  this->highest_metal=0;
  this->path_number=1;
  this->layerNo=0;
  PnRDB::Drc_info drc_info2; drc_info2.MaxLayer=0; 
  drc_info2.Metalmap.clear(); drc_info2.Viamap.clear();
  drc_info2.Metal_info.clear(); drc_info2.Via_info.clear(); 
  drc_info2.MaskID_Metal.clear(); drc_info2.MaskID_Via.clear();
  this->drc_info=drc_info2;
}

void RawRouter::InsertPlistToSet_x(std::set<RouterDB::SinkData, RouterDB::SinkDataComp>& Set_x, std::vector<std::vector<RouterDB::point> >& plist){
  RouterDB::SinkData temp_sink;
  for(unsigned int i=0;i<plist.size();i++){
      temp_sink.metalIdx = i;
      for(unsigned int j=0;j<plist[i].size();j++){
           RouterDB::point temp_point;
           temp_sink.coord.clear();
           temp_point.x = plist[i][j].x;
           temp_point.y = plist[i][j].y;
           temp_sink.coord.push_back(temp_point);
           //temp_sink.iterNet = plist[i][j].iterNet;
           Set_x.insert(temp_sink);
      }
  }
};

std::vector<std::vector<RouterDB::point> > RawRouter::FindPlist(std::set<RouterDB::SinkData, RouterDB::SinkDataComp>& Set_x, RouterDB::point LL, RouterDB::point UR){
  std::vector<std::vector<RouterDB::point> > plist;
  plist.resize(this->layerNo);

  std::set<RouterDB::SinkData, RouterDB::SinkData2Comp> Set_y;
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp >::iterator itlowx, itupx, xitx;
  std::set<RouterDB::SinkData, RouterDB::SinkData2Comp >::iterator itlowy, itupy, xity; 
  

  //std::cout<<"set@@@@@set"<<std::endl;
  RouterDB::SinkData temp_sink_up;
  RouterDB::SinkData temp_sink_low;
  temp_sink_up.coord.push_back(UR);
  temp_sink_up.metalIdx=this->highest_metal;
  //temp_sink_up.iterNet=this->Nets.size();
  itupx= Set_x.upper_bound(temp_sink_up);//what if on the margin?
  temp_sink_low.coord.push_back(LL);
  temp_sink_low.metalIdx=this->lowest_metal;
  //temp_sink_low.iterNet=-2;
  itlowx = Set_x.lower_bound(temp_sink_low);

  for(xitx=itlowx; xitx!=itupx; ++xitx){
      Set_y.insert(*xitx);
     }

  itupy = Set_y.upper_bound(temp_sink_up);
  itlowy = Set_y.lower_bound(temp_sink_low);
  //for(xitx=itlowx; xitx!=itupx; ++xitx){
  for(xity=itlowy;xity!=itupy;++xity){
       RouterDB::point temp_point;
       temp_point.x = xity->coord[0].x;
       //std::cout<<"FindPlist in this area, x,y,metalIdx,iterNet "<< temp_point.x<<" "<<temp_point.y<<" "<<xity->metalIdx<<std::endl;
       temp_point.y = xity->coord[0].y;
       //temp_point.iterNet = xity->iterNet;
       plist[xity->metalIdx].push_back(temp_point);
  }

  return plist;

};

std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> RawRouter::findviaset(std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> &Pset_via, RouterDB::point LL, RouterDB::point UR){

  std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> set;
  std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp >::iterator itlowx, itupx, xitx; 
  

  //std::cout<<"set@@@@@set"<<std::endl;
  std::pair<int, RouterDB::point> temp_sink_up;
  std::pair<int, RouterDB::point> temp_sink_low;
  temp_sink_up.second=UR;
  temp_sink_up.first=this->highest_metal;
  //temp_sink_up.iterNet=this->Nets.size();
  itupx= Pset_via.upper_bound(temp_sink_up);//what if on the margin?
  temp_sink_low.second=LL;
  temp_sink_low.first=this->lowest_metal;
  //temp_sink_low.iterNet=-2;
  itlowx = Pset_via.lower_bound(temp_sink_low);


  for(xitx=itlowx; xitx!=itupx; ++xitx){
      set.insert(*xitx);
     }

  return set;

};

std::set<RouterDB::SinkData, RouterDB::SinkDataComp> RawRouter::Findset(std::set<RouterDB::SinkData, RouterDB::SinkDataComp>& Set_x, RouterDB::point LL, RouterDB::point UR){

  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> set;
  std::set<RouterDB::SinkData, RouterDB::SinkData2Comp> Set_y;
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp >::iterator itlowx, itupx, xitx;
  std::set<RouterDB::SinkData, RouterDB::SinkData2Comp >::iterator itlowy, itupy, xity; 
  

  //std::cout<<"set@@@@@set"<<std::endl;
  RouterDB::SinkData temp_sink_up;
  RouterDB::SinkData temp_sink_low;
  temp_sink_up.coord.push_back(UR);
  temp_sink_up.metalIdx=this->highest_metal;
  //temp_sink_up.iterNet=this->Nets.size();
  itupx= Set_x.upper_bound(temp_sink_up);//what if on the margin?
  temp_sink_low.coord.push_back(LL);
  temp_sink_low.metalIdx=this->lowest_metal;
  //temp_sink_low.iterNet=-2;
  itlowx = Set_x.lower_bound(temp_sink_low);
  
  //std::cout<<"LL,UR "<<"("<<LL.x<<","<<LL.y<<") ("<<UR.x<<","<<UR.y<<")"<<std::endl;

  for(xitx=itlowx; xitx!=itupx; ++xitx){
      Set_y.insert(*xitx);
     }

  itupy = Set_y.upper_bound(temp_sink_up);
  itlowy = Set_y.lower_bound(temp_sink_low);

  //for(xitx=itlowx; xitx!=itupx; ++xitx){
  for(xity=itlowy;xity!=itupy;++xity){
       set.insert(*xity);
  }

  return set;

};


std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > RawRouter::FindsetPlist(std::set<RouterDB::SinkData, RouterDB::SinkDataComp>& Set_x, RouterDB::point LL, RouterDB::point UR){

  std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > plist;
  plist.resize(this->layerNo);
  std::set<RouterDB::SinkData, RouterDB::SinkData2Comp> Set_y;
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp >::iterator itlowx, itupx, xitx;
  std::set<RouterDB::SinkData, RouterDB::SinkData2Comp >::iterator itlowy, itupy, xity; 
  

  //std::cout<<"set@@@@@set"<<std::endl;
  RouterDB::SinkData temp_sink_up;
  RouterDB::SinkData temp_sink_low;
  temp_sink_up.coord.push_back(UR);
  temp_sink_up.metalIdx=this->highest_metal;
  //temp_sink_up.iterNet=this->Nets.size();
  itupx= Set_x.upper_bound(temp_sink_up);//what if on the margin?
  temp_sink_low.coord.push_back(LL);
  temp_sink_low.metalIdx=this->lowest_metal;
  //temp_sink_low.iterNet=-2;
  itlowx = Set_x.lower_bound(temp_sink_low);
  
  //std::cout<<"LL,UR "<<"("<<LL.x<<","<<LL.y<<") ("<<UR.x<<","<<UR.y<<")"<<std::endl;

  for(xitx=itlowx; xitx!=itupx; ++xitx){
      Set_y.insert(*xitx);
     }

  itupy = Set_y.upper_bound(temp_sink_up);
  itlowy = Set_y.lower_bound(temp_sink_low);

  //for(xitx=itlowx; xitx!=itupx; ++xitx){
  for(xity=itlowy;xity!=itupy;++xity){
       RouterDB::point temp_point;
       temp_point.x = xity->coord[0].x;
       //std::cout<<"FindPlist in this area, x,y,metalIdx,iterNet "<< temp_point.x<<" "<<temp_point.y<<" "<<xity->metalIdx<<std::endl;
       temp_point.y = xity->coord[0].y;
       //temp_point.iterNet = xity->iterNet;
       plist[xity->metalIdx].insert(temp_point);
  }

  return plist;

};

std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > RawRouter::Plist2Set(std::vector<std::vector<RouterDB::point> >& plist){
  std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> Sets;
  for (unsigned int i = 0; i < plist.size();i++){
    std::set<RouterDB::point, RouterDB::pointXYComp> Set;
    for (unsigned int j = 0; j < plist[i].size(); j++)
    {
      Set.insert(plist[i][j]);
    }
    Sets.push_back(Set);
  }
  return Sets;
}

void RawRouter::InsertPlistToSet(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> &Set, std::vector<std::vector<RouterDB::point>> &plist){
  unsigned int size = Set.size();
  if(plist.size()!=size)return;
  for (unsigned int i = 0; i < size;i++){
    for (unsigned int j = 0; j < plist[i].size();j++){
      Set[i].insert(plist[i][j]);
    }
  }
}

std::set<int> RawRouter::CheckOverlap(std::vector<RouterDB::SegPiece>& splist, int LLx, int LLy, int URx, int URy) {
  std::multiset<RouterDB::SegOrder, RouterDB::SegOrderComp > LLxSet, URxSet, LLySet, URySet;
  std::multiset<RouterDB::SegOrder, RouterDB::SegOrderComp >::iterator itlow, itup, xit;
  std::set<int> Set1;
  RouterDB::SegOrder ele;
  // 1. remove outlier from LLx>A(URx)
  // initialize LLx set
  for( std::vector<RouterDB::SegPiece>::iterator it=splist.begin(); it!=splist.end(); ++it) {
    ele.index=it-splist.begin();
    ele.val=it->LLx;
    LLxSet.insert(ele);
  }
  // find upper bound of LLx set
  ele.val=URx;
  itup=LLxSet.upper_bound(ele);
  for(std::multiset<RouterDB::SegOrder, RouterDB::SegOrderComp >::iterator xit=LLxSet.begin(); xit!=itup; ++xit) {
    Set1.insert ( xit->index);
  } // LLxSet [0, URx)

  // 2. remove outlier from URx<A(LLx)
  // initialize URx set
  for(std::set<int>::iterator it=Set1.begin(); it!=Set1.end(); ++it) {
    ele.index=*it;
    ele.val=splist.at(*it).URx;
    URxSet.insert(ele);
  }
  Set1.clear();
  // find lower bound of URx set
  ele.val=LLx;
  itlow=URxSet.lower_bound(ele);
  for(std::multiset<RouterDB::SegOrder, RouterDB::SegOrderComp >::iterator xit=itlow; xit!=URxSet.end(); ++xit) {
    Set1.insert( xit->index );
  } // URxSet [LLx, MAX]

  // 3. remove outlier from LLy>A(URy)
  // initialize LLy set
  for(std::set<int>::iterator it=Set1.begin(); it!=Set1.end(); ++it) {
    ele.index=*it;
    ele.val=splist.at(*it).LLy;
    LLySet.insert(ele);
  }
  Set1.clear();
  // find upper bound of LLy set
  ele.val=URy;
  itup=LLySet.upper_bound(ele);
  for(std::multiset<RouterDB::SegOrder, RouterDB::SegOrderComp >::iterator xit=LLySet.begin(); xit!=itup; ++xit) {
    Set1.insert ( xit->index);
  } // LLySet [0, URy)

  // 4. remove outlier from URy<A(LLy)
  // intialize URy set
  for(std::set<int>::iterator it=Set1.begin(); it!=Set1.end(); ++it) {
    ele.index=*it;
    ele.val=splist.at(*it).URy;
    URySet.insert(ele);
  }
  Set1.clear();
  // find lower bound of URy set
  ele.val=LLy;
  itlow=URySet.lower_bound(ele);
  for(std::multiset<RouterDB::SegOrder, RouterDB::SegOrderComp >::iterator xit=itlow; xit!=URySet.end(); ++xit) {
    Set1.insert( xit->index );
  } // URySet [LLy, MAX]

  return Set1;
  //std::set_intersection(Set1.begin(),Set1.end(),Set2.begin(),Set2.end(),std::inserter(intersect,intersect.begin()));
  //CombSet2.insert(intersect.begin(), intersect.end());

  //intersect.clear();
  //std::set_intersection(CombSet.begin(),CombSet.end(),CombSet2.begin(),CombSet2.end(),std::inserter(intersect,intersect.begin()));
  //return intersect;


}
