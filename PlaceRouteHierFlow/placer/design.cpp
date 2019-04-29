#include "design.h"

design::design() {
  bias_graph=92;
  hasAsymBlock=true;
  hasSymGroup=false;
}

design::design(PnRDB::hierNode& node) {
  bias_graph=node.bias_graph; // from node
  for(vector<PnRDB::blockComplex>::iterator it=node.Blocks.begin(); it!=node.Blocks.end(); it++) {
    block tmpblock;
    tmpblock.name=(it->instance).name;
    //cout<<tmpblock.name<<endl;
    for(vector<PnRDB::point>::iterator pit=(it->instance).originBox.polygon.begin(); pit!=(it->instance).originBox.polygon.end();++pit) {
      placerDB::point tmppoint={pit->x, pit->y};
      tmpblock.boundary.polygon.push_back(tmppoint);
    }
    tmpblock.type=(it->instance).type;
    tmpblock.width=(it->instance).width;
    tmpblock.height=(it->instance).height;
    //cout<<tmpblock.height<<endl;
    // [wbxu] Following lines have be updated to support multi contacts
    for(vector<PnRDB::pin>::iterator pit=(it->instance).blockPins.begin(); pit!=(it->instance).blockPins.end(); pit++) {
      block::pin tmppin;
      placerDB::point tpoint;
      tmppin.name=pit->name;
      tmppin.type=pit->type;
      tmppin.netIter=pit->netIter;
      //cout<<tmppin.name<<endl;
      for(vector<PnRDB::contact>::iterator cit=pit->pinContacts.begin();cit!=pit->pinContacts.end();++cit) {
        tpoint={ cit->originCenter.x, cit->originCenter.y };
        tmppin.center.push_back(tpoint);
        tmppin.boundary.resize(tmppin.boundary.size()+1);
        for(vector<PnRDB::point>::iterator qit=cit->originBox.polygon.begin(); qit!=cit->originBox.polygon.end(); ++qit) {
          tpoint={qit->x, qit->y};
          tmppin.boundary.back().polygon.push_back(tpoint);
        }
      }
      tmpblock.blockPins.push_back(tmppin);
    }
    //it->instance.
    this->Blocks.push_back(tmpblock);
  }
  for(vector<PnRDB::terminal>::iterator it=node.Terminals.begin();it!=node.Terminals.end();++it) {
    terminal tmpter;
    tmpter.name=it->name;
    tmpter.netIter=it->netIter;
    this->Terminals.push_back(tmpter);
  }
  for(vector<PnRDB::net>::iterator it=node.Nets.begin();it!=node.Nets.end();it++) {
    placerDB::net tmpnet;
    tmpnet.name=it->name;
    tmpnet.priority=it->priority;
    for(vector<PnRDB::connectNode>::iterator nit=it->connected.begin(); nit!=it->connected.end(); ++nit) {
      placerDB::NType tmptype;
      if (nit->type==PnRDB::Block) {tmptype=placerDB::Block;}
      else if (nit->type==PnRDB::Terminal) {tmptype=placerDB::Terminal;}
      else {cerr<<"Placer-Error: incorrect connected node type"<<endl;}
      placerDB::Node tmpnode={tmptype, nit->iter, nit->iter2};
      tmpnet.connected.push_back(tmpnode);
    }
    this->Nets.push_back(tmpnet);
  }
  for(vector<PnRDB::SymmPairBlock>::iterator it=node.SPBlocks.begin(); it!=node.SPBlocks.end();++it) {
    this->SPBlocks.resize(SPBlocks.size()+1);
    //vector< pair<int,int> > sympair;
    //vector< pair<int,placerDB::Smark> > selfsym;
    for(vector< pair<int,int> >::iterator sit=it->sympair.begin();sit!=it->sympair.end();++sit) {
      this->SPBlocks.back().sympair.push_back(make_pair(sit->first, sit->second));
    }
    for(vector< pair<int,PnRDB::Smark> >::iterator sit=it->selfsym.begin();sit!=it->selfsym.end();++sit ) {
      placerDB::Smark axis;
      if(sit->second==PnRDB::H) {axis=placerDB::H;}
      else if (sit->second==PnRDB::V) {axis=placerDB::V;}
      else {cout<<"Placer-Error: incorrect Smark"<<endl; continue;}
      this->SPBlocks.back().selfsym.push_back(make_pair(sit->first, axis));
    }
  }
  for(vector<PnRDB::SymmNet>::iterator it=node.SNets.begin();it!=node.SNets.end();++it) {
    placerDB::net tmpnet1,tmpnet2;
    tmpnet1.name=it->net1.name;
    //tmpnet1.priority=it->net1.priority;
    for(vector<PnRDB::connectNode>::iterator nit=it->net1.connected.begin(); nit!=it->net1.connected.end(); ++nit) {
      placerDB::NType tmptype;
      if (nit->type==PnRDB::Block) {tmptype=placerDB::Block;}
      else if (nit->type==PnRDB::Terminal) {tmptype=placerDB::Terminal;}
      else {cerr<<"Placer-Error: incorrect connected node type"<<endl;}
      placerDB::Node tmpnode={tmptype, nit->iter, nit->iter2};
      tmpnet1.connected.push_back(tmpnode);
    }
    tmpnet2.name=it->net2.name;
    //tmpnet2.priority=it->net2.priority;
    for(vector<PnRDB::connectNode>::iterator nit=it->net2.connected.begin(); nit!=it->net2.connected.end(); ++nit) {
      placerDB::NType tmptype;
      if (nit->type==PnRDB::Block) {tmptype=placerDB::Block;}
      else if (nit->type==PnRDB::Terminal) {tmptype=placerDB::Terminal;}
      else {cerr<<"Placer-Error: incorrect connected node type"<<endl;}
      placerDB::Node tmpnode={tmptype, nit->iter, nit->iter2};
      tmpnet2.connected.push_back(tmpnode);
    }
    SymmNet tmpsnet;
    tmpsnet.net1=tmpnet1; tmpsnet.net2=tmpnet2;
    this->SNets.push_back(tmpsnet);
    //cout<<"# " <<this->SNets.size()<<endl;
  }
  for(vector<PnRDB::Preplace>::iterator it=node.Preplace_blocks.begin(); it!=node.Preplace_blocks.end(); ++it) {
    this->Preplace_blocks.resize(this->Preplace_blocks.size()+1);
    this->Preplace_blocks.back().blockid1=it->blockid1;
    this->Preplace_blocks.back().blockid2=it->blockid2;
    this->Preplace_blocks.back().conner=it->conner;
    this->Preplace_blocks.back().distance=it->distance;
    this->Preplace_blocks.back().horizon=it->horizon;
  }
  for(vector<PnRDB::Alignment>::iterator it=node.Alignment_blocks.begin();it!=node.Alignment_blocks.end();++it) {
    this->Alignment_blocks.resize(this->Alignment_blocks.size()+1);
    this->Alignment_blocks.back().blockid1=it->blockid1;
    this->Alignment_blocks.back().blockid2=it->blockid2;
    this->Alignment_blocks.back().distance=it->distance;
    this->Alignment_blocks.back().horizon=it->horizon;
  }
  for(vector<PnRDB::Abument>::iterator it=node.Abument_blocks.begin();it!=node.Abument_blocks.end();++it) {
    this->Abument_blocks.resize(this->Abument_blocks.size()+1);
    this->Abument_blocks.back().blockid1=it->blockid1;
    this->Abument_blocks.back().blockid2=it->blockid2;
    this->Abument_blocks.back().distance=it->distance;
    this->Abument_blocks.back().horizon=it->horizon;
  }
  for(vector<PnRDB::MatchBlock>::iterator it=node.Match_blocks.begin();it!=node.Match_blocks.end();++it) {
    this->Match_blocks.resize(this->Match_blocks.size()+1);
    this->Match_blocks.back().blockid1=it->blockid1;
    this->Match_blocks.back().blockid2=it->blockid2;
  }
  constructSymmGroup();
  hasAsymBlock=checkAsymmetricBlockExist();
  hasSymGroup=(not SBlocks.empty());
}

int design::GetSizeofBlocks() {
  return Blocks.size();
}

int design::GetSizeofTerminals() {
  return Terminals.size();
}

int design::GetSizeofNets() {
  return Nets.size();
}

int design::GetSizeofSBlocks() {
  return SBlocks.size();
}

design::design(string blockfile, string netfile) {
  bias_graph=92;
  readBlockFile(blockfile);
  readNetFile(netfile);
  hasAsymBlock=checkAsymmetricBlockExist();
  hasSymGroup=(not SBlocks.empty());
}

/*
design::design(string blockfile, string netfile, string cfile) {
  bias_graph=100;
  readBlockFile(blockfile);
  readNetFile(netfile);
  readConstFile(cfile);
  constructSymmGroup();
  hasAsymBlock=checkAsymmetricBlockExist();
  hasSymGroup=(not SBlocks.empty());
}
*/
//added by yg
design::design(string blockfile, string netfile, string cfile) {
  bias_graph=92;
  readBlockFile(blockfile);
  readNetFile(netfile);
  readConstFile(cfile);
  constructSymmGroup();
  readRandConstFile(cfile);
  hasAsymBlock=checkAsymmetricBlockExist();
  hasSymGroup=(not SBlocks.empty());
}

design::design(string blockfile, string netfile, string cfile, string random_cfile) {
  bias_graph=92;
  readBlockFile(blockfile);
  readNetFile(netfile);
  readConstFile(cfile);
  constructSymmGroup();
  readRandConstFile(random_cfile);
  hasAsymBlock=checkAsymmetricBlockExist();
  hasSymGroup=(not SBlocks.empty());
}

design::design(string blockfile, string netfile, string cfile, string random_const_file, int write_out_flag) {
  bias_graph=92;
  readBlockFile(blockfile);
  readNetFile(netfile);
  readConstFile(cfile);
  Generate_random_const(random_const_file);
  hasAsymBlock=checkAsymmetricBlockExist();
  hasSymGroup=(not SBlocks.empty());
}


//add be yaguang
void design::Generate_random_const(string random_constrain_file) {
	
	int const_type_number = 4;
	
	//Const_type = [pre-placer,alignment-v,abument-h,matchblocks]
	/*
	1. pre-placer: 200 distance to rr, v
	1. alignment: 0 distance, v.
	2. abument: 0 dsitance, v. w distance h.
	*/
	
	srand (time(NULL));
	
    int Const_size = (rand()%Blocks.size()) /3;
	
	vector<int> Const_type_list;
	pair<int,int> const_pair;
	vector<pair<int,int>> const_pair_vector;
	int Const_type;
	
	for(int i=0;i<= Const_size;i++){
	 Const_type = rand()%const_type_number;
	 Const_type_list.push_back(Const_type);
	}
	
	for(int i=0;i<= Const_size;i++){
		
		//generate const pairs
		const_pair.first = rand()%Blocks.size();
		const_pair.second = rand()%Blocks.size();
		while(const_pair.first == const_pair.second){
		const_pair.second = rand()%Blocks.size();
		}
		//redundant?
		const_pair_vector.push_back(const_pair);
	}
	
	ofstream fout;
	fout.open(random_constrain_file.c_str());
	fout<<"#This is a random constrains file."<<endl;
	//fout<<"Current constrains include preplace, alignment and abutment."<<endl;
	int distance=0;
	for(int i=0;i<= Const_size;i++){
		if(Const_type_list[i]==0){
                        int h_p = (rand()%2);
                        while(distance<100){
                        distance = (rand()%10)*50;
                        }
			fout<<"Preplace ("<<" "<<Blocks[const_pair_vector[i].first].name<<" "<<Blocks[const_pair_vector[i].second].name<<" "<<distance<<" "<<h_p<<" "<<")"<<endl;
                        distance = 0;
		}
		if(Const_type_list[i]==1){
                        int h_ali = (rand()%2);
                        while(distance<100){
                        distance = (rand()%10)*50;
                        }
			fout<<"Alignment ("<<" "<<Blocks[const_pair_vector[i].first].name<<" "<<Blocks[const_pair_vector[i].second].name<<" "<<0<<" "<<h_ali<<" "<<")"<<endl;
                       distance = 0;
		}
		if(Const_type_list[i]==2){
	                 int h_abu = (rand()%2);
                         while(distance<100){
                        distance = (rand()%10)*50;
                        }
			fout<<"Abument ("<<" "<<Blocks[const_pair_vector[i].first].name<<" "<<Blocks[const_pair_vector[i].second].name<<" "<<0<<" "<<h_abu<<" "<<")"<<endl;
                         distance = 0;
		}
		if(Const_type_list[i]==3){
	                 int h_abu = (rand()%2);
                         while(distance<100){
                        distance = (rand()%10)*50;
                        }
			//fout<<"MatchBlock ("<<" "<<Blocks[const_pair_vector[i].first].name<<" "<<Blocks[const_pair_vector[i].second].name<<" "<<0<<" "<<h_abu<<" "<<")"<<endl;
			fout<<"MatchBlock ("<<" "<<Blocks[const_pair_vector[i].first].name<<" "<<Blocks[const_pair_vector[i].second].name<<" "<<")"<<endl;
                         distance = 0;
		}
		
	}

	int bias_graph = 0;
	while(bias_graph<200){	
    bias_graph = (rand()%10) *50;
    }	
	
	fout<<"bias_graph ("<<" "<<bias_graph<<" "<<")"<<endl;	
	
	fout.close();
}

void design::readRandConstFile(string random_constrain_file) {
	ifstream fin;
	string def;
	fin.open(random_constrain_file.c_str());
	
	vector<string> temp, tempsec;
	size_t found;
	
	int *p=0;
	int p_temp=0;
	p=&p_temp;
	
	while(!fin.eof()) {
		getline(fin, def);
		temp=split_by_spaces(def);
		
		
		if(temp[0].compare("Preplace")==0){
			string block_first=temp[2];
			string block_second=temp[3];
			int distance= atoi(temp[4].c_str());
			int horizon = atoi(temp[5].c_str());
                
			Preplace preplace_const;
			for(int i=0;i<(int)Blocks.size();i++) {
			     if(Blocks.at(i).name.compare(block_first)==0) {
					 preplace_const.blockid1 = i;
					 break;
				 }
			}
			for(int i=0;i<(int)Blocks.size();i++) {
				if(Blocks.at(i).name.compare(block_second)==0) {
					preplace_const.blockid2 = i;
					break;
				}else
				{ 
				  preplace_const.conner = block_second;
				}
			}
			preplace_const.distance = distance;
			preplace_const.horizon = horizon;
			Preplace_blocks.push_back(preplace_const);
		}
		
		if(temp[0].compare("Alignment")==0){
			string block_first=temp[2];
			string block_second=temp[3];
			int distance= atoi(temp[4].c_str());
			int horizon = atoi(temp[5].c_str());

			Alignment alignment_const;
			for(int i=0;i<(int)Blocks.size();i++) {
				if(Blocks.at(i).name.compare(block_first)==0) {
					alignment_const.blockid1 = i;
					break;
				}
			}
			for(int i=0;i<(int)Blocks.size();i++) {
				if(Blocks.at(i).name.compare(block_second)==0) {
					alignment_const.blockid2 = i;
					break;
				}
			}
			alignment_const.distance = distance;
			alignment_const.horizon = horizon;
			Alignment_blocks.push_back(alignment_const);	
		}
		
		if(temp[0].compare("Abument")==0){
			string block_first=temp[2];
			string block_second=temp[3];
			int distance= atoi(temp[4].c_str());
			int horizon = atoi(temp[5].c_str());
			
			Abument abument_const;
			
			for(int i=0;i<(int)Blocks.size();i++) {
				if(Blocks.at(i).name.compare(block_first)==0) {
					abument_const.blockid1 = i;
					break;
				}
			}
			for(int i=0;i<(int)Blocks.size();i++) {
				if(Blocks.at(i).name.compare(block_second)==0) {
					abument_const.blockid2 = i;
					break;
				}
			}
			abument_const.distance = distance;
			abument_const.horizon = horizon;
			Abument_blocks.push_back(abument_const);
		}
		if(temp[0].compare("MatchBlock")==0){
			string block_first=temp[2];
			string block_second=temp[3];
			//int distance= atoi(temp[4].c_str());
			//int horizon = atoi(temp[5].c_str());
			
			MatchBlock match_const;
			
			for(int i=0;i<(int)Blocks.size();i++) {
				if(Blocks.at(i).name.compare(block_first)==0) {
					match_const.blockid1 = i;
					break;
				}
			}
			for(int i=0;i<(int)Blocks.size();i++) {
				if(Blocks.at(i).name.compare(block_second)==0) {
					match_const.blockid2 = i;
					break;
				}
			}
			//match_const.distance = distance;
			//match_const.horizon = horizon;
			Match_blocks.push_back(match_const);
		}
		if(temp[0].compare("bias_graph")==0){

			int distance= atoi(temp[2].c_str());
                	bias_graph = distance;
			//Preplace_blocks.push_back(preplace_const);
		}		

	
	}
    
	
	
}

//


void design::readNetFile(string netfile) {
  ifstream fin;
  string def;
  fin.open(netfile.c_str());
  
  vector<string> temp;
  size_t found;
  
  int *p=0;
  int p_temp=0;
  p=&p_temp;

  int netNo, pinNo;
  while(!fin.eof()) {
    getline(fin, def);
    if((found=def.find("NumNets"))!=string::npos) {
      temp=get_true_word(found,def,0,';',p);
      netNo=stoi(temp[2]);
      break;
    }
  }
 
  while(!fin.eof()) {
    getline(fin, def);
    if((found=def.find("NumPins"))!=string::npos) {
      temp=get_true_word(found,def,0,';',p);
      pinNo=stoi(temp[2]);
      break;
    }
  }
  cout<<"Placer-Info: reading "<<netNo<<" nets and "<<pinNo<<" pins ..."<<endl;
  while(!fin.eof()) {
    getline(fin,def);
    if((found=def.find(":"))!=string::npos) {
      temp=split_by_spaces(def);
      string netname=temp[0];
      int dno=stoi(temp[2]);
      vector<placerDB::Node> tmpNlist;
      //cout<<netname<<" "<<temp[2]<<endl;
      for(int i=0;i<dno;i++) {
        getline(fin,def);
        temp=split_by_spaces(def);
        placerDB::Node tmpNode;
        bool mark=false;
        if(temp[0].compare("terminal")==0) {
          for(int k=0;k<(int)Terminals.size(); k++) {
            if(mark) {break;}
            if(Terminals.at(k).name.compare(temp[1])==0) {
              tmpNode.type=placerDB::Terminal;
              tmpNode.iter=k;
              tmpNode.iter2=-1;
              Terminals.at(k).netIter=(int)Nets.size();
              mark=true;
            }
          }
        } else {
          for(int k=0;k<(int)Blocks.size(); k++) {
            if(mark) {break;}
            if(Blocks.at(k).name.compare(temp[0])==0) {
              for(int j=0;j<(int)Blocks.at(k).blockPins.size();j++) {
                if(mark) {break;}
                if(Blocks.at(k).blockPins.at(j).name.compare(temp[1])==0) {
                  tmpNode.type=placerDB::Block;
                  tmpNode.iter=j;
                  tmpNode.iter2=k;
                  Blocks.at(k).blockPins.at(j).netIter=(int)Nets.size();
                  mark=true;
                }
              }
            }
          }
        }
        tmpNlist.push_back(tmpNode);
        //cout<<def<<endl;
      }
      Nets.resize(Nets.size()+1);
      Nets.back().connected=tmpNlist;
      Nets.back().name=netname;
    }
  }
}

void design::readBlockFile(string blockfile) {
  ifstream fin;
  string def;
  fin.open(blockfile.c_str());
  
  vector<string> temp, tempsec;
  size_t found;
  
  int *p=0;
  int p_temp=0;
  p=&p_temp;
  
  placerDB::point p1,p2,p3,p4;
  int blockNo, terminalNo;
  while(!fin.eof()) {
    getline(fin, def);
    if((found=def.find("NumHardRectilinearBlocks"))!=string::npos) {
      temp=get_true_word(found,def,0,';',p);
      blockNo=stoi(temp[2]);
      break;
    }
  }
 
  while(!fin.eof()) {
    getline(fin, def);
    if((found=def.find("NumTerminals"))!=string::npos) {
      temp=get_true_word(found,def,0,';',p);
      terminalNo=stoi(temp[2]);
      break;
    }
  }
  cout<<"Placer-Info: reading "<<blockNo<<" blocks and "<<terminalNo<<" terminals ..."<<endl;
  getline(fin, def); 
  for(int i=0;i<blockNo;i++) {
    getline(fin, def);
    //cout<<i<<"-"<<def;
    temp=split_by_spaces(def);
    block tmpblock;
    tmpblock.SBidx=-1;
    tmpblock.counterpart=-1;
    tmpblock.name=temp[0];
    tmpblock.type=temp[1];
    found=def.find("(");
    temp=get_true_word(found,def,0,';',p);
    //int width, height;
    p1.x=stoi(temp[0].substr(1,temp[0].length()-2)); p1.y=stoi(temp[1].substr(0,temp[1].length()-1));
    p2.x=stoi(temp[2].substr(1,temp[2].length()-2)); p2.y=stoi(temp[3].substr(0,temp[3].length()-1));
    p3.x=stoi(temp[4].substr(1,temp[4].length()-2)); p3.y=stoi(temp[5].substr(0,temp[5].length()-1));
    p4.x=stoi(temp[6].substr(1,temp[6].length()-2)); p4.y=stoi(temp[7].substr(0,temp[7].length()-1));
    tmpblock.width=abs(p3.x-p1.x);
    tmpblock.height=abs(p2.y-p1.y);
    tmpblock.boundary.polygon.push_back(p1);
    tmpblock.boundary.polygon.push_back(p2);
    tmpblock.boundary.polygon.push_back(p3);
    tmpblock.boundary.polygon.push_back(p4);
    //tmpblock.blockPins.resize(tmpblock.blockPins.size()+1);
    //tmpblock.blockPins.back().name="B";
    Blocks.push_back(tmpblock);
    //cout<<p1.x<<p1.y<<p2.x<<p2.y<<p3.x<<p3.y<<p4.x<<p4.y<<endl;
    //cout<<temp[0]<<endl;
  }
  //cout<<"end"<<endl;
  while(!fin.eof()) {
    getline(fin, def);
    if((found=def.find("BLOCK"))!=string::npos) {
      temp=split_by_spaces(def);
      //cout<<temp[1]<<" "<<temp[temp.size()-2]<<endl;
      int bi;
      int pno=stoi(temp[temp.size()-2]);
      string target=temp[1];
      for(bi=0;bi<(int)Blocks.size();bi++) {
        if(Blocks.at(bi).name.compare(target)==0) { break; }
      }
      for(int i=0;i<pno;i++) {
        getline(fin, def);
        if((found=def.find("INT"))==string::npos) {
          tempsec=split_by_spaces(def);
          //cout<<def<<endl;
          p1.x=stoi(tempsec[2].substr(1,tempsec[2].length()-2)); p1.y=stoi(tempsec[3].substr(0,tempsec[3].length()-1));
          p2.x=stoi(tempsec[4].substr(1,tempsec[4].length()-2)); p2.y=stoi(tempsec[5].substr(0,tempsec[5].length()-1));
          p3.x=stoi(tempsec[6].substr(1,tempsec[6].length()-2)); p3.y=stoi(tempsec[7].substr(0,tempsec[7].length()-1));
          p4.x=stoi(tempsec[8].substr(1,tempsec[8].length()-2)); p4.y=stoi(tempsec[9].substr(0,tempsec[9].length()-1));
          //cout<<tempsec[0]<<" "<<tempsec[1]<<" "<<p1.x<<","<<p1.y<<" "<<p2.x<<","<<p2.y<<" "<<p3.x<<","<<p3.y<<" "<<p4.x<<","<<p4.y<<endl;
          Blocks.at(bi).blockPins.resize(Blocks.at(bi).blockPins.size()+1);
          Blocks.at(bi).blockPins.back().name=tempsec[0];
          Blocks.at(bi).blockPins.back().center.resize(Blocks.at(bi).blockPins.back().center.size()+1);
          Blocks.at(bi).blockPins.back().center.back().x=(p3.x+p1.x)/2;
          Blocks.at(bi).blockPins.back().center.back().y=(p2.y+p1.y)/2;
          Blocks.at(bi).blockPins.back().boundary.resize(Blocks.at(bi).blockPins.back().boundary.size()+1);
          Blocks.at(bi).blockPins.back().boundary.back().polygon.push_back(p1);
          Blocks.at(bi).blockPins.back().boundary.back().polygon.push_back(p2);
          Blocks.at(bi).blockPins.back().boundary.back().polygon.push_back(p3);
          Blocks.at(bi).blockPins.back().boundary.back().polygon.push_back(p4);
        }
      }
    }
    if((found=def.find("terminal"))!=string::npos) {
      for(int i=0;i<terminalNo;i++) {
        temp=split_by_spaces(def);
        terminal tmpterm;
        tmpterm.name=temp[0];
        Terminals.push_back(tmpterm);
        //cout<<tmpterm.name<<endl;
        getline(fin, def);
      }
    //  break;
    }
  }
  
}

void design::readConstFile(string cfile) {
  ifstream fin;
  string def;
  fin.open(cfile.c_str());
  
  vector<string> temp, tempsec;
  size_t found;
  
  int *p=0;
  int p_temp=0;
  p=&p_temp;
  
  while(!fin.eof()) {
    getline(fin, def);
    temp=split_by_spaces(def);
    if(temp[0].compare("SymmNet")==0) {
      string word=temp[2];
      word=word.substr(1);
      word=word.substr(0, word.length()-1);
      //cout<<word<<endl;
      tempsec=StringSplitbyChar(word, ',');
      //cout<<tempsec[0]<<" "<<tempsec[1]<<endl;
      placerDB::net tmpnet;
      for(vector<string>::iterator it=tempsec.begin(); it!=tempsec.end(); it++) {
        if(it==tempsec.begin()) {
          tmpnet.name=*it;
        } else {
          if(it->find("/")!=string::npos) {
            vector<string> tempthd=StringSplitbyChar(*it, '/');
            for(int i=0;i<(int)Blocks.size();i++) {
              if(Blocks.at(i).name.compare(tempthd[0])==0) {
                for(int j=0;j<(int)Blocks.at(i).blockPins.size();j++) {
                  if(Blocks.at(i).blockPins.at(j).name.compare(tempthd[1])==0) {
                    //cout<<j<<i<<endl;
                    placerDB::Node newnode={placerDB::Block, j, i};
                    tmpnet.connected.push_back(newnode);
                    break;
                  }
                }
                break;
              }
            }
            //cout<<*it<<" is pin"<<tempthd[0]<<tempthd[1]<<endl;
          } else {
            for(int i=0;i<(int)Terminals.size();i++) {
              if(Terminals.at(i).name.compare(*it)==0) {
                placerDB::Node newnode={placerDB::Terminal, i, -1};
                tmpnet.connected.push_back(newnode);
                break;
              }
            }
            //cout<<*it<<" is terminal"<<endl;
          }
        }
      }
      word=temp[4];
      word=word.substr(1);
      word=word.substr(0, word.length()-1);
      tempsec=StringSplitbyChar(word, ',');
      placerDB::net tmpnet2;
      for(vector<string>::iterator it=tempsec.begin(); it!=tempsec.end(); it++) {
        if(it==tempsec.begin()) {
          tmpnet2.name=*it;
        } else {
          if(it->find("/")!=string::npos) {
            vector<string> tempthd=StringSplitbyChar(*it, '/');
            for(int i=0;i<(int)Blocks.size();i++) {
              if(Blocks.at(i).name.compare(tempthd[0])==0) {
                for(int j=0;j<(int)Blocks.at(i).blockPins.size();j++) {
                  if(Blocks.at(i).blockPins.at(j).name.compare(tempthd[1])==0) {
                    //cout<<j<<i<<endl;
                    placerDB::Node newnode={placerDB::Block, j, i};
                    tmpnet2.connected.push_back(newnode);
                    break;
                  }
                }
                break;
              }
            }
            //cout<<*it<<" is pin"<<tempthd[0]<<tempthd[1]<<endl;
          } else {
            for(int i=0;i<(int)Terminals.size();i++) {
              if(Terminals.at(i).name.compare(*it)==0) {
                placerDB::Node newnode={placerDB::Terminal, i, -1};
                tmpnet2.connected.push_back(newnode);
                break;
              }
            }
            //cout<<*it<<" is terminal"<<endl;
          }
        }
      }
      SNets.resize(SNets.size()+1);
      SNets.back().net1=tmpnet;
      SNets.back().net2=tmpnet2;
    } else if (temp[0].compare("CritNet")==0) {
      for(int i=0;i<(int)Nets.size();i++) {
        if(Nets.at(i).name.compare(temp[2])==0) {
          Nets.at(i).priority=temp[4];
          break;
        }
      }
    }
  }
}

design::design(const design& other) {
  this->Blocks=other.Blocks;
  this->Terminals=other.Terminals;
  this->Nets=other.Nets;
  this->SNets=other.SNets;
  this->SBlocks=other.SBlocks;
  this->Preplace_blocks=other.Preplace_blocks;
  this->Alignment_blocks=other.Alignment_blocks;
  this->Abument_blocks=other.Abument_blocks;
  this->Match_blocks=other.Match_blocks;
  this->bias_graph=other.bias_graph;
  this->hasAsymBlock=other.hasAsymBlock;
  this->hasSymGroup=other.hasSymGroup;
}

design& design::operator= (const design& other) {
  this->Blocks=other.Blocks;
  this->Terminals=other.Terminals;
  this->Nets=other.Nets;
  this->SNets=other.SNets;
  this->SBlocks=other.SBlocks;
  this->Preplace_blocks=other.Preplace_blocks;
  this->Alignment_blocks=other.Alignment_blocks;
  this->Abument_blocks=other.Abument_blocks;
  this->Match_blocks=other.Match_blocks;
  this->bias_graph=other.bias_graph;
  this->hasAsymBlock=other.hasAsymBlock;
  this->hasSymGroup=other.hasSymGroup;
  return *this;
}

void design::PrintDesign() {
  cout<<"== Print Design "<<endl;
  cout<<"bias_graph: "<<bias_graph<<endl;
  PrintBlocks();
  PrintTerminals();
  PrintNets();
  PrintConstraints();
  PrintSymmGroup();
}

void design::PrintSymmGroup() {
  cout<<endl<<"=== Symmetric Groups ==="<<endl;
  for(vector<placerDB::SymmBlock>::iterator si=SBlocks.begin(); si!=SBlocks.end(); ++si) {
    cout<<"Group node: "<<si->dnode<<endl;
    for(vector<pair<int,int> >::iterator pi=si->sympair.begin(); pi!=si->sympair.end(); ++pi) {
      cout<<"\tsymmetric pair "<<pi->first<<" vs "<<pi->second<<endl;
    }
    for(vector<pair<int,placerDB::Smark> >::iterator pi=si->selfsym.begin(); pi!=si->selfsym.end(); ++pi) {
      cout<<"\tself-symmetric "<<pi->first<<" at "<<pi->second<<endl;
    }
  }
}

void design::PrintBlocks() {
  cout<<"=== Blocks ==="<<endl;
  for(vector<block>::iterator it=Blocks.begin(); it!=Blocks.end(); it++) {
    cout<<"Name: "<<(*it).name<<"; SBidx: "<<it->SBidx<<"; counterpart: "<<it->counterpart<<endl;
    cout<<"\ttype: "<<(*it).type<<"; width: "<<(*it).width<<"; height: "<<(*it).height<<"; bbox: ";
    for(vector<placerDB::point>::iterator it2=(*it).boundary.polygon.begin(); it2!=(*it).boundary.polygon.end(); ++it2 ) {
      cout<<"{"<<(*it2).x<<","<<(*it2).y<<"}";
    }
    cout<<endl;
    for(vector<block::pin>::iterator it3=it->blockPins.begin(); it3!=it->blockPins.end(); ++it3) {
      cout<<"\tPin: "<<it3->name<<" net:"<<it3->netIter<<" center:";
      for(vector<placerDB::point>::iterator it4=it3->center.begin();it4!=it3->center.end();++it4) {
        cout<<" {"<<it4->x<<","<<it4->y<<"}";
      }
      cout<<"\t\tbbox: ";
      for(vector<placerDB::bbox>::iterator it5=it3->boundary.begin();it5!=it3->boundary.end();++it5) {
        cout<<" {";
        for(vector<placerDB::point>::iterator it4=it5->polygon.begin(); it4!=it5->polygon.end(); ++it4) {
          cout<<" {"<<it4->x<<","<<it4->y<<"}";
        }
        cout<<" }";
      }
      cout<<endl;
    }
    cout<<endl;
  }
}

void design::PrintConstraints() {
  cout<<"=== SymmNet Constraits ==="<<endl;
  for(vector<SymmNet>::iterator it=SNets.begin(); it!=SNets.end(); ++it) {
    cout<<it->net1.name;
    for(vector<placerDB::Node>::iterator ni=it->net1.connected.begin(); ni!=it->net1.connected.end(); ni++) {
      cout<<"-{"<<ni->type<<","<<ni->iter<<","<<ni->iter2<<"}";
      if(ni->type==placerDB::Block) {cout<<"@"<<Blocks.at(ni->iter2).name<<"/"<<Blocks.at(ni->iter2).blockPins.at(ni->iter).name;}
      if(ni->type==placerDB::Terminal) {cout<<"@"<<Terminals.at(ni->iter).name;}
    }
    cout<<" "<<it->net2.name;
    for(vector<placerDB::Node>::iterator ni=it->net2.connected.begin(); ni!=it->net2.connected.end(); ni++) {
      cout<<"-{"<<ni->type<<","<<ni->iter<<","<<ni->iter2<<"}";
      if(ni->type==placerDB::Block) {cout<<"@"<<Blocks.at(ni->iter2).name<<"/"<<Blocks.at(ni->iter2).blockPins.at(ni->iter).name;}
      if(ni->type==placerDB::Terminal) {cout<<"@"<<Terminals.at(ni->iter).name;}
    }
    cout<<endl;
  }
  cout<<"=== SymmPairBlock Constraints ==="<<endl;
  for(vector<SymmPairBlock>::iterator it=SPBlocks.begin(); it!=SPBlocks.end(); ++it) {
    for(vector< pair<int,int> >::iterator sit=it->sympair.begin(); sit!=it->sympair.end(); ++sit ) {
      cout<<"sympair "<<sit->first<<"@"<<Blocks.at(sit->first).name<<" vs "<<sit->second<<"@"<<Blocks.at(sit->second).name<<endl;
    }
    for(vector< pair<int,placerDB::Smark> >::iterator sit=it->selfsym.begin();sit!=it->selfsym.end();++sit) {
      cout<<"selfsym "<<sit->first<<"@"<<Blocks.at(sit->first).name<<" symmetric to "<<sit->second<<endl;
    }
  }
  cout<<"=== Preplace_blocks Constraits ==="<<endl;
  for(vector<Preplace>::iterator it=Preplace_blocks.begin();it!=Preplace_blocks.end();++it) {
    cout<<"block1-"<<it->blockid1<<" ;block2-"<<it->blockid2<<" ;corner-"<<it->conner<<" ;distance-"<<it->distance<<" ;horizon-"<<it->horizon<<endl;
  }
  cout<<"=== Alignment_blocks Constraits ==="<<endl;
  for(vector<Alignment>::iterator it=Alignment_blocks.begin();it!=Alignment_blocks.end();++it) {
    cout<<"block1-"<<it->blockid1<<" ;block2-"<<it->blockid2<<" ;distance-"<<it->distance<<" ;horizon-"<<it->horizon<<endl;
  }
  cout<<"=== Abument_blocks Constraits ==="<<endl;
  for(vector<Abument>::iterator it=Abument_blocks.begin();it!=Abument_blocks.end();++it) {
    cout<<"block1-"<<it->blockid1<<" ;block2-"<<it->blockid2<<" ;distance-"<<it->distance<<" ;horizon-"<<it->horizon<<endl;
  }
  cout<<"=== Match_blocks Constraits ==="<<endl;
  for(vector<MatchBlock>::iterator it=Match_blocks.begin();it!=Match_blocks.end();++it) {
    cout<<"block1-"<<it->blockid1<<" ;block2-"<<it->blockid2<<endl;
  }
}

void design::PrintTerminals() {
  cout<<"=== Terminals ==="<<endl;
  for(vector<terminal>::iterator it=Terminals.begin(); it!=Terminals.end(); ++it) {
    cout<<"Name: "<<it->name<<" net:"<<it->netIter<<"@"<<Nets.at(it->netIter).name<<endl;
  }
  cout<<endl;
}

void design::PrintNets() {
  cout<<"=== Nets ==="<<endl;
  for(vector<placerDB::net>::iterator it=Nets.begin(); it!=Nets.end(); ++it) {
    cout<<"Name: "<<(*it).name<<" Priority: "<<it->priority<<endl;
    cout<<"\tConnected: "<<endl;
    for(vector<placerDB::Node>::iterator it2=(*it).connected.begin(); it2!=(*it).connected.end(); ++it2) {
      cout<<"\t\ttype: "<<(*it2).type<<"; iter: "<<(*it2).iter<<"; iter2:"<<(*it2).iter2;
      if(it2->type==placerDB::Block) {cout<<" "<<Blocks.at(it2->iter2).name<<"/"<<Blocks.at(it2->iter2).blockPins.at(it2->iter).name<<endl;}
      if(it2->type==placerDB::Terminal) {cout<<" "<<Terminals.at(it2->iter).name<<endl;}
    }
  }
  cout<<endl;
}

int design::GetBlockWidth(int blockid, placerDB::Omark ort) {
  if(ort==placerDB::N or ort==placerDB::S or ort==placerDB::FN or ort==placerDB::FS) {
  return Blocks.at(blockid).width;
  } else {
  return Blocks.at(blockid).height;
  }
}

int design::GetBlockHeight(int blockid, placerDB::Omark ort) {
  if(ort==placerDB::N or ort==placerDB::S or ort==placerDB::FN or ort==placerDB::FS) {
  return Blocks.at(blockid).height;
  } else {
  return Blocks.at(blockid).width;
  }
}

placerDB::point design::GetBlockCenter(int blockid, placerDB::Omark ort) {
  placerDB::point p;
  p.x=GetBlockWidth(blockid, ort)/2;
  p.y=GetBlockHeight(blockid, ort)/2;
  return p;
}

placerDB::point design::GetBlockAbsCenter(int blockid, placerDB::Omark ort, placerDB::point LL) {
  placerDB::point p;
  p.x=GetBlockWidth(blockid, ort)/2+LL.x;
  p.y=GetBlockHeight(blockid, ort)/2+LL.y;
  return p;
}


placerDB::point design::GetPlacedPosition(placerDB::point oldp, int width, int height, placerDB::Omark ort) {
  placerDB::point p;
  int WW=width; int HH=height; int X=oldp.x; int Y=oldp.y;
  switch(ort) {
    case placerDB::N: p.x=X;	p.y=Y;
            break;
    case placerDB::S: p.x=WW-X;	p.y=HH-Y;
            break;
    case placerDB::W: p.x=HH-Y;	p.y=X;
            break;
    case placerDB::E: p.x=Y;	p.y=WW-X;
            break;
    case placerDB::FN:p.x=WW-X;	p.y=Y; 
            break;
    case placerDB::FS:p.x=X;	p.y=HH-Y;
            break;
    case placerDB::FW:p.x=Y;	p.y=X;
            break;
    case placerDB::FE:p.x=HH-Y;	p.y=WW-X;
            break;
    default:p.x=X;	p.y=Y;
            break;
  }
  return p;
}

PnRDB::point design::GetPlacedPnRPosition(PnRDB::point oldp, int width, int height, placerDB::Omark ort) {
  PnRDB::point p;
  int WW=width; int HH=height; int X=oldp.x; int Y=oldp.y;
  switch(ort) {
    case placerDB::N: p.x=X;	p.y=Y;
            break;
    case placerDB::S: p.x=WW-X;	p.y=HH-Y;
            break;
    case placerDB::W: p.x=HH-Y;	p.y=X;
            break;
    case placerDB::E: p.x=Y;	p.y=WW-X;
            break;
    case placerDB::FN:p.x=WW-X;	p.y=Y; 
            break;
    case placerDB::FS:p.x=X;	p.y=HH-Y;
            break;
    case placerDB::FW:p.x=Y;	p.y=X;
            break;
    case placerDB::FE:p.x=HH-Y;	p.y=WW-X;
            break;
    default:p.x=X;	p.y=Y;
            break;
  }
  return p;
}



vector<placerDB::point> design::GetPlacedBlockPinRelPosition(int blockid, int pinid, placerDB::Omark ort) {
  vector<placerDB::point> newCenter;
  for(vector<placerDB::point>::iterator it=Blocks.at(blockid).blockPins.at(pinid).center.begin();it!=Blocks.at(blockid).blockPins.at(pinid).center.end();++it) {
    newCenter.push_back( GetPlacedPosition(*it, Blocks.at(blockid).width, Blocks.at(blockid).height, ort) );
  }
  return newCenter;
  //return GetPlacedPosition(Blocks.at(blockid).blockPins.at(pinid).center, Blocks.at(blockid).width, Blocks.at(blockid).height, ort);
}

vector<placerDB::point> design::GetPlacedBlockPinAbsPosition(int blockid, int pinid, placerDB::Omark ort, placerDB::point LL) {
  vector<placerDB::point> p;
  p=GetPlacedBlockPinRelPosition(blockid, pinid, ort);
  for(vector<placerDB::point>::iterator it=p.begin();it!=p.end();++it) {
    (it->x)+=LL.x; (it->y)+=LL.y;
  }
  return p;
}

vector<placerDB::point> design::GetPlacedBlockRelBoundary(int blockid, placerDB::Omark ort) {
  vector<placerDB::point> newp;
  for(vector<placerDB::point>::iterator it=Blocks.at(blockid).boundary.polygon.begin(); it!=Blocks.at(blockid).boundary.polygon.end(); ++it) {
    newp.push_back( GetPlacedPosition(*it, Blocks.at(blockid).width, Blocks.at(blockid).height, ort) );
  }
  return newp;
}

vector<placerDB::point> design::GetPlacedBlockAbsBoundary(int blockid, placerDB::Omark ort, placerDB::point LL) {
  vector<placerDB::point> newp=GetPlacedBlockRelBoundary(blockid, ort);
  for(vector<placerDB::point>::iterator it=newp.begin(); it!=newp.end(); ++it) {
    (it->x)+=LL.x;
    (it->y)+=LL.y;
  }
  return newp;
}

vector<vector<placerDB::point> > design::GetPlacedBlockPinRelBoundary(int blockid, int pinid, placerDB::Omark ort) {
  vector<vector<placerDB::point> > newp;
  for(vector<placerDB::bbox>::iterator it=Blocks.at(blockid).blockPins.at(pinid).boundary.begin(); it!=Blocks.at(blockid).blockPins.at(pinid).boundary.end(); ++it) {
    newp.resize(newp.size()+1);
    for(vector<placerDB::point>::iterator it2=it->polygon.begin();it2!=it->polygon.end();++it2) {
      newp.back().push_back( GetPlacedPosition(*it2, Blocks.at(blockid).width, Blocks.at(blockid).height, ort) );
    }
  }
  //for(vector<placerDB::point>::iterator it=Blocks.at(blockid).blockPins.at(pinid).boundary.polygon.begin(); it!=Blocks.at(blockid).blockPins.at(pinid).boundary.polygon.end(); ++it) {
  //  newp.push_back( GetPlacedPosition(*it, Blocks.at(blockid).width, Blocks.at(blockid).height, ort) );
  //}
  return newp;
}

vector<vector<placerDB::point> > design::GetPlacedBlockPinAbsBoundary(int blockid, int pinid, placerDB::Omark ort, placerDB::point LL) {
  vector<vector<placerDB::point> > newp=GetPlacedBlockPinRelBoundary(blockid, pinid, ort);
  for(vector<vector<placerDB::point> >::iterator it=newp.begin(); it!=newp.end(); ++it) {
    for(vector<placerDB::point>::iterator it2=it->begin();it2!=it->end();++it2) {
      (it2->x)+=LL.x;
      (it2->y)+=LL.y;
    }
  }
  return newp;
}

PnRDB::point design::GetPlacedBlockInterMetalAbsPoint(int blockid, placerDB::Omark ort, PnRDB::point& originP, placerDB::point LL) {
  PnRDB::point placedP=GetPlacedPnRPosition(originP, Blocks.at(blockid).width, Blocks.at(blockid).height, ort);
  placedP.x+=LL.x;
  placedP.y+=LL.y;
  return placedP;
}

PnRDB::point design::GetPlacedBlockInterMetalRelPoint(int blockid, placerDB::Omark ort, PnRDB::point& originP) {
  return GetPlacedPnRPosition(originP, Blocks.at(blockid).width, Blocks.at(blockid).height, ort);
}

PnRDB::bbox design::GetPlacedBlockInterMetalRelBox(int blockid, placerDB::Omark ort, PnRDB::bbox& originBox) {
  PnRDB::bbox placedBox;
  int x=INT_MAX; int X=INT_MIN;
  int y=INT_MAX; int Y=INT_MIN;
  for(int i=0;i<(int)originBox.polygon.size();i++) {
    placedBox.polygon.push_back( GetPlacedPnRPosition(originBox.polygon.at(i), Blocks.at(blockid).width, Blocks.at(blockid).height, ort) );
  }
  for(int i=0;i<(int)placedBox.polygon.size();i++) {
    if(x>placedBox.polygon.at(i).x) {x=placedBox.polygon.at(i).x;}
    if(X<placedBox.polygon.at(i).x) {X=placedBox.polygon.at(i).x;}
    if(y>placedBox.polygon.at(i).y) {y=placedBox.polygon.at(i).y;}
    if(Y<placedBox.polygon.at(i).y) {Y=placedBox.polygon.at(i).y;}
  }
  placedBox.LL.x=x; placedBox.LL.y=y;
  placedBox.LR.x=X; placedBox.LR.y=y;
  placedBox.UR.x=X; placedBox.UR.y=Y;
  placedBox.UL.x=x; placedBox.UL.y=Y;
  return placedBox;
}

PnRDB::bbox design::GetPlacedBlockInterMetalAbsBox(int blockid, placerDB::Omark ort, PnRDB::bbox& originBox, placerDB::point LL) {
  PnRDB::bbox placedBox=GetPlacedBlockInterMetalRelBox(blockid, ort, originBox);
  for(int i=0;i<(int)placedBox.polygon.size();i++) {
    placedBox.polygon.at(i).x+=LL.x;
    placedBox.polygon.at(i).y+=LL.y;
  }
  placedBox.LL.x+=LL.x;
  placedBox.LL.y+=LL.y;
  placedBox.UL.x+=LL.x;
  placedBox.UL.y+=LL.y;
  placedBox.LR.x+=LL.x;
  placedBox.LR.y+=LL.y;
  placedBox.UR.x+=LL.x;
  placedBox.UR.y+=LL.y;
  return placedBox;
}

int design::GetBlockPinNum(int blockid) {
  return (int)Blocks.at(blockid).blockPins.size();
}

string design::GetBlockPinName(int blockid, int pinid) {
  return Blocks.at(blockid).blockPins.at(pinid).name;
}

string design::GetBlockName(int blockid) {
  return Blocks.at(blockid).name;
}

string design::GetTerminalName(int termid) {
  return Terminals.at(termid).name;
}

vector<pair<int,int> > design::checkSympairInSymmBlock(vector<placerDB::SymmBlock>& SBs, vector< pair<int,int> >& Tsympair) {
  vector<pair<int,int> > pp;
  //vector<int> first; vector<int> second; bool mark=false;
  for(int j=0; j<(int)SBs.size(); ++j ) {
    for(vector< pair<int,int> >::iterator pi=SBs.at(j).sympair.begin(); pi!=SBs.at(j).sympair.end(); ++pi) {
      for( int i=0; i<(int)Tsympair.size(); ++i ) {
        if( pi->first==Tsympair.at(i).first and pi->second==Tsympair.at(i).second ) {
          pp.push_back(make_pair(j,i));
        }
      }
    }
  }
  //pair<int,int> pp=make_pair(first,second);
  return pp;
}

vector<pair<int,int> > design::checkSelfsymInSymmBlock(vector<placerDB::SymmBlock>& SBs, vector< pair<int,placerDB::Smark> >& Tselfsym) {
  vector<pair<int,int> > pp;
  //int first=-1; int second=-1; bool mark=false;
  for(int j=0; j<(int)SBs.size(); ++j ) {
    for(vector< pair<int,placerDB::Smark> >::iterator pi=SBs.at(j).selfsym.begin(); pi!=SBs.at(j).selfsym.end(); ++pi) {
      for( int i=0; i<(int)Tselfsym.size(); ++i ) {
        if( pi->first==Tselfsym.at(i).first and pi->second==Tselfsym.at(i).second ) { 
          pp.push_back(make_pair(j,i));
        }
      }
    }
  }
  //pair<int,int> pp=make_pair(first,second);
  return pp;
}

placerDB::point design::GetMultPolyCenterPoint(vector<placerDB::point>& pL) {
  if(pL.empty()) {cerr<<"Placer-Error: empty input"<<endl;}
  int x=pL.at(0).x, X=pL.at(0).x, y=pL.at(0).y, Y=pL.at(0).y;
  for(vector<placerDB::point>::iterator it=pL.begin()+1;it!=pL.end();++it) {
    if(it->x<x) {x=it->x; }
    if(it->x>X) {X=it->x; }
    if(it->y<y) {y=it->y; }
    if(it->y>Y) {Y=it->y; }
  }
  placerDB::point newp={ (X-x)/2, (Y-y)/2};
  return newp;
}

void design::constructSymmGroup() {
  // Known issues: 
  // 1. The merging of individual symmetry nets into symmetry group depends on the order of nets.
  // If the common objects of two symmetry-net groups exist in another symmetry-net group,
  // the merging will not be completed.
  // Known limitation:
  // 1. The symmetric pair in the symmetry group should have the same object type. 
  // E.g. mixing of terminal and block will be ignored.
  // 2. The self-symmetry object should be block rather than terminal.
  int dnidx=(int)Blocks.size()+2; // vertices:  blocks, source, sink, dummynodes
  int net1Sink, net2Sink;
  pair<int,int> tpair;
  vector< pair<int,int> > tmpsympair;
  vector< pair<int,placerDB::Smark> > tmpselfsym;
  vector<placerDB::SymmBlock> SBs;
  for(vector<SymmNet>::iterator sni=SNets.begin(); sni!=SNets.end(); sni++) {
    tmpsympair.clear(); tmpselfsym.clear();
    //cout<<sni->net1.name<<" vs "<<sni->net2.name<<endl;
    for(int i=0;i<(int)(sni->net1).connected.size();i++) {
      if(sni->net1.connected.at(i).type!=sni->net2.connected.at(i).type) {
        cout<<"Placer-Warning: different object type found in symmetric nets! Skip those objects..."<<endl; continue;
      }
      if(sni->net1.connected.at(i).type==placerDB::Terminal) {
        //cout<<sni->net1.connected.at(i).iter<<endl;
        //cout<<sni->net2.connected.at(i).iter<<endl;
        net1Sink=sni->net1.connected.at(i).iter+(int)Blocks.size();
        net2Sink=sni->net2.connected.at(i).iter+(int)Blocks.size();
      } else if(sni->net1.connected.at(i).type==placerDB::Block) {
        net1Sink=sni->net1.connected.at(i).iter2;
        net2Sink=sni->net2.connected.at(i).iter2;
      }
      tpair= (net1Sink<net2Sink)?make_pair(net1Sink, net2Sink):make_pair(net2Sink,net1Sink);
      //cout<<tpair.first<<" "<<tpair.second<<endl;
      if(tpair.first==tpair.second) { // if self-symmetric block
        if(tpair.first<(int)Blocks.size()) {
          cout<<"Block "<<sni->net1.connected.at(i).iter2<<"@"<<Blocks.at(sni->net1.connected.at(i).iter2).name<<  " pin "<<sni->net1.connected.at(i).iter<<"@"<<Blocks.at(sni->net1.connected.at(i).iter2).blockPins.at(sni->net1.connected.at(i).iter).name<<endl;
          vector<placerDB::point> p1V=Blocks.at(sni->net1.connected.at(i).iter2).blockPins.at(sni->net1.connected.at(i).iter).center;
          vector<placerDB::point> p2V=Blocks.at(sni->net2.connected.at(i).iter2).blockPins.at(sni->net2.connected.at(i).iter).center;
          placerDB::point p1=GetMultPolyCenterPoint(p1V);
          placerDB::point p2=GetMultPolyCenterPoint(p2V);
          //placerDB::point p1=Blocks.at(sni->net1.connected.at(i).iter2).blockPins.at(sni->net1.connected.at(i).iter).center;
          //placerDB::point p2=Blocks.at(sni->net2.connected.at(i).iter2).blockPins.at(sni->net2.connected.at(i).iter).center;
          placerDB::Smark tsmark= placerDB::H;
          //placerDB::Smark tsmark= ( abs(p1.x-p2.x)<abs(p1.y-p2.y) ) ? placerDB::V : placerDB::H;
          tmpselfsym.push_back(make_pair(tpair.first, tsmark));
        } else {cout<<"Placer-Warning: self-symmetric terminal found! Skip this object..."<<endl;continue;}
      } else { // if paired-symmetric block
        tmpsympair.push_back(tpair);
      }
    }
    for(int i=0;i<(int)tmpsympair.size();i++) {
      cout<<"paired-symmectric: "<<tmpsympair.at(i).first<<","<<tmpsympair.at(i).second<<endl;
    }
    for(int i=0;i<(int)tmpselfsym.size();i++) {
      cout<<"self-symmectric: "<<tmpselfsym.at(i).first<<","<<tmpselfsym.at(i).second<<endl;
    }
    MergeNewBlockstoSymmetryGroup(tmpsympair, tmpselfsym, SBs);
    //vector<pair<int,int> > matchedPair,matchedSelf;
    //matchedPair=checkSympairInSymmBlock(SBs, tmpsympair);
    //matchedSelf=checkSelfsymInSymmBlock(SBs, tmpselfsym);
    //if(matchedPair.empty()) {
    //  if(matchedSelf.empty()) { // neither matched
    //    cout<<"New symmetric group "<<endl;
    //    SBs.resize(SBs.size()+1);
    //    SBs.back().sympair=tmpsympair;
    //    SBs.back().selfsym=tmpselfsym;
    //    //SBs.back().dnode=dnidx++;
    //  } else { // only matched self-symmetric
    //    int gidx=matchedSelf[0].first;
    //    for(vector<pair<int,int> >::iterator itt=matchedSelf.begin();itt!=matchedSelf.end();++itt) {
    //      if(itt->first!=gidx) {
    //        for(vector<pair<int,int> >::iterator spit=SBs.at(itt->first).sympair.begin();spit!=SBs.at(itt->first).sympair.end();++spit) {SBs.at(gidx).sympair.push_back(*spit);}
    //        for(vector<pair<int,placerDB::Smark> >::iterator spit=SBs.at(itt->first).selfsym.begin();spit!=SBs.at(itt->first).selfsym.end();++spit) {SBs.at(gidx).selfsym.push_back(*spit);}
    //        cout<<"Move SB#"<<itt->first<<" to SB#"<<gidx<<endl;
    //        SBs.at(itt->first).sympair.clear();
    //        SBs.at(itt->first).selfsym.clear();
    //      }
    //    }
    //    cout<<"Append symmetric group #"<<gidx<<endl;
    //    for(int i=0;i<(int)tmpsympair.size();i++) { SBs.at(gidx).sympair.push_back( tmpsympair.at(i) ); }
    //    for(int i=0;i<(int)tmpselfsym.size();i++) {
    //      bool found=false;
    //      for(vector<pair<int,int> >::iterator mit=matchedSelf.begin();mit!=matchedSelf.end();++mit) {
    //        if(i==mit->second) {found=true;break;}
    //      }
    //      if(!found) SBs.at(gidx).selfsym.push_back( tmpselfsym.at(i) ); 
    //    }
    //  }
    //} else {
    //  if(matchedSelf.empty()) { // only matched paired-symmetric  
    //    int gidx=matchedPair[0].first;
    //    for(vector<pair<int,int> >::iterator itt=matchedPair.begin();itt!=matchedPair.end();++itt) {
    //      if(itt->first!=gidx) {
    //        for(vector<pair<int,int> >::iterator spit=SBs.at(itt->first).sympair.begin();spit!=SBs.at(itt->first).sympair.end();++spit) {SBs.at(gidx).sympair.push_back(*spit);}
    //        for(vector<pair<int,placerDB::Smark> >::iterator spit=SBs.at(itt->first).selfsym.begin();spit!=SBs.at(itt->first).selfsym.end();++spit) {SBs.at(gidx).selfsym.push_back(*spit);}
    //        cout<<"Move SB#"<<itt->first<<" to SB#"<<gidx<<endl;
    //        SBs.at(itt->first).sympair.clear();
    //        SBs.at(itt->first).selfsym.clear();
    //      }
    //    }
    //    cout<<"Append symmetric group #"<<gidx<<endl;
    //    for(int i=0;i<(int)tmpsympair.size();i++) { 
    //      bool found=false;
    //      for(vector<pair<int,int> >::iterator mit=matchedPair.begin();mit!=matchedPair.end();++mit) {
    //        if(i==mit->second) {found=true;break;}
    //      }
    //      if(!found) SBs.at(gidx).sympair.push_back( tmpsympair.at(i) ); 
    //    }
    //    for(int i=0;i<(int)tmpselfsym.size();i++) { SBs.at(gidx).selfsym.push_back( tmpselfsym.at(i) ); }
    //  } else { // both matched
    //    int gidx=matchedSelf[0].first;
    //    for(vector<pair<int,int> >::iterator itt=matchedSelf.begin();itt!=matchedSelf.end();++itt) {
    //      if(itt->first!=gidx) {
    //        for(vector<pair<int,int> >::iterator spit=SBs.at(itt->first).sympair.begin();spit!=SBs.at(itt->first).sympair.end();++spit) {SBs.at(gidx).sympair.push_back(*spit);}
    //        for(vector<pair<int,placerDB::Smark> >::iterator spit=SBs.at(itt->first).selfsym.begin();spit!=SBs.at(itt->first).selfsym.end();++spit) {SBs.at(gidx).selfsym.push_back(*spit);}
    //        cout<<"Move SB#"<<itt->first<<" to SB#"<<gidx<<endl;
    //        SBs.at(itt->first).sympair.clear();
    //        SBs.at(itt->first).selfsym.clear();
    //      }
    //    }
    //    for(vector<pair<int,int> >::iterator itt=matchedPair.begin();itt!=matchedPair.end();++itt) {
    //      if(itt->first!=gidx) {
    //        for(vector<pair<int,int> >::iterator spit=SBs.at(itt->first).sympair.begin();spit!=SBs.at(itt->first).sympair.end();++spit) {SBs.at(gidx).sympair.push_back(*spit);}
    //        for(vector<pair<int,placerDB::Smark> >::iterator spit=SBs.at(itt->first).selfsym.begin();spit!=SBs.at(itt->first).selfsym.end();++spit) {SBs.at(gidx).selfsym.push_back(*spit);}
    //        cout<<"Move SB#"<<itt->first<<" to SB#"<<gidx<<endl;
    //        SBs.at(itt->first).sympair.clear();
    //        SBs.at(itt->first).selfsym.clear();
    //      }
    //    }
    //    for(int i=0;i<(int)tmpselfsym.size();i++) {
    //      bool found=false;
    //      for(vector<pair<int,int> >::iterator mit=matchedSelf.begin();mit!=matchedSelf.end();++mit) {
    //        if(i==mit->second) {found=true;break;}
    //      }
    //      if(!found) SBs.at(gidx).selfsym.push_back( tmpselfsym.at(i) ); 
    //    }
    //    for(int i=0;i<(int)tmpsympair.size();i++) { 
    //      bool found=false;
    //      for(vector<pair<int,int> >::iterator mit=matchedPair.begin();mit!=matchedPair.end();++mit) {
    //        if(i==mit->second) {found=true;break;}
    //      }
    //      if(!found) SBs.at(gidx).sympair.push_back( tmpsympair.at(i) ); 
    //    }
    //  }
    //} 
  }
  for(vector<SymmPairBlock>::iterator sni=SPBlocks.begin(); sni!=SPBlocks.end(); sni++) {
    MergeNewBlockstoSymmetryGroup(sni->sympair, sni->selfsym, SBs);
  }
  SBlocks.clear();
  for(vector<placerDB::SymmBlock>::iterator it=SBs.begin();it!=SBs.end();++it) {
    if(it->sympair.empty() and it->selfsym.empty()) {continue;}
    SBlocks.resize(SBlocks.size()+1);
    SBlocks.back().sympair=it->sympair;
    SBlocks.back().selfsym=it->selfsym;
    SBlocks.back().dnode=dnidx++;
  }
  for(int i=0;i<(int)SBlocks.size(); ++i) {
    for(vector< pair<int,int> >::iterator pit=SBlocks[i].sympair.begin(); pit!=SBlocks[i].sympair.end(); ++pit) {
      if(pit->first<(int)Blocks.size()) {Blocks.at(pit->first).SBidx=i; Blocks.at(pit->first).counterpart=pit->second;  }
      if(pit->second<(int)Blocks.size()) {Blocks.at(pit->second).SBidx=i; Blocks.at(pit->second).counterpart=pit->first;  }
    }
    for(vector< pair<int,placerDB::Smark> >::iterator sit=SBlocks[i].selfsym.begin(); sit!=SBlocks[i].selfsym.end(); ++sit) {
      if(sit->first<(int)Blocks.size()) {Blocks.at(sit->first).SBidx=i; Blocks.at(sit->first).counterpart=sit->first;  }
    }
  }
}

void design::MergeNewBlockstoSymmetryGroup(vector< pair<int,int> >& tmpsympair,  vector< pair<int,placerDB::Smark> >& tmpselfsym, vector<placerDB::SymmBlock>& SBs ) {
  vector<pair<int,int> > matchedPair,matchedSelf;
  matchedPair=checkSympairInSymmBlock(SBs, tmpsympair);
  matchedSelf=checkSelfsymInSymmBlock(SBs, tmpselfsym);
  if(matchedPair.empty()) {
    if(matchedSelf.empty()) { // neither matched
      cout<<"New symmetric group "<<endl;
      SBs.resize(SBs.size()+1);
      SBs.back().sympair=tmpsympair;
      SBs.back().selfsym=tmpselfsym;
      //SBs.back().dnode=dnidx++;
    } else { // only matched self-symmetric
      int gidx=matchedSelf[0].first;
      for(vector<pair<int,int> >::iterator itt=matchedSelf.begin();itt!=matchedSelf.end();++itt) {
        if(itt->first!=gidx) {
          for(vector<pair<int,int> >::iterator spit=SBs.at(itt->first).sympair.begin();spit!=SBs.at(itt->first).sympair.end();++spit) {SBs.at(gidx).sympair.push_back(*spit);}
          for(vector<pair<int,placerDB::Smark> >::iterator spit=SBs.at(itt->first).selfsym.begin();spit!=SBs.at(itt->first).selfsym.end();++spit) {SBs.at(gidx).selfsym.push_back(*spit);}
          cout<<"Move SB#"<<itt->first<<" to SB#"<<gidx<<endl;
          SBs.at(itt->first).sympair.clear();
          SBs.at(itt->first).selfsym.clear();
        }
      }
      cout<<"Append symmetric group #"<<gidx<<endl;
      for(int i=0;i<(int)tmpsympair.size();i++) { SBs.at(gidx).sympair.push_back( tmpsympair.at(i) ); }
      for(int i=0;i<(int)tmpselfsym.size();i++) {
        bool found=false;
        for(vector<pair<int,int> >::iterator mit=matchedSelf.begin();mit!=matchedSelf.end();++mit) {
          if(i==mit->second) {found=true;break;}
        }
        if(!found) SBs.at(gidx).selfsym.push_back( tmpselfsym.at(i) ); 
      }
    }
  } else {
    if(matchedSelf.empty()) { // only matched paired-symmetric  
      int gidx=matchedPair[0].first;
      for(vector<pair<int,int> >::iterator itt=matchedPair.begin();itt!=matchedPair.end();++itt) {
        if(itt->first!=gidx) {
          for(vector<pair<int,int> >::iterator spit=SBs.at(itt->first).sympair.begin();spit!=SBs.at(itt->first).sympair.end();++spit) {SBs.at(gidx).sympair.push_back(*spit);}
          for(vector<pair<int,placerDB::Smark> >::iterator spit=SBs.at(itt->first).selfsym.begin();spit!=SBs.at(itt->first).selfsym.end();++spit) {SBs.at(gidx).selfsym.push_back(*spit);}
          cout<<"Move SB#"<<itt->first<<" to SB#"<<gidx<<endl;
          SBs.at(itt->first).sympair.clear();
          SBs.at(itt->first).selfsym.clear();
        }
      }
      cout<<"Append symmetric group #"<<gidx<<endl;
      for(int i=0;i<(int)tmpsympair.size();i++) { 
        bool found=false;
        for(vector<pair<int,int> >::iterator mit=matchedPair.begin();mit!=matchedPair.end();++mit) {
          if(i==mit->second) {found=true;break;}
        }
        if(!found) SBs.at(gidx).sympair.push_back( tmpsympair.at(i) ); 
      }
      for(int i=0;i<(int)tmpselfsym.size();i++) { SBs.at(gidx).selfsym.push_back( tmpselfsym.at(i) ); }
    } else { // both matched
      int gidx=matchedSelf[0].first;
      for(vector<pair<int,int> >::iterator itt=matchedSelf.begin();itt!=matchedSelf.end();++itt) {
        if(itt->first!=gidx) {
          for(vector<pair<int,int> >::iterator spit=SBs.at(itt->first).sympair.begin();spit!=SBs.at(itt->first).sympair.end();++spit) {SBs.at(gidx).sympair.push_back(*spit);}
          for(vector<pair<int,placerDB::Smark> >::iterator spit=SBs.at(itt->first).selfsym.begin();spit!=SBs.at(itt->first).selfsym.end();++spit) {SBs.at(gidx).selfsym.push_back(*spit);}
          cout<<"Move SB#"<<itt->first<<" to SB#"<<gidx<<endl;
          SBs.at(itt->first).sympair.clear();
          SBs.at(itt->first).selfsym.clear();
        }
      }
      for(vector<pair<int,int> >::iterator itt=matchedPair.begin();itt!=matchedPair.end();++itt) {
        if(itt->first!=gidx) {
          for(vector<pair<int,int> >::iterator spit=SBs.at(itt->first).sympair.begin();spit!=SBs.at(itt->first).sympair.end();++spit) {SBs.at(gidx).sympair.push_back(*spit);}
          for(vector<pair<int,placerDB::Smark> >::iterator spit=SBs.at(itt->first).selfsym.begin();spit!=SBs.at(itt->first).selfsym.end();++spit) {SBs.at(gidx).selfsym.push_back(*spit);}
          cout<<"Move SB#"<<itt->first<<" to SB#"<<gidx<<endl;
          SBs.at(itt->first).sympair.clear();
          SBs.at(itt->first).selfsym.clear();
        }
      }
      for(int i=0;i<(int)tmpselfsym.size();i++) {
        bool found=false;
        for(vector<pair<int,int> >::iterator mit=matchedSelf.begin();mit!=matchedSelf.end();++mit) {
          if(i==mit->second) {found=true;break;}
        }
        if(!found) SBs.at(gidx).selfsym.push_back( tmpselfsym.at(i) ); 
      }
      for(int i=0;i<(int)tmpsympair.size();i++) { 
        bool found=false;
        for(vector<pair<int,int> >::iterator mit=matchedPair.begin();mit!=matchedPair.end();++mit) {
          if(i==mit->second) {found=true;break;}
        }
        if(!found) SBs.at(gidx).sympair.push_back( tmpsympair.at(i) ); 
      }
    }
  } 
}

int design::GetBlockSymmGroup(int blockid) {
  return Blocks.at(blockid).SBidx;
}

int design::GetBlockCounterpart(int blockid) {
  return Blocks.at(blockid).counterpart;
}


vector<int> design::GetRealBlockListfromSymmGroup(int sgid) {
  vector<int> blist;
  if(sgid>=0 and sgid<(int)SBlocks.size()) {
    for(vector< pair<int,int> >::iterator sit=SBlocks.at(sgid).sympair.begin(); sit!=SBlocks.at(sgid).sympair.end(); ++sit) {
      if(sit->first<(int)Blocks.size()) {blist.push_back(sit->first);}
      if(sit->second<(int)Blocks.size()) {blist.push_back(sit->second);}
    }
    for(vector<pair<int,placerDB::Smark> >::iterator sit=SBlocks.at(sgid).selfsym.begin(); sit!=SBlocks.at(sgid).selfsym.end(); ++sit) {
      if(sit->first<(int)Blocks.size()) {blist.push_back(sit->first);}//cout<<"Push "<<sit->first<<endl;}
    }
  }
  return blist;
}

vector<int> design::GetRealBlockPlusAxisListfromSymmGroup(int sgid) {
  vector<int> blist;
  if(sgid>=0 and sgid<(int)SBlocks.size()) {
    for(vector< pair<int,int> >::iterator sit=SBlocks.at(sgid).sympair.begin(); sit!=SBlocks.at(sgid).sympair.end(); ++sit) {
      if(sit->first<(int)Blocks.size()) {blist.push_back(sit->first);}
      if(sit->second<(int)Blocks.size()) {blist.push_back(sit->second);}
    }
    for(vector<pair<int,placerDB::Smark> >::iterator sit=SBlocks.at(sgid).selfsym.begin(); sit!=SBlocks.at(sgid).selfsym.end(); ++sit) {
      if(sit->first<(int)Blocks.size()) {blist.push_back(sit->first);}//cout<<"Push "<<sit->first<<endl;}
    }
    blist.push_back(SBlocks.at(sgid).dnode);
  }
  return blist;
}

vector<int> design::GetBlockListfromSymmGroup(int sgid) {
  vector<int> blist;
  if(sgid>=0 and sgid<(int)SBlocks.size()) {
    for(vector< pair<int,int> >::iterator sit=SBlocks.at(sgid).sympair.begin(); sit!=SBlocks.at(sgid).sympair.end(); ++sit) {
      blist.push_back(sit->first);
      blist.push_back(sit->second);
    }
    for(vector< pair<int,placerDB::Smark> >::iterator sit=SBlocks.at(sgid).selfsym.begin(); sit!=SBlocks.at(sgid).selfsym.end(); ++sit) {
      blist.push_back(sit->first);
    }
  }
  return blist;
}

placerDB::point design::GetTerminalCenter(int teridx) {
  return Terminals.at(teridx).center;
}

bool design::checkSymmetricBlockExist() {
  bool mark=false;
  for(int i=0;i<(int)Blocks.size();i++) {
    if (Blocks.at(i).SBidx!=-1) {mark=true; break;}
  }
  return mark;
}

bool design::checkAsymmetricBlockExist() {
  bool mark=false;
  for(int i=0;i<(int)Blocks.size();i++) {
    if (Blocks.at(i).SBidx==-1) {mark=true; break;}
  }
  return mark;
}
