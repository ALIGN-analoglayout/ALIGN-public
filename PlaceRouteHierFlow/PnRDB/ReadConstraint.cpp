#include "PnRdatabase.h"

#include <iostream>
#include <fstream>
#include <iomanip>

bool PnRdatabase::ReadConstraint(PnRDB::hierNode& node, string fpath, string suffix) {
  ifstream fin;
  string def;
  vector<string> temp, tempsec;
  size_t found;
  string cfile=fpath+"/"+node.name+"."+suffix;
  std::cout<<"start to read const file "<<cfile<<std::endl;
  // constraint format issues(comma): Alignment, Preplace, MatchBlock, Abutment
  fin.exceptions(ifstream::failbit | ifstream::badbit);
  try {
    fin.open(cfile.c_str());
    while(fin.peek()!=EOF) {
      getline(fin, def);
      //std::cout<<"line "<<def<<std::endl;
      if(def.compare("")==0) {continue;}
      temp=split_by_spaces(def);
      //for(int i=0;i<temp.size();i++) {cout<<" ? "<<temp[i];}
      //cout<<endl;
      if(temp[0].compare("SymmNet")==0) {
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        //cout<<word<<endl;
        tempsec=StringSplitbyChar(word, ',');
        //cout<<tempsec[0]<<" "<<tempsec[1]<<endl;
        PnRDB::net tmpnet;
        for(vector<string>::iterator it=tempsec.begin(); it!=tempsec.end(); it++) {
          if(it==tempsec.begin()) {
            tmpnet.name=*it;
          } else {
            if(it->find("/")!=string::npos) { // if block pin
              vector<string> tempthd=StringSplitbyChar(*it, '/');
              for(int i=0;i<(int)node.Blocks.size();i++) {
                if(node.Blocks.at(i).instance.back().name.compare(tempthd[0])==0) {
                  for(int j=0;j<(int)node.Blocks.at(i).instance.back().blockPins.size();j++) {
                    if(node.Blocks.at(i).instance.back().blockPins.at(j).name.compare(tempthd[1])==0) {
                      //cout<<j<<" "<<i<<endl;
                      PnRDB::connectNode newnode={PnRDB::Block, j, i};
                      tmpnet.connected.push_back(newnode);
                      break;
                    }
                  }
                  break;
                }
              }
              //cout<<*it<<" is pin"<<tempthd[0]<<"/"<<tempthd[1]<<endl;
            } else { // if terminal
              for(int i=0;i<(int)node.Terminals.size();i++) {
                if(node.Terminals.at(i).name.compare(*it)==0) {
                  PnRDB::connectNode newnode={PnRDB::Terminal, i, -1};
                  tmpnet.connected.push_back(newnode);
                  break;
                }
              }
              //cout<<*it<<" is terminal"<<endl;
            }
          }
        }
        word=temp[4];
        //cout<<word<<endl;
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        tempsec=StringSplitbyChar(word, ',');
        //cout<<tempsec[0]<<" "<<tempsec[1]<<endl;
        PnRDB::net tmpnet2;
        for(vector<string>::iterator it=tempsec.begin(); it!=tempsec.end(); it++) {
          if(it==tempsec.begin()) {
            tmpnet2.name=*it;
          } else {
            if(it->find("/")!=string::npos) { // if block pin
              vector<string> tempthd=StringSplitbyChar(*it, '/');
              for(int i=0;i<(int)node.Blocks.size();i++) {
                //std::cout<<"block "<<node.Blocks.at(i).instance.back().name<<std::endl;
                if(node.Blocks.at(i).instance.back().name.compare(tempthd[0])==0) {
                  for(int j=0;j<(int)node.Blocks.at(i).instance.back().blockPins.size();j++) {
                    //std::cout<<"\t pin "<<node.Blocks.at(i).instance.back().blockPins.at(j).name<<std::endl;
                    if(node.Blocks.at(i).instance.back().blockPins.at(j).name.compare(tempthd[1])==0) {
                      //cout<<j<<" "<<i<<endl;
                      PnRDB::connectNode newnode={PnRDB::Block, j, i};
                      tmpnet2.connected.push_back(newnode);
                      break;
                    }
                  }
                  break;
                }
              }
              //cout<<*it<<" is pin"<<tempthd[0]<<"/"<<tempthd[1]<<endl;
            } else { // if terminal
              for(int i=0;i<(int)node.Terminals.size();i++) {
                if(node.Terminals.at(i).name.compare(*it)==0) {
                  PnRDB::connectNode newnode={PnRDB::Terminal, i, -1};
                  tmpnet2.connected.push_back(newnode);
                  break;
                }
              }
              //cout<<*it<<" is terminal"<<endl;
            }
          }
        }
        int iter1=-1, iter2=-1; // iterator in Nets
        for(int i=0;i<(int)node.Nets.size()&&(iter1==-1||iter2==-1);i++) {
          if(node.Nets.at(i).name.compare(tmpnet.name)==0) {iter1=i;}
          if(node.Nets.at(i).name.compare(tmpnet2.name)==0) {iter2=i;}
        }
        node.Nets.at(iter1).symCounterpart=iter2;
        node.Nets.at(iter1).iter2SNetLsit=node.SNets.size();
        node.Nets.at(iter2).symCounterpart=iter1;
        node.Nets.at(iter2).iter2SNetLsit=node.SNets.size();
        node.SNets.resize(node.SNets.size()+1);
        node.SNets.back().net1=tmpnet;
        node.SNets.back().net2=tmpnet2;
        node.SNets.back().iter1=iter1;
        node.SNets.back().iter2=iter2;
      } else if (temp[0].compare("CritNet")==0) {
        for(int i=0;i<(int)node.Nets.size();i++) {
          if(node.Nets.at(i).name.compare(temp[2])==0) {
            node.Nets.at(i).priority=temp[4];
            break;
          }
        }
      } else if(temp[0].compare("Preplace")==0){
        string block_first=temp[2];
        string block_second=temp[3];
        int distance= atoi(temp[4].c_str());
        int horizon = atoi(temp[5].c_str());
        PnRDB::Preplace preplace_const;
	preplace_const.blockid1 = -1;
	preplace_const.blockid2 = -1;


        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_first)==0) {
            preplace_const.blockid1 = i;
            break;
          }
        }
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_second)==0) {
            preplace_const.blockid2 = i;
            break;
          } else {
            preplace_const.conner = block_second;
          }
        }
        preplace_const.distance = distance;
        preplace_const.horizon = horizon;


	if ( preplace_const.blockid1 == -1) {
	  cout << "-E- ReadConstraint: Preplace: couldn't find block1:" << block_first << endl;
	}
	if ( preplace_const.blockid2 == -1) {
	  cout << "-E- ReadConstraint: Preplace: couldn't find block2:" << block_second << endl;
	}

	if ( preplace_const.blockid1 != -1 && preplace_const.blockid2!= -1) {
	  node.Preplace_blocks.push_back(preplace_const);
	}



      } else if(temp[0].compare("Alignment")==0){
        string block_first=temp[2];
        string block_second=temp[3];
        int distance= atoi(temp[4].c_str());
        int horizon = atoi(temp[5].c_str());
        PnRDB::Alignment alignment_const;
	alignment_const.blockid1 = -1;
	alignment_const.blockid2 = -1;


        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_first)==0) {
            alignment_const.blockid1 = i;
            break;
          }
        }
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_second)==0) {
            alignment_const.blockid2 = i;
            break;
          }
        }
        alignment_const.distance = distance;
        alignment_const.horizon = horizon;

	if ( alignment_const.blockid1 == -1) {
	  cout << "-E- ReadConstraint: Alignment: couldn't find block1:" << block_first << endl;
	}
	if ( alignment_const.blockid2 == -1) {
	  cout << "-E- ReadConstraint: Alignment: couldn't find block2:" << block_second << endl;
	}

	if ( alignment_const.blockid1 != -1 && alignment_const.blockid2!= -1) {
	  node.Alignment_blocks.push_back(alignment_const);
	}


      } else if(temp[0].compare("Abument")==0){
        string block_first=temp[2];
        string block_second=temp[3];
        int distance= atoi(temp[4].c_str());
        int horizon = atoi(temp[5].c_str());
      
        PnRDB::Abument abument_const;
	abument_const.blockid1 = -1;
	abument_const.blockid2 = -1;
      
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_first)==0) {
            abument_const.blockid1 = i;
            break;
          }
        }
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_second)==0) {
            abument_const.blockid2 = i;
            break;
          }
        }
        abument_const.distance = distance;
        abument_const.horizon = horizon;

	if ( abument_const.blockid1 == -1) {
	  cout << "-E- ReadConstraint: Abument: couldn't find block1:" << block_first << endl;
	}
	if ( abument_const.blockid2 == -1) {
	  cout << "-E- ReadConstraint: Abument: couldn't find block2:" << block_second << endl;
	}

	if ( abument_const.blockid1 != -1 && abument_const.blockid2!= -1) {
	  node.Abument_blocks.push_back(abument_const);
	}
      } else if(temp[0].compare("MatchBlock")==0){
        string block_first=temp[2];
        string block_second=temp[4];
        //int distance= atoi(temp[4].c_str());
        //int horizon = atoi(temp[5].c_str());
      
        PnRDB::MatchBlock match_const;
	match_const.blockid1 = -1;
	match_const.blockid2 = -1;
      
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_first)==0) {
            match_const.blockid1 = i;
            break;
          }
        }
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_second)==0) {
            match_const.blockid2 = i;
            break;
          }
        }

	if ( match_const.blockid1 == -1) {
	  cout << "-E- ReadConstraint: MatchBlock: couldn't find block1:" << block_first << endl;
	}
	if ( match_const.blockid2 == -1) {
	  cout << "-E- ReadConstraint: MatchBlock: couldn't find block2:" << block_second << endl;
	}

        //match_const.distance = distance;
        //match_const.horizon = horizon;
	if ( match_const.blockid1 != -1 && match_const.blockid2!= -1) {
	  node.Match_blocks.push_back(match_const);
	}
      } else if(temp[0].compare("bias_graph")==0){
        int distance= atoi(temp[2].c_str());
        node.bias_Hgraph = distance;
        node.bias_Vgraph = distance;
      } else if(temp[0].compare("bias_Hgraph")==0 ) {
        int distance= atoi(temp[2].c_str());
        node.bias_Hgraph = distance;
      } else if(temp[0].compare("bias_Vgraph")==0 ) {
        int distance= atoi(temp[2].c_str());
        node.bias_Vgraph = distance;
      } else if (temp[0].compare("ShieldNet")==0) {
        string shield_net=temp[2];
        for(int i=0;i<(int)node.Nets.size();i++) {
          if(node.Nets.at(i).name.compare(shield_net)==0) {
            node.Nets.at(i).shielding=true; break;
          }
        }
      } else if (temp[0].compare("SymmBlock")==0) { 
        PnRDB::SymmPairBlock temp_SymmPairBlock;
        pair<int,int> temp_pair;
        pair<int,PnRDB::Smark> temp_selfsym;
        for(unsigned int i=2;i<temp.size();i=i+2){
          string word=temp[i];
          word=word.substr(1);
          word=word.substr(0, word.length()-1);
          tempsec=StringSplitbyChar(word, ',');
          if((found=temp[i].find(","))!=string::npos) { // sympair
            for(int k=0;k<(int)node.Blocks.size();k++) {
              if(node.Blocks.at(k).instance.back().name.compare(tempsec[0])==0) {temp_pair.first = k;}
              if(node.Blocks.at(k).instance.back().name.compare(tempsec[1])==0) {temp_pair.second = k;}
            }
            int temp_int;
            if(temp_pair.first>temp_pair.second){
              temp_int = temp_pair.second;
              temp_pair.second = temp_pair.first;
              temp_pair.first = temp_int;
            } else if (temp_pair.first==temp_pair.second) {
              std::cerr<<"PnRDB-Error: same block in paired symmetry group"<<std::endl;
            }
            temp_SymmPairBlock.sympair.push_back(temp_pair);
          } else { // selfsym
            for(int j=0;j<(int)node.Blocks.size();j++) {
              if(node.Blocks.at(j).instance.back().name.compare(word)==0) {
                temp_selfsym.first =  j;
                temp_selfsym.second = PnRDB::H;
                temp_SymmPairBlock.selfsym.push_back(temp_selfsym);
                break;
              }
            }
          }
        }
        node.SPBlocks.push_back(temp_SymmPairBlock);
      }else if(temp[0].compare("CC")==0){
        PnRDB::CCCap temp_cccap;
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_cccap.CCCap_name = word;
        word = temp[6];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_cccap.Unit_capacitor = word;
        word=temp[4];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        //cout<<word<<endl;
        tempsec=StringSplitbyChar(word, ',');
        for(unsigned int p=0;p<tempsec.size();p++){ 
            temp_cccap.size.push_back(atoi(tempsec[p].c_str()));
           }
        if(temp.size()>9){
          temp_cccap.cap_ratio = 1;
          word=temp[8];
          word=word.substr(1);
          word=word.substr(0, word.length()-1);
          //cout<<word<<endl;
          tempsec=StringSplitbyChar(word, ',');
          temp_cccap.cap_r = atoi(tempsec[0].c_str());
          temp_cccap.cap_s = atoi(tempsec[1].c_str());
          }
        //temp_cccap.size = temp[4]; //size?
        
        node.CC_Caps.push_back(temp_cccap);
      } else if (temp[0].compare("AlignBlock")==0) {
        PnRDB::AlignBlock alignment_unit;
        if(temp[2].compare("H")==0) {
          alignment_unit.horizon=1;
        } else {
          alignment_unit.horizon=0;
        }
        for(int j=4;j<(int)temp.size();j+=2) {
          for(int i=0;i<(int)node.Blocks.size();i++) {
            if(node.Blocks.at(i).instance.back().name.compare(temp[j])==0) {
              alignment_unit.blocks.push_back(i);
              break;
            }
          }
        }
        //std::cout<<"AlignBlock "<<alignment_unit.horizon<<" @ ";
        for(unsigned int i=0;i<alignment_unit.blocks.size();i++) {std::cout<<alignment_unit.blocks[i]<<" ";}
        //std::cout<<std::endl;
        node.Align_blocks.push_back(alignment_unit);
      } else if (temp[0].compare("PortLocation")==0) {
        // PortLocation(X,L) 
        // This constraint indicates the location of the port ‘X’
        // Considering the block as a rectangle, the edges can be divided into 12 sections as shown in the figure below.
        //  L indicates the approximate position of the port. Value of L should be taken from the set
        // {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT, }
        PnRDB::PortPos tmp_portpos;
        //std::cout<<temp[4]<<temp[2]<<std::endl;
        if(temp[4].compare("TL")==0) {
          tmp_portpos.pos=PnRDB::TL;
          //std::cout<<"TL\n";
        } else if(temp[4].compare("TC")==0) {
	  //std::cout<<"TC\n";
          tmp_portpos.pos=PnRDB::TC;
        } else if(temp[4].compare("TR")==0) {
          //std::cout<<"TR\n";
          tmp_portpos.pos=PnRDB::TR;
        } else if(temp[4].compare("RT")==0) {
          //std::cout<<"RT\n";
          tmp_portpos.pos=PnRDB::RT;
        } else if(temp[4].compare("RC")==0) {
          //std::cout<<"RC\n";
          tmp_portpos.pos=PnRDB::RC;
        } else if(temp[4].compare("RB")==0) {
          //std::cout<<"RB\n";
          tmp_portpos.pos=PnRDB::RB;
        } else if(temp[4].compare("BL")==0) {
          //std::cout<<"BL\n";
          tmp_portpos.pos=PnRDB::BL;
        } else if(temp[4].compare("BC")==0) {
          //std::cout<<"BC\n";
          tmp_portpos.pos=PnRDB::BC;
        } else if(temp[4].compare("BR")==0) {
          //std::cout<<"BR\n";
          tmp_portpos.pos=PnRDB::BR;
        } else if(temp[4].compare("LB")==0) {
          //std::cout<<"LB\n";
          tmp_portpos.pos=PnRDB::LB;
        } else if(temp[4].compare("LC")==0) {
          //std::cout<<"LC\n";
          tmp_portpos.pos=PnRDB::LC;
        } else if(temp[4].compare("LT")==0) {
          //std::cout<<"LT\n";
          tmp_portpos.pos=PnRDB::LT;
        }
        string name=temp[2];
        for(int k=0;k<(int)node.Terminals.size();++k) {
          //std::cout<<name<<" vs "<<node.Terminals.at(k).name<<std::endl;
          if(node.Terminals.at(k).name.compare(name)==0) {
            tmp_portpos.tid=k;
            break;
          }
        }
        std::cout<<"PortLocation "<<tmp_portpos.tid<<" @ "<<tmp_portpos.pos<<std::endl;
        node.Port_Location.push_back(tmp_portpos);
      }else if (temp[0].compare("R_const")==0){
        PnRDB::R_const temp_r_const;
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_r_const.net_name=word;
        for(int i=4;i<temp.size()-1;i=i+2){
           word=temp[i];
           word=word.substr(1);
           word=word.substr(0, word.length()-1);
           //cout<<word<<endl;
           tempsec=StringSplitbyChar(word, ',');
           temp_r_const.start_pin.push_back(tempsec[0]);
           temp_r_const.end_pin.push_back(tempsec[1]);
           temp_r_const.R.push_back(atoi(tempsec[2].c_str()));
        }
        node.R_Constraints.push_back(temp_r_const);
      }else if (temp[0].compare("C_const")==0){
        PnRDB::C_const temp_c_const;
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_c_const.net_name=word;
        for(int i=4;i<temp.size()-1;i=i+2){
           word=temp[i];
           word=word.substr(1);
           word=word.substr(0, word.length()-1);
           //cout<<word<<endl;
           tempsec=StringSplitbyChar(word, ',');
           temp_c_const.start_pin.push_back(tempsec[0]);
           temp_c_const.end_pin.push_back(tempsec[1]);
           temp_c_const.C.push_back(atoi(tempsec[2].c_str()));
        }
        node.C_Constraints.push_back(temp_c_const);

      }
    }
    fin.close();
    //std::cout<<"end read const file "<<cfile<<std::endl;
    return true;
  } catch(ifstream::failure e) {
    cerr<<"PnRDB-Error: fail to read constraint file "<<endl;
  }
  return false;
}
