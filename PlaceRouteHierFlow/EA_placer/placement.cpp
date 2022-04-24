#include "placement.h"

#include "spdlog/spdlog.h"
// #define DEBUG
Placement::Placement() {}

void Placement::place(PnRDB::hierNode &current_node) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.place");
  // step 1: transfroming info. of current_node to Blocks and Nets
  // create a small function for this
  float area, scale_factor;
  int max_block_number = 1000;
  int max_net_number = 100;
  int max_conection_number = 100;
  circuit_name = current_node.name;

  // for bins
  unit_x_bin = (float)1 / 16;
  unit_y_bin = (float)1 / 16;
  x_dimension_bin = 16;  // number of bin, number of pe
  y_dimension_bin = 16;  // number of bin, number of pe

  Bin_D.x = unit_x_bin;
  Bin_D.y = unit_y_bin;
  logger->debug("start reading node file");
  area = readInputNode(current_node);

  // for blocks
  unit_x = (float)1 / Blocks.size();
  unit_y = (float)1 / Blocks.size();
  x_dimension = Blocks.size();  // number of pe
  y_dimension = x_dimension;    // S number of pe
  Chip_D.x = (float)1;
  Chip_D.y = (float)1;

  for (unsigned int i = 0; i < x_dimension_bin; ++i) {
    vector<bin> temp_bins;
    for (unsigned int j = 0; j < y_dimension_bin; ++j) {
      bin temp_bin;
      temp_bin.Dpoint.x = unit_x_bin;
      temp_bin.Dpoint.y = unit_y_bin;
      temp_bin.Cpoint.x = i * unit_x_bin + unit_x_bin / 2;
      temp_bin.Cpoint.y = j * unit_y_bin + unit_y_bin / 2;
      temp_bin.Index.x = i;
      temp_bin.Index.y = j;
      temp_bins.push_back(temp_bin);
    }
    Bins.push_back(temp_bins);
  }

  // step 2: Given a initial position for each block
  // create a small function for this
  // need to estimate a area to do placement
  // scale into 1x1
  // initial position for each block
  for (unsigned int i = 0; i < originalBlockCNT; i++) {
    Blocks[i].original_Dpoint.x = current_node.Blocks[i].instance[0].width;
    Blocks[i].original_Dpoint.y = current_node.Blocks[i].instance[0].height;
  }
  logger->debug("Unify the block coordinate");
  scale_factor = 40.0;
  Unify_blocks(area, scale_factor);
  find_uni_cell();
  splitNode_MS(uni_cell_Dpoint.y, uni_cell_Dpoint.x);
  int tol_diff = 3;
  split_net();
  modify_symm_after_split(current_node);
  update_hiernode(current_node);

  // read alignment constrains
  read_alignment(current_node);
  read_order(current_node);
  clock_t start, end;
  start = clock();

  Initilize_Placement_Rand(current_node);
  end = clock();
  logger->debug("initialize runtime: {0} s", (double)(end - start) / CLOCKS_PER_SEC);

  print_blocks_nets();
  // step 3: call E_placer
  logger->debug("start ePlacement");
  PlotPlacement(602);
  // restore_MS();
  // PlotPlacement(601);
  E_Placer(current_node);
  PlotPlacement(6021);
  bool isCompact = true;

  // restore_MS();
  PlotPlacement(603);
  // setp 4: write back to HierNode
  writeback(current_node);
}

void Placement::Pull_back() {
  auto logger = spdlog::default_logger()->clone("placer.Placement.Pull_back");
  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    if (Blocks[i].Cpoint.x + Blocks[i].Dpoint.x / 2 > Chip_D.x) {
      Blocks[i].Cpoint.x = Chip_D.x - Blocks[i].Dpoint.x / 2 - (1.5) * Bin_D.x / 2;
      // Blocks[i].Cpoint.x = Chip_D.x - Blocks[i].Dpoint.x/2;
    }
    if (Blocks[i].Cpoint.y + Blocks[i].Dpoint.y / 2 > Chip_D.y) {
      Blocks[i].Cpoint.y = Chip_D.y - Blocks[i].Dpoint.y / 2 - (1.5) * Bin_D.y / 2;
      // Blocks[i].Cpoint.y = Chip_D.y - Blocks[i].Dpoint.y/2;
    }
    if (Blocks[i].Cpoint.x - Blocks[i].Dpoint.x / 2 < 0) {
      Blocks[i].Cpoint.x = Blocks[i].Dpoint.x / 2 + (1.5) * Bin_D.x / 2;
      // Blocks[i].Cpoint.x = Blocks[i].Dpoint.x/2;
    }
    if (Blocks[i].Cpoint.y - Blocks[i].Dpoint.y / 2 < 0) {
      Blocks[i].Cpoint.y = Blocks[i].Dpoint.y / 2 + (1.5) * Bin_D.y / 2;
      // Blocks[i].Cpoint.y = Blocks[i].Dpoint.y/2;
    }
  }
}

void Placement::Pull_back_vector(vector<float> &temp_vector, bool x_or_y) {  // 1 is x, 0 is y

  auto logger = spdlog::default_logger()->clone("placer.Placement.Pull_back_vector");
  for (unsigned int i = 0; i < temp_vector.size(); ++i) {
    if (x_or_y) {
      if (temp_vector[i] + Blocks[i].Dpoint.x / 2 > Chip_D.x) {
        temp_vector[i] = Chip_D.x - Blocks[i].Dpoint.x / 2 - (1.5) * Bin_D.x / 2;
        // temp_vector[i] = Chip_D.x - Blocks[i].Dpoint.x/2;
      }
      if (temp_vector[i] - Blocks[i].Dpoint.x / 2 < 0) {
        temp_vector[i] = Blocks[i].Dpoint.x / 2 + (1.5) * Bin_D.x / 2;
        // temp_vector[i] = Blocks[i].Dpoint.x/2;
      }
    } else {
      if (temp_vector[i] + Blocks[i].Dpoint.y / 2 > Chip_D.y) {
        temp_vector[i] = Chip_D.y - Blocks[i].Dpoint.y / 2 - (1.5) * Bin_D.y / 2;
        // temp_vector[i] = Chip_D.y - Blocks[i].Dpoint.y/2;
      }
      if (temp_vector[i] - Blocks[i].Dpoint.y / 2 < 0) {
        temp_vector[i] = Blocks[i].Dpoint.y / 2 + (1.5) * Bin_D.y / 2;
        // temp_vector[i] = Blocks[i].Dpoint.y/2;
      }
    }
  }
}

void Placement::Initilize_Placement_Rand(PnRDB::hierNode &current_node) {
  for (unsigned int i = 0; i < originalBlockCNT; ++i) {
    if (Blocks[i].Cpoint.x < 0.3 or Blocks[i].Cpoint.y < 0.3) {
      Blocks[i].Cpoint.x = 0.3 + (float)(rand() % 400) / 1000;
      Blocks[i].Cpoint.y = 0.3 + (float)(rand() % 400) / 1000;
    }
  }
  for (int i = originalBlockCNT; i < Blocks.size(); ++i) {
    int id = Blocks[i].splitedsource;
    Blocks[i].Cpoint.x = Blocks[id].Cpoint.x - 0.1 + (float)(rand() % 200) / 1000;
    Blocks[i].Cpoint.y = Blocks[id].Cpoint.y - 0.1 + (float)(rand() % 200) / 1000;
    // Blocks[i].Cpoint.x = 0.45 + (float)(rand() % 100) / 1000;
    // Blocks[i].Cpoint.y = 0.45 + (float)(rand() % 100) / 1000;
  }
}

void Placement::Update_Bin_Density() {
  float unit_density = 1;

  for (unsigned int i = 0; i < Bins.size(); ++i) {
    for (unsigned int j = 0; j < Bins[i].size(); ++j) {
      Bins[i][j].density = 0.0;
    }
  }

  for (unsigned int i = 0; i < Bins.size(); ++i) {
    for (unsigned int j = 0; j < Bins[i].size(); ++j) {
      for (unsigned int k = 0; k < Blocks.size(); ++k) {
        float x_common_length = 0.0;
        bool x_common;
        x_common = Find_Common_Area(Blocks[k].Cpoint.x, Blocks[k].Dpoint.x, Bins[i][j].Cpoint.x, Bins[i][j].Dpoint.x, x_common_length);
        float y_common_length = 0.0;
        bool y_common;
        y_common = Find_Common_Area(Blocks[k].Cpoint.y, Blocks[k].Dpoint.y, Bins[i][j].Cpoint.y, Bins[i][j].Dpoint.y, y_common_length);

        if (x_common and y_common) {
          Bins[i][j].density += unit_density * x_common_length * y_common_length;
        }
      }

      Bins[i][j].density = Bins[i][j].density / (Bin_D.x * Bin_D.y);
    }
  }
}

bool Placement::Find_Common_Area(float x_center_block, float block_width, float x_center_bin, float bin_width, float &common_length) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.Find_Common_Area");
  float x_lower_block = x_center_block - block_width / 2;
  float x_upper_block = x_center_block + block_width / 2;
  float x_lower_bin = x_center_bin - bin_width / 2;
  float x_upper_bin = x_center_bin + bin_width / 2;

  float eqv_x_lower = max(x_lower_block, x_lower_bin);
  float eqv_x_upper = min(x_upper_block, x_upper_bin);

  common_length = eqv_x_upper - eqv_x_lower;

  if (common_length > 0) {
    return true;
  } else {
    return false;
  }
}

void Placement::Cal_Eforce_Block(int block_id) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.Cal_Eforce_Block");
  // Q: should compare with replace's implementation
  Blocks[block_id].Eforce.x = 0.0;
  Blocks[block_id].Eforce.y = 0.0;

  for (unsigned int i = 0; i < Bins.size(); ++i) {
    for (unsigned int j = 0; j < Bins[i].size(); ++j) {
      float x_common_length;
      bool x_common;
      x_common = Find_Common_Area(Blocks[block_id].Cpoint.x, Blocks[block_id].Dpoint.x, Bins[i][j].Cpoint.x, Bins[i][j].Dpoint.x, x_common_length);
      float y_common_length;
      bool y_common;
      y_common = Find_Common_Area(Blocks[block_id].Cpoint.y, Blocks[block_id].Dpoint.y, Bins[i][j].Cpoint.y, Bins[i][j].Dpoint.y, y_common_length);

      if (x_common and y_common) {  // Q: should be x_common_length*y_common_length?
        Blocks[block_id].Eforce.x += (y_common_length * x_common_length / (Bin_D.x * Bin_D.y)) * Bins[i][j].Eforce.x;
        Blocks[block_id].Eforce.y += (y_common_length * x_common_length / (Bin_D.x * Bin_D.y)) * Bins[i][j].Eforce.y;
      }
    }
  }
}

float Placement::Cal_HPWL() {
  float HPWL = 0;
  for (unsigned int i = 0; i < Nets.size(); ++i) {
    vector<float> x_value;
    vector<float> y_value;
    for (unsigned int j = 0; j < Nets[i].connected_block.size(); ++j) {
      int block_index = Nets[i].connected_block[j];
      x_value.push_back(Blocks[block_index].Cpoint.x);
      y_value.push_back(Blocks[block_index].Cpoint.y);
    }
    float max_x = x_value[0];
    float min_x = x_value[0];
    float max_y = y_value[0];
    float min_y = y_value[0];
    for (unsigned int j = 0; j < x_value.size(); ++j) {
      if (max_x < x_value[j]) max_x = x_value[j];
      if (min_x > x_value[j]) min_x = x_value[j];
      if (max_y < y_value[j]) max_y = y_value[j];
      if (min_y > y_value[j]) min_y = y_value[j];
    }
    HPWL += abs(max_x - min_x) + abs(max_y - min_y);
  }
  return HPWL;
}

void Placement::PlotPlacement(int index) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.PlotPlacement");
  string outfile = to_string(index) + ".plt";

  ofstream fout;
  fout.open(outfile.c_str());

  // set title
  fout << "#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)" << endl;
  fout << "\nset title\" #Blocks= " << Blocks.size() << ", #Nets= " << Nets.size() << ", Area=" << Chip_D.x * Chip_D.y << ", HPWL= " << Cal_HPWL() << " \""
       << endl;
  fout << "\nset nokey" << endl;
  fout << "#   Uncomment these two lines starting with \"set\"" << endl;
  fout << "#   to save an EPS file for inclusion into a latex document" << endl;
  fout << "# set terminal postscript eps color solid 20" << endl;
  fout << "# set output \"result.eps\"" << endl << endl;
  fout << "#   Uncomment these two lines starting with \"set\"" << endl;
  fout << "#   to save a PS file for printing" << endl;
  fout << "set term jpeg" << endl;
  fout << "set output \"" << to_string(index) + ".jpg"
       << "\"" << endl
       << endl;

  // set range
  float bias = 0;
  fout << "\nset xrange [" << 0.0 - bias << ":" << Chip_D.x + bias << "]" << endl;
  fout << "\nset yrange [" << 0.0 - bias << ":" << Chip_D.y + bias << "]" << endl;

  // set labels for blocks
  /*
    for(int i=0;i<(int)Blocks.size();++i) {
      fout<<"\nset label \""<<" B"+to_string(i)<<"\" at "<<Blocks[i].Cpoint.x<<" , "<<Blocks[i].Cpoint.y<<" center "<<endl;
    }
    */

  for (int i = 0; i < originalBlockCNT; ++i) {
    // fout << "\nset label \"" << Blocks[i].blockname << "\" at " << Blocks[i].Cpoint.x << " , " << Blocks[i].Cpoint.y << " center " << endl;
    fout << "\nset label \"" << Blocks[i].blockname << "\" at " << Blocks[i].Cpoint.x << " , " << Blocks[i].Cpoint.y << " center " << endl;
  }

  // fout << "\nplot[:][:] \'-\' with lines linestyle 3 lc 2,  \'-\' with lines linestyle 7 lc 2, "<<
  //       "\'-\' with lines linestyle 1 lc 2, \'-\' with lines linestyle 0 lc 2" << endl
  //      << endl;
  ;

  for (int i = 0; i < originalBlockCNT; ++i) {
    fout << "\nplot[:][:] \'-\' with lines linestyle 3 lc " << to_string(2 * i) << ",  \'-\' with lines linestyle 7 lc " << to_string(i * 2) << ", "
         << "\'-\' with lines linestyle 1 lc " << to_string(i * 2) << ", \'-\' with lines linestyle 0 lc " << to_string(i * 2) << "" << endl
         << endl;
    fout << "\t" << Blocks[i].Cpoint.x - Blocks[i].Dpoint.x / 2 << "\t" << Blocks[i].Cpoint.y - Blocks[i].Dpoint.y / 2 << endl;
    fout << "\t" << Blocks[i].Cpoint.x - Blocks[i].Dpoint.x / 2 << "\t" << Blocks[i].Cpoint.y + Blocks[i].Dpoint.y / 2 << endl;
    fout << "\t" << Blocks[i].Cpoint.x + Blocks[i].Dpoint.x / 2 << "\t" << Blocks[i].Cpoint.y + Blocks[i].Dpoint.y / 2 << endl;
    fout << "\t" << Blocks[i].Cpoint.x + Blocks[i].Dpoint.x / 2 << "\t" << Blocks[i].Cpoint.y - Blocks[i].Dpoint.y / 2 << endl;
    fout << "\t" << Blocks[i].Cpoint.x - Blocks[i].Dpoint.x / 2 << "\t" << Blocks[i].Cpoint.y - Blocks[i].Dpoint.y / 2 << endl;
    fout << endl;
  }
  fout << "\nEOF" << endl;
  /*
    // plot connections
    for(int i=0;i<Nets.size();i++){
      for(int j=0;j<Nets[i].connected_block.size()-1;j++){
        int first_block_index = Nets[i].connected_block[j];
        int second_block_index = Nets[i].connected_block[j+1];
        fout<<"\t"<<Blocks[first_block_index].Cpoint.x<<"\t"<<Blocks[first_block_index].Cpoint.y<<endl;
        fout<<"\t"<<Blocks[second_block_index].Cpoint.x<<"\t"<<Blocks[second_block_index].Cpoint.y<<endl;
        fout<<"\t"<<Blocks[first_block_index].Cpoint.x<<"\t"<<Blocks[first_block_index].Cpoint.y<<endl<<endl;
      }
      if(Nets[i].connected_block.size()-1>0) fout<<"\nEOF"<<endl;
    }
    */

  fout.close();
}

// WA model
// void Placement::Cal_WA_Net_Force()
// {

//   for (unsigned int i = 0; i < Nets.size(); ++i)
//   {

//     Nets[i].PSumNetforce.x = LSE_Net_SUM_P(i, 1);
//     Nets[i].PSumNetforce.y = LSE_Net_SUM_P(i, 0);
//     Nets[i].NSumNetforce.x = LSE_Net_SUM_N(i, 1);
//     Nets[i].NSumNetforce.y = LSE_Net_SUM_N(i, 0);

//     Nets[i].PSumNetforce_WA.x = WA_Net_SUM_P(i, 1);
//     Nets[i].PSumNetforce_WA.y = WA_Net_SUM_P(i, 0);
//     Nets[i].NSumNetforce_WA.x = WA_Net_SUM_N(i, 1);
//     Nets[i].NSumNetforce_WA.y = WA_Net_SUM_N(i, 0);
//   }

//   for (unsigned int i = 0; i < Blocks.size(); ++i)
//   {

//     Blocks[i].Net_block_force_P.x = LSE_block_P(i, 1);
//     Blocks[i].Net_block_force_P.y = LSE_block_P(i, 0);
//     Blocks[i].Net_block_force_N.x = LSE_block_N(i, 1);
//     Blocks[i].Net_block_force_N.y = LSE_block_N(i, 0);
//   }

//   for (unsigned int i = 0; i < Blocks.size(); ++i)
//   {
//     Blocks[i].Netforce.x = 0;
//     Blocks[i].Netforce.y = 0;
//     for (unsigned int j = 0; j < Blocks[i].connected_net.size(); j++)
//     {
//       int net_index = Blocks[i].connected_net[j];

//       Ppoint_F PSumNetforce = Nets[net_index].PSumNetforce;
//       Ppoint_F NSumNetforce = Nets[net_index].NSumNetforce;
//       Ppoint_F PSumNetforce_WA = Nets[net_index].PSumNetforce_WA;
//       Ppoint_F NSumNetforce_WA = Nets[net_index].NSumNetforce_WA;
//       float x_positive = ((1 + Blocks[i].Cpoint.x / gammar) * Blocks[i].Net_block_force_P.x * PSumNetforce.x - Blocks[i].Net_block_force_P.x *
//       PSumNetforce_WA.x) / (PSumNetforce.x * PSumNetforce.x); float x_nagative = ((1 + Blocks[i].Cpoint.x / gammar) * Blocks[i].Net_block_force_N.x *
//       NSumNetforce.x - Blocks[i].Net_block_force_N.x * NSumNetforce_WA.x) / (NSumNetforce.x * NSumNetforce.x); float y_positive = ((1 + Blocks[i].Cpoint.y /
//       gammar) * Blocks[i].Net_block_force_P.y * PSumNetforce.y - Blocks[i].Net_block_force_P.y * PSumNetforce_WA.y) / (PSumNetforce.y * PSumNetforce.y);
//       float y_nagative = ((1 + Blocks[i].Cpoint.y / gammar) * Blocks[i].Net_block_force_N.y * NSumNetforce.y - Blocks[i].Net_block_force_N.y *
//       NSumNetforce_WA.y) / (NSumNetforce.y * NSumNetforce.y); Blocks[i].Netforce.x += x_positive - x_nagative; Blocks[i].Netforce.y += y_positive -
//       y_nagative;
//     }
//   }
// }

void Placement::Cal_WA_Net_Force() {
  auto logger = spdlog::default_logger()->clone("placer.Placement.Cal_WA_Net_Force");
  for (unsigned int i = 0; i < Nets.size(); ++i) {
    Nets[i].PSumNetforce.x = LSE_Net_SUM_P(i, 1);
    Nets[i].PSumNetforce.y = LSE_Net_SUM_P(i, 0);
    Nets[i].NSumNetforce.x = LSE_Net_SUM_N(i, 1);
    Nets[i].NSumNetforce.y = LSE_Net_SUM_N(i, 0);

    Nets[i].PSumNetforce_WA.x = WA_Net_SUM_P(i, 1);
    Nets[i].PSumNetforce_WA.y = WA_Net_SUM_P(i, 0);
    Nets[i].NSumNetforce_WA.x = WA_Net_SUM_N(i, 1);
    Nets[i].NSumNetforce_WA.y = WA_Net_SUM_N(i, 0);

    logger->debug("net sum {0} {1} {2} {3} {4} {5} {6} {7} {8}", i, Nets[i].PSumNetforce.x, Nets[i].PSumNetforce.y, Nets[i].NSumNetforce.x,
                  Nets[i].NSumNetforce.y, Nets[i].PSumNetforce_WA.x, Nets[i].PSumNetforce_WA.y, Nets[i].NSumNetforce_WA.x, Nets[i].NSumNetforce_WA.y);
  }

  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    Blocks[i].Net_block_force_P.x = LSE_block_P(i, 1);
    Blocks[i].Net_block_force_P.y = LSE_block_P(i, 0);
    Blocks[i].Net_block_force_N.x = LSE_block_N(i, 1);
    Blocks[i].Net_block_force_N.y = LSE_block_N(i, 0);
    logger->debug("block single net force {0} {1} {2} {3}", Blocks[i].Net_block_force_P.x, Blocks[i].Net_block_force_P.y, Blocks[i].Net_block_force_N.x,
                  Blocks[i].Net_block_force_N.y);
  }

  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    Blocks[i].Netforce.x = 0;
    Blocks[i].Netforce.y = 0;
    logger->debug("block {0}", i);
    for (unsigned int j = 0; j < Blocks[i].connected_net.size(); j++) {
      int net_index = Blocks[i].connected_net[j];

      Ppoint_F PSumNetforce = Nets[net_index].PSumNetforce;
      Ppoint_F NSumNetforce = Nets[net_index].NSumNetforce;
      Ppoint_F PSumNetforce_WA = Nets[net_index].PSumNetforce_WA;
      Ppoint_F NSumNetforce_WA = Nets[net_index].NSumNetforce_WA;
      logger->debug("block info {0} net index {1} {2} {3} {4} {5} {6} {7} {8}", i, net_index, Nets[net_index].PSumNetforce.x, Nets[net_index].PSumNetforce.y,
                    Nets[net_index].NSumNetforce.x, Nets[net_index].NSumNetforce.y, Nets[net_index].PSumNetforce_WA.x, Nets[net_index].PSumNetforce_WA.y,
                    Nets[net_index].NSumNetforce_WA.x, Nets[net_index].NSumNetforce_WA.y);

      float x_positive =
          ((1 + Blocks[i].Cpoint.x / gammar) * Blocks[i].Net_block_force_P.x * PSumNetforce.x - Blocks[i].Net_block_force_P.x * PSumNetforce_WA.x) /
          (PSumNetforce.x * PSumNetforce.x);
      float x_nagative =
          ((1 + Blocks[i].Cpoint.x / gammar) * Blocks[i].Net_block_force_N.x * NSumNetforce.x - Blocks[i].Net_block_force_N.x * NSumNetforce_WA.x) /
          (NSumNetforce.x * NSumNetforce.x);
      float y_positive =
          ((1 + Blocks[i].Cpoint.y / gammar) * Blocks[i].Net_block_force_P.y * PSumNetforce.y - Blocks[i].Net_block_force_P.y * PSumNetforce_WA.y) /
          (PSumNetforce.y * PSumNetforce.y);
      float y_nagative =
          ((1 + Blocks[i].Cpoint.y / gammar) * Blocks[i].Net_block_force_N.y * NSumNetforce.y - Blocks[i].Net_block_force_N.y * NSumNetforce_WA.y) /
          (NSumNetforce.y * NSumNetforce.y);
      if (net_index >= originalNetCNT) {
        Blocks[i].Netforce.x += dummy_net_weight * (x_positive - x_nagative);
        Blocks[i].Netforce.y += dummy_net_weight * (y_positive - y_nagative);
      } else {
        Blocks[i].Netforce.x += (x_positive - x_nagative);
        Blocks[i].Netforce.y += (y_positive - y_nagative);
      }
    }
    logger->debug("block net force {0} force {1} {2}", i, Blocks[i].Netforce.x, Blocks[i].Netforce.y);
  }
}

float Placement::WA_Net_SUM_P(int net_index, bool x_or_y) {
  // 1/r *( sum xi*exp(xi/r) )

  float result = 0.0;

  for (unsigned int i = 0; i < Nets[net_index].connected_block.size(); i++) {
    int block_index = Nets[net_index].connected_block[i];

    if (x_or_y) {  // 1 for x
      result += Blocks[block_index].Cpoint.x * Exp_Function(Blocks[block_index].Cpoint.x, gammar);
    } else {
      result += Blocks[block_index].Cpoint.y * Exp_Function(Blocks[block_index].Cpoint.y, gammar);
    }
  }

  return result / gammar;
}

float Placement::WA_Net_SUM_N(int net_index, bool x_or_y) {
  // 1/r *( sum xi*exp(-xi/r) )

  float result = 0.0;

  for (unsigned int i = 0; i < Nets[net_index].connected_block.size(); i++) {
    int block_index = Nets[net_index].connected_block[i];

    if (x_or_y) {  // 1 for x
      result += Blocks[block_index].Cpoint.x * Exp_Function(-Blocks[block_index].Cpoint.x, gammar);
    } else {
      result += Blocks[block_index].Cpoint.y * Exp_Function(-Blocks[block_index].Cpoint.y, gammar);
    }
  }

  return result / gammar;
}
// End WA model

// Area model
void Placement::Cal_LSE_Area_Force() {
  float Area_SUM_P_X = Area_SUM_P(1);
  float Area_SUM_P_Y = Area_SUM_P(0);

  float Area_SUM_N_X = Area_SUM_N(1);
  float Area_SUM_N_Y = Area_SUM_N(0);

  float LSE_X = gammar * (log((double)Area_SUM_P_X) - log((double)Area_SUM_N_X));
  float LSE_Y = gammar * (log((double)Area_SUM_P_Y) - log((double)Area_SUM_N_Y));

  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    Blocks[i].Net_block_force_P.x = LSE_block_P(i, 1);
    Blocks[i].Net_block_force_P.y = LSE_block_P(i, 0);
    Blocks[i].Net_block_force_N.x = LSE_block_N(i, 1);
    Blocks[i].Net_block_force_N.y = LSE_block_N(i, 0);
  }

  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    Blocks[i].Areaforce.x = (Blocks[i].Net_block_force_P.x / Area_SUM_P_X - Blocks[i].Net_block_force_N.x / Area_SUM_N_X) * LSE_Y;
    Blocks[i].Areaforce.y = (Blocks[i].Net_block_force_P.y / Area_SUM_P_Y - Blocks[i].Net_block_force_N.y / Area_SUM_N_Y) * LSE_X;
  }
}

float Placement::Area_SUM_P(bool x_or_y) {
  float result = 0.0;

  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    if (x_or_y) {
      result += Exp_Function(Blocks[i].Cpoint.x, gammar);
    } else {
      result += Exp_Function(Blocks[i].Cpoint.y, gammar);
    }
  }

  return result;
}

float Placement::Area_SUM_N(bool x_or_y) {
  float result = 0.0;

  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    if (x_or_y) {
      result += Exp_Function(-Blocks[i].Cpoint.x, gammar);
    } else {
      result += Exp_Function(-Blocks[i].Cpoint.y, gammar);
    }
  }

  return result;
}

float Placement::LSE_Net_SUM_P(int net_index, bool x_or_y) {
  float result = 0.0;

  for (unsigned int i = 0; i < Nets[net_index].connected_block.size(); i++) {
    int block_index = Nets[net_index].connected_block[i];

    if (x_or_y) {  // 1 for x
      result += Exp_Function(Blocks[block_index].Cpoint.x, gammar);
    } else {
      result += Exp_Function(Blocks[block_index].Cpoint.y, gammar);
    }
  }

  return result;
}

float Placement::LSE_Net_SUM_N(int net_index, bool x_or_y) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.Update_Bin_Density");
  float result = 0.0;

  for (unsigned int i = 0; i < Nets[net_index].connected_block.size(); i++) {
    int block_index = Nets[net_index].connected_block[i];

    if (x_or_y) {  // 1 for x
      result += Exp_Function(-Blocks[block_index].Cpoint.x, gammar);

    } else {
      result += Exp_Function(-Blocks[block_index].Cpoint.y, gammar);
    }
  }

  return result;
}

float Placement::LSE_block_P(int block_index, int x_or_y) {
  float result = 0.0;

  if (x_or_y) {  // 1 for x
    result += Exp_Function(Blocks[block_index].Cpoint.x, gammar);
  } else {
    result += Exp_Function(Blocks[block_index].Cpoint.y, gammar);
  }

  return result;
}

float Placement::LSE_block_N(int block_index, int x_or_y) {
  float result = 0.0;

  if (x_or_y) {  // 1 for x
    result += Exp_Function(-Blocks[block_index].Cpoint.x, gammar);
  } else {
    result += Exp_Function(-Blocks[block_index].Cpoint.y, gammar);
  }

  return result;
}

float Placement::Exp_Function(float x, float gammar) {
  // float result = exp(x/gammar);
  float offset = 0;
  // float result = Fast_Exp(x/gammar-offset);
  float result = exp(x / gammar - offset);

  return result;
}

// Q: might need a fast exp cal function
// END LSE model

void Placement::Cal_Density_Eforce() {
  auto logger = spdlog::default_logger()->clone("placer.Placement.Cal_Density_Eforce");

  int binCntX = x_dimension_bin;
  int binCntY = y_dimension_bin;
  float binSizeX = unit_x_bin;
  float binSizeY = unit_y_bin;

  replace::FFT fft(binCntX, binCntY, binSizeX, binSizeY);

  for (unsigned int i = 0; i < binCntX; ++i) {
    for (unsigned int j = 0; j < binCntY; j++) {
      fft.updateDensity(i, j, Bins[i][j].density);
    }
  }

  fft.doFFT();

  for (unsigned int i = 0; i < binCntX; ++i) {
    for (unsigned int j = 0; j < binCntY; ++j) {
      auto eForcePair = fft.getElectroForce(i, j);
      Bins[i][j].Eforce.x = eForcePair.first;
      Bins[i][j].Eforce.y = eForcePair.second;

      float electroPhi = fft.getElectroPhi(i, j);
      Bins[i][j].Ephi = electroPhi;
    }
    // sumPhi_ += electroPhi*static_cast<float>(bin->nonPlaceArea()+bin->instPlacedArea()+bin->fillerArea());
  }

  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    Cal_Eforce_Block(i);
  }
}

void Placement::Cal_force() {
  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    //  Blocks[i].Force.x = lambda*Blocks[i].Eforce.x - beta*Blocks[i].Netforce.x;
    //  Blocks[i].Force.y = lambda*Blocks[i].Eforce.y - beta*Blocks[i].Netforce.y;

    Blocks[i].Force.x = lambda * Blocks[i].Eforce.x - beta * Blocks[i].Netforce.x - sym_beta * Blocks[i].Symmetricforce.x - area_beta * Blocks[i].Areaforce.x;
    Blocks[i].Force.y = lambda * Blocks[i].Eforce.y - beta * Blocks[i].Netforce.y - sym_beta * Blocks[i].Symmetricforce.y - area_beta * Blocks[i].Areaforce.y;
    //  std::cout<<"symmetricforce/all"<<sym_beta*Blocks[i].Symmetricforce.x<<", "<<sym_beta*Blocks[i].Symmetricforce.y<<std::endl;
    //  if(isnan(Blocks[i].Force.x))
    //  {
    //    Blocks[i].Force.x = 0;
    //  }
    //  if(isnan(Blocks[i].Force.y))
    //  {
    //    Blocks[i].Force.y = 0;
    //  }
  }
}

float Placement::Cal_Overlap() {
  auto logger = spdlog::default_logger()->clone("placer.Placement.Cal_Overlap");
  float max_overlap = 0.0f;

  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    Blocks[i].overlap = 0.0f;

    for (unsigned int j = 0; j < Blocks.size(); ++j) {
      if (i != j) {
        float x_common_length = 0.0;
        bool x_common;
        x_common = Find_Common_Area(Blocks[i].Cpoint.x, Blocks[i].Dpoint.x, Blocks[j].Cpoint.x, Blocks[j].Dpoint.x, x_common_length);
        float y_common_length = 0.0;
        bool y_common;
        y_common = Find_Common_Area(Blocks[i].Cpoint.y, Blocks[i].Dpoint.y, Blocks[j].Cpoint.y, Blocks[j].Dpoint.y, y_common_length);

        if (x_common and y_common) {
          float overlap = x_common_length * y_common_length / (Blocks[i].Dpoint.x * Blocks[i].Dpoint.y);
          if (overlap > Blocks[i].overlap) {
            Blocks[i].overlap = overlap;
          }
          // Blocks[i].overlap += overlap;
        }
      }
    }
  }

  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    if (max_overlap < Blocks[i].overlap) {
      max_overlap = Blocks[i].overlap;
    }
  }

  logger->debug("Max overlap {0}", max_overlap);

  return max_overlap;
}

void Placement::E_Placer(PnRDB::hierNode &current_node) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.E_Placer");
  int i = 0;

  // force to align and order
  // force_alignment();
  vector<float> uc_y, vc_y, vl_y;
  vector<float> uc_x, vc_x, vl_x;
  force_order(vc_x, vl_x, vc_y, vl_y);
  force_alignment(vc_x, vl_x, vc_y, vl_y);

  Update_Bin_Density();

  // gradient cal
  Cal_WA_Net_Force();

  Cal_Density_Eforce();

  Cal_sym_Force();

  Cal_LSE_Area_Force();
  Cal_force();

  float ac_x = 1.0f;
  vector<float> pre_vc_x, pre_vl_x;
  pre_conditioner(pre_vl_x, 1);  // 1 x direction

  // vector<float> uc_x,vc_x,vl_x;
  Extract_Placement_Vectors(uc_x, 1);

  Extract_Placement_Vectors(vc_x, 1);

  Extract_Placement_Vectors(vl_x, 1);


  float ac_y = 1.0f;
  vector<float> pre_vc_y, pre_vl_y;
  pre_conditioner(pre_vl_y, 0);  // 1 x direction

  // vector<float> uc_y,vc_y,vl_y;
  Extract_Placement_Vectors(uc_y, 0);

  Extract_Placement_Vectors(vc_y, 0);

  Extract_Placement_Vectors(vl_y, 0);

  bool start_flag = 1;
  Update_Bin_Density();


  float stop_density = 0.01;
  float max_density = 1.0;
  float current_max_density = 10.0;
  int count_number = 0;
  int upper_count_number = 80;
  float current_overlap = 1.0;
  float symmetricMin = 0.3;  // need to tune
  // initialize dummy net weight
  // dummy_net_weight = 0.001;
  // float dummy_net_weight_rate = dummy_net_weight_rate;
  // float dummy_net_target = 3.0;
  float dummy_net_weight_increase = cal_weight_init_increase(dummy_net_rate, dummy_net_weight, dummy_net_target, 100);
  vector<float> Density;
  vector<float> Overlap;

  PlotPlacement(0);
  current_overlap = Cal_Overlap();


  while ((current_overlap > 0.3 or symCheck(symmetricMin)) and count_number < upper_count_number) {  // Q: stop condition
    // while(i<20){//Q: stop condition
    Density.push_back(current_max_density);
    current_overlap = Cal_Overlap();
    Overlap.push_back(current_overlap);
    if (current_max_density < max_density) {
      max_density = current_max_density;

    } else if (current_max_density == Density.back()) {

      count_number++;
    }

    //  Density.push_back(current_max_density);

    // if(lambda<100)
    lambda = lambda * 1.1;
    beta = beta * 0.95;
    if (sym_beta < 0.1) {
      sym_beta = sym_beta * 1.05;
    }

    logger->debug("sym_beta:= {0}", sym_beta);
    // force to align
    if (i % 10 == 0) {
      force_order(vc_x, vl_x, vc_y, vl_y);
      force_alignment(vc_x, vl_x, vc_y, vl_y);

      //  force_alignment();
    }

    // PlotPlacement(i);

    Update_Bin_Density();
    // gradient cal
    Cal_WA_Net_Force();
    cal_dummy_net_weight(dummy_net_weight, dummy_net_rate, dummy_net_weight_increase);
    Cal_Density_Eforce();

    Cal_sym_Force();
    Cal_LSE_Area_Force();
    Cal_force();

    pre_conditioner(pre_vc_x, 1);  // 1 x direction

    Nesterov_based_iteration(ac_x, uc_x, vc_x, vl_x, pre_vc_x, pre_vl_x, start_flag);
// two direction y

    pre_conditioner(pre_vc_y, 0);  // 0 y direction

    Nesterov_based_iteration(ac_y, uc_y, vc_y, vl_y, pre_vc_y, pre_vl_y, start_flag);
    logger->debug("iteration {0} step size {1} {2}", i, ac_x, ac_y);
    Pull_back_vector(uc_x, 1);
    Pull_back_vector(uc_y, 0);
    Feedback_Placement_Vectors(uc_x, 1);
    Feedback_Placement_Vectors(uc_y, 0);
    Pull_back_vector(vc_x, 1);
    Pull_back_vector(vl_x, 1);
    Pull_back_vector(vc_y, 0);
    Pull_back_vector(vl_y, 0);
    // PlotPlacement(i);

    start_flag = 0;
    i++;
  }

  // exit(0);
  while (!check_order()) {
    force_order(vc_x, vl_x, vc_y, vl_y);
    force_alignment(vc_x, vl_x, vc_y, vl_y);
  }

  // restore_MS();
  PlotPlacement(count_number);
  logger->debug("iter num when stop:={0}", count_number);
}


void Placement::Extract_Placement_Vectors(vector<float> &temp_vector, bool x_or_y) {  // 1 is x, 0 is y

  temp_vector.clear();
  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    if (x_or_y) {
      temp_vector.push_back(Blocks[i].Cpoint.x);
    } else {
      temp_vector.push_back(Blocks[i].Cpoint.y);
    }
  }
}

void Placement::Feedback_Placement_Vectors(vector<float> &temp_vector, bool x_or_y) {  // 1 is x, 0 is y

  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    if (x_or_y) {
      Blocks[i].Cpoint.x = temp_vector[i];
    } else {
      Blocks[i].Cpoint.y = temp_vector[i];
    }
  }
}

void Placement::Nesterov_based_iteration(float &ac, vector<float> &uc, vector<float> &vc, vector<float> &vl, vector<float> &pre_vc, vector<float> &pre_vl,
                                         bool start_flag) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.Nesterov_based_iteration");
  // Q:
  // Cal_WA_Net_Force();
  // Cal_bin_force(); to be implemented
  // this function works for one direction, need to call twice x/y
  // Q:

  // start nesterov method
  // algorithm 1 of ePlace-MS: Electrostatics-Based Placement forMixed-Size Circuits
  float an;          // current/last step size
  vector<float> un;  // next/current/last vector u
  vector<float> vn;  // next/current/last vector u
// float ak = BkTrk(vc,vl,pre_vc,pre_vl); //Q: the port defination of BkTrk is not correct

  if (!start_flag) {
    // if(0){
    BkTrk(ac, an, uc, vc, vl, pre_vc, pre_vl);  // Q: the port defination of BkTrk is not correct
  }
// Q: BkTrk need to be revised since back tracing is not considered

  for (unsigned int i = 0; i < uc.size(); ++i) {
    // un.push_back(vc[i]-ac*pre_vc[i]); //QQQ:LIYG Huge change
    un.push_back(vc[i] + ac * pre_vc[i]);
  }

  an = (1 + sqrt(1 + 4 * ac * ac)) / 2;

  for (unsigned int i = 0; i < uc.size(); ++i) {
    vn.push_back(un[i] + (ac - 1) * (un[i] - uc[i]) / an);
  }

  // ac = an;
  uc = un;
  vl = vc;
  vc = vn;
  pre_vl = pre_vc;
}

void Placement::BkTrk(float &ac, float &an, vector<float> &uc, vector<float> &vc, vector<float> &vl, vector<float> &pre_vc, vector<float> &pre_vl) {
// algorithm 2 of ePlace-MS: Electrostatics-Based Placement forMixed-Size Circuits

  float hat_ac = vector_fraction(vc, vl, pre_vc, pre_vl);

  vector<float> hat_un;
  cal_hat_un(hat_ac, hat_un, vc, pre_vc);

  vector<float> hat_vn;
  cal_hat_vn(ac, an, hat_vn, hat_un, uc);



  ac = hat_ac;
  //  if(isnan(ac))
  //  {
  //    ac = 1;
  //  }
  //  else if(isnan(-ac))
  //  {
  //    ac = -1;
  //  }
}

float Placement::vector_fraction(vector<float> &vc, vector<float> &vl, vector<float> &pre_vc, vector<float> &pre_vl) {
  float sum_upper = 0.0;
  for (unsigned int i = 0; i < vc.size(); ++i) {
    sum_upper += (vc[i] - vl[i]) * (vc[i] - vl[i]);
  }
  sum_upper = sqrt(sum_upper);
  float sum_lower = 0.0;
  for (unsigned int i = 0; i < vc.size(); ++i) {
    sum_lower += (pre_vc[i] - pre_vl[i]) * (pre_vc[i] - pre_vl[i]);
  }
  sum_lower = sqrt(sum_lower);

  float hat_ac = sum_upper / sum_lower;
  return hat_ac;
}

void Placement::cal_hat_un(float &hat_ac, vector<float> &hat_un, vector<float> &vc, vector<float> &pre_vc) {
  for (unsigned int i = 0; i < vc.size(); ++i) {
    hat_un.push_back(vc[i] - hat_ac * pre_vc[i]);
  }
}

void Placement::cal_hat_vn(float &ac, float &an, vector<float> &hat_vn, vector<float> &hat_un, vector<float> &uc) {
  for (unsigned int i = 0; i < hat_un.size(); ++i) {
    hat_vn.push_back(hat_un[i] + (ac - 1) * (hat_un[i] - uc[i]) / an);
  }
}

// Calculating pre(vk) Q: also two directions
void Placement::pre_conditioner(vector<float> &Pre_Conditioner, bool x_or_y) {  // 1 is for x, 0 is for y

  vector<float> HPWL_Pre_Conditioner;
  WA_pre_conditioner(HPWL_Pre_Conditioner, x_or_y);
  // Yaguang (07/04/2021): found a bug - symmetry precondition pre_conditioner is missing actually. It can be calculated acctually

  vector<float> Desity_Pre_Conditioner;
  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    if (x_or_y) {
      Desity_Pre_Conditioner.push_back(Blocks[i].Dpoint.x);
    } else {
      Desity_Pre_Conditioner.push_back(Blocks[i].Dpoint.y);
    }
  }

  Pre_Conditioner.clear();
  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    if (x_or_y) {
      Pre_Conditioner.push_back(1 / (HPWL_Pre_Conditioner[i] + lambda * Desity_Pre_Conditioner[i]) * (Blocks[i].Force.x));
    } else {
      Pre_Conditioner.push_back(1 / (HPWL_Pre_Conditioner[i] + lambda * Desity_Pre_Conditioner[i]) * (Blocks[i].Force.y));
    }
  }
}

void Placement::WA_pre_conditioner(vector<float> &HPWL_Pre_Conditioner, bool x_or_y) {
  HPWL_Pre_Conditioner.clear();

  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    float sum = 0.0;
    sum = Blocks[i].connected_net.size();
    HPWL_Pre_Conditioner.push_back(sum);
  }
}

void Placement::WriteOut_Bins(int iteration) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.WriteOut_Bins");
  std::ofstream writoutfile;

  std::string file_name = to_string(iteration) + "_Iter_Bins.txt";

  writoutfile.open(file_name);

  for (unsigned int i = 0; i < Bins.size(); ++i) {
    for (unsigned int j = 0; j < Bins[i].size(); j++) {
      writoutfile << Bins[i][j].Cpoint.x << " " << Bins[i][j].Cpoint.y << " " << Bins[i][j].Dpoint.x << " " << Bins[i][j].Dpoint.y << " " << Bins[i][j].density
                  << " " << Bins[i][j].Ephi << " " << Bins[i][j].Eforce.x << " " << Bins[i][j].Eforce.y << std::endl;
    }
  }

  writoutfile.close();
}

// donghao start
// return the total area of all blocks
float Placement::readInputNode(PnRDB::hierNode &current_node) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.readInputNode");
  int blockIndex = 0;
  float totalArea = 0;
  Blocks.clear();
  Nets.clear();
  logger->debug("start reading blocks file");
  int blockCNT = current_node.Blocks.size();
  // initialize sysmmtric matrix
  symmetric_force_matrix = vector<vector<Ppoint_F>>(blockCNT);
  for (int i = 0; i < blockCNT; ++i) {
    symmetric_force_matrix[i] = vector<Ppoint_F>(blockCNT);
    for (int j = 0; j < blockCNT; ++j) {
      symmetric_force_matrix[i][j].x = 0;
      symmetric_force_matrix[i][j].y = 0;
    }
  }

  for (vector<PnRDB::blockComplex>::iterator it = current_node.Blocks.begin(); it != current_node.Blocks.end(); ++it) {
    for (int i = 0; i < 1; ++i) {
      block tempblock;
      // update block name
      tempblock.blockname = it->instance[i].name;
      Ppoint_F tempPoint1, tempPoint2;
      // update center point
      tempPoint1.x = (float)it->instance[i].originCenter.x;
      tempPoint1.y = (float)it->instance[i].originCenter.y;

      // tempPoint1.x = 0.0;
      // tempPoint1.y = 0.0;
      tempblock.Cpoint = tempPoint1;

      // update height and width
      tempPoint2.x = (float)it->instance[i].width;
      tempPoint2.y = (float)it->instance[i].height;
      totalArea += tempPoint2.x * tempPoint2.y;
      tempblock.Dpoint = tempPoint2;

      // set the init force as zero
      tempblock.Force.x = 0;
      tempblock.Force.y = 0;
      tempblock.Netforce.x = 0;
      tempblock.Netforce.y = 0;
      tempblock.Eforce.x = 0;
      tempblock.Eforce.y = 0;
      // set the init NET_BLOCK_FORCE_P/N = 1
      tempblock.Net_block_force_N.x = 1;
      tempblock.Net_block_force_N.y = 1;
      tempblock.Net_block_force_P.x = 1;
      tempblock.Net_block_force_P.y = 1;
      tempblock.index = blockIndex;
      ++blockIndex;
      // connected net will be update later
      Blocks.push_back(tempblock);
    }
  }

  // update net information
  int netIndex = 0;
  logger->debug("total block number: {0}", blockIndex);
  logger->debug("start reading net file");
  for (vector<PnRDB::net>::iterator it = current_node.Nets.begin(); it != current_node.Nets.end(); ++it) {
    net tempNet;
    logger->debug("current net id:{0}", netIndex);
    // update name of net
    tempNet.netname = it->name;
    // based on my understanding, iter2 is the block id
    // I do not care about iter, which means block pin/terminal
    tempNet.connected_block.clear();
    for (int i = 0; i != it->connected.size(); ++i) {
      int iter2 = it->connected[i].iter2;
      logger->debug("connected block id: {0}", iter2);
      if (iter2 >= 0) {
        tempNet.connected_block.push_back(iter2);
        Blocks[iter2].connected_net.push_back(netIndex);
      }
    }
    // update net index
    tempNet.index = netIndex;
    ++netIndex;

    tempNet.NSumNetforce.x = 0;
    tempNet.NSumNetforce.y = 0;
    tempNet.NSumNetforce_WA.x = 0;
    tempNet.NSumNetforce_WA.y = 0;

    tempNet.PSumNetforce.x = 0;
    tempNet.PSumNetforce.y = 0;
    tempNet.PSumNetforce_WA.x = 0;
    tempNet.PSumNetforce_WA.y = 0;
    Nets.push_back(tempNet);
  }

  // read the symmtirc

  for (vector<PnRDB::SymmPairBlock>::iterator it = current_node.SPBlocks.begin(); it != current_node.SPBlocks.end(); ++it) {


    SymmPairBlock tempSPB;

    tempSPB.selfsym.clear();
    tempSPB.sympair.clear();
    // tempSPB.selfsym = it->selfsym;
    // tempSPB.sympair = it->sympair;
    for (int i = 0; i < it->selfsym.size(); ++i) {
      tempSPB.selfsym.push_back(it->selfsym[i].first);
    }
    for (int i = 0; i < it->sympair.size(); ++i) {
      tempSPB.sympair.push_back(it->sympair[i]);
    }

    if (it->axis_dir == PnRDB::V) {
      // cond 1: only one sym pair
      tempSPB.horizon = 0;
      if (it->sympair.size() == 1 && it->selfsym.size() == 0) {
        int id0 = it->sympair[0].first;
        int id1 = it->sympair[0].second;

        symmetric_force_matrix[id0][id0].y += 2;
        symmetric_force_matrix[id0][id1].y -= 2;
        symmetric_force_matrix[id1][id0].y -= 2;
        symmetric_force_matrix[id1][id1].y += 2;

        tempSPB.axis.first = id0;
        tempSPB.axis.second = id1;
      } else if (it->selfsym.size() > 0)  // exist self sym, consider the first self sym block center as axis = x0
      {
        int base = it->selfsym[0].first;
        tempSPB.axis.first = base;
        tempSPB.axis.second = base;
        // for self sym (xi - x0)^2
        for (int i = 1; i < it->selfsym.size(); ++i) {
          int id = it->selfsym[i].first;
          logger->debug("V: cond2, id = {0}", id);
          symmetric_force_matrix[id][id].x += 8;
          symmetric_force_matrix[id][base].x -= 8;
          symmetric_force_matrix[base][id].x -= 8;
          symmetric_force_matrix[base][base].x += 8;
        }
        // for pair sym (xi + xj - 2*x0)^2
        for (int i = 0; i < it->sympair.size(); ++i) {
          int id0 = it->sympair[i].first;
          int id1 = it->sympair[i].second;
          logger->debug("V: cond2, id0 = {0}, id1:{1}", id0, id1);
          //(yi - yj)^2
          symmetric_force_matrix[id0][id0].y += 2;
          symmetric_force_matrix[id0][id1].y -= 2;
          symmetric_force_matrix[id1][id0].y -= 2;
          symmetric_force_matrix[id1][id1].y += 2;

          //(xi + xj - 2*x0)^2
          symmetric_force_matrix[id0][id0].x += 2;
          symmetric_force_matrix[id0][id1].x += 2;
          symmetric_force_matrix[id0][base].x -= 4;

          symmetric_force_matrix[id1][id0].x += 2;
          symmetric_force_matrix[id1][id1].x += 2;
          symmetric_force_matrix[id1][base].x -= 4;

          symmetric_force_matrix[base][id0].x -= 2;
          symmetric_force_matrix[base][id1].x -= 2;
          symmetric_force_matrix[base][base].x += 4;
        }
      } else if (it->sympair.size() > 1)  // no self sym, consider the center of first sym pair of blocks as axis = 1/2*(x0.first + x0.second)
      {
        int idbase0 = it->sympair[0].first;
        int idbase1 = it->sympair[0].second;
        tempSPB.axis.first = idbase0;
        tempSPB.axis.second = idbase1;
        symmetric_force_matrix[idbase0][idbase0].y += 2;
        symmetric_force_matrix[idbase0][idbase1].y -= 2;
        symmetric_force_matrix[idbase1][idbase0].y -= 2;
        symmetric_force_matrix[idbase1][idbase1].y += 2;
        for (int i = 1; i < it->sympair.size(); ++i) {
          int id0 = it->sympair[i].first;
          int id1 = it->sympair[i].second;
          //(yi - yj)^2
          symmetric_force_matrix[id0][id0].y += 2;
          symmetric_force_matrix[id0][id1].y -= 2;
          symmetric_force_matrix[id1][id0].y -= 2;
          symmetric_force_matrix[id1][id1].y += 2;
          //(xi + xj - x0 - x1)^2
          symmetric_force_matrix[id0][id0].x += 2;
          symmetric_force_matrix[id0][id1].x += 2;
          symmetric_force_matrix[id0][idbase0].x -= 2;
          symmetric_force_matrix[id0][idbase1].x -= 2;

          symmetric_force_matrix[id1][id0].x += 2;
          symmetric_force_matrix[id1][id1].x += 2;
          symmetric_force_matrix[id1][idbase0].x -= 2;
          symmetric_force_matrix[id1][idbase1].x -= 2;

          symmetric_force_matrix[idbase0][id0].x -= 2;
          symmetric_force_matrix[idbase0][id1].x -= 2;
          symmetric_force_matrix[idbase0][idbase0].x += 2;
          symmetric_force_matrix[idbase0][idbase1].x += 2;

          symmetric_force_matrix[idbase1][id0].x -= 2;
          symmetric_force_matrix[idbase1][id1].x -= 2;
          symmetric_force_matrix[idbase1][idbase0].x += 2;
          symmetric_force_matrix[idbase1][idbase1].x += 2;
        }
      } else {
        continue;
      }
    } else  // axis : H
    {
      tempSPB.horizon = 1;
      // cond 1: only one sym pair
      if (it->sympair.size() == 1 && it->selfsym.size() == 0) {
        int id0 = it->sympair[0].first;
        int id1 = it->sympair[1].second;
        tempSPB.axis.first = id0;
        tempSPB.axis.second = id1;
        symmetric_force_matrix[id0][id0].x += 2;
        symmetric_force_matrix[id0][id1].x -= 2;
        symmetric_force_matrix[id1][id0].x -= 2;
        symmetric_force_matrix[id1][id1].x += 2;
      } else if (it->selfsym.size() > 0)  // exist self sym, consider the first self sym block center as axis = x0
      {
        int base = it->selfsym[0].first;
        tempSPB.axis.first = base;
        tempSPB.axis.second = base;
        // for self sym (yi - y0)^2
        for (int i = 1; i < it->selfsym.size(); ++i) {
          int id = it->selfsym[i].first;
          symmetric_force_matrix[id][id].y += 8;
          symmetric_force_matrix[id][base].y -= 8;
          symmetric_force_matrix[base][id].y -= 8;
          symmetric_force_matrix[base][base].y += 8;
        }
        // for pair sym (xi + xj - 2*x0)^2
        for (int i = 0; i < it->sympair.size(); ++i) {
          int id0 = it->sympair[i].first;
          int id1 = it->sympair[i].second;

          //(xi - xj)^2
          symmetric_force_matrix[id0][id0].x += 2;
          symmetric_force_matrix[id0][id1].x -= 2;
          symmetric_force_matrix[id1][id0].x -= 2;
          symmetric_force_matrix[id1][id1].x += 2;

          //(yi + yj - 2*y0)^2
          symmetric_force_matrix[id0][id0].y += 2;
          symmetric_force_matrix[id0][id1].y += 2;
          symmetric_force_matrix[id0][base].y -= 4;

          symmetric_force_matrix[id1][id0].y += 2;
          symmetric_force_matrix[id1][id1].y += 2;
          symmetric_force_matrix[id1][base].y -= 4;

          symmetric_force_matrix[base][id0].y -= 2;
          symmetric_force_matrix[base][id1].y -= 2;
          symmetric_force_matrix[base][base].y += 4;
        }
      } else if (it->sympair.size() > 1)  // no self sym, consider the center of first sym pair of blocks as axis = 1/2*(x0.first + x0.second)
      {
        int idbase0 = it->sympair[0].first;
        int idbase1 = it->sympair[0].second;
        tempSPB.axis.first = idbase0;
        tempSPB.axis.second = idbase1;

        symmetric_force_matrix[idbase0][idbase0].x += 2;
        symmetric_force_matrix[idbase0][idbase1].x -= 2;
        symmetric_force_matrix[idbase1][idbase0].x -= 2;
        symmetric_force_matrix[idbase1][idbase1].x += 2;
        for (int i = 1; i < it->sympair.size(); ++i) {
          int id0 = it->sympair[i].first;
          int id1 = it->sympair[i].second;

          //(xi - xj)^2
          symmetric_force_matrix[id0][id0].x += 2;
          symmetric_force_matrix[id0][id1].x -= 2;
          symmetric_force_matrix[id1][id0].x -= 2;
          symmetric_force_matrix[id1][id1].x += 2;
          //(yi + yj - y0 - y1)^2
          symmetric_force_matrix[id0][id0].y += 2;
          symmetric_force_matrix[id0][id1].y += 2;
          symmetric_force_matrix[id0][idbase0].y -= 2;
          symmetric_force_matrix[id0][idbase1].y -= 2;

          symmetric_force_matrix[id1][id0].y += 2;
          symmetric_force_matrix[id1][id1].y += 2;
          symmetric_force_matrix[id1][idbase0].y -= 2;
          symmetric_force_matrix[id1][idbase1].y -= 2;

          symmetric_force_matrix[idbase0][id0].y -= 2;
          symmetric_force_matrix[idbase0][id1].y -= 2;
          symmetric_force_matrix[idbase0][idbase0].y += 2;
          symmetric_force_matrix[idbase0][idbase1].y += 2;

          symmetric_force_matrix[idbase1][id0].y -= 2;
          symmetric_force_matrix[idbase1][id1].y -= 2;
          symmetric_force_matrix[idbase1][idbase0].y += 2;
          symmetric_force_matrix[idbase1][idbase1].y += 2;
        }
      } else {
        continue;
      }
    }
    SPBlocks.push_back(tempSPB);
  }
  // PRINT symmetric _force matrix
  logger->debug("symmetric_force matrix");
  for (int i = 0; i < blockCNT; ++i) {
    for (int j = 0; j < blockCNT; ++j) {
      logger->debug("({0}, {1})", symmetric_force_matrix[i][j].x, symmetric_force_matrix[i][j].y);
    }
  }
  // return the total area
  originalBlockCNT = Blocks.size();
  originalNetCNT = Nets.size();
  return totalArea;
}

void Placement::splitNode_MS(float uniHeight, float uniWidth) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.Update_Bin_Density");
  logger->debug("split Node MS: debug 0");
  int original_block_num = originalBlockCNT;
  for (int i = 0; i < original_block_num; ++i) {
    // step 1: determine the x-direction Standard blocks num
    logger->debug("split Node MS: debug 1");
    Ppoint_F split_numF;
    Ppoint_I split_numI;
    split_numF.y = ceil(Blocks[i].Dpoint.y / uniHeight);
    split_numF.x = ceil(Blocks[i].Dpoint.x / uniWidth);
    split_numI.x = int(split_numF.x);
    split_numI.y = int(split_numF.y);
    // step 2: determine the y-direction standard blocks num
    int num_of_add_blocks = split_numI.y * split_numI.x - 1;
    if (num_of_add_blocks > 0) {
      Blocks[i].splited = 1;
      Blocks[i].Dpoint.x = uniWidth;
      Blocks[i].Dpoint.y = uniHeight;
      Blocks[i].split_shape = split_numF;  // save the information to restore
    }
    int id = Blocks.size();
    for (int j = 0; j < num_of_add_blocks; ++j) {
      logger->debug("split Node MS: debug 2");
      block temp;
      temp.blockname = Blocks[i].blockname + "_" + to_string(j + 1);
      temp.Dpoint.x = uniWidth;
      temp.Dpoint.y = uniHeight;
      temp.splited = 0;
      temp.splitedsource = i;
      temp.index = id;
      Blocks.push_back(temp);
      Blocks[i].spiltBlock.push_back(id);
      ++id;
    }
    // edit the splited module in original block, and add x*y-1 splited block into
    // push the
    logger->debug("split Node MS: debug 3");
    if (num_of_add_blocks > 0 and Blocks[i].commonCentroid == 0) {
      addNet_for_one_split_Blocks(i, split_numI);
    }

    logger->debug("split Node MS: debug 4");
  }
}

void Placement::addNet_for_one_split_Blocks(int blockID, Ppoint_I num) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.addNet_for_one_split_Blocks");
  // step 1: put all block id into a x by y 2d array
  logger->debug("add net for one splited blocks: debug 0");
  vector<vector<int>> ID_array;
  ID_array.clear();
  for (int i = 0; i < num.x; ++i) {
    int id = 0;
    vector<int> row;
    row.clear();
    for (int j = 0; j < num.y; ++j) {
      row.push_back(Blocks[blockID].spiltBlock[id]);
      ++id;
      if (id == Blocks[blockID].spiltBlock.size()) {
        break;
      }
    }
    ID_array.push_back(row);
  }
  logger->debug("add net for one splited blocks: debug 1");
  // put the source block into the center position
  Ppoint_I centerPoint;
  centerPoint.x = (num.x - 1) / 2;
  centerPoint.y = (num.y - 1) / 2;
  logger->debug("add net for one splited blocks: debug 2");
  ID_array[num.x - 1].push_back(ID_array[centerPoint.x][centerPoint.y]);
  ID_array[centerPoint.x][centerPoint.y] = blockID;

  logger->debug("add net for one splited blocks: debug 3");
  // add net for each block to connect the adjacent block
  int netID = Nets.size();
  for (int i = 0; i < num.x; ++i) {
    for (int j = 0; j < num.y; ++j) {
      logger->debug("add net for one splited blocks: debug 4");
      net temp1, temp2;
      if (i < num.x - 1) {
        logger->debug("add net for one splited blocks: debug 5");
        temp1.index = netID;
        logger->debug("add net for one splited blocks: debug 6");
        temp1.connected_block.push_back(ID_array[i][j]);
        logger->debug("add net for one splited blocks: debug 7");
        temp1.connected_block.push_back(ID_array[i + 1][j]);
        logger->debug("add net for one splited blocks: debug 8");
        Blocks[ID_array[i][j]].connected_net.push_back(netID);
        logger->debug("add net for one splited blocks: debug 9");
        logger->debug("{0}", ID_array[i + 1][j]);
        Blocks[ID_array[i + 1][j]].connected_net.push_back(netID);
        logger->debug("add net for one splited blocks: debug 10");
        ++netID;
        temp1.weight = dummy_net_weight;
        Nets.push_back(temp1);
      }
      if (j < num.y - 1) {
        logger->debug("add net for one splited blocks: debug 11");
        temp2.index = netID;
        temp2.connected_block.push_back(ID_array[i][j]);
        temp2.connected_block.push_back(ID_array[i][j + 1]);
        temp2.weight = dummy_net_weight;
        Blocks[ID_array[i][j]].connected_net.push_back(netID);
        Blocks[ID_array[i][j + 1]].connected_net.push_back(netID);
        Nets.push_back(temp2);
        ++netID;
      }
    }
  }
  logger->debug("add net for one splited blocks: debug 4");
}

void Placement::update_netlist_after_split_MS() {
  // step 1: for all original nets, split the
}
void Placement::Unify_blocks(float area, float scale_factor) {
  float height = sqrt(scale_factor * area);
  this->est_Size.x = height;
  this->est_Size.y = height;

  for (int i = 0; i < Blocks.size(); i++) {
    Blocks[i].Cpoint.x /= height;
    Blocks[i].Cpoint.y /= height;
    Blocks[i].Dpoint.x /= height;
    Blocks[i].Dpoint.y /= height;
  }
}

void Placement::find_uni_cell() {
  // Ppoint_F uni_cell_Dpoint;
  float min_x = Blocks[0].Dpoint.x, min_y = Blocks[0].Dpoint.y;
  float max_x = Blocks[0].Dpoint.x, max_y = Blocks[0].Dpoint.y;
  for (int i = 1; i < originalBlockCNT; ++i) {
    min_x = min(min_x, Blocks[i].Dpoint.x);
    min_y = min(min_y, Blocks[i].Dpoint.y);
    max_x = max(max_x, Blocks[i].Dpoint.x);
    max_y = max(max_y, Blocks[i].Dpoint.y);
  }
  uni_cell_Dpoint.x = (max_x / min_x <= 2) ? min_x : (max_x / 2);
  uni_cell_Dpoint.y = (max_y / min_y <= 2) ? min_y : (max_y / 2);
  /**
  uni_cell_Dpoint.x = Blocks[0].Dpoint.x;
  uni_cell_Dpoint.y = Blocks[0].Dpoint.y;
  int id = 0;
  for (int i = 1; i < originalBlockCNT; ++i)
  {
    if(Blocks[i].Dpoint.x < uni_cell_Dpoint.x)
    {
      uni_cell_Dpoint.x = Blocks[i].Dpoint.x;
    }
    if(Blocks[i].Dpoint.y < uni_cell_Dpoint.y)
    {
      uni_cell_Dpoint.y = Blocks[i].Dpoint.y;
    }
  }
  **/
  // uni_cell_Dpoint = Blocks[id].Dpoint;
  // return uni_cell_Dpoint;
}

void Placement::merge_two_vectors(vector<pair<int, int>> &v1, vector<pair<int, int>> &v2) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.merge_two_vectors");
  logger->debug("merge 2 vectors: debug 0a");
  vector<pair<int, int>> A, B;
  logger->debug("merge 2 vectors: debug 0b");
  if (v1.size() > v2.size()) {
    // A.swap(v1);
    // B.swap(v2);
  } else {
    v1.swap(v2);
  }
  logger->debug("merge 2 vectors: debug 1");
  // calculate the period
  int period, sizeA, sizeB, pos;
  sizeA = v1.size();
  sizeB = v2.size();
  pos = 0;
  if (sizeB != 0) {
    period = sizeA / sizeB + 1;
    pos = 1;
  }

  logger->debug("merge 2 vectors: debug 2");
  for (int i = 0; i < v2.size(); ++i) {
    logger->debug("merge 2 vectors: debug 3");
    v1.insert(v1.begin() + pos, v2[i]);
    pos += period;
    logger->debug("merge 2 vectors: debug 4");
  }
  // save the result into v1
  // v1.swap(A);
  // v2.swap(B);
  logger->debug("merge 2 vectors: debug 5");
}
void Placement::match_vector_into_pairs(vector<int> &q, vector<pair<int, int>> &pairs) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.match_vector_into_pairs");
  pairs.clear();
  int i = 0;
  if (q.size() % 2 == 1) {
    pair<int, int> temp;
    temp.first = q[0];
    temp.second = -2;  //-2 means dummy ;-1 means empty;>0 means occupy
    pairs.push_back(temp);
    ++i;
  }
  for (; i + 1 < q.size(); i = i + 2) {
    pair<int, int> temp;
    temp.first = q[i];
    temp.second = q[i + 1];  //-2 means dummy ;-1 means empty;>0 means occupy
    pairs.push_back(temp);
  }
}
void Placement::restore_MS() {
  for (int i = 0; i < originalBlockCNT; ++i) {
    // restore the shape

    // restore the center
    if (Blocks[i].commonCentroid == 0 and Blocks[i].splited == 1) {
      Ppoint_F split_shape = Blocks[i].split_shape;
      Blocks[i].Dpoint.x *= split_shape.x;
      Blocks[i].Dpoint.y *= split_shape.y;
      for (int j = 0; j < Blocks[i].spiltBlock.size(); ++j) {
        Blocks[i].Cpoint.x += Blocks[Blocks[i].spiltBlock[j]].Cpoint.x;
        Blocks[i].Cpoint.y += Blocks[Blocks[i].spiltBlock[j]].Cpoint.y;

        Blocks[Blocks[i].spiltBlock[j]].Cpoint.x = 0;
        Blocks[Blocks[i].spiltBlock[j]].Cpoint.y = 0;
      }
      Blocks[i].Cpoint.x /= Blocks[i].spiltBlock.size() + 1;
      Blocks[i].Cpoint.y /= Blocks[i].spiltBlock.size() + 1;
    }
  }
}

void Placement::restore_MS(PnRDB::hierNode &current_node) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.restore_MS");
  logger->debug("restore ms debug:0");
  current_node.isFirstILP = 0;
  PnRDB::hierNode copy_node(current_node);
  current_node.Blocks.erase(current_node.Blocks.end() - (Blocks.size() - originalBlockCNT), current_node.Blocks.end());
  logger->debug("restore ms debug:1");
  current_node.Nets.erase(current_node.Nets.end() - (Nets.size() - originalNetCNT), current_node.Nets.end());

  for (int i = 0; i < current_node.SPBlocks.size(); ++i) {
    int j = 0;
    while (j < current_node.SPBlocks[i].selfsym.size() && current_node.SPBlocks[i].selfsym[j].first < originalBlockCNT) {
      ++j;
    }

    if (j < current_node.SPBlocks[i].selfsym.size()) {
      current_node.SPBlocks[i].selfsym.erase(current_node.SPBlocks[i].selfsym.begin() + j, current_node.SPBlocks[i].selfsym.end());
    }

    j = 0;
    while (j < current_node.SPBlocks[i].sympair.size() && current_node.SPBlocks[i].sympair[j].first < originalBlockCNT &&
           current_node.SPBlocks[i].sympair[j].second < originalBlockCNT) {
      ++j;
    }

    if (j < current_node.SPBlocks[i].sympair.size()) {
      current_node.SPBlocks[i].sympair.erase(current_node.SPBlocks[i].sympair.begin() + j, current_node.SPBlocks[i].sympair.end());
    }
  }
  // std::cout<<"restore ms debug:3"<<std::endl;
  // restore the size of block
  int idx = 0;
  for (int i = 0; i < current_node.Nets.size(); ++i) {
    current_node.Nets[i].weight = 1.0;
  }
  logger->debug("restore ms debug:4");
  for (int i = 0; i < current_node.Blocks.size(); ++i) {
    for (int j = 0; j < 1; ++j) {
      if (Blocks[idx].splited) {
        current_node.Blocks[i].instance[j].height *= (int)ceil(Blocks[idx].split_shape.y);
        current_node.Blocks[i].instance[j].width *= (int)ceil(Blocks[idx].split_shape.x);
        current_node.Blocks[i].instance[j].originBox.UR.y *= (int)ceil(Blocks[idx].split_shape.y);
        current_node.Blocks[i].instance[j].originBox.UR.x *= (int)ceil(Blocks[idx].split_shape.x);
        current_node.Blocks[i].instance[j].originCenter.y *= (int)ceil(Blocks[idx].split_shape.y);
        current_node.Blocks[i].instance[j].originCenter.x *= (int)ceil(Blocks[idx].split_shape.x);
      }
      ++idx;
    }
  }

  logger->debug("restore ms debug:5");
  // merge CC block
  // make origin block in CC size to zero
  int id_new_block = originalBlockCNT;
  // Ppoint_F uni_cell_Dpoint;
  // uni_cell_Dpoint.x = Blocks[0].Dpoint.x;
  // uni_cell_Dpoint.y = Blocks[0].Dpoint.y;
  Ppoint_I uni_cell_shape;
  uni_cell_shape.x = (int)(est_Size.x * uni_cell_Dpoint.x);
  uni_cell_shape.y = (int)(est_Size.y * uni_cell_Dpoint.y);
  for (auto &s : current_node.SPBlocks) {
    for (auto &p : s.sympair) {
      if (original_to_new_block_map.find(p.first) != original_to_new_block_map.end()) p.first = original_to_new_block_map[p.first];
      if (original_to_new_block_map.find(p.second) != original_to_new_block_map.end()) p.second = original_to_new_block_map[p.second];
    }
    for (auto &p : s.selfsym) {
      if (original_to_new_block_map.find(p.first) != original_to_new_block_map.end()) p.first = original_to_new_block_map[p.first];
    }
  }
  for (auto &a : current_node.Align_blocks) {
    for (auto &b : a.blocks) {
      if (original_to_new_block_map.find(b) != original_to_new_block_map.end()) b = original_to_new_block_map[b];
    }
  }
  for (auto &order : current_node.Ordering_Constraints) {
    for (auto &b : order.first) {
      if (original_to_new_block_map.find(b) != original_to_new_block_map.end()) b = original_to_new_block_map[b];
    }
  }
  PlotPlacement(601);
}
// donghao end

void Placement::print_blocks_nets() {
  auto logger = spdlog::default_logger()->clone("placer.Placement.print_blocks_nets");
  logger->debug("print information about blocks");
  for (int i = 0; i < Blocks.size(); ++i) {
    logger->debug("block id {0}", Blocks[i].index);
    logger->debug("block position: ({0}, {1}), d:({2}, {3})", Blocks[i].Cpoint.x, Blocks[i].Cpoint.y, Blocks[i].Dpoint.x, Blocks[i].Dpoint.y);

    logger->debug("connect net:");
    for (int j = 0; j < Blocks[i].connected_net.size(); ++j) {
      logger->debug("{0}", Blocks[i].connected_net[j]);
    }
  }

  logger->debug("print information about nets");
  for (int i = 0; i < Nets.size(); ++i) {
    logger->debug("net id {0}", Nets[i].index);
    // std::cout << "block position: (" << Blocks[i].Cpoint.x << ", " << Blocks[i].Cpoint.y << ")"
    //           << "d:(" << Blocks[i].Dpoint.x << ", " << Blocks[i].Dpoint.y << ")" << std::endl;

    logger->debug("connect block:");
    for (int j = 0; j < Nets[i].connected_block.size(); ++j) {
      logger->debug("{0}", Nets[i].connected_block[j]);
    }
  }
}

void Placement::Cal_sym_Force() {
  auto logger = spdlog::default_logger()->clone("placer.Placement.Update_Bin_Density");


  for (int i = 0; i < symmetric_force_matrix.size(); ++i) {
    Blocks[i].Symmetricforce.x = 0;
    Blocks[i].Symmetricforce.y = 0;
    for (int j = 0; j < symmetric_force_matrix[i].size(); ++j) {

      Blocks[i].Symmetricforce.x += symmetric_force_matrix[i][j].x * Blocks[j].Cpoint.x;
      Blocks[i].Symmetricforce.y += symmetric_force_matrix[i][j].y * Blocks[j].Cpoint.y;

    }
    if (isnan(Blocks[i].Symmetricforce.x)) {

      Blocks[i].Symmetricforce.x = 0;
    }
    if (isnan(Blocks[i].Symmetricforce.y)) {
      Blocks[i].Symmetricforce.y = 0;
    }
  }
}

void Placement::read_alignment(PnRDB::hierNode &current_node) {
  //###############################################
  // old version using struct Alignment//
  //###############################################
  // float height = this->est_Size.y;
  // float weight = this->est_Size.x;
  // Alignment_blocks.clear();

  // for(int i = 0;i < current_node.Alignment_blocks.size();++i)
  // {

  // Alignment temp;
  // //find the larger blocks
  // float s1,s2;
  // int id1,id2;
  // id1 = current_node.Alignment_blocks[i].blockid1;
  // id2 = current_node.Alignment_blocks[i].blockid2;

  // s1 = Blocks[id1].Dpoint.x * Blocks[id1].Dpoint.y;
  // s2 = Blocks[id2].Dpoint.x * Blocks[id2].Dpoint.y;
  // if(s2 > s1)
  // {
  //   temp.blockid1 = id2;
  //   temp.blockid2 = id1;
  // }
  // else
  // {
  //   temp.blockid1 = id1;
  //   temp.blockid2 = id2;
  // }

  // temp.horizon = current_node.Alignment_blocks[i].horizon;
  // if(temp.horizon == 1)//LL1.x = LL2.x ->c1.x - d1.x/2 = c2.x - d2.x/2
  // //distance = c2.x - c1.x = d2.x/2 - d1.x/2
  // {
  //   temp.distance = 0.5*(Blocks[temp.blockid2].Dpoint.x - Blocks[temp.blockid1].Dpoint.x);
  // }
  // else
  // {
  //   temp.distance = 0.5*(Blocks[temp.blockid2].Dpoint.y - Blocks[temp.blockid1].Dpoint.y);
  // }

  // Alignment_blocks.push_back(temp);

  //###############################################
  // new version using struct AlignBLock//
  //###############################################

  // }
  AlignBlocks.clear();
  for (int i = 0; i < current_node.Align_blocks.size(); ++i) {
    AlignBlock temp;
    PnRDB::AlignBlock *curAlign = &current_node.Align_blocks[i];
    temp.blocks.clear();
    temp.blocks = curAlign->blocks;
    temp.horizon = curAlign->horizon;
    // find the largest blocks and put it into begin()
    AlignBlocks.push_back(temp);
  }
}

void Placement::force_alignment(vector<float> &vc_x, vector<float> &vl_x, vector<float> &vc_y, vector<float> &vl_y) {
  //###############################################
  // old version using struct Alignment//
  //###############################################

  // for(int i = 0;i < Alignment_blocks.size();++i)
  // {
  //   int id1 = Alignment_blocks[i].blockid1;
  //   int id2 = Alignment_blocks[i].blockid2;
  //   float distance = Alignment_blocks[i].distance;
  //   if(Alignment_blocks[i].horizon == 1)
  //   {
  //     Blocks[id2].Cpoint.x = Blocks[id1].Cpoint.x + distance;
  //   }
  //   else
  //   {
  //     Blocks[id2].Cpoint.y = Blocks[id1].Cpoint.y + distance;
  //   }
  // }
  auto logger = spdlog::default_logger()->clone("placer.Placement.force_alignment");
  logger->debug("force align begin");
  for (int i = 0; i < AlignBlocks.size(); ++i) {
    int headIdx = AlignBlocks[i].blocks[0];
    Ppoint_F head_pos = Blocks[headIdx].Cpoint;
    Ppoint_F head_dem = Blocks[headIdx].Dpoint;
    float center = 0;
    if (AlignBlocks[i].horizon) {
      for (int j = 0; j < AlignBlocks[i].blocks.size(); ++j) {
        int cur_idx = AlignBlocks[i].blocks[j];
        Ppoint_F cur_dem = Blocks[cur_idx].Dpoint;
        float distance = 1 / 2 * (cur_dem.y);
        center += Blocks[cur_idx].Cpoint.y - distance;
      }
      center /= AlignBlocks[i].blocks.size();
      for (int j = 0; j < AlignBlocks[i].blocks.size(); ++j) {
        int cur_idx = AlignBlocks[i].blocks[j];
        Ppoint_F cur_dem = Blocks[cur_idx].Dpoint;
        float distance = 1 / 2 * (cur_dem.y);
        Blocks[cur_idx].Cpoint.y = center + distance;
        // update vl and vc
        if (vl_y.size() > cur_idx) {
          // vl_y[cur_idx] = Blocks[cur_idx].Cpoint.y;
          vc_y[cur_idx] = Blocks[cur_idx].Cpoint.y;
        }
      }
    } else {
      for (int j = 0; j < AlignBlocks[i].blocks.size(); ++j) {
        int cur_idx = AlignBlocks[i].blocks[j];
        Ppoint_F cur_dem = Blocks[cur_idx].Dpoint;
        float distance = 1 / 2 * (cur_dem.x);
        center += Blocks[cur_idx].Cpoint.x - distance;
      }
      center /= AlignBlocks[i].blocks.size();
      for (int j = 0; j < AlignBlocks[i].blocks.size(); ++j) {
        int cur_idx = AlignBlocks[i].blocks[j];
        Ppoint_F cur_dem = Blocks[cur_idx].Dpoint;
        float distance = 1 / 2 * (cur_dem.x);
        Blocks[cur_idx].Cpoint.x = center + distance;
        // update vl and vc
        if (vl_x.size() > cur_idx) {
          // vl_x[cur_idx] = Blocks[cur_idx].Cpoint.x;
          vc_x[cur_idx] = Blocks[cur_idx].Cpoint.x;
        }
      }
    }
  }
  for (int i = 0; i < SPBlocks.size(); ++i) {
    int headIdx = SPBlocks[i].selfsym[0];
    Ppoint_F head_pos = Blocks[headIdx].Cpoint;
    Ppoint_F head_dem = Blocks[headIdx].Dpoint;
    float center = 0;
    if (SPBlocks[i].horizon) {
      for (auto i_selfsym : SPBlocks[i].selfsym) {
        center += Blocks[i_selfsym].Cpoint.y;
      }
      for (auto i_sympair : SPBlocks[i].sympair) {
        center += Blocks[i_sympair.first].Cpoint.y;
        center += Blocks[i_sympair.second].Cpoint.y;
      }
      center /= (SPBlocks[i].selfsym.size() + SPBlocks[i].sympair.size() * 2);
      for (auto i_selfsym : SPBlocks[i].selfsym) {
        Blocks[i_selfsym].Cpoint.y = center;
        // update vl and vc
        if (vl_y.size() > i_selfsym) {
          vc_y[i_selfsym] = Blocks[i_selfsym].Cpoint.y;
        }
      }
      for (auto i_sympair : SPBlocks[i].sympair) {
        int diff = center - (Blocks[i_sympair.first].Cpoint.y + Blocks[i_sympair.second].Cpoint.y) / 2;
        Blocks[i_sympair.first].Cpoint.y += diff;
        Blocks[i_sympair.second].Cpoint.y += diff;
        if (vl_y.size() > i_sympair.first) {
          vc_y[i_sympair.first] = Blocks[i_sympair.first].Cpoint.y;
        }
        if (vl_y.size() > i_sympair.second) {
          vc_y[i_sympair.second] = Blocks[i_sympair.second].Cpoint.y;
        }
      }
    } else {
      for (auto i_selfsym : SPBlocks[i].selfsym) {
        center += Blocks[i_selfsym].Cpoint.x;
      }
      for (auto i_sympair : SPBlocks[i].sympair) {
        center += Blocks[i_sympair.first].Cpoint.x;
        center += Blocks[i_sympair.second].Cpoint.x;
      }
      center /= (SPBlocks[i].selfsym.size() + SPBlocks[i].sympair.size() * 2);
      for (auto i_selfsym : SPBlocks[i].selfsym) {
        Blocks[i_selfsym].Cpoint.x = center;
        // update vl and vc
        if (vl_x.size() > i_selfsym) {
          // vl_x[cur_idx] = Blocks[cur_idx].Cpoint.x;
          vc_x[i_selfsym] = Blocks[i_selfsym].Cpoint.x;
        }
      }
      for (auto i_sympair : SPBlocks[i].sympair) {
        int diff = center - (Blocks[i_sympair.first].Cpoint.x + Blocks[i_sympair.second].Cpoint.x) / 2;
        Blocks[i_sympair.first].Cpoint.x += diff;
        Blocks[i_sympair.second].Cpoint.x += diff;
        if (vl_x.size() > i_sympair.first) {
          vc_x[i_sympair.first] = Blocks[i_sympair.first].Cpoint.x;
        }
        if (vl_x.size() > i_sympair.second) {
          vc_x[i_sympair.second] = Blocks[i_sympair.second].Cpoint.x;
        }
      }
    }
  }
  logger->debug("force align finish");
}

void Placement::read_order(PnRDB::hierNode &current_node) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.read_order");
  Ordering_Constraints = current_node.Ordering_Constraints;
  logger->debug("ordering constraints size: {0}", Ordering_Constraints.size());
}

void Placement::force_order(vector<float> &vc_x, vector<float> &vl_x, vector<float> &vc_y, vector<float> &vl_y) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.force_order");
  // step 1: put the Cpoint into verctor
  for (int i = 0; i < Ordering_Constraints.size(); ++i) {
    vector<Ppoint_F> Centers = vector<Ppoint_F>();
    for (int j = 0; j < Ordering_Constraints[i].first.size(); ++j) {
      logger->debug("ordering id before sort: {0}", Ordering_Constraints[i].first[j]);
      Centers.push_back(Blocks[Ordering_Constraints[i].first[j]].Cpoint);
      logger->debug("pos: {0}, {1}", Centers[j].x, Centers[j].y);
    }
    // step 2: sort the Cpoint vector
    if (Ordering_Constraints[i].second == PnRDB::H) {
      sort(Centers.begin(), Centers.end(), comp_x);
    } else {
      sort(Centers.begin(), Centers.end(), comp_y);
    }
    // step 3: assign the sorted cpoint

    for (int j = 0; j < Ordering_Constraints[i].first.size(); ++j) {
      int id = Ordering_Constraints[i].first[j];
      logger->debug("ordering id after sort: {0}", id);
      if (Ordering_Constraints[i].second == PnRDB::H) {
        Blocks[id].Cpoint.x = Centers[j].x;
        if (vl_x.size() > id) {
          // vl_x[id] = Blocks[id].Cpoint.x;
          vc_x[id] = Blocks[id].Cpoint.x;
        }
      } else {
        Blocks[id].Cpoint.y = Centers[j].y;
        if (vl_y.size() > id) {
          // vl_y[id] = Blocks[id].Cpoint.y;
          vc_y[id] = Blocks[id].Cpoint.y;
        }
      }

      logger->debug("pos: {0}, {1}", Centers[j].x, Centers[j].y);
    }
  }
}

bool Placement::check_order() {
  auto logger = spdlog::default_logger()->clone("placer.Placement.check_order");
  // step 1: put the Cpoint into verctor
  for (int i = 0; i < Ordering_Constraints.size(); ++i) {
    if (Ordering_Constraints[i].second == PnRDB::H) {
      for (int j = 0; j < Ordering_Constraints[i].first.size() - 1; ++j) {
        if (Blocks[Ordering_Constraints[i].first[j]].Cpoint.x > Blocks[Ordering_Constraints[i].first[j + 1]].Cpoint.x) return false;
      }
    } else {
      for (int j = 0; j < Ordering_Constraints[i].first.size() - 1; ++j) {
        if (Blocks[Ordering_Constraints[i].first[j]].Cpoint.y < Blocks[Ordering_Constraints[i].first[j + 1]].Cpoint.y) return false;
      }
    }
  }
  return true;
}

bool Placement::comp_x(Ppoint_F c1, Ppoint_F c2) { return c1.x < c2.x; }

bool Placement::comp_y(Ppoint_F c1, Ppoint_F c2) { return c1.y > c2.y; }

void Placement::writeback(PnRDB::hierNode &current_node) {
  int idx = 0;
  for (vector<PnRDB::blockComplex>::iterator it = current_node.Blocks.begin(); it != current_node.Blocks.end(); ++it) {
    for (int i = 0; i < 1; ++i) {
      it->instance[i].placedCenter.x = (int)(est_Size.x * Blocks[idx].Cpoint.x);
      it->instance[i].placedCenter.y = (int)(est_Size.y * Blocks[idx].Cpoint.y);

      it->instance[i].placedBox.LL.x = (int)(est_Size.x * Blocks[idx].Cpoint.x) - it->instance[i].width / 2;
      it->instance[i].placedBox.LL.y = (int)(est_Size.y * Blocks[idx].Cpoint.y) - it->instance[i].height / 2;

      it->instance[i].placedBox.UR.x = (int)(est_Size.x * Blocks[idx].Cpoint.x) + it->instance[i].width / 2;
      it->instance[i].placedBox.UR.y = (int)(est_Size.y * Blocks[idx].Cpoint.y) + it->instance[i].height / 2;
      it->instance[i].orient = PnRDB::N;
      ++idx;
    }
  }
}

bool Placement::symCheck(float tol) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.symCheck");
  float tot_bias = 0;
  for (int i = 0; i < SPBlocks.size(); ++i) {
    if (SPBlocks[i].horizon) {
      // step 1: find the axis
      float axis, axis_double;
      int baseid0, baseid1;
      baseid0 = SPBlocks[i].axis.first;
      baseid1 = SPBlocks[i].axis.second;
      axis = 0.5 * (Blocks[baseid0].Cpoint.y + Blocks[baseid1].Cpoint.y);
      axis_double = axis * 2;
      // step 2: evalue all modules in sympair
      for (int j = 0; j < SPBlocks[i].sympair.size(); ++j) {
        int id0 = SPBlocks[i].sympair[j].first;
        int id1 = SPBlocks[i].sympair[j].second;
        tot_bias += fabs(Blocks[id0].Cpoint.y + Blocks[id1].Cpoint.y - axis_double);
      }
      // step 3: evalue all modules in selfs0.211138m0.211138
      for (int j = 0; j < SPBlocks[i].selfsym.size(); ++j) {
        int id0 = SPBlocks[i].selfsym[j];
        tot_bias += fabs(Blocks[id0].Cpoint.y - axis);
      }
    } else {
      // step 1: find the axis
      float axis, axis_double;
      int baseid0, baseid1;
      baseid0 = SPBlocks[i].axis.first;
      baseid1 = SPBlocks[i].axis.second;
      axis = 0.5 * (Blocks[baseid0].Cpoint.x + Blocks[baseid1].Cpoint.x);
      axis_double = axis * 2;
      // step 2: evalue all modules in sympair
      for (int j = 0; j < SPBlocks[i].sympair.size(); ++j) {
        int id0 = SPBlocks[i].sympair[j].first;
        int id1 = SPBlocks[i].sympair[j].second;
        tot_bias += fabs(Blocks[id0].Cpoint.x + Blocks[id1].Cpoint.x - axis_double);
      }
      // step 3: evalue all modules in selfsym
      for (int j = 0; j < SPBlocks[i].selfsym.size(); ++j) {
        int id0 = SPBlocks[i].selfsym[j];
        tot_bias += fabs(Blocks[id0].Cpoint.x - axis);
      }
    }
  }
  logger->debug("tot_symmetric bias = {0}", tot_bias);
  return tot_bias > tol;
}

void Placement::update_hiernode(PnRDB::hierNode &current_node) {
  // update blocks
  Ppoint_I uni_cell_shape;
  uni_cell_shape.x = (int)(est_Size.x * uni_cell_Dpoint.x);
  uni_cell_shape.y = (int)(est_Size.y * uni_cell_Dpoint.y);
  for (int i = originalBlockCNT; i < Blocks.size(); ++i) {
    // add blockcomplex
    PnRDB::block tempBlock;
    tempBlock.name = Blocks[i].blockname;
    tempBlock.orient = PnRDB::N;
    tempBlock.height = uni_cell_shape.y;
    tempBlock.width = uni_cell_shape.x;
    tempBlock.originBox.LL.x = 0, tempBlock.originBox.LL.y = 0;
    tempBlock.originBox.UR.x = tempBlock.width, tempBlock.originBox.LL.y = tempBlock.height;

    PnRDB::blockComplex tempBlockComplex;
    tempBlockComplex.instNum = 1;
    tempBlockComplex.instance.push_back(tempBlock);
    current_node.Blocks.push_back(tempBlockComplex);
  }
  // update netlist
  for (int i = originalNetCNT; i < Nets.size(); ++i) {
    PnRDB::net tempNet;
    tempNet.weight = Nets[i].weight;
    for (int j = 0; j < Nets[i].connected_block.size(); ++j) {
      PnRDB::connectNode tempNode;
      tempNode.iter2 = Nets[i].connected_block[j];
      tempNode.type = PnRDB::Block;
      tempNode.iter = 0;
      tempNet.connected.push_back(tempNode);
    }
    current_node.Nets.push_back(tempNet);
  }
  // update ordering and alignment
  // set a flag?

  // update the size of block
  int idx = 0;
  for (int i = 0; i < current_node.Blocks.size(); ++i) {
    for (int j = 0; j < 1; ++j) {
      if (Blocks[idx].splited) {
        current_node.Blocks[i].instance[j].height /= int(ceil(Blocks[i].split_shape.y));
        current_node.Blocks[i].instance[j].width /= int(ceil(Blocks[i].split_shape.x));
        current_node.Blocks[i].instance[j].originBox.UR.y /= int(ceil(Blocks[i].split_shape.y));
        current_node.Blocks[i].instance[j].originBox.UR.x /= int(ceil(Blocks[i].split_shape.x));
        current_node.Blocks[i].instance[j].originCenter.y /= int(ceil(Blocks[i].split_shape.y));
        current_node.Blocks[i].instance[j].originCenter.x /= int(ceil(Blocks[i].split_shape.x));
      }
      ++idx;
    }
  }
  current_node.isFirstILP = true;
}

void Placement::split_net() {
  for (int i = 0; i < originalNetCNT; ++i) {
    vector<int> chosen_block;
    float weight = 1;
    for (int j = 0; j < Nets[i].connected_block.size(); ++j) {
      int id = Nets[i].connected_block[j];
      chosen_block.push_back(0);
      weight /= (float)(Blocks[id].spiltBlock.size() + 1);
    }
    int id0 = Nets[i].connected_block[0];
    Nets[i].weight = 0;
    while (chosen_block[0] <= Blocks[id0].spiltBlock.size()) {
      net tempNet;
      tempNet.index = Nets.size();
      for (int j = 0; j < Nets[i].connected_block.size(); ++j) {
        int id = Nets[i].connected_block[j];
        int chosenID;
        if (chosen_block[j] < Blocks[id].spiltBlock.size()) {
          chosenID = Blocks[id].spiltBlock[chosen_block[j]];
        } else {
          chosenID = id;
        }
        tempNet.connected_block.push_back(chosenID);
        Blocks[chosenID].connected_net.push_back(tempNet.index);
      }
      tempNet.weight = weight;
      Nets.push_back(tempNet);

      // update chosen block vector
      chosen_block[chosen_block.size() - 1] += 1;
      for (int j = Nets[i].connected_block.size() - 1; j >= 0; --j) {
        int id = Nets[i].connected_block[j];
        if (chosen_block[j] > Blocks[id].spiltBlock.size() and j > 0) {
          chosen_block[j] = 0;
          chosen_block[j - 1] += 1;
        }
      }
    }
  }
}

// void Placement::compact_cc()
// {
//   for(int i = 0;i < commonCentroids.size();++i)
//   {
//     Ppoint_F center;
//     for(int)
//   }
// }

void Placement::modify_symm_after_split(PnRDB::hierNode &current_node) {
  for (int i = 0; i < current_node.SPBlocks.size(); ++i) {
    // check all pair symmtirc blocks
    int pair_symm_num = current_node.SPBlocks[i].sympair.size();
    for (int j = 0; j < pair_symm_num; ++j) {
      int originid0 = current_node.SPBlocks[i].sympair[j].first;
      int originid1 = current_node.SPBlocks[i].sympair[j].second;

      Ppoint_F shape = Blocks[originid0].split_shape;
      int xlen = (int)ceil(shape.x);
      for (int k = 0; k < Blocks[originid0].spiltBlock.size(); ++k) {
        pair<int, int> temp;
        temp.first = Blocks[originid0].spiltBlock[k];
        temp.second = Blocks[originid1].spiltBlock[k];
        current_node.SPBlocks[i].sympair.push_back(temp);
      }
    }
    // check all self symmtric blocks
    int self_symm_num = current_node.SPBlocks[i].selfsym.size();
    PnRDB::Smark dir = current_node.SPBlocks[i].axis_dir;
    for (int j = 0; j < self_symm_num; ++j) {
      int id = current_node.SPBlocks[i].selfsym[j].first;
      for (int k = 0; k < Blocks[id].spiltBlock.size(); ++k) {
        pair<int, PnRDB::Smark> temp;
        temp.first = Blocks[id].spiltBlock[k];
        temp.second = dir;
        current_node.SPBlocks[i].selfsym.push_back(temp);
      }
    }
  }

  // modify the sym_matrix
  for (int i = 0; i < symmetric_force_matrix.size(); ++i) {
    while (symmetric_force_matrix[i].size() < Blocks.size()) {
      Ppoint_F temp;
      temp.x = 0;
      temp.y = 0;
      symmetric_force_matrix[i].push_back(temp);
    }
  }
  while (symmetric_force_matrix.size() < Blocks.size()) {
    vector<Ppoint_F> temp;
    for (int i = 0; i < Blocks.size(); ++i) {
      Ppoint_F temp_point;
      temp_point.x = 0;
      temp_point.y = 0;
      temp.push_back(temp_point);
    }
    symmetric_force_matrix.push_back(temp);
  }
}

float Placement::cal_weight_init_increase(float &rate, float &init_val, float &target_val, float target_converge_iter) {
  float qn = pow(rate, target_converge_iter);
  float a1 = target_val * (1 - rate) / (1 - qn);
  return a1;
}

void Placement::cal_dummy_net_weight(float &weight, float &rate, float &increase) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.cal_dummy_net_weight");
  weight += increase;
  increase *= rate;
  logger->debug("dummy_net weight:= {0}", weight);
}

void Placement::set_dummy_net_weight(float init_weight, float rate, float targe) { dummy_net_weight = init_weight; }

void Placement::break_merged_cc(PnRDB::hierNode &current_node) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.break_merged_cc");
  update_pos(current_node);
  logger->debug("restore ms debug:0");
  string mark_of_cc = "CC_merge_cell";
  for (int i = 0; i < current_node.Blocks.size(); ++i) {
    logger->debug("restore ms debug:1");
    for (int j = 0; j < 1; ++j) {
      logger->debug("restore ms debug:2");
      if (current_node.Blocks[i].instance[j].name.find(mark_of_cc) != string::npos) {
        logger->debug("restore ms debug:3");
        // break the cc into its shape
        int pos = current_node.Blocks[i].instance[j].name.find(mark_of_cc);  // bug 1

        char ccID = current_node.Blocks[i].instance[j].name[pos + 15];  // bug 1
        int ccID_int = cc_name_to_id_map[current_node.Blocks[i].instance[j].name];
        // int ccID_int = ccID - 48 - 1;  // bug 2
        logger->debug("restore ms debug:4");
        // determine the period and center
        Ppoint_F center, period, LL;
        center.x = (float)current_node.Blocks[i].instance[j].placedCenter.x / est_Size.x;
        center.y = (float)current_node.Blocks[i].instance[j].placedCenter.y / est_Size.y;

        // LL.x = center.x - 1/2*(float)current_node.Blocks[i].instance[j].width/est_Size.x;
        // LL.y = center.y - 1/2*(float)current_node.Blocks[i].instance[j].height/est_Size.y;
        LL.x = (float)(current_node.Blocks[i].instance[j].placedCenter.x - current_node.Blocks[i].instance[j].width / 2) / est_Size.x;   // bug
        LL.y = (float)(current_node.Blocks[i].instance[j].placedCenter.y - current_node.Blocks[i].instance[j].height / 2) / est_Size.y;  // bug

        // LL.x = center.x - 1/2 *uni_cell.x * commonCentroids[ccID_int].shape.x;
        // LL.y = center.y - 1/2 *uni_cell.y * commonCentroids[ccID_int].shape.y;
        logger->debug("width of CC {0} = {1}", ccID_int, current_node.Blocks[i].instance[j].width);
        logger->debug("height of CC {0} = {1}", ccID_int, current_node.Blocks[i].instance[j].height);

        logger->debug("LL:= {0}, {1}", LL.x * est_Size.x, LL.y * est_Size.y);
        // std::cout<<"width *0.5:= center -LL "<<current_node.Blocks[i].instance[j].placedCenter.x - <<", "<<center.y-LL.y<<endl;

        if (commonCentroids[ccID_int].shape.x > 1) {
          logger->debug("restore ms debug:5");
          period.x = (float)current_node.Blocks[i].instance[j].width / est_Size.x / (commonCentroids[ccID_int].shape.x);  // bug
          // period.x = 0;
        } else {
          period.x = 0;
        }
        if (commonCentroids[ccID_int].shape.y > 1) {
          logger->debug("restore ms debug:6");
          period.y = (float)current_node.Blocks[i].instance[j].height / est_Size.y / (commonCentroids[ccID_int].shape.y);  // bug
          // period.y = 0;
        } else {
          period.y = 0;
        }
        // period = uni_cell;
        logger->debug("restore ms debug:7: {0}", ccID_int);
        // range the pos of each cell
        for (int ii = 0; ii < commonCentroids[ccID_int].shape.x; ++ii) {
          for (int jj = 0; jj < commonCentroids[ccID_int].shape.y; ++jj) {
            // if(commonCentroids[ccID_int].fillin_matrix[ii][jj]>=0)
            // {
            int id = commonCentroids[ccID_int].fillin_matrix[ii][jj];
            logger->debug("restore ms debug:7a: {0}", id);
            Blocks[id].Cpoint.x = LL.x + ii * period.x + 0.5 * period.x;  // bug 3
            Blocks[id].Cpoint.y = LL.y + jj * period.y + 0.5 * period.y;
            ;
            Blocks[id].Dpoint.x = period.x;
            Blocks[id].Dpoint.y = period.y;
            // }
          }
        }
      }
    }
  }
  for (auto b : new_to_original_block_map) {
    current_node.Blocks[b.first].instance[0].name = current_node.Blocks[b.second].instance[0].name;
  }
  for (auto b : original_to_new_block_map) {
    current_node.Blocks[b.first].instance[0].originBox = current_node.Blocks[b.second].instance[0].originBox;
    current_node.Blocks[b.first].instance[0].originCenter = current_node.Blocks[b.second].instance[0].originCenter;
    current_node.Blocks[b.first].instance[0].placedBox = current_node.Blocks[b.second].instance[0].placedBox;
    current_node.Blocks[b.first].instance[0].placedCenter = current_node.Blocks[b.second].instance[0].placedCenter;
    current_node.Blocks[b.first].instance[0].orient = current_node.Blocks[b.second].instance[0].orient;
    current_node.Blocks[b.first].instance[0].PowerNets = current_node.Blocks[b.second].instance[0].PowerNets;
    current_node.Blocks[b.first].instance[0].blockPins = current_node.Blocks[b.second].instance[0].blockPins;
    current_node.Blocks[b.first].instance[0].interMetals = current_node.Blocks[b.second].instance[0].interMetals;
    current_node.Blocks[b.first].instance[0].interVias = current_node.Blocks[b.second].instance[0].interVias;
    current_node.Blocks[b.first].instance[0].dummy_power_pin = current_node.Blocks[b.second].instance[0].dummy_power_pin;
    current_node.Blocks[b.first].instance[0].GuardRings = current_node.Blocks[b.second].instance[0].GuardRings;
    current_node.Blocks[b.first].instance[0].width = current_node.Blocks[b.second].instance[0].width;
    current_node.Blocks[b.first].instance[0].height = current_node.Blocks[b.second].instance[0].height;
  }
  for (auto &n : current_node.Nets) {
    for (auto &c : n.connected) {
      if (c.type == PnRDB::Block && c.iter2 >= originalBlockCNT) {
        c.iter2 = new_to_original_block_map[c.iter2];
      }
    }
  }
  current_node.Blocks.erase(current_node.Blocks.begin() + originalBlockCNT, current_node.Blocks.end());
  /**for (auto b = current_node.Blocks.begin(); b != current_node.Blocks.end();) {
    if(b->instance[0].isRead==false){
      b = current_node.Blocks.erase(b);
    }else{
      ++b;
    }
  }**/
  PlotPlacement(604);
}

void Placement::update_pos(PnRDB::hierNode &current_node) {
  auto logger = spdlog::default_logger()->clone("placer.Placement.update_pos");
  int idx = 0;

  for (int i = 0; i < current_node.Blocks.size(); ++i) {
    for (int j = 0; j < 1; ++j) {
      if (current_node.Blocks[i].instance[j].isRead) {
        Blocks[idx].Cpoint.x = (float)current_node.Blocks[i].instance[j].placedCenter.x / est_Size.x;
        Blocks[idx].Cpoint.y = (float)current_node.Blocks[i].instance[j].placedCenter.y / est_Size.y;
        logger->debug("update_pos: {0} Cpoint:= {1} {2}", Blocks[idx].blockname, current_node.Blocks[i].instance[j].placedCenter.x,
                      current_node.Blocks[i].instance[j].placedCenter.y);
      }

      // Blocks[idx].Cpoint.x = 0;
      // Blocks[idx].Cpoint.y = 0;
      idx++;
      if (idx == originalBlockCNT)  // bug
      {
        return;  // bug
      }
    }
  }
}