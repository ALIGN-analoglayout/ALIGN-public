#include "ILP_solver.h"
#include "spdlog/spdlog.h"
#include <iostream>
#include <algorithm>
#include <malloc.h>
#include <signal.h>
#include "ILPSolverIf.h"

void ILP_solver::lpsolve_logger(lprec* lp, void* userhandle, char* buf) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.lpsolve_logger");

  // Strip leading newline
  while ((unsigned char)*buf == '\n') buf++;
  // Log non-empty lines
  if (*buf != '\0') logger->debug("Placer lpsolve: {0}", buf);
}

double ILP_solver::CalculateCost(const design& mydesign) const {
  Pdatatype hyper;
  double cost = 0;
  cost += area;
  cost += HPWL * hyper.LAMBDA;
  double match_cost = 0;
  for (const auto& mbi : mydesign.Match_blocks) {
    match_cost +=
        abs(Blocks[mbi.blockid1].x + mydesign.Blocks[mbi.blockid1][0].width / 2 - Blocks[mbi.blockid2].x - mydesign.Blocks[mbi.blockid2][0].width / 2) +
        abs(Blocks[mbi.blockid1].y + mydesign.Blocks[mbi.blockid1][0].height / 2 - Blocks[mbi.blockid2].y - mydesign.Blocks[mbi.blockid2][0].height / 2);
  }
  cost += match_cost * hyper.BETA;
  cost += ratio * Aspect_Ratio_weight;
  cost += 0.0 / area * hyper.PHI; //dead_area
  cost += linear_const * hyper.PI;
  cost += multi_linear_const * hyper.PII;
  assert(!isnan(cost));
  return cost;
}

double ILP_solver::GenerateValidSolutionAnalytical(design& mydesign, PnRDB::Drc_info& drcInfo, PnRDB::hierNode& node) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.GenerateValidSolutionAnalytical");

  ++mydesign._totalNumCostCalc;
  auto roundup = [](int& v, int pitch) { v = pitch * ((v + pitch - 1) / pitch); };
  int v_metal_index = -1;
  int h_metal_index = -1;
  for (unsigned int i = 0; i < drcInfo.Metal_info.size(); ++i) {
    if (drcInfo.Metal_info[i].direct == 0) {
      v_metal_index = i;
      break;
    }
  }
  for (unsigned int i = 0; i < drcInfo.Metal_info.size(); ++i) {
    if (drcInfo.Metal_info[i].direct == 1) {
      h_metal_index = i;
      break;
    }
  }
  int x_pitch = drcInfo.Metal_info[v_metal_index].grid_unit_x;
  int y_pitch = drcInfo.Metal_info[h_metal_index].grid_unit_y;

  // each block has 4 vars, x, y, H_flip, V_flip;
  int N_var = mydesign.Blocks.size() * 4 + mydesign.Nets.size() * 2;
  // i*4+1: x
  // i*4+2:y
  // i*4+3:H_flip
  // i*4+4:V_flip
  // x = pitch * n_p + offset_i * is_ith_offset
  // sum(is_ith_offset) = 1
  // one var for each offset and each pitch
  int place_on_grid_var_start = N_var;
  int place_on_grid_var_count = 0;
  for(unsigned int i=0;i<mydesign.Blocks.size();i++){
    if (mydesign.Blocks[i][0].xoffset.size()) place_on_grid_var_count += int(mydesign.Blocks[i][0].xoffset.size()) + 1;
    if (mydesign.Blocks[i][0].yoffset.size()) place_on_grid_var_count += int(mydesign.Blocks[i][0].yoffset.size()) + 1;
  }
  N_var += place_on_grid_var_count;
  lprec* lp = make_lp(0, N_var);
  set_verbose(lp, IMPORTANT);
  put_logfunc(lp, &ILP_solver::lpsolve_logger, NULL);
  // set_outputfile(lp, const_cast<char*>("/dev/null"));

  // set integer constraint, H_flip and V_flip can only be 0 or 1
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    set_int(lp, i * 4 + 1, TRUE);
    set_int(lp, i * 4 + 2, TRUE);
    set_int(lp, i * 4 + 3, TRUE);
    set_int(lp, i * 4 + 4, TRUE);
    set_binary(lp, i * 4 + 3, TRUE);
    set_binary(lp, i * 4 + 4, TRUE);
  }
  // offset is ORed, only one is chosen, the select vars are 0 or 1, with sum 1
  int temp_pointer = place_on_grid_var_start;
  if(!node.isFirstILP){
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
      if (mydesign.Blocks[i][0].xoffset.size()){
        for (unsigned int j = 0;j<mydesign.Blocks[i][0].xoffset.size();j++){
          set_binary(lp, temp_pointer + j, TRUE);
        }
        set_int(lp, temp_pointer + int(mydesign.Blocks[i][0].xoffset.size()), TRUE);
        temp_pointer += int(mydesign.Blocks[i][0].xoffset.size()) + 1;
      }
      if (mydesign.Blocks[i][0].yoffset.size()){
        for (unsigned int j = 0;j<mydesign.Blocks[i][0].yoffset.size();j++){
          set_binary(lp, temp_pointer + j, TRUE);
        }
        set_int(lp, temp_pointer + int(mydesign.Blocks[i][0].yoffset.size()), TRUE);
        temp_pointer += int(mydesign.Blocks[i][0].yoffset.size()) + 1;
      }
    }
  }
  

  //place on grid flipping constraint
  if(!node.isFirstILP){
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
      if (mydesign.Blocks[i][0].xflip == 1) {
        double sparserow[1] = {1};
        int colno[1] = {int(i) * 4 + 2};
        if (!add_constraintex(lp, 1, sparserow, colno, EQ, 0)) logger->error("error");
      } else if (mydesign.Blocks[i][0].xflip == -1) {
        double sparserow[1] = {1};
        int colno[1] = {int(i) * 4 + 2};
        if (!add_constraintex(lp, 1, sparserow, colno, EQ, 1)) logger->error("error");
      }
      if (mydesign.Blocks[i][0].yflip == 1) {
        double sparserow[1] = {1};
        int colno[1] = {int(i) * 4 + 3};
        if (!add_constraintex(lp, 1, sparserow, colno, EQ, 0)) logger->error("error");
      } else if (mydesign.Blocks[i][0].yflip == -1) {
        double sparserow[1] = {1};
        int colno[1] = {int(i) * 4 + 3};
        if (!add_constraintex(lp, 1, sparserow, colno, EQ, 1)) logger->error("error");
      }
    }
  }
  

  //place on grid constraint
  if(!node.isFirstILP){
    temp_pointer = place_on_grid_var_start;
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
      if (mydesign.Blocks[i][0].xoffset.size()) {
        // x + is_filp *width - pitch * n_p - sum(offset_i * is_ith_offset) = 0
        {
          double sparserow[3 + mydesign.Blocks[i][0].xoffset.size()];
          sparserow[0] = 1;
          sparserow[1] = double(mydesign.Blocks[i][0].width);
          sparserow[2] = double(-mydesign.Blocks[i][0].xpitch);
          for (unsigned int j = 0; j < mydesign.Blocks[i][0].xoffset.size(); j++) sparserow[3 + j] = double(-mydesign.Blocks[i][0].xoffset[j]);
          int colno[3 + mydesign.Blocks[i][0].xoffset.size()];
          colno[0] = int(i) * 4;
          colno[1] = int(i) * 4 + 2;
          colno[2] = int(temp_pointer + mydesign.Blocks[i][0].xoffset.size());
          for (unsigned int j = 0; j < mydesign.Blocks[i][0].xoffset.size(); j++) colno[3 + j] = int(temp_pointer + j);
          if (!add_constraintex(lp, 3 + mydesign.Blocks[i][0].xoffset.size(), sparserow, colno, EQ, 0)) logger->error("error");
        }
        // sum(is_ith_offset) = 1
        double sparserow[mydesign.Blocks[i][0].xoffset.size()];
        int colno[mydesign.Blocks[i][0].xoffset.size()];
        for(unsigned int j=0;j<mydesign.Blocks[i][0].xoffset.size();j++){
          colno[j] = int(temp_pointer + j);
          sparserow[j] = 1;
        }
        if (!add_constraintex(lp, mydesign.Blocks[i][0].xoffset.size(), sparserow, colno, EQ, 1)) logger->error("error");
        temp_pointer += int(mydesign.Blocks[i][0].xoffset.size()) + 1;
      }
      if (mydesign.Blocks[i][0].yoffset.size()) {
        // y + is_flip * height - pitch * n_p - offset_i * is_ith_offset = 0
        {
          double sparserow[3 + mydesign.Blocks[i][0].yoffset.size()];
          sparserow[0] = 1;
          sparserow[1] = double(mydesign.Blocks[i][0].height);
          sparserow[2] = double(-mydesign.Blocks[i][0].ypitch);
          for (unsigned int j = 0; j < mydesign.Blocks[i][0].yoffset.size(); j++) sparserow[3 + j] = double(-mydesign.Blocks[i][0].yoffset[j]);
          int colno[3 + mydesign.Blocks[i][0].yoffset.size()];
          colno[0] = int(i) * 4 + 1;
          colno[1] = int(i) * 4 + 3;
          colno[2] = int(temp_pointer + mydesign.Blocks[i][0].yoffset.size());
          for (unsigned int j = 0; j < mydesign.Blocks[i][0].yoffset.size(); j++) colno[3 + j] = int(temp_pointer + j);
          if (!add_constraintex(lp, 3 + mydesign.Blocks[i][0].yoffset.size(), sparserow, colno, EQ, 0)) logger->error("error");
        }
        // sum(is_ith_offset) = 1
        double sparserow[mydesign.Blocks[i][0].yoffset.size()];
        int colno[mydesign.Blocks[i][0].yoffset.size()];
        for(unsigned int j=0;j<mydesign.Blocks[i][0].yoffset.size();j++){
          colno[j] = int(temp_pointer + j);
          sparserow[j] = 1;
        }
        if (!add_constraintex(lp, mydesign.Blocks[i][0].yoffset.size(), sparserow, colno, EQ, 1)) logger->error("error");
        temp_pointer += int(mydesign.Blocks[i][0].yoffset.size()) + 1;
      }
    }
  }
  

  // overlap constraint
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    for (unsigned int j = i + 1; j < mydesign.Blocks.size(); j++) {
      if (block_order[i][j] & 0x0001) {
        // i is at the left of j
        double sparserow[2] = {-1, 1};
        int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
        if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[i][0].width + mydesign.bias_Hgraph)) logger->error("error");
      } else if (block_order[i][j] & 0x0002) {
        // i and j align to LLx
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
        if (!add_constraintex(lp, 2, sparserow, colno, EQ, 0)) logger->error("error");
      } else if (block_order[i][j] & 0x0004) {
        // i and j align to x center
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
        if (!add_constraintex(lp, 2, sparserow, colno, EQ, mydesign.Blocks[j][0].width / 2 - mydesign.Blocks[i][0].width / 2)) logger->error("error");
      } else if (block_order[i][j] & 0x0008) {
        // i and j align to URx
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
        if (!add_constraintex(lp, 2, sparserow, colno, EQ, mydesign.Blocks[j][0].width - mydesign.Blocks[i][0].width)) logger->error("error");
      } else if (block_order[i][j] & 0x0010) {
        // i is at the right of j
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
        if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[j][0].width + mydesign.bias_Hgraph)) logger->error("error");
      }
      if (block_order[i][j] & 0x0100) {
        // i is at below j
        double sparserow[2] = {-1, 1};
        int colno[2] = {int(i) * 4 + 2, int(j) * 4 + 2};
        if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[i][0].height + mydesign.bias_Vgraph)) logger->error("error");
      } else if (block_order[i][j] & 0x0200) {
        // i and j align to LLy
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 2, int(j) * 4 + 2};
        if (!add_constraintex(lp, 2, sparserow, colno, EQ, 0)) logger->error("error");
      } else if (block_order[i][j] & 0x0400) {
        // i and j align to y center
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 2, int(j) * 4 + 2};
        if (!add_constraintex(lp, 2, sparserow, colno, EQ, mydesign.Blocks[j][0].height / 2 - mydesign.Blocks[i][0].height / 2)) logger->error("error");
      } else if (block_order[i][j] & 0x0800) {
        // i and j align to URy
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 2, int(j) * 4 + 2};
        if (!add_constraintex(lp, 2, sparserow, colno, EQ, mydesign.Blocks[j][0].height - mydesign.Blocks[i][0].height)) logger->error("error");
      } else if (block_order[i][j] & 0x1000) {
        // i is above j
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 2, int(j) * 4 + 2};
        if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[j][0].height + mydesign.bias_Vgraph)) logger->error("error");
      }
    }
  }
  /**
  for (int i = 0; i < mydesign.Blocks.size(); i++) {
    int i_pos_index = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), i) - curr_sp.posPair.begin();
    int i_neg_index = find(curr_sp.negPair.begin(), curr_sp.negPair.end(), i) - curr_sp.negPair.begin();
    for (int j = i + 1; j < mydesign.Blocks.size(); j++) {
      int j_pos_index = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), j) - curr_sp.posPair.begin();
      int j_neg_index = find(curr_sp.negPair.begin(), curr_sp.negPair.end(), j) - curr_sp.negPair.begin();
      if (i_pos_index < j_pos_index) {
        if (i_neg_index < j_neg_index) {
          // i is left of j
          double sparserow[2] = {1, -1};
          int colno[2] = {i * 4 + 1, j * 4 + 1};
          if (!add_constraintex(lp, 2, sparserow, colno, LE, -mydesign.Blocks[i][curr_sp.selected[i]].width - mydesign.bias_Hgraph)) logger->error("error");
        } else {
          // i is above j
          double sparserow[2] = {1, -1};
          int colno[2] = {i * 4 + 2, j * 4 + 2};
          if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[j][curr_sp.selected[j]].height + mydesign.bias_Vgraph)) logger->error("error");
        }
      } else {
        if (i_neg_index < j_neg_index) {
          // i is be low j
          double sparserow[2] = {1, -1};
          int colno[2] = {i * 4 + 2, j * 4 + 2};
          if (!add_constraintex(lp, 2, sparserow, colno, LE, -mydesign.Blocks[i][curr_sp.selected[i]].height - mydesign.bias_Vgraph)) logger->error("error");
        } else {
          // i is right of j
          double sparserow[2] = {1, -1};
          int colno[2] = {i * 4 + 1, j * 4 + 1};
          if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[j][curr_sp.selected[j]].width + mydesign.bias_Hgraph)) logger->error("error");
        }
      }
    }
  }**/

  // x>=0, y>=0
  for (unsigned int i = 0; i < node.Blocks.size(); i++) {
    {
      double sparserow[1] = {1};
      int colno[1] = {int(i) * 4 + 1};
      if (!add_constraintex(lp, 1, sparserow, colno, GE, 0)) logger->error("error");
    }
    {
      double sparserow[1] = {1};
      int colno[1] = {int(i) * 4 + 2};
      if (!add_constraintex(lp, 1, sparserow, colno, GE, 0)) logger->error("error");
    }
  }

  // symmetry block constraint
  for (const auto& SPBlock : mydesign.SPBlocks) {
    if (SPBlock.axis_dir == placerDB::H) {
      // constraint inside one pair
      for (unsigned int i = 0; i < SPBlock.sympair.size(); i++) {
        int first_id = SPBlock.sympair[i].first, second_id = SPBlock.sympair[i].second;
        // each pair has opposite V flip
        {
          double sparserow[2] = {1, 1};
          int colno[2] = {first_id * 4 + 4, second_id * 4 + 4};
          add_constraintex(lp, 2, sparserow, colno, EQ, 1);
        }
        // x center of blocks in each pair are the same
        //{
        // double sparserow[2] = {1, -1};
        // int colno[2] = {first_id * 4 + 1, second_id * 4 + 1};
        // int first_x_center = mydesign.Blocks[first_id][curr_sp.selected[first_id]].width / 2;
        // int second_x_center = mydesign.Blocks[second_id][curr_sp.selected[second_id]].width / 2;
        // add_constraintex(lp, 2, sparserow, colno, EQ, -first_x_center + second_x_center);
        //}
      }

      // constraint between two pairs
      for (unsigned int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        int i_first_y_center = mydesign.Blocks[i_first_id][0].height / 4;
        int i_second_y_center = mydesign.Blocks[i_second_id][0].height / 4;
        for (unsigned int j = i + 1; j < SPBlock.sympair.size(); j++) {
          // the y center of the two pairs are the same
          int j_first_id = SPBlock.sympair[j].first, j_second_id = SPBlock.sympair[j].second;
          int j_first_y_center = mydesign.Blocks[j_first_id][0].height / 4;
          int j_second_y_center = mydesign.Blocks[j_second_id][0].height / 4;
          double sparserow[4] = {0.5, 0.5, -0.5, -0.5};
          int colno[4] = {i_first_id * 4 + 2, i_second_id * 4 + 2, j_first_id * 4 + 2, j_second_id * 4 + 2};
          int bias = -i_first_y_center - i_second_y_center + j_first_y_center + j_second_y_center;
          add_constraintex(lp, 4, sparserow, colno, EQ, bias);
        }
      }

      // constraint between a pair and a selfsym
      for (unsigned int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        int i_first_y_center = mydesign.Blocks[i_first_id][0].height / 4;
        int i_second_y_center = mydesign.Blocks[i_second_id][0].height / 4;
        for (unsigned int j = 0; j < SPBlock.selfsym.size(); j++) {
          // the y center of the pair and the selfsym are the same
          int j_id = SPBlock.selfsym[j].first;
          int j_y_center = mydesign.Blocks[j_id][0].height / 2;
          double sparserow[3] = {0.5, 0.5, -1};
          int colno[3] = {i_first_id * 4 + 2, i_second_id * 4 + 2, j_id * 4 + 2};
          int bias = -i_first_y_center - i_second_y_center + j_y_center;
          add_constraintex(lp, 3, sparserow, colno, EQ, bias);
        }
      }

      // constraint between two selfsyms
      for (unsigned int i = 0; i < SPBlock.selfsym.size(); i++) {
        int i_id = SPBlock.selfsym[i].first;
        int i_y_center = mydesign.Blocks[i_id][0].height / 2;
        for (unsigned int j = i + 1; j < SPBlock.selfsym.size(); j++) {
          // the y center of the two selfsyms are the same
          int j_id = SPBlock.selfsym[j].first;
          int j_y_center = mydesign.Blocks[j_id][0].height / 2;
          double sparserow[2] = {1, -1};
          int colno[2] = {i_id * 4 + 2, j_id * 4 + 2};
          int bias = -i_y_center + j_y_center;
          add_constraintex(lp, 2, sparserow, colno, EQ, bias);
        }
      }
    } else {
      // axis_dir==V
      // constraint inside one pair
      for (unsigned int i = 0; i < SPBlock.sympair.size(); i++) {
        int first_id = SPBlock.sympair[i].first, second_id = SPBlock.sympair[i].second;
        // each pair has opposite H flip
        {
          double sparserow[2] = {1, 1};
          int colno[2] = {first_id * 4 + 3, second_id * 4 + 3};
          add_constraintex(lp, 2, sparserow, colno, EQ, 1);
        }
        // y center of blocks in each pair are the same
        //{
        // double sparserow[2] = {1, -1};
        // int colno[2] = {first_id * 4 + 2, second_id * 4 + 2};
        // int first_y_center = mydesign.Blocks[first_id][curr_sp.selected[first_id]].height / 2;
        // int second_y_center = mydesign.Blocks[second_id][curr_sp.selected[second_id]].height / 2;
        // add_constraintex(lp, 2, sparserow, colno, EQ, -first_y_center + second_y_center);
        //}
      }

      // constraint between two pairs
      for (unsigned int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        int i_first_x_center = mydesign.Blocks[i_first_id][0].width / 4;
        int i_second_x_center = mydesign.Blocks[i_second_id][0].width / 4;
        for (unsigned int j = i + 1; j < SPBlock.sympair.size(); j++) {
          // the x center of the two pairs are the same
          int j_first_id = SPBlock.sympair[j].first, j_second_id = SPBlock.sympair[j].second;
          int j_first_x_center = mydesign.Blocks[j_first_id][0].width / 4;
          int j_second_x_center = mydesign.Blocks[j_second_id][0].width / 4;
          double sparserow[4] = {0.5, 0.5, -0.5, -0.5};
          int colno[4] = {i_first_id * 4 + 1, i_second_id * 4 + 1, j_first_id * 4 + 1, j_second_id * 4 + 1};
          int bias = -i_first_x_center - i_second_x_center + j_first_x_center + j_second_x_center;
          add_constraintex(lp, 4, sparserow, colno, EQ, bias);
        }
      }

      // constraint between a pair and a selfsym
      for (unsigned int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        int i_first_x_center = mydesign.Blocks[i_first_id][0].width / 4;
        int i_second_x_center = mydesign.Blocks[i_second_id][0].width / 4;
        for (unsigned int j = 0; j < SPBlock.selfsym.size(); j++) {
          // the x center of the pair and the selfsym are the same
          int j_id = SPBlock.selfsym[j].first;
          int j_x_center = mydesign.Blocks[j_id][0].width / 2;
          double sparserow[3] = {0.5, 0.5, -1};
          int colno[3] = {i_first_id * 4 + 1, i_second_id * 4 + 1, j_id * 4 + 1};
          int bias = -i_first_x_center - i_second_x_center + j_x_center;
          add_constraintex(lp, 3, sparserow, colno, EQ, bias);
        }
      }

      // constraint between two selfsyms
      for (unsigned int i = 0; i < SPBlock.selfsym.size(); i++) {
        int i_id = SPBlock.selfsym[i].first;
        int i_x_center = mydesign.Blocks[i_id][0].width / 2;
        for (unsigned int j = i + 1; j < SPBlock.selfsym.size(); j++) {
          // the x center of the two selfsyms are the same
          int j_id = SPBlock.selfsym[j].first;
          int j_x_center = mydesign.Blocks[j_id][0].width / 2;
          double sparserow[2] = {1, -1};
          int colno[2] = {i_id * 4 + 1, j_id * 4 + 1};
          int bias = -i_x_center + j_x_center;
          add_constraintex(lp, 2, sparserow, colno, EQ, bias);
        }
      }
    }
  }
  /**
  // align block constraint
  for (auto alignment_unit : mydesign.Align_blocks) {
    for (int j = 0; j < alignment_unit.blocks.size() - 1; j++) {
      int first_id = alignment_unit.blocks[j], second_id = alignment_unit.blocks[j + 1];
      if (alignment_unit.horizon == 1) {
        // same y
        double sparserow[2] = {1, -1};
        int colno[2] = {first_id * 4 + 2, second_id * 4 + 2};
        add_constraintex(lp, 2, sparserow, colno, EQ, 0);
      } else {
        // same x
        double sparserow[2] = {1, -1};
        int colno[2] = {first_id * 4 + 1, second_id * 4 + 1};
        add_constraintex(lp, 2, sparserow, colno, EQ, 0);
      }
    }
  }**/

  // set_add_rowmode(lp, FALSE);
  {
    double row[N_var + 1] = {0};
    Pdatatype hyper;
    #ifndef min_displacement
    // add HPWL in cost
    for (unsigned int i = 0; i < mydesign.Nets.size(); i++) {
      vector<pair<int, int>> blockids;
      /// for (int j = 0; j < mydesign.Nets[i].connected.size(); j++) {
      /// if (mydesign.Nets[i].connected[j].type == placerDB::Block &&
      ///(blockids.size() == 0 || mydesign.Nets[i].connected[j].iter2 != curr_sp.negPair[blockids.back().first]))
      /// blockids.push_back(std::make_pair(find(curr_sp.negPair.begin(), curr_sp.negPair.end(), mydesign.Nets[i].connected[j].iter2) - curr_sp.negPair.begin(),
      /// mydesign.Nets[i].connected[j].iter));
      //}
      set<pair<pair<int, int>, int>> block_pos_x_set;
      set<pair<pair<int, int>, int>> block_pos_y_set;
      for (unsigned int j = 0; j < mydesign.Nets[i].connected.size(); j++) {
        if (mydesign.Nets[i].connected[j].type == placerDB::Block) {
          block_pos_x_set.insert(std::make_pair(std::make_pair(mydesign.Nets[i].connected[j].iter2, mydesign.Nets[i].connected[j].iter),
                                               node.Blocks[mydesign.Nets[i].connected[j].iter2].instance[0].placedCenter.x));
          block_pos_y_set.insert(std::make_pair(std::make_pair(mydesign.Nets[i].connected[j].iter2, mydesign.Nets[i].connected[j].iter),
                                               node.Blocks[mydesign.Nets[i].connected[j].iter2].instance[0].placedCenter.y));
        }
        // blockids.push_back(std::make_pair(find(curr_sp.negPair.begin(), curr_sp.negPair.end(), mydesign.Nets[i].connected[j].iter2) -
        // curr_sp.negPair.begin(), mydesign.Nets[i].connected[j].iter));
      }
      vector<pair<pair<int, int>, int>> block_pos_x(block_pos_x_set.begin(), block_pos_x_set.end());
      vector<pair<pair<int, int>, int>> block_pos_y(block_pos_y_set.begin(), block_pos_y_set.end());
      if (block_pos_x.size() < 2) continue;
      sort(block_pos_x.begin(), block_pos_x.end(), [](const pair<pair<int, int>, int>& a, const pair<pair<int, int>, int>& b) { return a.second < b.second; });
      sort(block_pos_y.begin(), block_pos_y.end(), [](const pair<pair<int, int>, int>& a, const pair<pair<int, int>, int>& b) { return a.second < b.second; });
      // sort(blockids.begin(), blockids.end(), [](const pair<int, int>& a, const pair<int, int>& b) { return a.first <= b.first; });
      /**int LLblock_id = curr_sp.negPair[blockids.front().first], LLpin_id = blockids.front().second;
      int LLblock_width = mydesign.Blocks[LLblock_id][curr_sp.selected[LLblock_id]].width,
          LLblock_height = mydesign.Blocks[LLblock_id][curr_sp.selected[LLblock_id]].height;
      int LLpin_x = mydesign.Blocks[LLblock_id][curr_sp.selected[LLblock_id]].blockPins[LLpin_id].center.front().x,
          LLpin_y = mydesign.Blocks[LLblock_id][curr_sp.selected[LLblock_id]].blockPins[LLpin_id].center.front().y;
      int URblock_id = curr_sp.negPair[blockids.back().first], URpin_id = blockids.back().second;
      int URblock_width = mydesign.Blocks[URblock_id][curr_sp.selected[URblock_id]].width,
          URblock_height = mydesign.Blocks[URblock_id][curr_sp.selected[URblock_id]].height;
      int URpin_x = mydesign.Blocks[URblock_id][curr_sp.selected[URblock_id]].blockPins[URpin_id].center.front().x,
          URpin_y = mydesign.Blocks[URblock_id][curr_sp.selected[URblock_id]].blockPins[URpin_id].center.front().y;**/
      int Lblock_id = block_pos_x.front().first.first, Lpin_id = block_pos_x.front().first.second;
      int Rblock_id = block_pos_x.back().first.first, Rpin_id = block_pos_x.back().first.second;
      int Lblock_width = mydesign.Blocks[Lblock_id][0].width, Lblock_height = mydesign.Blocks[Lblock_id][0].height;
      int Rblock_width = mydesign.Blocks[Rblock_id][0].width, Rblock_height = mydesign.Blocks[Rblock_id][0].height;
      int Lpin_x = mydesign.Blocks[Lblock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Lblock_id][0].blockPins[Lpin_id].center.front().x
                                                                      : mydesign.Blocks[Lblock_id][0].width / 2,
          Lpin_y = mydesign.Blocks[Lblock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Lblock_id][0].blockPins[Lpin_id].center.front().y
                                                                      : mydesign.Blocks[Lblock_id][0].height / 2;
      int Rpin_x = mydesign.Blocks[Rblock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Rblock_id][0].blockPins[Rpin_id].center.front().x
                                                                      : mydesign.Blocks[Rblock_id][0].width / 2,
          Rpin_y = mydesign.Blocks[Rblock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Rblock_id][0].blockPins[Rpin_id].center.front().y
                                                                      : mydesign.Blocks[Rblock_id][0].height / 2;

      int Dblock_id = block_pos_y.front().first.first, Dpin_id = block_pos_y.front().first.second;
      int Ublock_id = block_pos_y.back().first.first, Upin_id = block_pos_y.back().first.second;
      int Dblock_width = mydesign.Blocks[Dblock_id][0].width, Dblock_height = mydesign.Blocks[Dblock_id][0].height;
      int Ublock_width = mydesign.Blocks[Ublock_id][0].width, Ublock_height = mydesign.Blocks[Ublock_id][0].height;
      int Dpin_x = mydesign.Blocks[Dblock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Dblock_id][0].blockPins[Dpin_id].center.front().x
                                                                      : mydesign.Blocks[Dblock_id][0].width / 2,
          Dpin_y = mydesign.Blocks[Dblock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Dblock_id][0].blockPins[Dpin_id].center.front().y
                                                                      : mydesign.Blocks[Dblock_id][0].height / 2;
      int Upin_x = mydesign.Blocks[Ublock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Ublock_id][0].blockPins[Upin_id].center.front().x
                                                                      : mydesign.Blocks[Ublock_id][0].width / 2,
          Upin_y = mydesign.Blocks[Ublock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Ublock_id][0].blockPins[Upin_id].center.front().y
                                                                      : mydesign.Blocks[Ublock_id][0].height / 2;

      // min abs(LLx+(LLwidth-2LLpinx)*LLHflip+LLpinx-URx-(URwidth-2URpinx)*URHflip-URpinx)=HPWLx
      //-> (LLx+(LLwidth-2LLpinx)*LLHflip+LLpinx-URx-(URwidth-2URpinx)*URHflip-URpinx)<=HPWLx
      //  -(LLx+(LLwidth-2LLpinx)*LLHflip+LLpinx-URx-(URwidth-2URpinx)*URHflip-URpinx)<=HPWLx
      if(Lblock_id!=Rblock_id){
        {
          double sparserow[5] = {hyper.LAMBDA, (Lblock_width - 2 * Lpin_x) * hyper.LAMBDA, -hyper.LAMBDA,
                                -(Rblock_width - 2 * Rpin_x) * hyper.LAMBDA, -1};
          int colno[5] = {Lblock_id * 4 + 1, Lblock_id * 4 + 3, Rblock_id * 4 + 1, Rblock_id * 4 + 3, int(mydesign.Blocks.size()) * 4 + int(i) * 2 + 1};
          add_constraintex(lp, 5, sparserow, colno, LE, -Lpin_x + Rpin_x);
        }
        {
          double sparserow[5] = {-hyper.LAMBDA, -(Lblock_width - 2 * Lpin_x) * hyper.LAMBDA, hyper.LAMBDA,
                                (Rblock_width - 2 * Rpin_x) * hyper.LAMBDA, -1};
          int colno[5] = {Lblock_id * 4 + 1, Lblock_id * 4 + 3, Rblock_id * 4 + 1, Rblock_id * 4 + 3, int(mydesign.Blocks.size()) * 4 + int(i) * 2 + 1};
          add_constraintex(lp, 5, sparserow, colno, LE, Lpin_x - Rpin_x);
        }
        row[mydesign.Blocks.size() * 4 + i * 2 + 1] = 1;
      }
      if(Dblock_id!=Ublock_id){
        {
          double sparserow[5] = {hyper.LAMBDA, (Dblock_height - 2 * Dpin_y) * hyper.LAMBDA, -hyper.LAMBDA,
                                -(Ublock_height - 2 * Upin_y) * hyper.LAMBDA, -1};
          int colno[5] = {Dblock_id * 4 + 2, Dblock_id * 4 + 4, Ublock_id * 4 + 2, Ublock_id * 4 + 4, int(mydesign.Blocks.size()) * 4 + int(i) * 2 + 2};
          add_constraintex(lp, 5, sparserow, colno, LE, -Dpin_y + Upin_y);
        }
        {
          double sparserow[5] = {-hyper.LAMBDA, -(Dblock_height - 2 * Dpin_y) * hyper.LAMBDA, hyper.LAMBDA,
                                (Ublock_height - 2 * Upin_y) * hyper.LAMBDA, -1};
          int colno[5] = {Dblock_id * 4 + 2, Dblock_id * 4 + 4, Ublock_id * 4 + 2, Ublock_id * 4 + 4, int(mydesign.Blocks.size()) * 4 + int(i) * 2 + 2};
          add_constraintex(lp, 5, sparserow, colno, LE, Dpin_y - Upin_y);
        }
        row[mydesign.Blocks.size() * 4 + i * 2 + 2] = 1;
      }
    }
    #endif

    // add area in cost
    int estimated_width = 0, estimated_height = 0;
    // estimate width
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
      estimated_width += mydesign.Blocks[i][0].width;
    }
    // add estimated area
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
      row[i * 4 + 2] += estimated_width / 2;
    }
    // estimate height
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
      estimated_height += mydesign.Blocks[i][0].height;
    }
    // add estimated area
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
      row[i * 4 + 1] += estimated_height / 2;
    }

    set_obj_fn(lp, row);
    set_minim(lp);
    set_timeout(lp, 10);
    //print_lp(lp);
    #ifndef ilp
    //set_presolve(lp, PRESOLVE_ROWS | PRESOLVE_COLS | PRESOLVE_LINDEP, get_presolveloops(lp));
    #endif
    int ret = solve(lp);
    if (ret != 0 && ret != 1) {
      delete_lp(lp);
	  ++mydesign._infeasILPFail;
      return -1;
    }
  }

  double var[N_var];
  #ifdef ilp
  get_variables(lp, var);
  #else
  int Norig_columns, Norig_rows, i;
  Norig_columns = get_Norig_columns(lp);
  Norig_rows = get_Norig_rows(lp);
  for(i = 1; i <= Norig_columns; i++) {
    var[i - 1] = get_var_primalresult(lp, Norig_rows + i);
  }
  #endif
  delete_lp(lp);
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    Blocks[i].x = var[i * 4];
    Blocks[i].y = var[i * 4 + 1];
    roundup(Blocks[i].x, x_pitch);
    roundup(Blocks[i].y, y_pitch);
    Blocks[i].H_flip = var[i * 4 + 2];
    Blocks[i].V_flip = var[i * 4 + 3];
  }

  // calculate LL and UR
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    LL.x = std::min(LL.x, Blocks[i].x);
    LL.y = std::min(LL.y, Blocks[i].y);
    UR.x = std::max(UR.x, Blocks[i].x + mydesign.Blocks[i][0].width);
    UR.y = std::max(UR.y, Blocks[i].y + mydesign.Blocks[i][0].height);
  }
  // calculate area
  area = double(UR.x - LL.x) * double(UR.y - LL.y);
  /**
  // calculate dead area
  dead_area = area;
  for (int i = 0; i < mydesign.Blocks.size(); i++) {
    dead_area -= double(mydesign.Blocks[i][0].width) * double(mydesign.Blocks[i][0].height);
  }
  // calculate ratio
  // ratio = std::max(double(UR.x - LL.x) / double(UR.y - LL.y), double(UR.y - LL.y) / double(UR.x - LL.x));
  **/
  ratio = double(UR.x - LL.x) / double(UR.y - LL.y);
  if (ratio < Aspect_Ratio[0] || ratio > Aspect_Ratio[1]) {
	  ++mydesign._infeasAspRatio;
	  return -1;
  }
  if (placement_box[0] > 0 && (UR.x - LL.x > placement_box[0]) || placement_box[1] > 0 && (UR.y - LL.y > placement_box[1])) {
	  ++mydesign._infeasPlBound;
	  return -1;
  }
  // calculate HPWL
  HPWL = 0;
  for (const auto& neti : mydesign.Nets) {
    int HPWL_min_x = UR.x, HPWL_min_y = UR.y, HPWL_max_x = 0, HPWL_max_y = 0;
    for (const auto& connectedj : neti.connected) {
      if (connectedj.type == placerDB::Block) {
        int iter2 = connectedj.iter2, iter = connectedj.iter;
        if (mydesign.Blocks[iter2][0].blockPins.size() > 0) {
          for (const auto& centerk : mydesign.Blocks[iter2][0].blockPins[iter].center) {
            // calculate contact center
            int pin_x = centerk.x;
            int pin_y = centerk.y;
            if (Blocks[iter2].H_flip) pin_x = mydesign.Blocks[iter2][0].width - pin_x;
            if (Blocks[iter2].V_flip) pin_y = mydesign.Blocks[iter2][0].height - pin_y;
            pin_x += Blocks[iter2].x;
            pin_y += Blocks[iter2].y;
            HPWL_min_x = std::min(HPWL_min_x, pin_x);
            HPWL_max_x = std::max(HPWL_max_x, pin_x);
            HPWL_min_y = std::min(HPWL_min_y, pin_y);
            HPWL_max_y = std::max(HPWL_max_y, pin_y);
          }
        } else {
          int pin_x = mydesign.Blocks[iter2][0].width / 2;
          int pin_y = mydesign.Blocks[iter2][0].height / 2;
          if (Blocks[iter2].H_flip) pin_x = mydesign.Blocks[iter2][0].width - pin_x;
          if (Blocks[iter2].V_flip) pin_y = mydesign.Blocks[iter2][0].height - pin_y;
          pin_x += Blocks[iter2].x;
          pin_y += Blocks[iter2].y;
          HPWL_min_x = std::min(HPWL_min_x, pin_x);
          HPWL_max_x = std::max(HPWL_max_x, pin_x);
          HPWL_min_y = std::min(HPWL_min_y, pin_y);
          HPWL_max_y = std::max(HPWL_max_y, pin_y);
        }
      }
    }
    HPWL += (HPWL_max_y - HPWL_min_y) + (HPWL_max_x - HPWL_min_x);
  }
  // calculate linear constraint
  linear_const = 0;
  std::vector<std::vector<double>> feature_value;
  for (const auto& neti : mydesign.Nets) {
    std::vector<std::vector<placerDB::point>> center_points;
    for (const auto& connectedj : neti.connected) {
      if (connectedj.type == placerDB::Block) {
        std::vector<placerDB::point> pos;
        if (mydesign.Blocks[connectedj.iter2][0].blockPins.size() > 0) {
          for (const auto& ci : mydesign.Blocks[connectedj.iter2][0].blockPins[connectedj.iter].center) {
            placerDB::point newp;
            newp.x = ci.x;
            newp.y = ci.y;
            if (Blocks[connectedj.iter2].H_flip) newp.x = mydesign.Blocks[connectedj.iter2][0].width - newp.x;
            if (Blocks[connectedj.iter2].V_flip) newp.y = mydesign.Blocks[connectedj.iter2][0].height - newp.y;
            newp.x += Blocks[connectedj.iter2].x;
            newp.y += Blocks[connectedj.iter2].y;
            pos.push_back(newp);
          }
          if (!pos.empty()) center_points.push_back(pos);
        } else {
          placerDB::point newp;
          newp.x = mydesign.Blocks[connectedj.iter2][0].width / 2;
          newp.y = mydesign.Blocks[connectedj.iter2][0].height / 2;
          if (Blocks[connectedj.iter2].H_flip) newp.x = mydesign.Blocks[connectedj.iter2][0].width - newp.x;
          if (Blocks[connectedj.iter2].V_flip) newp.y = mydesign.Blocks[connectedj.iter2][0].height - newp.y;
          newp.x += Blocks[connectedj.iter2].x;
          newp.y += Blocks[connectedj.iter2].y;
          pos.push_back(newp);
          center_points.push_back(pos);
        }
      } else if (connectedj.type == placerDB::Terminal) {
        center_points.push_back({mydesign.Terminals[connectedj.iter].center});
      }
    }
    std::vector<double> temp_feature = Calculate_Center_Point_feature(center_points);
    feature_value.push_back(temp_feature);
    double temp_sum = 0;
    for (unsigned int j = 0; j < neti.connected.size(); j++) temp_sum += neti.connected[j].alpha * temp_feature[j];
    temp_sum = std::max(temp_sum - neti.upperBound, double(0));
    linear_const += temp_sum;
  }

  // calculate multi linear constraint
  multi_linear_const = 0;
  /**
  for (const auto& constrainti : mydesign.ML_Constraints) {
    double temp_sum = 0;
    for (const auto& constraintj : constrainti.Multi_linearConst) {
      for (unsigned int k = 0; k < constraintj.pins.size(); k++) {
        int index_i = 0;
        int index_j = 0;
        for (unsigned int m = 0; m < mydesign.Nets.size(); m++) {
          for (unsigned int n = 0; n < mydesign.Nets[m].connected.size(); n++) {
            if (mydesign.Nets[m].connected[n].iter2 == constraintj.pins[k].first && mydesign.Nets[m].connected[n].iter == constraintj.pins[k].second) {
              index_i = m;
              index_j = n;
              break;
            }
          }
        }
        temp_sum += constraintj.alpha[k] * feature_value[index_i][index_j];
      }
    }
    temp_sum = std::min(temp_sum, constrainti.upperBound);
    multi_linear_const += temp_sum;
  }
  **/

  double cost = CalculateCost(mydesign);
  return cost;
}

void ILP_solver::updateTerminalCenterAnalytical(design& mydesign) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.updateTerminalCenter");

  int Xmax = UR.x;
  int Ymax = UR.y;
  vector<placerDB::point> pos;
  placerDB::point p, bp;
  int alpha;
  vector<placerDB::point> pos_pin;
  std::set<int> solved_terminals;
  // for each terminal
  for (unsigned int i = 0; i < mydesign.Terminals.size(); i++) {
    if (solved_terminals.find(i) != solved_terminals.end()) continue;
    solved_terminals.insert(i);
    int netIdx = mydesign.Terminals.at(i).netIter;
    int sbIdx = mydesign.Terminals.at(i).SBidx;
    int cp = mydesign.Terminals.at(i).counterpart;
    if (netIdx < 0 || netIdx >= mydesign.Nets.size()) {
      logger->error("Placer-Warning: terminal {0} is dangling; set it on origin", i);
      mydesign.Terminals.at(i).center = {0, 0};
      continue;
    }
    if ((mydesign.Nets.at(netIdx).priority).compare("min") == 0) {
      alpha = 4;
    } else if ((mydesign.Nets.at(netIdx).priority).compare("mid") == 0) {
      alpha = 2;
    } else {
      alpha = 1;
    }
    alpha *= mydesign.Nets.at(netIdx).weight;  // add weight to reflect the modification for bigMacros
    if (sbIdx != -1) {                         // in symmetry group
      placerDB::Smark axis = mydesign.SBlocks[sbIdx].axis_dir;
      if (cp == (int)i) {  // self-symmetric
        if (axis == placerDB::V) {
          int axis_X = Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first].x + mydesign.Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first][0].width / 2;
          int distTerm = INT_MAX;
          placerDB::point tp(axis_X, 0);
          for (const auto& ci : mydesign.Nets[netIdx].connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
                p += bp;
                if (p.y < distTerm) {
                  distTerm = p.y;
                  tp.y = 0;
                }
                if (Ymax - p.y < distTerm) {
                  distTerm = Ymax - p.y;
                  tp.y = Ymax;
                }
              }
            }
          }
          mydesign.Terminals.at(i).center = tp;
        } else if (axis == placerDB::H) {
          int axis_Y = Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first].y + mydesign.Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first][0].height / 2;
          int distTerm = INT_MAX;
          placerDB::point tp(0, axis_Y);
          for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
                p += bp;
                if (p.x < distTerm) {
                  distTerm = p.x;
                  tp.x = 0;
                }
                if (Xmax - p.x < distTerm) {
                  distTerm = Xmax - p.x;
                  tp.x = Xmax;
                }
              }
            }
          }
          mydesign.Terminals.at(i).center = tp;
        } else {
          logger->error("Placer-Error: incorrect axis direction");
        }
      } else {  // symmetry pair
        if (solved_terminals.find(cp) != solved_terminals.end()) continue;
        solved_terminals.insert(cp);
        int netIdx2 = mydesign.Terminals.at(cp).netIter;
        if (netIdx2 < 0 or netIdx2 >= mydesign.Nets.size()) {
          logger->error("Placer-Error: terminal {0} is not dangling, but its counterpart {1} is dangling; set them on origin", i, cp);
          mydesign.Terminals.at(i).center = {0, 0};
          mydesign.Terminals.at(cp).center = {0, 0};
          continue;
        }
        int alpha2;
        if ((mydesign.Nets.at(netIdx2).priority).compare("min") == 0) {
          alpha2 = 4;
        } else if ((mydesign.Nets.at(netIdx2).priority).compare("mid") == 0) {
          alpha2 = 2;
        } else {
          alpha2 = 1;
        }
        alpha2 *= mydesign.Nets.at(netIdx2).weight;  // add weight to reflect the modification for bigMacros
        if (axis == placerDB::V) {
          placerDB::point tpL1, tpR1;
          int distTermL = INT_MAX, distTermR = INT_MAX;
          for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
                p += bp;
                if (p.x < distTermL) {
                  distTermL = p.x;
                  tpL1.x = 0;
                  tpL1.y = p.y;
                }
                if (Xmax - p.x < distTermR) {
                  distTermR = Xmax - p.x;
                  tpR1.x = Xmax;
                  tpR1.y = p.y;
                }
              }
            }
          }
          placerDB::point tpL2, tpR2;
          int distTermL2 = INT_MAX, distTermR2 = INT_MAX;
          for (const auto& ci : mydesign.Nets.at(netIdx2).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
                p += bp;
                if (p.x < distTermL2) {
                  distTermL2 = p.x;
                  tpL2.x = 0;
                  tpL2.y = p.y;
                }
                if (Xmax - p.x < distTermR2) {
                  distTermR2 = Xmax - p.x;
                  tpR2.x = Xmax;
                  tpR2.y = p.y;
                }
              }
            }
          }
          if (distTermL * alpha + distTermR2 * alpha2 < distTermR * alpha + distTermL2 * alpha2) {
            mydesign.Terminals.at(i).center = tpL1;
            mydesign.Terminals.at(cp).center = tpR2;
          } else {
            mydesign.Terminals.at(i).center = tpR1;
            mydesign.Terminals.at(cp).center = tpL2;
          }
        } else if (axis == placerDB::H) {
          placerDB::point tpL1, tpU1;
          int distTermL = INT_MAX, distTermU = INT_MAX;
          for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
                p += bp;
                if (p.y < distTermL) {
                  distTermL = p.y;
                  tpL1.x = p.x;
                  tpL1.y = 0;
                }
                if (Ymax - p.y < distTermU) {
                  distTermU = Ymax - p.y;
                  tpU1.x = p.x;
                  tpU1.y = Ymax;
                }
              }
            }
          }
          placerDB::point tpL2, tpU2;
          int distTermL2 = INT_MAX, distTermU2 = INT_MAX;
          for (const auto& ci : mydesign.Nets.at(netIdx2).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
                p += bp;
                if (p.y < distTermL2) {
                  distTermL2 = p.y;
                  tpL2.x = p.x;
                  tpL2.y = 0;
                }
                if (Ymax - p.y < distTermU2) {
                  distTermU2 = Ymax - p.y;
                  tpU2.x = p.x;
                  tpU2.y = Ymax;
                }
              }
            }
          }
          if (distTermL * alpha + distTermU2 * alpha2 < distTermU * alpha + distTermL2 * alpha2) {
            mydesign.Terminals.at(i).center = tpL1;
            mydesign.Terminals.at(cp).center = tpU2;
          } else {
            mydesign.Terminals.at(i).center = tpU1;
            mydesign.Terminals.at(cp).center = tpL2;
          }
        } else {
          logger->error("Placer-Error: incorrect axis direction");
        }
      }
    } else {  // not in symmetry group
      int tar = -1;
      for (unsigned int j = 0; j < mydesign.Port_Location.size(); j++) {
        if (mydesign.Port_Location.at(j).tid == (int)i) {
          tar = j;
          break;
        }
      }
      if (tar != -1) {  // specifiy PortLocation constraint
        int x1 = Xmax / 3, x2 = Xmax * 2 / 3, x3 = Xmax;
        int y1 = Ymax / 3, y2 = Ymax * 2 / 3, y3 = Ymax;
        placerDB::point tp;
        pos.clear();
        for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
          if (ci.type == placerDB::Block) {
            bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
            for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
              p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
              if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
              if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
              p += bp;
              pos.push_back(p);
            }
          }
        }
        int shot = -1;
        int distTerm = INT_MAX;
        for (unsigned int k = 0; k < pos.size(); k++) {
          p = pos.at(k);
          // Bmark {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT};
          switch (mydesign.Port_Location.at(tar).pos) {
            case placerDB::TL:
              if (p.x >= 0 and p.x <= x1) {
                if (Ymax - p.y < distTerm) {
                  distTerm = Ymax - p.y;
                  shot = k;
                  tp = {p.x, Ymax};
                }
              } else {
                if (std::abs(p.x - 0) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - 0) + Ymax - p.y;
                  shot = k;
                  tp = {0, Ymax};
                }
                if (std::abs(p.x - x1) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x1) + Ymax - p.y;
                  shot = k;
                  tp = {x1, Ymax};
                }
              }
              break;
            case placerDB::TC:
              if (p.x >= x1 and p.x <= x2) {
                if (Ymax - p.y < distTerm) {
                  distTerm = Ymax - p.y;
                  shot = k;
                  tp = {p.x, Ymax};
                }
              } else {
                if (std::abs(p.x - x2) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x2) + Ymax - p.y;
                  shot = k;
                  tp = {x2, Ymax};
                }
                if (std::abs(p.x - x1) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x1) + Ymax - p.y;
                  shot = k;
                  tp = {x1, Ymax};
                }
              }
              break;
            case placerDB::TR:
              if (p.x >= x2 and p.x <= x3) {
                if (Ymax - p.y < distTerm) {
                  distTerm = Ymax - p.y;
                  shot = k;
                  tp = {p.x, Ymax};
                }
              } else {
                if (std::abs(p.x - x2) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x2) + Ymax - p.y;
                  shot = k;
                  tp = {x2, Ymax};
                }
                if (std::abs(p.x - x3) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x3) + Ymax - p.y;
                  shot = k;
                  tp = {x3, Ymax};
                }
              }
              break;
            case placerDB::RT:
              if (p.y >= y2 and p.y <= y3) {
                if (Xmax - p.x < distTerm) {
                  distTerm = Xmax - p.x;
                  shot = k;
                  tp = {Xmax, p.y};
                }
              } else {
                if (std::abs(p.y - y2) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y2) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y2};
                }
                if (std::abs(p.y - y3) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y3) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y3};
                }
              }
              break;
            case placerDB::RC:
              if (p.y >= y1 and p.y <= y2) {
                if (Xmax - p.x < distTerm) {
                  distTerm = Xmax - p.x;
                  shot = k;
                  tp = {Xmax, p.y};
                }
              } else {
                if (std::abs(p.y - y2) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y2) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y2};
                }
                if (std::abs(p.y - y1) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y1) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y1};
                }
              }
              break;
            case placerDB::RB:
              if (p.y >= 0 and p.y <= y1) {
                if (Xmax - p.x < distTerm) {
                  distTerm = Xmax - p.x;
                  shot = k;
                  tp = {Xmax, p.y};
                }
              } else {
                if (std::abs(p.y - 0) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - 0) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, 0};
                }
                if (std::abs(p.y - y1) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y1) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y1};
                }
              }
              break;
            case placerDB::BL:
              if (p.x >= 0 and p.x <= x1) {
                if (p.y < distTerm) {
                  distTerm = p.y;
                  shot = k;
                  tp = {p.x, 0};
                }
              } else {
                if (std::abs(p.x - 0) + p.y < distTerm) {
                  distTerm = std::abs(p.x - 0) + p.y;
                  shot = k;
                  tp = {0, 0};
                }
                if (std::abs(p.x - x1) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x1) + p.y;
                  shot = k;
                  tp = {x1, 0};
                }
              }
              break;
            case placerDB::BC:
              if (p.x >= x1 and p.x <= x2) {
                if (p.y < distTerm) {
                  distTerm = p.y;
                  shot = k;
                  tp = {p.x, 0};
                }
              } else {
                if (std::abs(p.x - x2) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x2) + p.y;
                  shot = k;
                  tp = {x2, 0};
                }
                if (std::abs(p.x - x1) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x1) + p.y;
                  shot = k;
                  tp = {x1, 0};
                }
              }
              break;
            case placerDB::BR:
              if (p.x >= x2 and p.x <= x3) {
                if (p.y < distTerm) {
                  distTerm = p.y;
                  shot = k;
                  tp = {p.x, 0};
                }
              } else {
                if (std::abs(p.x - x2) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x2) + p.y;
                  shot = k;
                  tp = {x2, 0};
                }
                if (std::abs(p.x - x3) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x3) + p.y;
                  shot = k;
                  tp = {x3, 0};
                }
              }
              break;
            case placerDB::LT:
              if (p.y >= y2 and p.y <= y3) {
                if (p.x < distTerm) {
                  distTerm = p.x;
                  shot = k;
                  tp = {0, p.y};
                }
              } else {
                if (std::abs(p.y - y2) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y2) + p.x;
                  shot = k;
                  tp = {0, y2};
                }
                if (std::abs(p.y - y3) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y3) + p.x;
                  shot = k;
                  tp = {0, y3};
                }
              }
              break;
            case placerDB::LC:
              if (p.y >= y1 and p.y <= y2) {
                if (p.x < distTerm) {
                  distTerm = p.x;
                  shot = k;
                  tp = {0, p.y};
                }
              } else {
                if (std::abs(p.y - y2) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y2) + p.x;
                  shot = k;
                  tp = {0, y2};
                }
                if (std::abs(p.y - y1) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y1) + p.x;
                  shot = k;
                  tp = {0, y1};
                }
              }
              break;
            case placerDB::LB:
              if (p.y >= 0 and p.y <= y1) {
                if (p.x < distTerm) {
                  distTerm = p.x;
                  shot = k;
                  tp = {0, p.y};
                }
              } else {
                if (std::abs(p.y - 0) + p.x < distTerm) {
                  distTerm = std::abs(p.y - 0) + p.x;
                  shot = k;
                  tp = {0, 0};
                }
                if (std::abs(p.y - y1) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y1) + p.x;
                  shot = k;
                  tp = {0, y1};
                }
              }
              break;
            default:
              logger->warn("Placer-Warning: incorrect port position");
          }
        }
        if (shot != -1) {
          mydesign.Terminals.at(i).center = tp;
        }
      } else {  // no constraint
        placerDB::point tp;
        int distTerm = INT_MAX;
        for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
          if (ci.type == placerDB::Block) {
            if (mydesign.Blocks[ci.iter2][0].blockPins.size() == 0) continue;
            bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
            for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
              p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
              if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
              if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
              p += bp;
              if (p.x < distTerm) {
                distTerm = p.x;
                tp = {0, p.y};
              }
              if (Xmax - p.x < distTerm) {
                distTerm = Xmax - p.x;
                tp = {Xmax, p.y};
              }
              if (p.y < distTerm) {
                distTerm = p.y;
                tp = {p.x, 0};
              }
              if (Ymax - p.y < distTerm) {
                distTerm = Ymax - p.y;
                tp = {p.x, Ymax};
              }
            }
          }
        }
        mydesign.Terminals.at(i).center = tp;
      }
    }
  }
}

void ILP_solver::UpdateSymmetryNetInfoAnalytical(design& mydesign, PnRDB::hierNode& node, int i, int SBidx, placerDB::Smark axis_dir) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.UpdateSymmetryNetInfo");

  int axis_coor = 0;
  if (axis_dir == placerDB::V) {
    if (mydesign.SBlocks[SBidx].selfsym.size() > 0) {
      // self sym x axis coordinate
      axis_coor = Blocks[mydesign.SBlocks[SBidx].selfsym[0].first].x + mydesign.Blocks[mydesign.SBlocks[SBidx].selfsym[0].first][0].width / 2;
    } else {
      // sym pair x axis coordinate
      axis_coor = Blocks[mydesign.SBlocks[SBidx].sympair[0].first].x / 2 + mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].first][0].width / 4 +
                  Blocks[mydesign.SBlocks[SBidx].sympair[0].second].x / 2 + mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].second][0].width / 4;
    }
  } else if (axis_dir == placerDB::H) {
    if (mydesign.SBlocks[SBidx].selfsym.size() > 0) {
      axis_coor = Blocks[mydesign.SBlocks[SBidx].selfsym[0].first].y + mydesign.Blocks[mydesign.SBlocks[SBidx].selfsym[0].first][0].height / 2;
    } else {
      axis_coor = Blocks[mydesign.SBlocks[SBidx].sympair[0].first].y / 2 + mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].first][0].height / 4 +
                  Blocks[mydesign.SBlocks[SBidx].sympair[0].second].y / 2 + mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].second][0].height / 4;
    }
  } else {
    logger->error("Placer-Error: incorrect symmetry axis direction");
  }
  string net1 = mydesign.SNets.at(i).net1.name;
  string net2 = mydesign.SNets.at(i).net2.name;
  for (std::vector<PnRDB::net>::iterator it = node.Nets.begin(); it != node.Nets.end(); ++it) {
    if (it->name.compare(net1) == 0 || it->name.compare(net2) == 0) {
      it->axis_dir = PnRDB::Smark(int(axis_dir));
      it->axis_coor = axis_coor;
    }
  }
}

void ILP_solver::UpdateHierNodeAnalytical(design& mydesign, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo) {
  node.width = UR.x;
  node.height = UR.y;
  node.HPWL = HPWL;
  node.HPWL_extend = HPWL_extend;
  node.HPWL_extend_wo_terminal = node.HPWL_extend - HPWL_extend_terminal;  // HPWL without terminal nets' HPWL
  node.area_norm = area_norm;
  node.HPWL_norm = HPWL_norm;
  node.constraint_penalty = constraint_penalty;
  node.cost = cost;

  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    node.Blocks.at(i).selectedInstance = 0;
    node.HPWL_extend += node.Blocks[i].instance[node.Blocks.at(i).selectedInstance].HPWL_extend_wo_terminal;
    node.HPWL_extend_wo_terminal += node.Blocks[i].instance[node.Blocks.at(i).selectedInstance].HPWL_extend_wo_terminal;
    placerDB::Omark ort;
    if (Blocks[i].H_flip) {
      if (Blocks[i].V_flip)
        ort = placerDB::S;
      else
        ort = placerDB::FN;
    } else {
      if (Blocks[i].V_flip)
        ort = placerDB::FS;
      else
        ort = placerDB::N;
    }
    UpdateBlockinHierNode(mydesign, ort, node, i, 0, drcInfo);
  }
  UpdateTerminalinHierNode(mydesign, node, drcInfo);
  for (unsigned int i = 0; i < mydesign.SNets.size(); ++i) {
    int SBidx = mydesign.SNets.at(i).SBidx;
    placerDB::Smark axis_dir = mydesign.SBlocks[i].axis_dir;
    UpdateSymmetryNetInfoAnalytical(mydesign, node, i, SBidx, axis_dir);
  }
}

/**
void ILP_solver::PlotPlacementAnalytical(design& mydesign, string outfile, bool plot_pin, bool plot_terminal, bool plot_net) {
  // cout << "Placer-Info: create gnuplot file" << endl;
  placerDB::point p, bp;
  if(!mydesign.is_first_ILP){
    ofstream f("Results/" + mydesign.name + "_gds/" + mydesign.name + ".csv", std::ios::app);
    if(f.is_open()){
      f << mydesign.placement_id << " " << area << " " << HPWL << endl;
    }
    f.close();
  }

  ofstream fout;
  vector<placerDB::point> p_pin;
  fout.open(outfile.c_str());
  fout << "#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)" << endl;
  fout << "\nset title \" "<< mydesign.name << " #Blocks= " << mydesign.Blocks.size() << ", #Terminals= " << mydesign.Terminals.size() << ", #Nets= " << mydesign.Nets.size()
       << ",Area=" << area << ", HPWL= " << HPWL << " \"" << endl;
  fout << "\nset nokey" << endl;
  fout << "#   Uncomment these two lines starting with \"set\"" << endl;
  fout << "#   to save an EPS file for inclusion into a latex document" << endl;
  fout << "# set terminal postscript eps color solid 20" << endl;
  fout << "# set output \"result.eps\"" << endl << endl;
  fout << "#   Uncomment these two lines starting with \"set\"" << endl;
  fout << "#   to save a PS file for printing" << endl;
  fout << "# set terminal postscript portrait color solid 20" << endl;
  fout << "# set output \"result.ps\"" << endl << endl;

  int bias = 100;
  int range = std::max(UR.x, UR.y) + bias;
  fout << "\nset xrange [" << LL.x - bias << ":" << UR.x + bias << "]" << endl;
  fout << "\nset yrange [" << LL.y - bias << ":" << UR.y + bias << "]" << endl;
  // set labels for blocks
  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    placerDB::point tp;
    tp.x = Blocks[i].x + mydesign.Blocks[i][0].width / 2;
    tp.y = Blocks[i].y + mydesign.Blocks[i][0].height / 2;
    if(mydesign.Blocks[i][0].width>0 && mydesign.Blocks[i][0].height>0)
      fout << "\nset label \"" << mydesign.Blocks[i][0].name << "\" at " << tp.x << " , " << tp.y << " center " << endl;
    if (plot_pin) {
      for (unsigned int j = 0; j < mydesign.Blocks[i][0].blockPins.size(); j++) {
        for (unsigned int k = 0; k < mydesign.Blocks[i][0].blockPins[j].center.size(); k++) {
          placerDB::point newp;
          newp.x = mydesign.Blocks[i][0].blockPins[j].center[k].x;
          newp.y = mydesign.Blocks[i][0].blockPins[j].center[k].y;
          if (Blocks[i].H_flip) newp.x = mydesign.Blocks[i][0].width - newp.x;
          if (Blocks[i].V_flip) newp.y = mydesign.Blocks[i][0].height - newp.y;
          newp.x += Blocks[i].x;
          newp.y += Blocks[i].y;
          fout << "\nset label \"" << mydesign.Blocks[i][0].blockPins[j].name << "\" at " << newp.x << " , " << newp.y << endl;
          fout << endl;
        }
      }
    }
  }

  // set labels for terminals
  // cout << "set labels for terminals..." << endl;
  if (plot_terminal) {
    for (const auto& ni : mydesign.Nets) {
      // for each pin
      for (const auto& ci : ni.connected) {
        if (ci.type == placerDB::Terminal) {
          int tno = ci.iter;
          fout << "\nset label \"" << mydesign.Terminals.at(tno).name << "\" at " << mydesign.Terminals.at(tno).center.x << " , "
              << mydesign.Terminals.at(tno).center.y << " center                " << endl;
          break;
        }
      }
    }
  }

  // plot blocks
  fout << "\nplot[:][:] \'-\' with lines linestyle 3";
  if(plot_pin)fout << ", \'-\' with lines linestyle 7";
  if(plot_terminal)fout << ", \'-\' with lines linestyle 1";
  if(plot_net)fout << ", \'-\' with lines linestyle 0";
  fout << endl << endl;
  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    vector<placerDB::point> newp = mydesign.Blocks[i][0].boundary.polygon;
    fout << "# block " << mydesign.Blocks[i][0].name << " select " << 0 << " bsize " << newp.size() << endl;
    for (unsigned int it = 0; it < newp.size(); it++) {
      fout << "\t" << newp[it].x + Blocks[i].x << "\t" << newp[it].y + Blocks[i].y << endl;
    }
    fout << "\t" << newp[0].x + Blocks[i].x << "\t" << newp[0].y + Blocks[i].y << endl;
    fout << endl;
  }
  fout << "\nEOF" << endl;

  // plot block pins
  if(plot_pin){
    for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
      for (unsigned int j = 0; j < mydesign.Blocks[i][0].blockPins.size(); j++) {
        for (unsigned int k = 0; k < mydesign.Blocks[i][0].blockPins[j].boundary.size(); k++) {
          for (unsigned int it = 0; it < mydesign.Blocks[i][0].blockPins[j].boundary[k].polygon.size(); it++) {
            placerDB::point newp;
            newp.x = mydesign.Blocks[i][0].blockPins[j].boundary[k].polygon[it].x;
            newp.y = mydesign.Blocks[i][0].blockPins[j].boundary[k].polygon[it].y;
            if (Blocks[i].H_flip) newp.x = mydesign.Blocks[i][0].width - newp.x;
            if (Blocks[i].V_flip) newp.y = mydesign.Blocks[i][0].height - newp.y;
            newp.x += Blocks[i].x;
            newp.y += Blocks[i].y;
            fout << "\t" << newp.x << "\t" << newp.y << endl;
          }
          placerDB::point newp;
          newp.x = mydesign.Blocks[i][0].blockPins[j].boundary[k].polygon[0].x;
          newp.y = mydesign.Blocks[i][0].blockPins[j].boundary[k].polygon[0].y;
          if (Blocks[i].H_flip) newp.x = mydesign.Blocks[i][0].width - newp.x;
          if (Blocks[i].V_flip) newp.y = mydesign.Blocks[i][0].height - newp.y;
          newp.x += Blocks[i].x;
          newp.y += Blocks[i].y;
          fout << "\t" << newp.x << "\t" << newp.y << endl;
          fout << endl;
        }
      }
    }
    fout << "\nEOF" << endl;
  }

  // plot terminals
  if (plot_terminal) {
    for (const auto& ni : mydesign.Nets) {
      // for each pin
      for (const auto& ci : ni.connected) {
        if (ci.type == placerDB::Terminal) {
          int tno = ci.iter;
          int bias = 20;
          fout << endl;
          fout << "\t" << mydesign.Terminals.at(tno).center.x - bias << "\t" << mydesign.Terminals.at(tno).center.y - bias << endl;
          fout << "\t" << mydesign.Terminals.at(tno).center.x - bias << "\t" << mydesign.Terminals.at(tno).center.y + bias << endl;
          fout << "\t" << mydesign.Terminals.at(tno).center.x + bias << "\t" << mydesign.Terminals.at(tno).center.y + bias << endl;
          fout << "\t" << mydesign.Terminals.at(tno).center.x + bias << "\t" << mydesign.Terminals.at(tno).center.y - bias << endl;
          fout << "\t" << mydesign.Terminals.at(tno).center.x - bias << "\t" << mydesign.Terminals.at(tno).center.y - bias << endl;
          break;
        }
      }
    }
    fout << "\nEOF" << endl;
  }

  // plot nets
  if(plot_net){
    for (vector<placerDB::net>::iterator ni = mydesign.Nets.begin(); ni != mydesign.Nets.end(); ++ni) {
      placerDB::point tp;
      vector<placerDB::point> pins;
      // for each pin
      for (const auto& ci : ni->connected) {
        if (ci.type == placerDB::Block) {
          if (mydesign.Blocks[ci.iter2][0].blockPins.size() > 0) {
            if (mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size() > 0) {
              tp.x = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[0].x;
              tp.y = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[0].y;
              if (Blocks[ci.iter2].H_flip) tp.x = mydesign.Blocks[ci.iter2][0].width - tp.x;
              if (Blocks[ci.iter2].V_flip) tp.y = mydesign.Blocks[ci.iter2][0].height - tp.y;
              tp.x += Blocks[ci.iter2].x;
              tp.y += Blocks[ci.iter2].y;
              pins.push_back(tp);
            }
          } else {
            tp.x = mydesign.Blocks[ci.iter2][0].width / 2;
            tp.y = mydesign.Blocks[ci.iter2][0].height / 2;
            if (Blocks[ci.iter2].H_flip) tp.x = mydesign.Blocks[ci.iter2][0].width - tp.x;
            if (Blocks[ci.iter2].V_flip) tp.y = mydesign.Blocks[ci.iter2][0].height - tp.y;
            tp.x += Blocks[ci.iter2].x;
            tp.y += Blocks[ci.iter2].y;
            pins.push_back(tp);
          }
        } else if (ci.type == placerDB::Terminal) {
          pins.push_back(mydesign.Terminals.at(ci.iter).center);
        }
      }
      fout << "\n#Net: " << ni->name << endl;
      if (pins.size() >= 2) {
        for (int i = 1; i < (int)pins.size(); i++) {
          fout << "\t" << pins.at(0).x << "\t" << pins.at(0).y << endl;
          fout << "\t" << pins.at(i).x << "\t" << pins.at(i).y << endl;
          fout << "\t" << pins.at(0).x << "\t" << pins.at(0).y << endl << endl;
        }
      }
    }
    fout << "\nEOF" << endl;
  }
  fout << endl << "pause -1 \'Press any key\'";
  fout.close();
}**/

