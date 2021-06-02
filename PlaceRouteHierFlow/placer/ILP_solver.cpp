#include "ILP_solver.h"
#include <stdexcept>

ILP_solver::ILP_solver() {}

ILP_solver::ILP_solver(design& mydesign) {
  LL.x = INT_MAX;
  LL.y = INT_MAX;
  UR.x = INT_MIN;
  UR.x = INT_MIN;
  Blocks.resize(mydesign.Blocks.size());
  Aspect_Ratio_weight = mydesign.Aspect_Ratio_weight;
  memcpy(Aspect_Ratio, mydesign.Aspect_Ratio, sizeof(mydesign.Aspect_Ratio));
  memcpy(placement_box, mydesign.placement_box, sizeof(mydesign.placement_box));
}

ILP_solver::ILP_solver(const ILP_solver& solver) {
  Blocks = solver.Blocks;
  LL = solver.LL;
  UR = solver.UR;
  area = solver.area;
  HPWL = solver.HPWL;
  cost = solver.cost;
  constraint_penalty = solver.constraint_penalty;
  area_norm = solver.area_norm;
  HPWL_norm = solver.HPWL_norm;
  ratio = solver.ratio;
  linear_const = solver.linear_const;
  multi_linear_const = solver.multi_linear_const;
  Aspect_Ratio_weight = solver.Aspect_Ratio_weight;
  memcpy(Aspect_Ratio, solver.Aspect_Ratio, sizeof(solver.Aspect_Ratio));
  memcpy(placement_box, solver.placement_box, sizeof(solver.placement_box));
}

ILP_solver& ILP_solver::operator=(const ILP_solver& solver) {
  Blocks = solver.Blocks;
  LL = solver.LL;
  UR = solver.UR;
  area = solver.area;
  cost = solver.cost;
  constraint_penalty = solver.constraint_penalty;
  HPWL = solver.HPWL;
  area_norm = solver.area_norm;
  HPWL_norm = solver.HPWL_norm;
  ratio = solver.ratio;
  multi_linear_const = solver.multi_linear_const;
  Aspect_Ratio_weight = solver.Aspect_Ratio_weight;
  memcpy(Aspect_Ratio, solver.Aspect_Ratio, sizeof(solver.Aspect_Ratio));
  memcpy(placement_box, solver.placement_box, sizeof(solver.placement_box));
  return *this;
}

void ILP_solver::lpsolve_logger(lprec* lp, void* userhandle, char* buf) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.lpsolve_logger");

  // Strip leading newline
  while ((unsigned char)*buf == '\n') buf++;
  // Log non-empty lines
  if (*buf != '\0') logger->debug("Placer lpsolve: {0}", buf);
}

double ILP_solver::GenerateValidSolution(design& mydesign, SeqPair& curr_sp, PnRDB::Drc_info& drcInfo) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.GenerateValidSolution");

  // each block has 4 vars, x, y, H_flip, V_flip;
  unsigned int N_var = mydesign.Blocks.size() * 4 + mydesign.Nets.size() * 2;
  // i*4+1: x
  // i*4+2:y
  // i*4+3:H_flip
  // i*4+4:V_flip
  lprec* lp = make_lp(0, N_var);
  set_verbose(lp, IMPORTANT);
  put_logfunc(lp, &ILP_solver::lpsolve_logger, NULL);
  //set_outputfile(lp, const_cast<char*>("/dev/null"));

  // set integer constraint, H_flip and V_flip can only be 0 or 1
  for (int i = 0; i < mydesign.Blocks.size(); i++) {
    set_int(lp, i * 4 + 1, TRUE);
    set_int(lp, i * 4 + 2, TRUE);
    set_int(lp, i * 4 + 3, TRUE);
    set_int(lp, i * 4 + 4, TRUE);
    set_binary(lp, i * 4 + 3, TRUE);
    set_binary(lp, i * 4 + 4, TRUE);
  }

  // overlap constraint
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    int i_pos_index = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), i) - curr_sp.posPair.begin();
    int i_neg_index = find(curr_sp.negPair.begin(), curr_sp.negPair.end(), i) - curr_sp.negPair.begin();
    for (unsigned int j = i + 1; j < mydesign.Blocks.size(); j++) {
      int j_pos_index = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), j) - curr_sp.posPair.begin();
      int j_neg_index = find(curr_sp.negPair.begin(), curr_sp.negPair.end(), j) - curr_sp.negPair.begin();
      if (i_pos_index < j_pos_index) {
        if (i_neg_index < j_neg_index) {
          // i is left of j
          double sparserow[2] = {1, -1};
          int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
          if (!add_constraintex(lp, 2, sparserow, colno, LE, -mydesign.Blocks[i][curr_sp.selected[i]].width - mydesign.bias_Hgraph)) logger->error("error");
        } else {
          // i is above j
          double sparserow[2] = {1, -1};
          int colno[2] = {int(i) * 4 + 2, int(j) * 4 + 2};
          if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[j][curr_sp.selected[j]].height + mydesign.bias_Vgraph)) logger->error("error");
        }
      } else {
        if (i_neg_index < j_neg_index) {
          // i is be low j
          double sparserow[2] = {1, -1};
          int colno[2] = {int(i) * 4 + 2, int(j) * 4 + 2};
          if (!add_constraintex(lp, 2, sparserow, colno, LE, -mydesign.Blocks[i][curr_sp.selected[i]].height - mydesign.bias_Vgraph)) logger->error("error");
        } else {
          // i is right of j
          double sparserow[2] = {1, -1};
          int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
          if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[j][curr_sp.selected[j]].width + mydesign.bias_Hgraph)) logger->error("error");
        }
      }
    }
  }

  // x>=0, y>=0
  for (auto id : curr_sp.negPair) {
    if (id < int(mydesign.Blocks.size())) {
      // x>=0
      {
        double sparserow[1] = {1};
        int colno[1] = {id * 4 + 1};
        if (!add_constraintex(lp, 1, sparserow, colno, GE, 0)) logger->error("error");
      }
      // y>=0
      {
        double sparserow[1] = {1};
        int colno[1] = {id * 4 + 2};
        if (!add_constraintex(lp, 1, sparserow, colno, GE, 0)) logger->error("error");
      }
    }
  }

  // symmetry block constraint
  for (auto SPBlock : mydesign.SPBlocks) {
    if (SPBlock.axis_dir == placerDB::H) {
      // constraint inside one pair
      for (int i = 0; i < SPBlock.sympair.size(); i++) {
        int first_id = SPBlock.sympair[i].first, second_id = SPBlock.sympair[i].second;
        // each pair has opposite V flip
        {
          double sparserow[2] = {1, 1};
          int colno[2] = {first_id * 4 + 4, second_id * 4 + 4};
          add_constraintex(lp, 2, sparserow, colno, EQ, 1);
        }
        // x center of blocks in each pair are the same
        {
          double sparserow[2] = {1, -1};
          int colno[2] = {first_id * 4 + 1, second_id * 4 + 1};
          int first_x_center = mydesign.Blocks[first_id][curr_sp.selected[first_id]].width / 2;
          int second_x_center = mydesign.Blocks[second_id][curr_sp.selected[second_id]].width / 2;
          add_constraintex(lp, 2, sparserow, colno, EQ, -first_x_center + second_x_center);
        }
      }

      // constraint between two pairs
      for (int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        int i_first_y_center = mydesign.Blocks[i_first_id][curr_sp.selected[i_first_id]].height / 4;
        int i_second_y_center = mydesign.Blocks[i_second_id][curr_sp.selected[i_second_id]].height / 4;
        for (unsigned int j = i + 1; j < SPBlock.sympair.size(); j++) {
          // the y center of the two pairs are the same
          int j_first_id = SPBlock.sympair[j].first, j_second_id = SPBlock.sympair[j].second;
          int j_first_y_center = mydesign.Blocks[j_first_id][curr_sp.selected[j_first_id]].height / 4;
          int j_second_y_center = mydesign.Blocks[j_second_id][curr_sp.selected[j_second_id]].height / 4;
          double sparserow[4] = {0.5, 0.5, -0.5, -0.5};
          int colno[4] = {i_first_id * 4 + 2, i_second_id * 4 + 2, j_first_id * 4 + 2, j_second_id * 4 + 2};
          int bias = -i_first_y_center - i_second_y_center + j_first_y_center + j_second_y_center;
          add_constraintex(lp, 4, sparserow, colno, EQ, bias);
        }
      }

      // constraint between a pair and a selfsym
      for (int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        int i_first_y_center = mydesign.Blocks[i_first_id][curr_sp.selected[i_first_id]].height / 4;
        int i_second_y_center = mydesign.Blocks[i_second_id][curr_sp.selected[i_second_id]].height / 4;
        for (unsigned int j = 0; j < SPBlock.selfsym.size(); j++) {
          // the y center of the pair and the selfsym are the same
          int j_id = SPBlock.selfsym[j].first;
          int j_y_center = mydesign.Blocks[j_id][curr_sp.selected[j_id]].height / 2;
          double sparserow[3] = {0.5, 0.5, -1};
          int colno[3] = {i_first_id * 4 + 2, i_second_id * 4 + 2, j_id * 4 + 2};
          int bias = -i_first_y_center - i_second_y_center + j_y_center;
          add_constraintex(lp, 3, sparserow, colno, EQ, bias);
        }
      }

      // constraint between two selfsyms
      for (int i = 0; i < SPBlock.selfsym.size(); i++) {
        int i_id = SPBlock.selfsym[i].first;
        int i_y_center = mydesign.Blocks[i_id][curr_sp.selected[i_id]].height / 2;
        for (unsigned int j = i + 1; j < SPBlock.selfsym.size(); j++) {
          // the y center of the two selfsyms are the same
          int j_id = SPBlock.selfsym[j].first;
          int j_y_center = mydesign.Blocks[j_id][curr_sp.selected[j_id]].height / 2;
          double sparserow[2] = {1, -1};
          int colno[2] = {i_id * 4 + 2, j_id * 4 + 2};
          int bias = -i_y_center + j_y_center;
          add_constraintex(lp, 2, sparserow, colno, EQ, bias);
        }
      }
    } else {
      // axis_dir==V
      // constraint inside one pair
      for (int i = 0; i < SPBlock.sympair.size(); i++) {
        int first_id = SPBlock.sympair[i].first, second_id = SPBlock.sympair[i].second;
        // each pair has opposite H flip
        {
          double sparserow[2] = {1, 1};
          int colno[2] = {first_id * 4 + 3, second_id * 4 + 3};
          add_constraintex(lp, 2, sparserow, colno, EQ, 1);
        }
        // y center of blocks in each pair are the same
        {
          double sparserow[2] = {1, -1};
          int colno[2] = {first_id * 4 + 2, second_id * 4 + 2};
          int first_y_center = mydesign.Blocks[first_id][curr_sp.selected[first_id]].height / 2;
          int second_y_center = mydesign.Blocks[second_id][curr_sp.selected[second_id]].height / 2;
          add_constraintex(lp, 2, sparserow, colno, EQ, -first_y_center + second_y_center);
        }
      }

      // constraint between two pairs
      for (int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        int i_first_x_center = mydesign.Blocks[i_first_id][curr_sp.selected[i_first_id]].width / 4;
        int i_second_x_center = mydesign.Blocks[i_second_id][curr_sp.selected[i_second_id]].width / 4;
        for (unsigned int j = i + 1; j < SPBlock.sympair.size(); j++) {
          // the x center of the two pairs are the same
          int j_first_id = SPBlock.sympair[j].first, j_second_id = SPBlock.sympair[j].second;
          int j_first_x_center = mydesign.Blocks[j_first_id][curr_sp.selected[j_first_id]].width / 4;
          int j_second_x_center = mydesign.Blocks[j_second_id][curr_sp.selected[j_second_id]].width / 4;
          double sparserow[4] = {0.5, 0.5, -0.5, -0.5};
          int colno[4] = {i_first_id * 4 + 1, i_second_id * 4 + 1, j_first_id * 4 + 1, j_second_id * 4 + 1};
          int bias = -i_first_x_center - i_second_x_center + j_first_x_center + j_second_x_center;
          add_constraintex(lp, 4, sparserow, colno, EQ, bias);
        }
      }

      // constraint between a pair and a selfsym
      for (int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        int i_first_x_center = mydesign.Blocks[i_first_id][curr_sp.selected[i_first_id]].width / 4;
        int i_second_x_center = mydesign.Blocks[i_second_id][curr_sp.selected[i_second_id]].width / 4;
        for (unsigned int j = 0; j < SPBlock.selfsym.size(); j++) {
          // the x center of the pair and the selfsym are the same
          int j_id = SPBlock.selfsym[j].first;
          int j_x_center = mydesign.Blocks[j_id][curr_sp.selected[j_id]].width / 2;
          double sparserow[3] = {0.5, 0.5, -1};
          int colno[3] = {i_first_id * 4 + 1, i_second_id * 4 + 1, j_id * 4 + 1};
          int bias = -i_first_x_center - i_second_x_center + j_x_center;
          add_constraintex(lp, 3, sparserow, colno, EQ, bias);
        }
      }

      // constraint between two selfsyms
      for (int i = 0; i < SPBlock.selfsym.size(); i++) {
        int i_id = SPBlock.selfsym[i].first;
        int i_x_center = mydesign.Blocks[i_id][curr_sp.selected[i_id]].width / 2;
        for (unsigned int j = i + 1; j < SPBlock.selfsym.size(); j++) {
          // the x center of the two selfsyms are the same
          int j_id = SPBlock.selfsym[j].first;
          int j_x_center = mydesign.Blocks[j_id][curr_sp.selected[j_id]].width / 2;
          double sparserow[2] = {1, -1};
          int colno[2] = {i_id * 4 + 1, j_id * 4 + 1};
          int bias = -i_x_center + j_x_center;
          add_constraintex(lp, 2, sparserow, colno, EQ, bias);
        }
      }
    }
  }

  // align block constraint
  for (auto alignment_unit : mydesign.Align_blocks) {
    for (unsigned int j = 0; j < alignment_unit.blocks.size() - 1; j++) {
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
  }

  // set_add_rowmode(lp, FALSE);
  {
    double row[N_var + 1] = {0};
    ConstGraph const_graph;

    // add HPWL in cost
    for (int i = 0; i < mydesign.Nets.size(); i++) {
      vector<pair<int, int>> blockids;
      for (unsigned int j = 0; j < mydesign.Nets[i].connected.size(); j++) {
        if (mydesign.Nets[i].connected[j].type == placerDB::Block &&
            (blockids.size() == 0 || mydesign.Nets[i].connected[j].iter2 != curr_sp.negPair[blockids.back().first]))
          blockids.push_back(std::make_pair(find(curr_sp.negPair.begin(), curr_sp.negPair.end(), mydesign.Nets[i].connected[j].iter2) - curr_sp.negPair.begin(),
                                            mydesign.Nets[i].connected[j].iter));
      }
      if (blockids.size() < 2) continue;
      sort(blockids.begin(), blockids.end(), [](const pair<int, int>& a, const pair<int, int>& b) { return a.first <= b.first; });
    }

    // add area in cost
    int URblock_pos_id = 0, URblock_neg_id = 0;
    int estimated_width = 0, estimated_height = 0;
    for (unsigned int i = curr_sp.negPair.size() - 1; i >= 0; i--) {
      if (curr_sp.negPair[i] < int(mydesign.Blocks.size())) {
        URblock_neg_id = i;
        break;
      }
    }
    URblock_pos_id = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), curr_sp.negPair[URblock_neg_id]) - curr_sp.posPair.begin();
    // estimate width
    for (int i = URblock_pos_id; i >= 0; i--) {
      if (curr_sp.posPair[i] < int(mydesign.Blocks.size())) {
        estimated_width += mydesign.Blocks[curr_sp.posPair[i]][curr_sp.selected[curr_sp.posPair[i]]].width;
      }
    }
    // add estimated area
    row[curr_sp.negPair[URblock_neg_id] * 4 + 2] += estimated_width / 2;
    // estimate height
    for (unsigned int i = URblock_pos_id; i < curr_sp.posPair.size(); i++) {
      if (curr_sp.posPair[i] < int(mydesign.Blocks.size())) {
        estimated_height += mydesign.Blocks[curr_sp.posPair[i]][curr_sp.selected[curr_sp.posPair[i]]].height;
      }
    }
    // add estimated area
    row[curr_sp.negPair[URblock_neg_id] * 4 + 1] += estimated_height / 2;

    set_obj_fn(lp, row);
    set_minim(lp);
    set_timeout(lp, 1);
    int ret = solve(lp);
    if (ret != 0 && ret != 1) {
      delete_lp(lp);
      return -1;
    }
  }

  double var[N_var];
  get_variables(lp, var);
  delete_lp(lp);
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
  for (int i = 0; i < mydesign.Blocks.size(); i++) {
    Blocks[i].x = var[i * 4];
    Blocks[i].y = var[i * 4 + 1];
    roundup(Blocks[i].x, x_pitch);
    roundup(Blocks[i].y, y_pitch);
    Blocks[i].H_flip = var[i * 4 + 2];
    Blocks[i].V_flip = var[i * 4 + 3];
  }
  auto hflipVec = curr_sp.GetFlip(true);
  auto vflipVec = curr_sp.GetFlip(false);
  if (!hflipVec.empty() && !vflipVec.empty()) {
    for (unsigned i = 0; i < mydesign.Blocks.size(); i++) {
      Blocks[i].H_flip = hflipVec[i];
      Blocks[i].V_flip = vflipVec[i];
    }
  }

  // calculate LL and UR
  LL.x = INT_MAX, LL.y = INT_MAX;
  UR.x = INT_MIN, UR.y = INT_MIN;
  for (int i = 0; i < mydesign.Blocks.size(); i++) {
    LL.x = std::min(LL.x, Blocks[i].x);
    LL.y = std::min(LL.y, Blocks[i].y);
    UR.x = std::max(UR.x, Blocks[i].x + mydesign.Blocks[i][curr_sp.selected[i]].width);
    UR.y = std::max(UR.y, Blocks[i].y + mydesign.Blocks[i][curr_sp.selected[i]].height);
  }
  // calculate area
  area = double(UR.x - LL.x) * double(UR.y - LL.y);
  //calculate norm area
  area_norm = area * 0.1 / mydesign.GetMaxBlockAreaSum();
  // calculate ratio
  // ratio = std::max(double(UR.x - LL.x) / double(UR.y - LL.y), double(UR.y - LL.y) / double(UR.x - LL.x));
  ratio = double(UR.x - LL.x) / double(UR.y - LL.y);
  if (ratio < Aspect_Ratio[0] || ratio > Aspect_Ratio[1]) return -1;
  if (placement_box[0] > 0 && (UR.x - LL.x > placement_box[0]) || placement_box[1] > 0 && (UR.y - LL.y > placement_box[1])) return -1;
  // calculate HPWL
  HPWL = 0;
  for (auto neti : mydesign.Nets) {
    int HPWL_min_x = UR.x, HPWL_min_y = UR.y, HPWL_max_x = 0, HPWL_max_y = 0;
    for (auto connectedj : neti.connected) {
      if (connectedj.type == placerDB::Block) {
        int iter2 = connectedj.iter2, iter = connectedj.iter;
        for (auto centerk : mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].center) {
          // calculate contact center
          int pin_x = centerk.x;
          int pin_y = centerk.y;
          if (Blocks[iter2].H_flip) pin_x = mydesign.Blocks[iter2][curr_sp.selected[iter2]].width - pin_x;
          if (Blocks[iter2].V_flip) pin_y = mydesign.Blocks[iter2][curr_sp.selected[iter2]].height - pin_y;
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

  //HPWL norm
  if (!mydesign.Nets.empty()) HPWL_norm = HPWL / mydesign.GetMaxBlockHPWLSum() / double(mydesign.Nets.size());
  // calculate linear constraint
  linear_const = 0;
  std::vector<std::vector<double>> feature_value;
  for (auto neti : mydesign.Nets) {
    std::vector<std::vector<placerDB::point>> center_points;
    for (auto connectedj : neti.connected) {
      if (connectedj.type == placerDB::Block) {
        std::vector<placerDB::point> pos;
        for (auto ci : mydesign.Blocks[connectedj.iter2][curr_sp.selected[connectedj.iter2]].blockPins[connectedj.iter].center) {
          placerDB::point newp;
          newp.x = ci.x;
          newp.y = ci.y;
          if (Blocks[connectedj.iter2].H_flip) newp.x = mydesign.Blocks[connectedj.iter2][curr_sp.selected[connectedj.iter2]].width - newp.x;
          if (Blocks[connectedj.iter2].V_flip) newp.y = mydesign.Blocks[connectedj.iter2][curr_sp.selected[connectedj.iter2]].height - newp.y;
          newp.x += Blocks[connectedj.iter2].x;
          newp.y += Blocks[connectedj.iter2].y;
          pos.push_back(newp);
        }
        center_points.push_back(pos);
      } else if (connectedj.type == placerDB::Terminal) {
        center_points.push_back({mydesign.Terminals[connectedj.iter].center});
      }
    }
    std::vector<double> temp_feature = Calculate_Center_Point_feature(center_points);
    feature_value.push_back(temp_feature);
    double temp_sum = 0;
    for (int j = 0; j < neti.connected.size(); j++) temp_sum += neti.connected[j].alpha * temp_feature[j];
    temp_sum = std::max(temp_sum - neti.upperBound, double(0));
    linear_const += temp_sum;
  }

  if (!mydesign.Nets.empty()) linear_const /= (mydesign.GetMaxBlockHPWLSum() * double(mydesign.Nets.size()));

  // calculate multi linear constraint
  multi_linear_const = 0;
  for (auto constrainti : mydesign.ML_Constraints) {
    double temp_sum = 0;
    for (auto constraintj : constrainti.Multi_linearConst) {
      for (int k = 0; k < constraintj.pins.size(); k++) {
        int index_i = 0;
        int index_j = 0;
        for (int m = 0; m < mydesign.Nets.size(); m++) {
          for (int n = 0; n < mydesign.Nets[m].connected.size(); n++) {
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

  double calculated_cost = CalculateCost(mydesign, curr_sp);
  cost = calculated_cost;
  return calculated_cost;
}

double ILP_solver::CalculateCost(design& mydesign, SeqPair& curr_sp) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.CalculateCost");

  ConstGraph const_graph;
  double cost = 0;

  if (false) {
    cost += area_norm;
    cost += HPWL_norm * const_graph.LAMBDA;
  } else {
    cost += log( area);
    if (HPWL > 0) {
      cost += log( HPWL) * const_graph.LAMBDA;
    }
  }

  double match_cost = 0;
  double max_dim = std::max(UR.x - LL.x, UR.y - LL.y);
  for (auto mbi : mydesign.Match_blocks) {
    match_cost += (abs(Blocks[mbi.blockid1].x + mydesign.Blocks[mbi.blockid1][curr_sp.selected[mbi.blockid1]].width / 2 - Blocks[mbi.blockid2].x -
                      mydesign.Blocks[mbi.blockid2][curr_sp.selected[mbi.blockid2]].width / 2) +
                  abs(Blocks[mbi.blockid1].y + mydesign.Blocks[mbi.blockid1][curr_sp.selected[mbi.blockid1]].height / 2 - Blocks[mbi.blockid2].y -
                      mydesign.Blocks[mbi.blockid2][curr_sp.selected[mbi.blockid2]].height / 2)) / max_dim ;
  }
  if (!mydesign.Match_blocks.empty()) match_cost /= (mydesign.Match_blocks.size());
  constraint_penalty =
    match_cost * const_graph.BETA +
    linear_const * const_graph.PI +
    multi_linear_const * const_graph.PII;
  cost += constraint_penalty;
  return cost;
}

void ILP_solver::WritePlacement(design& mydesign, SeqPair& curr_sp, string outfile) {
  ofstream fout;
  fout.open(outfile.c_str());
  // cout << "Placer-Info: write placement" << endl;
  fout << "# TAMU blocks 1.0" << endl << endl;
  fout << "DIE {" << LL.x << ", " << LL.y << "} {" << UR.x << "," << UR.y << "}" << endl << endl;
  for (int i = 0; i < mydesign.Blocks.size(); ++i) {
    string ort;
    if (!Blocks[i].H_flip && !Blocks[i].V_flip) {
      ort = "N";
    } else if (Blocks[i].H_flip && !Blocks[i].V_flip) {
      ort = "FN";
    } else if (!Blocks[i].H_flip && Blocks[i].V_flip) {
      ort = "FS";
    } else {
      ort = "S";
    }
    fout << mydesign.Blocks.at(i).back().name << "\t" << Blocks[i].x << "\t" << Blocks[i].y << "\t" << ort << endl;
  }
  fout << endl;
  for (auto ni : mydesign.Nets) {
    // for each pin
    for (auto ci : ni.connected) {
      if (ci.type == placerDB::Terminal) {
        int tno = ci.iter;
        fout << mydesign.Terminals.at(tno).name << "\t" << mydesign.Terminals.at(tno).center.x << "\t" << mydesign.Terminals.at(tno).center.y << endl;
        break;
      }
    }
  }
  fout.close();
}

void ILP_solver::PlotPlacement(design& mydesign, SeqPair& curr_sp, string outfile) {
  // cout << "Placer-Info: create gnuplot file" << endl;
  placerDB::point p, bp;
  ofstream fout;
  vector<placerDB::point> p_pin;
  fout.open(outfile.c_str());
  fout << "#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)" << endl;
  fout << "\nset title\" #Blocks= " << mydesign.Blocks.size() << ", #Terminals= " << mydesign.Terminals.size() << ", #Nets= " << mydesign.Nets.size()
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

  int bias = 50;
  int range = std::max(UR.x, UR.y) + bias;
  fout << "\nset xrange [" << LL.x - bias << ":" << UR.x + bias << "]" << endl;
  fout << "\nset yrange [" << LL.y - bias << ":" << UR.y + bias << "]" << endl;
  // set labels for blocks
  for (int i = 0; i < mydesign.Blocks.size(); ++i) {
    placerDB::point tp;
    tp.x = Blocks[i].x + mydesign.Blocks[i][curr_sp.selected[i]].width / 2;
    tp.y = Blocks[i].y + mydesign.Blocks[i][curr_sp.selected[i]].height / 2;
    fout << "\nset label \"" << mydesign.Blocks[i][curr_sp.selected[i]].name << "\" at " << tp.x << " , " << tp.y << " center " << endl;
    for (unsigned int j = 0; j < mydesign.Blocks[i][curr_sp.selected[i]].blockPins.size(); j++) {
      for (unsigned int k = 0; k < mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].center.size(); k++) {
        placerDB::point newp;
        newp.x = mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].center[k].x;
        newp.y = mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].center[k].y;
        if (Blocks[i].H_flip) newp.x = mydesign.Blocks[i][curr_sp.selected[i]].width - newp.x;
        if (Blocks[i].V_flip) newp.y = mydesign.Blocks[i][curr_sp.selected[i]].height - newp.y;
        newp.x += Blocks[i].x;
        newp.y += Blocks[i].y;
        fout << "\nset label \"" << mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].name << "\" at " << newp.x << " , " << newp.y << endl;
        fout << endl;
      }
    }
  }

  // set labels for terminals
  // cout << "set labels for terminals..." << endl;
  for (auto ni : mydesign.Nets) {
    // for each pin
    for (auto ci : ni.connected) {
      if (ci.type == placerDB::Terminal) {
        int tno = ci.iter;
        fout << "\nset label \"" << mydesign.Terminals.at(tno).name << "\" at " << mydesign.Terminals.at(tno).center.x << " , "
             << mydesign.Terminals.at(tno).center.y << " center                " << endl;
        break;
      }
    }
  }

  // plot blocks
  fout << "\nplot[:][:] \'-\' with lines linestyle 3, \'-\' with lines linestyle 7, \'-\' with lines linestyle 1, \'-\' with lines linestyle 0" << endl << endl;
  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    vector<placerDB::point> newp = mydesign.Blocks[i][curr_sp.selected[i]].boundary.polygon;
    fout << "# block " << mydesign.Blocks[i][curr_sp.selected[i]].name << " select " << curr_sp.selected[i] << " bsize " << newp.size() << endl;
    for (unsigned int it = 0; it < newp.size(); it++) {
      fout << "\t" << newp[it].x + Blocks[i].x << "\t" << newp[it].y + Blocks[i].y << endl;
    }
    fout << "\t" << newp[0].x + Blocks[i].x << "\t" << newp[0].y + Blocks[i].y << endl;
    fout << endl;
  }
  fout << "\nEOF" << endl;

  // plot block pins
  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    for (unsigned int j = 0; j < mydesign.Blocks[i][curr_sp.selected[i]].blockPins.size(); j++) {
      for (unsigned int k = 0; k < mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].boundary.size(); k++) {
        for (unsigned int it = 0; it < mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].boundary[k].polygon.size(); it++) {
          placerDB::point newp;
          newp.x = mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].boundary[k].polygon[it].x;
          newp.y = mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].boundary[k].polygon[it].y;
          if (Blocks[i].H_flip) newp.x = mydesign.Blocks[i][curr_sp.selected[i]].width - newp.x;
          if (Blocks[i].V_flip) newp.y = mydesign.Blocks[i][curr_sp.selected[i]].height - newp.y;
          newp.x += Blocks[i].x;
          newp.y += Blocks[i].y;
          fout << "\t" << newp.x << "\t" << newp.y << endl;
        }
        placerDB::point newp;
        newp.x = mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].boundary[k].polygon[0].x;
        newp.y = mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].boundary[k].polygon[0].y;
        if (Blocks[i].H_flip) newp.x = mydesign.Blocks[i][curr_sp.selected[i]].width - newp.x;
        if (Blocks[i].V_flip) newp.y = mydesign.Blocks[i][curr_sp.selected[i]].height - newp.y;
        newp.x += Blocks[i].x;
        newp.y += Blocks[i].y;
        fout << "\t" << newp.x << "\t" << newp.y << endl;
        fout << endl;
      }
    }
  }
  fout << "\nEOF" << endl;

  // plot terminals
  for (auto ni : mydesign.Nets) {
    // for each pin
    for (auto ci : ni.connected) {
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

  // plot nets
  for (vector<placerDB::net>::iterator ni = mydesign.Nets.begin(); ni != mydesign.Nets.end(); ++ni) {
    placerDB::point tp;
    vector<placerDB::point> pins;
    // for each pin
    for (auto ci : ni->connected) {
      if (ci.type == placerDB::Block) {
        if (mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size() > 0) {
          tp.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[0].x;
          tp.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[0].y;
          if (Blocks[ci.iter2].H_flip) tp.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - tp.x;
          if (Blocks[ci.iter2].V_flip) tp.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - tp.y;
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
  fout << endl << "pause -1 \'Press any key\'";
  fout.close();
}

std::vector<double> ILP_solver::Calculate_Center_Point_feature(std::vector<std::vector<placerDB::point>>& temp_contact) {
  std::vector<double> temp_x;
  std::vector<double> temp_y;
  std::vector<double> feature;
  double sum_x;
  double sum_y;
  for (int i = 0; i < temp_contact.size(); i++) {
    sum_x = 0;
    sum_y = 0;
    for (int j = 0; j < temp_contact[i].size(); j++) {
      sum_x = sum_x + (double)temp_contact[i][j].x;
      sum_y = sum_y + (double)temp_contact[i][j].y;
    }
    sum_x = sum_x / (double)temp_contact[i].size();
    sum_y = sum_y / (double)temp_contact[i].size();
    temp_x.push_back(sum_x);
    temp_y.push_back(sum_y);
  }

  sum_x = 0;
  sum_y = 0;
  for (int i = 0; i < temp_x.size(); i++) {
    sum_x = sum_x + temp_x[i];
    sum_y = sum_y + temp_y[i];
  }
  double center_x = sum_x / (double)temp_x.size();
  double center_y = sum_y / (double)temp_y.size();
  for (int i = 0; i < temp_x.size(); i++) {
    feature.push_back(abs(center_x - (double)temp_x[i]) + abs(center_y - (double)temp_y[i]));
  }
  return feature;
}

void ILP_solver::updateTerminalCenter(design& mydesign, SeqPair& curr_sp) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.updateTerminalCenter");

  int Xmax = UR.x;
  int Ymax = UR.y;
  vector<placerDB::point> pos;
  placerDB::point p, bp;
  int alpha;
  vector<placerDB::point> pos_pin;
  std::set<int> solved_terminals;
  // for each terminal
  for (int i = 0; i < mydesign.Terminals.size(); i++) {
    if (solved_terminals.find(i) != solved_terminals.end()) continue;
    solved_terminals.insert(i);
    int netIdx = mydesign.Terminals.at(i).netIter;
    int sbIdx = mydesign.Terminals.at(i).SBidx;
    int cp = mydesign.Terminals.at(i).counterpart;
    if (netIdx < 0 || netIdx >= int(mydesign.Nets.size())) {
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
      placerDB::Smark axis = curr_sp.GetSymmBlockAxis(sbIdx);
      if (cp == (int)i) {  // self-symmetric
        if (axis == placerDB::V) {
          int axis_X = Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first].x +
                       mydesign.Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first][curr_sp.selected[mydesign.SBlocks[sbIdx].selfsym[0].first]].width / 2;
          int distTerm = INT_MAX;
          placerDB::point tp(axis_X, 0);
          for (auto ci : mydesign.Nets[netIdx].connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
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
          int axis_Y = Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first].y +
                       mydesign.Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first][curr_sp.selected[mydesign.SBlocks[sbIdx].selfsym[0].first]].height / 2;
          int distTerm = INT_MAX;
          placerDB::point tp(0, axis_Y);
          for (auto ci : mydesign.Nets.at(netIdx).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
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
        if (netIdx2 < 0 || netIdx2 >= int(mydesign.Nets.size())) {
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
          for (auto ci : mydesign.Nets.at(netIdx).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
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
          for (auto ci : mydesign.Nets.at(netIdx2).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
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
          for (auto ci : mydesign.Nets.at(netIdx).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
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
          for (auto ci : mydesign.Nets.at(netIdx2).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
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
      for (int j = 0; j < mydesign.Port_Location.size(); j++) {
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
        for (auto ci : mydesign.Nets.at(netIdx).connected) {
          if (ci.type == placerDB::Block) {
            bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
            for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
              p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
              if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
              if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
              p += bp;
              pos.push_back(p);
            }
          }
        }
        int shot = -1;
        int distTerm = INT_MAX;
        for (int k = 0; k < pos.size(); k++) {
          p = pos.at(k);
          // Bmark {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT};
          switch (mydesign.Port_Location.at(tar).pos) {
            case placerDB::TL:
              if (p.x >= 0 && p.x <= x1) {
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
              if (p.x >= x1 && p.x <= x2) {
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
              if (p.x >= x2 && p.x <= x3) {
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
              if (p.y >= y2 && p.y <= y3) {
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
              if (p.y >= y1 && p.y <= y2) {
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
              if (p.y >= 0 && p.y <= y1) {
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
              if (p.x >= 0 && p.x <= x1) {
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
              if (p.x >= x1 && p.x <= x2) {
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
              if (p.x >= x2 && p.x <= x3) {
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
              if (p.y >= y2 && p.y <= y3) {
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
              if (p.y >= y1 && p.y <= y2) {
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
              if (p.y >= 0 && p.y <= y1) {
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
        for (auto ci : mydesign.Nets.at(netIdx).connected) {
          if (ci.type == placerDB::Block) {
            bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
            for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
              p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
              if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
              if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
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

void ILP_solver::UpdateHierNode(design& mydesign, SeqPair& curr_sp, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo) {
  node.width = UR.x;
  node.height = UR.y;
  node.HPWL = HPWL;
  node.area_norm = area_norm;
  node.HPWL_norm = HPWL_norm;
  node.constraint_penalty = constraint_penalty;
  node.cost = cost;

  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    node.Blocks.at(i).selectedInstance = curr_sp.GetBlockSelected(i);
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
    UpdateBlockinHierNode(mydesign, ort, node, i, curr_sp.GetBlockSelected(i), drcInfo);
  }
  UpdateTerminalinHierNode(mydesign, node, drcInfo);
  for (unsigned int i = 0; i < mydesign.SNets.size(); ++i) {
    int SBidx = mydesign.SNets.at(i).SBidx;
    placerDB::Smark axis_dir = curr_sp.GetSymmBlockAxis(SBidx);
    UpdateSymmetryNetInfo(mydesign, node, i, SBidx, axis_dir, curr_sp);
  }
}

void ILP_solver::UpdateBlockinHierNode(design& mydesign, placerDB::Omark ort, PnRDB::hierNode& node, int i, int sel, PnRDB::Drc_info& drcInfo) {
  vector<vector<placerDB::point>> boundary;
  vector<placerDB::point> center;
  vector<placerDB::point> bbox;
  placerDB::point bpoint;

  int x = Blocks[i].x;
  int y = Blocks[i].y;

  // SMB Hack
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
  roundup(x, x_pitch);
  roundup(y, y_pitch);

  placerDB::point LL = {x, y};
  bbox = mydesign.GetPlacedBlockAbsBoundary(i, ort, LL, sel);
  bpoint = mydesign.GetBlockAbsCenter(i, ort, LL, sel);
  auto& nd = node.Blocks.at(i).instance.at(sel);

  nd.orient = PnRDB::Omark(ort);
  nd.placedBox = ConvertBoundaryData(bbox);
  nd.placedCenter = ConvertPointData(bpoint);
  for (int j = 0; j < mydesign.GetBlockPinNum(i, sel); j++) {
    boundary = mydesign.GetPlacedBlockPinAbsBoundary(i, j, ort, LL, sel);
    center = mydesign.GetPlacedBlockPinAbsPosition(i, j, ort, LL, sel);
    for (unsigned int k = 0; k < nd.blockPins.at(j).pinContacts.size(); k++) {
      nd.blockPins.at(j).pinContacts.at(k).placedBox = ConvertBoundaryData(boundary.at(k));
      nd.blockPins.at(j).pinContacts.at(k).placedCenter = ConvertPointData(center.at(k));
    }
    // update pin vias
    for (unsigned int k = 0; k < node.Blocks.at(i).instance.at(sel).blockPins.at(j).pinVias.size(); k++) {
      auto& pv = nd.blockPins.at(j).pinVias.at(k);
      pv.placedpos = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, pv.originpos, LL, sel);
      pv.UpperMetalRect.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, pv.UpperMetalRect.originBox, LL, sel);
      pv.LowerMetalRect.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, pv.LowerMetalRect.originBox, LL, sel);
      pv.ViaRect.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, pv.ViaRect.originBox, LL, sel);
      pv.UpperMetalRect.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, pv.UpperMetalRect.originCenter, LL, sel);
      pv.LowerMetalRect.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, pv.LowerMetalRect.originCenter, LL, sel);
      pv.ViaRect.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, pv.ViaRect.originCenter, LL, sel);
    }
  }
  // update internal metals
  for (unsigned int j = 0; j < node.Blocks.at(i).instance.at(sel).interMetals.size(); j++) {
    auto& im = nd.interMetals.at(j);
    im.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, im.originBox, LL, sel);
    im.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, im.originCenter, LL, sel);
  }
  // update internal vias
  for (unsigned int j = 0; j < node.Blocks.at(i).instance.at(sel).interVias.size(); j++) {
    auto& iv = nd.interVias.at(j);
    iv.placedpos = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, iv.originpos, LL, sel);
    iv.UpperMetalRect.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, iv.UpperMetalRect.originBox, LL, sel);
    iv.LowerMetalRect.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, iv.LowerMetalRect.originBox, LL, sel);
    iv.ViaRect.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, iv.ViaRect.originBox, LL, sel);
    iv.UpperMetalRect.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, iv.UpperMetalRect.originCenter, LL, sel);
    iv.LowerMetalRect.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, iv.LowerMetalRect.originCenter, LL, sel);
    iv.ViaRect.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, iv.ViaRect.originCenter, LL, sel);
  }
}

void ILP_solver::UpdateTerminalinHierNode(design& mydesign, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo) {
  for (int i = 0; i < (int)mydesign.GetSizeofTerminals(); i++) {
    auto& tC = node.Terminals.at(i).termContacts;
    tC.clear();
    tC.resize(1);
    auto c = ConvertPointData(mydesign.GetTerminalCenter(i));
    tC.back().placedCenter = c;
    // tC.back() has other fields that remain at their default values: originBox, placedBox, originCenter
    tC.back().originCenter = c;
    tC.back().originBox.LL = c;
    tC.back().originBox.UR = c;
    tC.back().placedBox.LL = c;
    tC.back().placedBox.UR = c;
  }
  for (int i = 0; i < (int)mydesign.GetSizeofTerminals(); i++) {
    const auto& t = node.Terminals.at(i);
    PnRDB::pin temp_pin;
    temp_pin.name = t.name;
    temp_pin.type = t.type;
    temp_pin.netIter = t.netIter;
    temp_pin.pinContacts = t.termContacts;
    for (int j = 0; j < temp_pin.pinContacts.size(); j++) temp_pin.pinContacts[j].metal = drcInfo.Metal_info[0].name;
    node.blockPins.push_back(temp_pin);
  }
}

void ILP_solver::UpdateSymmetryNetInfo(design& mydesign, PnRDB::hierNode& node, int i, int SBidx, placerDB::Smark axis_dir, SeqPair& curr_sp) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.UpdateSymmetryNetInfo");

  int axis_coor = 0;
  if (axis_dir == placerDB::V) {
    if (mydesign.SBlocks[SBidx].selfsym.size() > 0) {
      // self sym x axis coordinate
      axis_coor = Blocks[mydesign.SBlocks[SBidx].selfsym[0].first].x +
                  mydesign.Blocks[mydesign.SBlocks[SBidx].selfsym[0].first][curr_sp.selected[mydesign.SBlocks[SBidx].selfsym[0].first]].width / 2;
    } else {
      // sym pair x axis coordinate
      axis_coor = Blocks[mydesign.SBlocks[SBidx].sympair[0].first].x / 2 +
                  mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].first][curr_sp.selected[mydesign.SBlocks[SBidx].sympair[0].first]].width / 4 +
                  Blocks[mydesign.SBlocks[SBidx].sympair[0].second].x / 2 +
                  mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].second][curr_sp.selected[mydesign.SBlocks[SBidx].sympair[0].second]].width / 4;
    }
  } else if (axis_dir == placerDB::H) {
    if (mydesign.SBlocks[SBidx].selfsym.size() > 0) {
      axis_coor = Blocks[mydesign.SBlocks[SBidx].selfsym[0].first].y +
                  mydesign.Blocks[mydesign.SBlocks[SBidx].selfsym[0].first][curr_sp.selected[mydesign.SBlocks[SBidx].selfsym[0].first]].height / 2;
    } else {
      axis_coor = Blocks[mydesign.SBlocks[SBidx].sympair[0].first].y / 2 +
                  mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].first][curr_sp.selected[mydesign.SBlocks[SBidx].sympair[0].first]].height / 4 +
                  Blocks[mydesign.SBlocks[SBidx].sympair[0].second].y / 2 +
                  mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].second][curr_sp.selected[mydesign.SBlocks[SBidx].sympair[0].second]].height / 4;
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

PnRDB::bbox ILP_solver::ConvertBoundaryData(vector<placerDB::point> Bdata) {
  PnRDB::bbox newBdata;
  PnRDB::point tmpp;
  int x = Bdata.at(0).x, X = Bdata.at(0).x, y = Bdata.at(0).y, Y = Bdata.at(0).y;
  for (vector<placerDB::point>::iterator it = Bdata.begin(); it != Bdata.end(); ++it) {
    tmpp.x = it->x;
    tmpp.y = it->y;
    if ((it->x) < x) {
      x = it->x;
    }
    if ((it->x) > X) {
      X = it->x;
    }
    if ((it->y) < y) {
      y = it->y;
    }
    if ((it->y) > Y) {
      Y = it->y;
    }
  }
  newBdata.LL = {x, y};
  newBdata.UR = {X, Y};
  return newBdata;
}

PnRDB::point ILP_solver::ConvertPointData(placerDB::point Pdata) {
  PnRDB::point newPdata;
  newPdata.x = Pdata.x;
  newPdata.y = Pdata.y;
  return newPdata;
}
