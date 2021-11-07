#include "Aplace.h"

#include "spdlog/spdlog.h"

double Aplace::CalculateObjective(design& caseNL, boost_vector& x_k, double lamda_wl, double lamda_sym, double lamda_bnd, double lamda_ovl) {
  auto logger = spdlog::default_logger()->clone("placer.Aplace.CalculateObjective");

  double sum = 0;
  double wl = CalculateWireLength(caseNL, x_k);
  double sym = CalculateSymmetryViolation(caseNL, x_k);
  double bnd = CalculateBoundaryViolation(caseNL, x_k);
  double ovl = CalculateOverlap(caseNL, x_k);
  sum += (lamda_wl * wl + lamda_sym * sym + lamda_bnd * bnd + lamda_ovl * ovl);
  logger->debug("sum {0} wl {1} sym {2} bnd {3} ovl {4}", sum, wl, sym, bnd, ovl);
  return sum;
}

double Aplace::CalculateObjectiveSmooth(design& caseNL, boost_vector& x_k, double lamda_wl, double lamda_sym, double lamda_bnd, double lamda_ovl,
                                        double alpha_wl, double alpha_ola, double alpha_olb, double alpha_bnd) {
  auto logger = spdlog::default_logger()->clone("placer.Aplace.CalculateObjectiveSmooth");

  double sum = 0;
  double wl = CalculateWireLengthSmooth(caseNL, x_k, alpha_wl);
  double sym = CalculateSymmetryViolation(caseNL, x_k);
  double bnd = CalculateBoundaryViolationSmooth(caseNL, x_k, alpha_bnd);
  double ovl = CalculateOverlapSmooth(caseNL, x_k, alpha_ola, alpha_olb);
  sum += (lamda_wl * wl + lamda_sym * sym + lamda_bnd * bnd + lamda_ovl * ovl);
  logger->debug("II sum {0} wl {1} sym {2} bnd {3} ovl {4}", sum, wl, sym, bnd, ovl);
  return sum;
}

void Aplace::ConjugateGrident(design& caseNL, string opath) {
  auto logger = spdlog::default_logger()->clone("placer.Aplace.ConjugateGrident");

  int vec_len = B_len * 2 + VSG_len + HSG_len;
  boost_vector G_j(vec_len);
  boost_vector G_k(vec_len);
  boost_vector x_j(vec_len);
  boost_vector x_k(vec_len);
  boost_vector D_j(vec_len);
  boost_vector D_k(vec_len);
  double alpha_wl = 2000, alpha_ola = 1500, alpha_olb = 1500, alpha_bnd = 2000;
  double lamda_wl = 4000, lamda_sym = 10, lamda_bnd = 2500, lamda_ovl = 10;
  // double lamda_wl=1500, lamda_sym=1, lamda_bnd=2500, lamda_ovl=10;
  double eps = 1e-5;
  double step_size = 0.4;
  // double beta;//, step;
  double f_j = 0.0;  //, f_k;
  int count = 0, MAX_COUNT = 300000;
  // 1. initialize g0 and d0, x0
  for (int i = 0; i < vec_len; ++i) {
    G_j(i) = 0;
    D_j(i) = 0;
  }  // G_j=0, D_j=0
  // x_j/x_k: {x_0,y_0,x_1,y_1,...,x_N-1,y_N-1,x_vs_0,...x_vs_M-1,y_hs_0,...,y_hs_P-1}
  for (int i = 0; i < this->B_len; ++i) {           // all blocks
    x_j(i * 2) = this->ABlocks.at(i).center.x;      // x
    x_j(i * 2 + 1) = this->ABlocks.at(i).center.y;  // y
  }
  for (int i = 0; i < this->VSG_len; ++i) {  // vertical symmetry group
    x_j(2 * this->B_len + i) = this->SGroups.at(this->VSG.at(i)).axis_coor;
  }
  for (int i = 0; i < this->HSG_len; ++i) {  // horizontal symmetry group
    x_j(2 * this->B_len + VSG_len + i) = this->SGroups.at(this->HSG.at(i)).axis_coor;
  }
  // logger->debug("G_j {0}",G_j);
  // logger->debug("x_j {0}",x_j);
  // logger->debug("D_j {0}",D_j);
  PlotPlacement(caseNL, x_j, opath + name + "_AP_init.plt");
  // 2. initialize gk and dk
  do {
    for (int i = 0; i < vec_len; ++i) {
      G_k(i) = 0;
    }  // G_k
    AddWireLengthGradient(G_k, x_j, caseNL, alpha_wl, lamda_wl);
    // std::cout<<"G_k WL "<<G_k<<std::endl;
    AddSymmetryGradient(G_k, x_j, caseNL, lamda_sym);
    // std::cout<<"G_k SYM "<<G_k<<std::endl;
    AddBoundaryGradient(G_k, x_j, caseNL, alpha_bnd, lamda_bnd);
    // std::cout<<"G_k SND "<<G_k<<std::endl;
    AddOverlapGradient(G_k, x_j, caseNL, alpha_ola, alpha_olb, lamda_ovl);
    // std::cout<<"G_k OVL "<<G_k<<std::endl;
    double beta, f_k;
    if (count == 0) {
      beta = 0;
      f_j = CalculateObjectiveSmooth(caseNL, x_j, lamda_wl, lamda_sym, lamda_bnd, lamda_ovl, alpha_wl, alpha_ola, alpha_olb, alpha_bnd);
      logger->debug("Placer-Info: initial cost {0}", f_j);
    } else {
      beta = boost::numeric::ublas::inner_prod(boost::numeric::ublas::trans(G_k), G_k - G_j) / boost::numeric::ublas::norm_2(G_j);
    }
    D_k = -1 * G_k + beta * D_j;  // D_k

    double step = step_size / boost::numeric::ublas::norm_2(D_k);

    x_k = x_j + step * D_k;

    // if(count%10000==0) {
    //  std::cout<<"x_k "<<x_k<<std::endl;
    //  PlotPlacement(caseNL, x_k, "AP_"+std::to_string(count/10000)+".plt");
    //  //CalculateObjective(caseNL, x_k, lamda_wl, lamda_sym, lamda_bnd, lamda_ovl);
    //}
    // f_k=CalculateObjective(caseNL, x_k, lamda_wl, lamda_sym, lamda_bnd, lamda_ovl);
    f_k = CalculateObjectiveSmooth(caseNL, x_k, lamda_wl, lamda_sym, lamda_bnd, lamda_ovl, alpha_wl, alpha_ola, alpha_olb, alpha_bnd);
    // std::cout<<"@SUM "<<f_k<<std::endl;
    if (std::abs(f_k - f_j) < eps) {
      logger->debug("Placer-Info: optimal solution found");
      break;
    }
    count++;
    f_j = f_k;
    G_j = G_k;
    x_j = x_k;
    D_j = D_k;
  } while (count <= MAX_COUNT);
  // logger->debug("Final x_k {0}",x_k);
  PlotPlacement(caseNL, x_k, opath + name + "_AP.plt");
  for (int i = 0; i < this->B_len; ++i) {
    this->ABlocks.at(i).center.x = x_k(i * 2);      // x
    this->ABlocks.at(i).center.y = x_k(i * 2 + 1);  // y
  }
  for (int i = 0; i < this->VSG_len; ++i) {  // vertical symmetry group
    this->SGroups.at(this->VSG.at(i)).axis_coor = x_k(2 * this->B_len + i);
  }
  for (int i = 0; i < this->HSG_len; ++i) {  // horizontal symmetry group
    this->SGroups.at(this->HSG.at(i)).axis_coor = x_k(2 * this->B_len + VSG_len + i);
  }
}

void Aplace::PlotPlacement(design& caseNL, boost_vector& x_k, string outfile) {
  auto logger = spdlog::default_logger()->clone("placer.Aplace.PlotPlacement");

  logger->debug("Placer-Info: create gnuplot file");
  int Xmax = this->width;
  int Ymax = this->height;
  placerDB::point p, bp;
  ofstream fout;
  std::vector<placerDB::point> p_pin;
  fout.open(outfile.c_str());
  fout << "#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)" << endl;
  fout << "\nset title\" #Blocks= " << caseNL.GetSizeofBlocks() << ", #Terminals= " << caseNL.GetSizeofTerminals() << ", #Nets= " << caseNL.GetSizeofNets()
       << " \"" << endl;
  fout << "\nset nokey" << endl;
  fout << "#   Uncomment these two lines starting with \"set\"" << endl;
  fout << "#   to save an EPS file for inclusion into a latex document" << endl;
  fout << "# set terminal postscript eps color solid 20" << endl;
  fout << "# set output \"result.eps\"" << endl << endl;
  fout << "#   Uncomment these two lines starting with \"set\"" << endl;
  fout << "#   to save a PS file for printing" << endl;
  fout << "# set terminal postscript portrait color solid 20" << endl;
  fout << "# set output \"result.ps\"" << endl << endl;

  int max = (Xmax > Ymax) ? Xmax : Ymax;
  int bias = 50;
  fout << "\nset xrange [" << 0 - max - bias << ":" << max + bias << "]" << endl;
  fout << "\nset yrange [" << 0 - bias << ":" << max + bias << "]" << endl;
  // set labels for blocks
  // cout<<"set labels for blocks..."<<endl;
  for (int i = 0; i < (int)caseNL.GetSizeofBlocks(); ++i) {
    placerDB::point tp;
    tp.x = x_k(2 * i) - caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
    tp.y = x_k(2 * i + 1) - caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
    placerDB::point ntp = caseNL.GetBlockAbsCenter(i, this->ABlocks.at(i).orient, tp, this->selected.at(i));
    fout << "\nset label \"" << caseNL.GetBlockName(i) << "\" at " << ntp.x << " , " << ntp.y << " center " << endl;
    for (int j = 0; j < caseNL.GetBlockPinNum(i, this->selected.at(i)); ++j) {
      p_pin = caseNL.GetPlacedBlockPinAbsPosition(i, j, this->ABlocks.at(i).orient, tp, this->selected.at(i));
      for (unsigned int k = 0; k < p_pin.size(); ++k) {
        placerDB::point newp = p_pin[k];
        fout << "\nset label \"" << caseNL.GetBlockPinName(i, j, this->selected.at(i)) << "\" at " << newp.x << " , " << newp.y << endl;
        fout << endl;
      }
    }
  }
  // set labels for terminals
  // cout<<"set labels for terminals..."<<endl;
  // for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
  //   bool hasTerminal=false;
  //   int distTerm=-1*NINF;
  //   int tno; placerDB::point tp;
  //   p_pin.clear();
  //   // for each pin
  //   for(std::vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
  //    if (ci->type==placerDB::Terminal) {
  //         hasTerminal=true; tno=ci->iter;
  //       }
  //     }
  //     if(hasTerminal) {
  //       fout<<"\nset label \""<<caseNL.Terminals.at(tno).name<<"\" at "<<caseNL.Terminals.at(tno).center.x<<" , "<<caseNL.Terminals.at(tno).center.y<<"
  //       center "<<endl;
  //     }
  //   }

  // plot blocks
  // cout<<"plot blocks..."<<endl;
  fout << "\nplot[:][:] \'-\' with lines linestyle 3, \'-\' with lines linestyle 7, \'-\'      with lines linestyle 1, \'-\' with lines linestyle 0" << endl
       << endl;
  ;
  for (int i = 0; i < (int)caseNL.GetSizeofBlocks(); ++i) {
    string ort;
    placerDB::point tp;
    tp.x = x_k(2 * i) - caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
    tp.y = x_k(2 * i + 1) - caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
    // std::vector<point> newp=caseNL.GetPlacedBlockAbsBoundary(i, E, tp);
    std::vector<placerDB::point> newp = caseNL.GetPlacedBlockAbsBoundary(i, this->ABlocks.at(i).orient, tp, this->selected.at(i));

    for (unsigned int it = 0; it < newp.size(); ++it) {
      fout << "\t" << newp[it].x << "\t" << newp[it].y << endl;
    }
    fout << "\t" << newp[0].x << "\t" << newp[0].y << endl;
    fout << endl;
  }
  fout << "\nEOF" << endl;
  std::vector<std::vector<placerDB::point> > newp_pin;
  // plot block pins
  // cout<<"plot block pins..."<<endl;
  for (int i = 0; i < (int)caseNL.GetSizeofBlocks(); ++i) {
    string ort;
    placerDB::point tp;
    tp.x = x_k(2 * i) - caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
    tp.y = x_k(2 * i + 1) - caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
    for (int j = 0; j < caseNL.GetBlockPinNum(i, this->selected.at(i)); ++j) {
      newp_pin = caseNL.GetPlacedBlockPinAbsBoundary(i, j, this->ABlocks.at(i).orient, tp, this->selected.at(i));
      for (unsigned int k = 0; k < newp_pin.size(); ++k) {
        std::vector<placerDB::point> newp_p = newp_pin[k];
        for (unsigned int it = 0; it < newp_p.size(); ++it) {
          fout << "\t" << newp_p[it].x << "\t" << newp_p[it].y << endl;
        }
        fout << "\t" << newp_p[0].x << "\t" << newp_p[0].y << endl;
        fout << endl;
      }
    }
  }
  fout << "\nEOF" << endl;

  // plot terminals
  // cout<<"plot terminals..."<<endl;
  // for(std::vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
  //   bool hasTerminal=false;
  //   int distTerm=-1*NINF;
  //   int tno; placerDB::point tp;
  //   // for each pin
  //   for(std::vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
  //     if (ci->type==placerDB::Terminal) {
  //       hasTerminal=true; tno=ci->iter;
  //     }
  //   }
  //   if(hasTerminal) {
  //     int bias=20;
  //     fout<<endl;
  //     fout<<"\t"<<caseNL.Terminals.at(tno).center.x-bias<<"\t"<<caseNL.Terminals.at(tno).center.y-bias<<endl;
  //     fout<<"\t"<<caseNL.Terminals.at(tno).center.x-bias<<"\t"<<caseNL.Terminals.at(tno).center.y+bias<<endl;
  //     fout<<"\t"<<caseNL.Terminals.at(tno).center.x+bias<<"\t"<<caseNL.Terminals.at(tno).center.y+bias<<endl;
  //     fout<<"\t"<<caseNL.Terminals.at(tno).center.x+bias<<"\t"<<caseNL.Terminals.at(tno).center.y-bias<<endl;
  //     fout<<"\t"<<caseNL.Terminals.at(tno).center.x-bias<<"\t"<<caseNL.Terminals.at(tno).center.y-bias<<endl;
  //   }
  // }
  // if(caseNL.Terminals.size()>0) {
  fout << "\nEOF" << endl;
  //}
  // plot nets
  // cout<<"plot nets..."<<endl;
  for (std::vector<placerDB::net>::iterator ni = caseNL.Nets.begin(); ni != caseNL.Nets.end(); ++ni) {
    // bool hasTerminal=false;
    // int distTerm=INT_MIN;
    // int tno;
    std::vector<placerDB::point> pins;
    pins.clear();
    // for each pin
    for (std::vector<placerDB::Node>::iterator ci = (ni->connected).begin(); ci != (ni->connected).end(); ++ci) {
      if (ci->type == placerDB::Block) {
        bp.x = x_k(2 * ci->iter2) - caseNL.GetBlockWidth(ci->iter2, this->ABlocks.at(ci->iter2).orient, this->selected.at(ci->iter2)) / 2;
        bp.y = x_k(2 * ci->iter2 + 1) - caseNL.GetBlockHeight(ci->iter2, this->ABlocks.at(ci->iter2).orient, this->selected.at(ci->iter2)) / 2;
        p_pin = caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, this->ABlocks.at(ci->iter2).orient, bp, this->selected.at(ci->iter2));

        if (!p_pin.empty()) {
          for (int i = 0; i < 1; ++i) {
            p = p_pin[i];
            pins.push_back(p);
          }
        }
      } else if (ci->type == placerDB::Terminal) {
        // hasTerminal=true; tno=ci->iter;
      }
    }
    // if(hasTerminal) {pins.push_back(caseNL.Terminals.at(tno).center);}
    fout << "\n#Net: " << ni->name << endl;
    if (pins.size() >= 2) {
      for (unsigned int i = 1; i < pins.size(); ++i) {
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

double Aplace::CalculateOverlapSmooth(design& caseNL, boost_vector& x_k, double alphaA, double alphaB) {
  double Oy, Ox, ex1, ex2, ex3, ey1, ey2, ey3;
  double iLLx, iLLy, jLLx, jLLy;
  double sum = 0;
  for (int i = 0; i < caseNL.GetSizeofBlocks(); ++i) {
    for (int j = i + 1; j < caseNL.GetSizeofBlocks(); ++j) {
      iLLx = x_k(i * 2) - caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
      iLLy = x_k(i * 2 + 1) - caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
      jLLx = x_k(j * 2) - caseNL.GetBlockWidth(j, this->ABlocks.at(j).orient, this->selected.at(j)) / 2;
      jLLy = x_k(j * 2 + 1) - caseNL.GetBlockHeight(j, this->ABlocks.at(j).orient, this->selected.at(j)) / 2;
      ex1 = exp(-1 * (iLLx + caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) - jLLx) / alphaA);
      ex2 = exp(-1 * (jLLx + caseNL.GetBlockWidth(j, this->ABlocks.at(j).orient, this->selected.at(j)) - iLLx) / alphaA);
      ex3 = exp(-1 *
                std::min(caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)),
                         caseNL.GetBlockWidth(j, this->ABlocks.at(j).orient, this->selected.at(j))) /
                alphaA);
      ey1 = exp(-1 * (iLLy + caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) - jLLy) / alphaA);
      ey2 = exp(-1 * (jLLy + caseNL.GetBlockHeight(j, this->ABlocks.at(j).orient, this->selected.at(j)) - iLLy) / alphaA);
      ey3 = exp(-1 *
                std::min(caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)),
                         caseNL.GetBlockHeight(j, this->ABlocks.at(j).orient, this->selected.at(j))) /
                alphaA);
      Ox = alphaB * log1p(exp(-1 * alphaA / alphaB * log(ex1 + ex2 + ex3)));
      Oy = alphaB * log1p(exp(-1 * alphaA / alphaB * log(ey1 + ey2 + ey3)));
      // Ox=log1p( exp( -1*alphaA/alphaB*log(ex1+ex2+ex3) ) );
      // Oy=log1p( exp( -1*alphaA/alphaB*log(ey1+ey2+ey3) ) );
      sum += Ox * Oy;
    }
  }
  return sum;
}

double Aplace::CalculateOverlap(design& caseNL, boost_vector& x_k) {
  double sum = 0;
  double Ox, Oy;
  double iLLx, iLLy, jLLx, jLLy;
  for (int i = 0; i < caseNL.GetSizeofBlocks(); ++i) {
    for (int j = i + 1; j < caseNL.GetSizeofBlocks(); ++j) {
      iLLx = x_k(i * 2) - caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
      iLLy = x_k(i * 2 + 1) - caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
      jLLx = x_k(j * 2) - caseNL.GetBlockWidth(j, this->ABlocks.at(j).orient, this->selected.at(j)) / 2;
      jLLy = x_k(j * 2 + 1) - caseNL.GetBlockHeight(j, this->ABlocks.at(j).orient, this->selected.at(j)) / 2;
      Ox = std::max(std::min(std::min(iLLx + caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) - jLLx,
                                      jLLx + caseNL.GetBlockWidth(j, this->ABlocks.at(j).orient, this->selected.at(j)) - iLLx),
                             (double)std::min(caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)),
                                              caseNL.GetBlockWidth(j, this->ABlocks.at(j).orient, this->selected.at(j)))),
                    0.0);
      Oy = std::max(std::min(std::min(iLLy + caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) - jLLy,
                                      jLLy + caseNL.GetBlockHeight(j, this->ABlocks.at(j).orient, this->selected.at(j)) - iLLy),
                             (double)std::min(caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)),
                                              caseNL.GetBlockHeight(j, this->ABlocks.at(j).orient, this->selected.at(j)))),
                    0.0);
      sum += Ox * Oy;
    }
  }
  return sum;
}

void Aplace::AddOverlapGradient(boost_vector& G_k, boost_vector& x_k, design& caseNL, double alphaA, double alphaB, double beta) {
  double Oy, Ox, ex1, ex2, ex3, ey1, ey2, ey3;
  double scale = beta;
  double iLLx, iLLy, jLLx, jLLy;
  for (int i = 0; i < caseNL.GetSizeofBlocks(); ++i) {
    for (int j = i + 1; j < caseNL.GetSizeofBlocks(); ++j) {
      iLLx = x_k(i * 2) - caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
      iLLy = x_k(i * 2 + 1) - caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
      jLLx = x_k(j * 2) - caseNL.GetBlockWidth(j, this->ABlocks.at(j).orient, this->selected.at(j)) / 2;
      jLLy = x_k(j * 2 + 1) - caseNL.GetBlockHeight(j, this->ABlocks.at(j).orient, this->selected.at(j)) / 2;
      ex1 = exp(-1 * (iLLx + caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) - jLLx) / alphaA);
      ex2 = exp(-1 * (jLLx + caseNL.GetBlockWidth(j, this->ABlocks.at(j).orient, this->selected.at(j)) - iLLx) / alphaA);
      ex3 = exp(-1 *
                std::min(caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)),
                         caseNL.GetBlockWidth(j, this->ABlocks.at(j).orient, this->selected.at(j))) /
                alphaA);
      ey1 = exp(-1 * (iLLy + caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) - jLLy) / alphaA);
      ey2 = exp(-1 * (jLLy + caseNL.GetBlockHeight(j, this->ABlocks.at(j).orient, this->selected.at(j)) - iLLy) / alphaA);
      ey3 = exp(-1 *
                std::min(caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)),
                         caseNL.GetBlockHeight(j, this->ABlocks.at(j).orient, this->selected.at(j))) /
                alphaA);
      // Ox=log1p( exp( -1*alphaA/alphaB*log(ex1+ex2+ex3) ) );
      // Oy=log1p( exp( -1*alphaA/alphaB*log(ey1+ey2+ey3) ) );
      Ox = alphaB * log1p(exp(-1 * alphaA / alphaB * log(ex1 + ex2 + ex3)));
      Oy = alphaB * log1p(exp(-1 * alphaA / alphaB * log(ey1 + ey2 + ey3)));
      G_k(2 * i) += scale * Oy * (exp(-1 * alphaA / alphaB * log(ex1 + ex2 + ex3)) * (ex1 - ex2) / (ex1 + ex2 + ex3)) /
                    (exp(-1 * alphaA / alphaB * log(ex1 + ex2 + ex3)) + 1);
      G_k(2 * i + 1) += scale * Ox * (exp(-1 * alphaA / alphaB * log(ey1 + ey2 + ey3)) * (ey1 - ey2) / (ey1 + ey2 + ey3)) /
                        (exp(-1 * alphaA / alphaB * log(ey1 + ey2 + ey3)) + 1);
      G_k(2 * j) += scale * Oy * (exp(-1 * alphaA / alphaB * log(ex1 + ex2 + ex3)) * (ex2 - ex1) / (ex1 + ex2 + ex3)) /
                    (exp(-1 * alphaA / alphaB * log(ex1 + ex2 + ex3)) + 1);
      G_k(2 * j + 1) += scale * Ox * (exp(-1 * alphaA / alphaB * log(ey1 + ey2 + ey3)) * (ey2 - ey1) / (ey1 + ey2 + ey3)) /
                        (exp(-1 * alphaA / alphaB * log(ey1 + ey2 + ey3)) + 1);
    }
  }
}

double Aplace::CalculateBoundaryViolationSmooth(design& caseNL, boost_vector& x_k, double alpha) {
  int xL = 0, yL = 0, xR = this->width, yR = this->height;
  double sum = 0;
  // double LLx,LLy;
  for (int i = 0; i < caseNL.GetSizeofBlocks(); ++i) {
    double LLx = x_k(2 * i) - caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
    double LLy = x_k(2 * i + 1) - caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
    double eXL = exp((xL - LLx) / alpha);
    double eXR = exp((LLx + caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) - xR) / alpha);
    double eYL = exp((yL - LLy) / alpha);
    double eYR = exp((LLy + caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) - yR) / alpha);
    sum += alpha * (log1p(eXL) + log1p(eXR) + log1p(eYL) + log1p(eYR));
  }
  return sum;
}

double Aplace::CalculateBoundaryViolation(design& caseNL, boost_vector& x_k) {
  double sum = 0;
  int xL = 0, yL = 0, xR = this->width, yR = this->height;
  // double LLx,LLy;
  for (int i = 0; i < caseNL.GetSizeofBlocks(); ++i) {
    double LLx = x_k(2 * i) - caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
    double LLy = x_k(2 * i + 1) - caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
    sum += std::max(xL - LLx, 0.0);
    sum += std::max(LLx + caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) - xR, 0.0);
    sum += std::max(yL - LLy, 0.0);
    sum += std::max(LLy + caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) - yR, 0.0);
    // std::cout<<"block "<<i<<" "<<std::max(xL-x_k(2*i), 0.0)<<" "<<std::max(x_k(2*i)+caseNL.GetBlockWidth(i,
    // this->ABlocks.at(i).orient,this->selected.at(i))-xR, 0.0)<<" "<<std::max(yL-x_k(2*i+1),0.0)<<" "<<std::max(x_k(2*i+1)+caseNL.GetBlockHeight(i,
    // this->ABlocks.at(i).orient,this->selected.at(i))-yR, 0.0)<<std::endl;
  }
  return sum;
}

void Aplace::AddBoundaryGradient(boost_vector& G_k, boost_vector& x_k, design& caseNL, double alpha, double beta) {
  int xL = 0, yL = 0, xR = this->width, yR = this->height;
  double scale = beta;
  // double LLx,LLy;
  for (int i = 0; i < caseNL.GetSizeofBlocks(); ++i) {
    double LLx = x_k(2 * i) - caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
    double LLy = x_k(2 * i + 1) - caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) / 2;
    double eXL = exp((xL - LLx) / alpha);
    double eXR = exp((LLx + caseNL.GetBlockWidth(i, this->ABlocks.at(i).orient, this->selected.at(i)) - xR) / alpha);
    double eYL = exp((yL - LLy) / alpha);
    double eYR = exp((LLy + caseNL.GetBlockHeight(i, this->ABlocks.at(i).orient, this->selected.at(i)) - yR) / alpha);
    G_k(2 * i) += scale * (-1 * eXL / (eXL + 1) + eXR / (eXR + 1));
    G_k(2 * i + 1) += scale * (-1 * eYL / (eYL + 1) + eYR / (eYR + 1));
  }
}

double Aplace::CalculateSymmetryViolation(design& caseNL, boost_vector& x_k) {
  double sum = 0;
  for (std::vector<int>::iterator it = this->VSG.begin(); it != this->VSG.end(); ++it) {
    // for each vertical symmetry group
    for (std::vector<pair<int, placerDB::Smark> >::iterator it2 = caseNL.SBlocks.at(*it).selfsym.begin(); it2 != caseNL.SBlocks.at(*it).selfsym.end(); ++it2) {
      // for each selfsymmetric block
      if (it2->first >= 0 && it2->first < caseNL.GetSizeofBlocks()) {
        sum += std::pow(x_k(2 * it2->first) - x_k(it - this->VSG.begin() + 2 * this->B_len), 2);  // (x_i-x_axis)^2
      }
    }
    for (std::vector<pair<int, int> >::iterator it2 = caseNL.SBlocks.at(*it).sympair.begin(); it2 != caseNL.SBlocks.at(*it).sympair.end(); ++it2) {
      // for each symmetry pair
      if (it2->first >= 0 && it2->first < caseNL.GetSizeofBlocks() && it2->second >= 0 && it2->second < caseNL.GetSizeofBlocks()) {
        sum += std::pow(x_k(2 * it2->first) + x_k(2 * it2->second) - 2 * x_k(it - this->VSG.begin() + 2 * this->B_len), 2);  // (x_i+x_j-2x_axis)^2
        sum += std::pow(x_k(2 * it2->first + 1) - x_k(2 * it2->second + 1), 2);                                              // (y_i-y_j)^2
      }
    }
  }
  for (std::vector<int>::iterator it = this->HSG.begin(); it != this->HSG.end(); ++it) {
    // for each vertical symmetry group
    for (std::vector<pair<int, placerDB::Smark> >::iterator it2 = caseNL.SBlocks.at(*it).selfsym.begin(); it2 != caseNL.SBlocks.at(*it).selfsym.end(); ++it2) {
      // for each selfsymmetric block
      if (it2->first >= 0 && it2->first < caseNL.GetSizeofBlocks()) {
        sum += std::pow(x_k(2 * it2->first + 1) - x_k(it - this->HSG.begin() + 2 * this->B_len + this->VSG_len), 2);  // (y_i-y_axis)^2
      }
    }
    for (std::vector<pair<int, int> >::iterator it2 = caseNL.SBlocks.at(*it).sympair.begin(); it2 != caseNL.SBlocks.at(*it).sympair.end(); ++it2) {
      // for each symmetry pair
      if (it2->first >= 0 && it2->first < caseNL.GetSizeofBlocks() && it2->second >= 0 && it2->second < caseNL.GetSizeofBlocks()) {
        sum += std::pow(x_k(2 * it2->first + 1) + x_k(2 * it2->second + 1) - 2 * x_k(it - this->HSG.begin() + 2 * this->B_len + this->VSG_len),
                        2);                                              // (y_i+y_j-2y_axis)^2
        sum += std::pow(x_k(2 * it2->first) - x_k(2 * it2->second), 2);  // (x_i-x_j)^2
      }
    }
  }
  return sum;
}

void Aplace::AddSymmetryGradient(boost_vector& G_k, boost_vector& x_k, design& caseNL, double beta) {
  double scale = beta;
  for (std::vector<int>::iterator it = this->VSG.begin(); it != this->VSG.end(); ++it) {
    // for each vertical symmetry group
    for (std::vector<pair<int, placerDB::Smark> >::iterator it2 = caseNL.SBlocks.at(*it).selfsym.begin(); it2 != caseNL.SBlocks.at(*it).selfsym.end(); ++it2) {
      // for each selfsymmetric block
      if (it2->first >= 0 && it2->first < caseNL.GetSizeofBlocks()) {
        G_k(2 * it2->first) += scale * 2 * (x_k(2 * it2->first) - x_k(it - this->VSG.begin() + 2 * this->B_len));  // 2(x_i-x_axis)
        // wbxu- temporarily fix the symmetry axis
        // G_k(it-this->VSG.begin()+2*this->B_len) += scale*2*( x_k(it-this->VSG.begin()+2*this->B_len)-x_k(2*it2->first) ); // 2(x_axis-x_i)
      }
    }
    for (std::vector<pair<int, int> >::iterator it2 = caseNL.SBlocks.at(*it).sympair.begin(); it2 != caseNL.SBlocks.at(*it).sympair.end(); ++it2) {
      // for each symmetry pair
      if (it2->first >= 0 && it2->first < caseNL.GetSizeofBlocks() && it2->second >= 0 && it2->second < caseNL.GetSizeofBlocks()) {
        G_k(2 * it2->first) +=
            scale * 2 * (x_k(2 * it2->first) + x_k(2 * it2->second) - 2 * x_k(it - this->VSG.begin() + 2 * this->B_len));  // 2(x_i+x_j-2x_axis)
        G_k(2 * it2->second) +=
            scale * 2 * (x_k(2 * it2->first) + x_k(2 * it2->second) - 2 * x_k(it - this->VSG.begin() + 2 * this->B_len));  // 2(x_j+x_i-2x_axis)
        G_k(2 * it2->first + 1) += scale * 2 * (x_k(2 * it2->first + 1) - x_k(2 * it2->second + 1));                       // 2(y_i-y_j)
        G_k(2 * it2->second + 1) += scale * 2 * (x_k(2 * it2->second + 1) - x_k(2 * it2->first + 1));                      // 2(y_j-y_i)
        // wbxu- temporarily fix the symmetry axis
        // G_k(it-this->VSG.begin()+2*this->B_len) += scale*4*( 2*x_k(it-this->VSG.begin()+2*this->B_len)-x_k(2*it2->first)-x_k(2*it2->second) ); //
        // 4(2x_axis-x_i-x_j)
      }
    }
  }
  for (std::vector<int>::iterator it = this->HSG.begin(); it != this->HSG.end(); ++it) {
    // for each vertical symmetry group
    for (std::vector<pair<int, placerDB::Smark> >::iterator it2 = caseNL.SBlocks.at(*it).selfsym.begin(); it2 != caseNL.SBlocks.at(*it).selfsym.end(); ++it2) {
      // for each selfsymmetric block
      if (it2->first >= 0 && it2->first < caseNL.GetSizeofBlocks()) {
        G_k(2 * it2->first + 1) += scale * 2 * (x_k(2 * it2->first + 1) - x_k(it - this->HSG.begin() + 2 * this->B_len + this->VSG_len));  // 2(y_i-y_axis)
        // wbxu- temporarily fix the symmetry axis
        // G_k(it-this->HSG.begin()+2*this->B_len+this->VSG_len) += scale*2*( x_k(it-this->HSG.begin()+2*this->B_len+this->VSG_len)-x_k(2*it2->first+1) ); //
        // 2(y_axis-y_i)
      }
    }
    for (std::vector<pair<int, int> >::iterator it2 = caseNL.SBlocks.at(*it).sympair.begin(); it2 != caseNL.SBlocks.at(*it).sympair.end(); ++it2) {
      // for each symmetry pair
      if (it2->first >= 0 && it2->first < caseNL.GetSizeofBlocks() && it2->second >= 0 && it2->second < caseNL.GetSizeofBlocks()) {
        G_k(2 * it2->first + 1) +=
            scale * 2 *
            (x_k(2 * it2->first + 1) + x_k(2 * it2->second + 1) - 2 * x_k(it - this->HSG.begin() + 2 * this->B_len + this->VSG_len));  // 2(y_i+y_j-2y_axis)
        G_k(2 * it2->second + 1) +=
            scale * 2 *
            (x_k(2 * it2->first + 1) + x_k(2 * it2->second + 1) - 2 * x_k(it - this->HSG.begin() + 2 * this->B_len + this->VSG_len));  // 2(y_j+y_i-2y_axis)
        G_k(2 * it2->first) += scale * 2 * (x_k(2 * it2->first) - x_k(2 * it2->second));                                               // 2(x_i-x_j)
        G_k(2 * it2->second) += scale * 2 * (x_k(2 * it2->second) - x_k(2 * it2->first));                                              // 2(x_j-x_i)
        // wbxu- temporarily fix the symmetry axis
        // G_k(it-this->HSG.begin()+2*this->B_len+this->VSG_len) += scale*4*(
        // 2*x_k(it-this->HSG.begin()+2*this->B_len+this->VSG_len)-x_k(2*it2->first+1)-x_k(2*it2->second+1) ); // 4(2y_axis-y_i-y_j)
      }
    }
  }
}

double Aplace::CalculateWireLengthSmooth(design& caseNL, boost_vector& x_k, double alpha) {
  double sum = 0;
  // double scale;
  for (int i = 0; i < (int)caseNL.Nets.size(); ++i) {
    // std::cout<<"net: "<<i<<std::endl;
    double scale = 1;
    if (caseNL.Nets.at(i).priority.compare("min") == 0) {
      scale = 4;
    } else if (caseNL.Nets.at(i).priority.compare("mid") == 0) {
      scale = 2;
    }
    double x_pos_base = 0;
    double x_neg_base = 0;
    double y_pos_base = 0;
    double y_neg_base = 0;
    for (std::vector<placerDB::Node>::iterator it = caseNL.Nets.at(i).connected.begin(); it != caseNL.Nets.at(i).connected.end(); ++it) {
      if (it->type == placerDB::Block) {
        int iter = it->iter;
        int iter2 = it->iter2;
        placerDB::point LL;
        LL.x = x_k(iter2 * 2) - caseNL.GetBlockWidth(iter2, this->ABlocks.at(iter2).orient, this->selected.at(iter2)) / 2;
        LL.y = x_k(iter2 * 2 + 1) - caseNL.GetBlockHeight(iter2, this->ABlocks.at(iter2).orient, this->selected.at(iter2)) / 2;
        std::vector<placerDB::point> tmpp = caseNL.GetPlacedBlockPinAbsPosition(iter2, iter, this->ABlocks.at(iter2).orient, LL, this->selected.at(iter2));
        if (tmpp.empty()) {
          continue;
        }
        int x = INT_MAX, y = INT_MAX, X = INT_MIN, Y = INT_MIN;
        for (int w = 0; w < (int)tmpp.size(); ++w) {
          if (tmpp.at(w).x < x) {
            x = tmpp.at(w).x;
          }
          if (tmpp.at(w).y < y) {
            y = tmpp.at(w).y;
          }
          if (tmpp.at(w).x > X) {
            X = tmpp.at(w).x;
          }
          if (tmpp.at(w).y > Y) {
            Y = tmpp.at(w).y;
          }
        }
        x_pos_base += exp(X / alpha);
        x_neg_base += exp(-1.0 * x / alpha);
        y_pos_base += exp(Y / alpha);
        y_neg_base += exp(-1.0 * y / alpha);
      }
    }
    sum += scale * alpha * (log(x_pos_base) + log(x_neg_base) + log(y_pos_base) + log(y_neg_base));
  }
  return sum;
}

double Aplace::CalculateWireLength(design& caseNL, boost_vector& x_k) {
  double sum = 0;
  // int Xmax=this->width;
  // int Ymax=this->height;
  std::vector<placerDB::point> pos;
  placerDB::point p, bp;
  int alpha;
  std::vector<placerDB::point> pos_pin;
  // for each net
  for (std::vector<placerDB::net>::iterator ni = caseNL.Nets.begin(); ni != caseNL.Nets.end(); ++ni) {
    pos.clear();
    // bool hasTerminal=false;
    // int distTerm=INT_MIN;
    if ((ni->priority).compare("min") == 0) {
      alpha = 4;
    } else if ((ni->priority).compare("mid") == 0) {
      alpha = 2;
    } else {
      alpha = 1;
    }
    // alpha*=ni->weight; // add weight to reflect the modification for bigMacros
    // for each pin
    for (std::vector<placerDB::Node>::iterator ci = (ni->connected).begin(); ci != (ni->connected).end(); ++ci) {
      if (ci->type == placerDB::Block) {
        bp.x = x_k(2 * ci->iter2) - caseNL.GetBlockWidth(ci->iter2, this->ABlocks.at(ci->iter2).orient, this->selected.at(ci->iter2)) / 2;
        bp.y = x_k(2 * ci->iter2 + 1) - caseNL.GetBlockHeight(ci->iter2, this->ABlocks.at(ci->iter2).orient, this->selected.at(ci->iter2)) / 2;
        pos_pin = caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, this->ABlocks.at(ci->iter2).orient, bp, this->selected.at(ci->iter2));
        // pos_pin_all.push_back(pos_pin);
        for (unsigned int i = 0; i < pos_pin.size(); ++i) {
          p = pos_pin[i];
          pos.push_back(p);
          // if( caseNL.GetBlockSymmGroup(ci->iter2)==-1  ) { // not in any symmetry group
          //  if(p.x<distTerm) {distTerm=p.x;}
          //  if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x;}
          //  if(p.y<distTerm) {distTerm=p.y;}
          //  if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y;}
          //} else { // if in symmetry group
          //  if ( this->SGroups.at(caseNL.GetBlockSymmGroup(ci->iter2)).axis_dir==placerDB::V  ) {
          //    if(p.x<distTerm) {distTerm=p.x;}
          //    if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x;}
          //  } else if ( this->SGroups.at(caseNL.GetBlockSymmGroup(ci->iter2)).axis_dir==placerDB::H  ) {
          //    if(p.y<distTerm) {distTerm=p.y;}
          //    if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y;}
          //  }
          //}
        }
      } else if (ci->type == placerDB::Terminal) {
        // cout<<"Terminal "<<ci->iter<<" ";
        // hasTerminal=true;
      }
    }
    int x = 0;
    int y = 0;
    for (std::vector<placerDB::point>::iterator pi = pos.begin(); pi != pos.end(); ++pi) {
      for (std::vector<placerDB::point>::iterator qi = pi + 1; qi != pos.end(); ++qi) {
        if (abs((pi->x) - (qi->x)) > x) {
          x = abs((pi->x) - (qi->x));
        }
        if (abs((pi->y) - (qi->y)) > y) {
          y = abs((pi->y) - (qi->y));
        }
        // sum+=abs((pi->x)-(qi->x));
        // sum+=abs((pi->y)-(qi->y));
      }
    }
    sum += ((x + y) * alpha);
    // if(hasTerminal) {sum+=(distTerm*alpha);}//cout<<"; range: "<<distTerm<<endl;}
  }
  return sum;
}

void Aplace::AddWireLengthGradient(boost_vector& G_k, boost_vector& x_k, design& caseNL, double alpha, double beta) {
  // double scale;
  for (int i = 0; i < (int)caseNL.Nets.size(); ++i) {
    // std::cout<<"net: "<<i<<std::endl;
    double scale = 1;
    if (caseNL.Nets.at(i).priority.compare("min") == 0) {
      scale = 4;
    } else if (caseNL.Nets.at(i).priority.compare("mid") == 0) {
      scale = 2;
    }
    scale *= beta;
    double x_pos_base = 0;
    double x_neg_base = 0;
    double y_pos_base = 0;
    double y_neg_base = 0;
    for (std::vector<placerDB::Node>::iterator it = caseNL.Nets.at(i).connected.begin(); it != caseNL.Nets.at(i).connected.end(); ++it) {
      if (it->type == placerDB::Block) {
        int iter = it->iter;
        int iter2 = it->iter2;
        placerDB::point LL;
        LL.x = x_k(iter2 * 2) - caseNL.GetBlockWidth(iter2, this->ABlocks.at(iter2).orient, this->selected.at(iter2)) / 2;
        LL.y = x_k(iter2 * 2 + 1) - caseNL.GetBlockHeight(iter2, this->ABlocks.at(iter2).orient, this->selected.at(iter2)) / 2;
        std::vector<placerDB::point> tmpp = caseNL.GetPlacedBlockPinAbsPosition(iter2, iter, this->ABlocks.at(iter2).orient, LL, this->selected.at(iter2));
        if (tmpp.empty()) {
          continue;
        }
        int x = INT_MAX, y = INT_MAX, X = INT_MIN, Y = INT_MIN;
        for (int w = 0; w < (int)tmpp.size(); ++w) {
          if (tmpp.at(w).x < x) {
            x = tmpp.at(w).x;
          }
          if (tmpp.at(w).y < y) {
            y = tmpp.at(w).y;
          }
          if (tmpp.at(w).x > X) {
            X = tmpp.at(w).x;
          }
          if (tmpp.at(w).y > Y) {
            Y = tmpp.at(w).y;
          }
        }
        x_pos_base += exp(X / alpha);
        x_neg_base += exp(-1.0 * x / alpha);
        y_pos_base += exp(Y / alpha);
        y_neg_base += exp(-1.0 * y / alpha);
      }
    }
    // std::cout<<"x_pos_base: "<<x_pos_base<<" x_neg_base: "<<x_neg_base<<std::endl;
    // std::cout<<"y_pos_base: "<<y_pos_base<<" y_neg_base: "<<y_neg_base<<std::endl;
    for (std::vector<placerDB::Node>::iterator it = caseNL.Nets.at(i).connected.begin(); it != caseNL.Nets.at(i).connected.end(); ++it) {
      if (it->type == placerDB::Block) {
        int iter = it->iter;
        int iter2 = it->iter2;
        placerDB::point LL;
        LL.x = x_k(iter2 * 2) - caseNL.GetBlockWidth(iter2, this->ABlocks.at(iter2).orient, this->selected.at(iter2)) / 2;
        LL.y = x_k(iter2 * 2 + 1) - caseNL.GetBlockHeight(iter2, this->ABlocks.at(iter2).orient, this->selected.at(iter2)) / 2;
        std::vector<placerDB::point> tmpp = caseNL.GetPlacedBlockPinAbsPosition(iter2, iter, this->ABlocks.at(iter2).orient, LL, this->selected.at(iter2));
        if (tmpp.empty()) {
          continue;
        }
        int x = INT_MAX, y = INT_MAX, X = INT_MIN, Y = INT_MIN;
        for (int w = 0; w < (int)tmpp.size(); ++w) {
          if (tmpp.at(w).x < x) {
            x = tmpp.at(w).x;
          }
          if (tmpp.at(w).y < y) {
            y = tmpp.at(w).y;
          }
          if (tmpp.at(w).x > X) {
            X = tmpp.at(w).x;
          }
          if (tmpp.at(w).y > Y) {
            Y = tmpp.at(w).y;
          }
        }
        G_k(iter2 * 2) += (scale * exp(X / alpha) / x_pos_base - scale * exp(-1.0 * x / alpha) / x_neg_base);
        G_k(iter2 * 2 + 1) += (scale * exp(Y / alpha) / y_pos_base - scale * exp(-1.0 * y / alpha) / y_neg_base);
        // std::cout<<"Updte cell "<<iter2<<std::endl;
        // std::cout<<"x+"<<scale*exp( X/alpha )/x_pos_base<<" x-"<<scale*exp( -1.0*x/alpha )/x_neg_base<<std::endl;
        // std::cout<<"y+"<<scale*exp( Y/alpha )/y_pos_base<<" y-"<<scale*exp( -1.0*y/alpha )/y_neg_base<<std::endl;
      }
    }
  }
}

Aplace::Aplace(PnRDB::hierNode& node, design& caseNL, string opath) {
  placerDB::point pp;
  this->name = node.name;
  this->B_len = caseNL.GetSizeofBlocks();
  this->selected.resize(this->B_len);
  for (int i = 0; i < this->B_len; ++i) {
    this->selected.at(i) = node.Blocks.at(i).selectedInstance;
  }
  // this->VSG_len=0; this->HSG_len=0;
  this->ABlocks.clear();
  this->SGroups.clear();
  for (std::vector<PnRDB::blockComplex>::iterator it = node.Blocks.begin(); it != node.Blocks.end(); ++it) {
    Ablock tmpAB;
    pp.x = it->instance.at(it->selectedInstance).placedCenter.x;
    pp.y = it->instance.at(it->selectedInstance).placedCenter.y;
    tmpAB.center = pp;
    tmpAB.orient = placerDB::Omark(it->instance.at(it->selectedInstance).orient);
    this->ABlocks.push_back(tmpAB);
  }
  for (std::vector<placerDB::SymmBlock>::iterator it = caseNL.SBlocks.begin(); it != caseNL.SBlocks.end(); ++it) {
    Sgroup tmpSG;
    tmpSG.axis_dir = it->axis_dir;
    tmpSG.axis_coor = it->axis_coor;
    this->SGroups.push_back(tmpSG);
    if (it->axis_dir == placerDB::V) {
      VSG.push_back(it - caseNL.SBlocks.begin());
    }
    if (it->axis_dir == placerDB::H) {
      HSG.push_back(it - caseNL.SBlocks.begin());
    }
  }
  this->VSG_len = VSG.size();
  this->HSG_len = HSG.size();
  this->width = node.width;
  this->height = node.height;
  PrintAplace();
  ConjugateGrident(caseNL, opath);
  PrintAplace();
}

void Aplace::PrintABlocks() {
  auto logger = spdlog::default_logger()->clone("placer.Aplace.PrintABlocks");

  for (int i = 0; i < (int)this->ABlocks.size(); ++i) {
    logger->debug("Blcok {0} C {1} O {2}", this->ABlocks.at(i).center.x, this->ABlocks.at(i).center.y, this->ABlocks.at(i).orient);
  }
}

void Aplace::PrintSGroups() {
  auto logger = spdlog::default_logger()->clone("placer.Aplace.PrintSGroups");

  for (int i = 0; i < (int)this->SGroups.size(); ++i) {
    logger->debug("SGroup {0} dir {1} coor {2}", i, this->SGroups.at(i).axis_dir, SGroups.at(i).axis_coor);
  }
}

void Aplace::PrintAplace() {
  PrintABlocks();
  PrintSGroups();
}

placerDB::Omark Aplace::GetBlockOrient(int i) { return this->ABlocks.at(i).orient; }

placerDB::point Aplace::GetBlockCenter(int i) { return this->ABlocks.at(i).center; }

placerDB::Smark Aplace::GetSBlockDir(int i) { return this->SGroups.at(i).axis_dir; }

int Aplace::GetSBlockCorr(int i) { return this->SGroups.at(i).axis_coor; }
