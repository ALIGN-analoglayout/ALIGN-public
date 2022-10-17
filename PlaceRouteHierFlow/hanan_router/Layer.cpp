#include "Layer.h"
#include "Util.h"
#include <fstream>
#include <iostream>

#include "nlohmann/json.hpp"

namespace DRC {

using json = nlohmann::json;
LayerInfo::LayerInfo(const std::string& ljfile, const int uu) : _sbottom{nullptr}, _stop{nullptr},
 _cbottom{nullptr}, _ctop{nullptr}, _pbottom{nullptr}, _ptop{nullptr}, _topMetal{0}, _populated{false}
{
  if (ljfile.empty()) {
    CERR<< "missing layers.json file" <<std::endl;
    return;
  }
  std::ifstream ifs(ljfile);
  if (!ifs) {
    CERR << "unable to open layers file " << ljfile <<std::endl;
    return;
  }
  auto oj = json::parse(ifs);
  auto itAbs = oj.find("Abstraction");
  if (itAbs != oj.end()) {
    for (auto& l : *itAbs) {
      auto it = l.find("Layer");
      if (it != l.end()) {
        std::string name = *it;
        it = l.find("Stack");
        if (it == l.end()) {
          it = l.find("GdsLayerNo");
          int gdsNo = (it != l.end()) ? static_cast<int>(*it) : -1;
          it = l.find("UnitR");
          float mur(0), lr(0), ur(0);
          if (it != l.end()) {
            mur = (*it)["Mean"];
            lr = (*it)["L_3Sigma"];
            ur = (*it)["U_3Sigma"];
          }
          it = l.find("Pitch");
          MetalLayer* mlayer(nullptr);
          if (it != l.end() && it->is_number_integer()) {
            mlayer = new MetalLayer(gdsNo, name, mur, lr, ur);
            COUT << "layer resistance : " << name << ' ' << mur << ' ' << lr << ' ' << ur << std::endl;
            mlayer->setPitch(static_cast<int>(*it));
          }
          if (mlayer != nullptr) {
            it = l.find("Width");
            if (it != l.end() && it->is_number_integer()) mlayer->setWidth(static_cast<int>(*it) * uu);
            it = l.find("MinL");
            if (it != l.end() && it->is_number_integer()) mlayer->setMinL(static_cast<int>(*it) * uu);
            it = l.find("MaxL");
            if (it != l.end() && it->is_number_integer()) mlayer->setMaxL(static_cast<int>(*it) * uu);
            it = l.find("EndToEnd");
            if (it != l.end() && it->is_number_integer()) mlayer->setE2E(static_cast<int>(*it) * uu);
            it = l.find("Offset");
            if (it != l.end() && it->is_number_integer()) mlayer->setOffset(static_cast<int>(*it) * uu);
            it = l.find("Direction");
            if (it != l.end() && it->is_string()) mlayer->setDirection(*it == "H" ? 0 : (*it == "V" ? 1 : 2));
            _mlayers.push_back(mlayer);
            _mlayerNameMap[name] = mlayer;
            _mgrids.push_back(Grid(mlayer->pitch(), mlayer->offset()));
          }
        }
      }
    }
    for (auto& l : *itAbs) {
      auto it = l.find("Layer");
      if (it != l.end()) {
        std::string name = *it;
        it = l.find("Stack");
        if (it != l.end()) {
          MetalLayer* layer1(nullptr), *layer2(nullptr);
          if ((*it).is_array()) {
            for (auto i : {0,1}) {
              std::string l = (*it)[i].is_string() ? static_cast<std::string>((*it)[i]) : "";
              if (!l.empty()) {
                auto itm = _mlayerNameMap.find(l);
                if (itm != _mlayerNameMap.end()) {
                  if (i == 0) {
                    layer1 = itm->second;
                  } else {
                    layer2 = itm->second;
                  }
                }
              }
            }
          }
          if (layer1 != nullptr || layer2 != nullptr) {
            it = l.find("GdsLayerNo");
            int gdsNo = (it != l.end()) ? static_cast<int>(*it) : -1;
            it = l.find("R");
            float mur(0), lr(0), ur(0);
            if (it != l.end()) {
              mur = (*it)["Mean"];
              lr = (*it)["L_3Sigma"];
              ur = (*it)["U_3Sigma"];
            }
            ViaLayer* vlayer = new ViaLayer(gdsNo, name, mur, lr, ur);
            vlayer->setLayerPair(layer1, layer2);
            int x(0), y(0);
            it = l.find("WidthX");
            if (it != l.end() && it->is_number_integer()) x = static_cast<int>(*it) * uu;
            it = l.find("WidthY");
            if (it != l.end() && it->is_number_integer()) y = static_cast<int>(*it) * uu;
            vlayer->setWidth(x, y);
            x = y = 0;
            it = l.find("SpaceX");
            if (it != l.end() && it->is_number_integer()) x = static_cast<int>(*it) * uu;
            it = l.find("SpaceY");
            if (it != l.end() && it->is_number_integer()) y = static_cast<int>(*it) * uu;
            vlayer->setSpace(x, y);
            x = y = 0;
            it = l.find("VencA_L");
            if (it != l.end() && it->is_number_integer()) x = static_cast<int>(*it) * uu;
            it = l.find("VencP_L");
            if (it != l.end() && it->is_number_integer()) y = static_cast<int>(*it) * uu;
            vlayer->setCoverL(x, y);
            x = y = 0;
            it = l.find("VencA_H");
            if (it != l.end() && it->is_number_integer()) x = static_cast<int>(*it) * uu;
            it = l.find("VencP_H");
            if (it != l.end() && it->is_number_integer()) y = static_cast<int>(*it) * uu;
            vlayer->setCoverU(x, y);
            x = y = 0;
            it = l.find("ViaCut");
            if (it != l.end()) {
              auto itv = it->find("Gen");
              if (itv != it->end() && *itv == "ViaArrayGenerator") {
                int wx{0}, wy{0}, sx{0}, sy{0}, nx{1}, ny{1};
                itv = it->find("WidthX");
                if (itv != it->end() && itv->is_number_integer()) wx = static_cast<int>(*itv) * uu;
                itv = it->find("WidthY");
                if (itv != it->end() && itv->is_number_integer()) wy = static_cast<int>(*itv) * uu;
                itv = it->find("SpaceX");
                if (itv != it->end() && itv->is_number_integer()) sx = static_cast<int>(*itv) * uu;
                itv = it->find("SpaceY");
                if (itv != it->end() && itv->is_number_integer()) sy = static_cast<int>(*itv) * uu;
                itv = it->find("NumX");
                if (itv != it->end() && itv->is_number_integer()) nx = static_cast<int>(*itv);
                itv = it->find("NumY");
                if (itv != it->end() && itv->is_number_integer()) ny = static_cast<int>(*itv);
                vlayer->addViaArray(wx, wy, sx, sy, nx, ny);
              }
            }
            _vlayers.push_back(vlayer);
          }
        }
      }
    }
  }
  auto itd = oj.find("design_info");
  if (itd != oj.end()) {
    std::string layers[] = {"top_signal_routing_layer", "bottom_signal_routing_layer",
      "top_power_routing_layer", "bottom_power_grid_layer",
      "top_clock_routing_layer", "bottom_clock_routing_layer"};
    MetalLayer** mlayers[] = {&_stop, &_sbottom, &_ptop, &_pbottom, &_ctop, &_cbottom};
    for (unsigned i = 0; i < 6; ++i) {
      auto it = itd->find(layers[i]);
      if (it != itd->end()) {
        auto itm = _mlayerNameMap.find(*it);
        if (itm != _mlayerNameMap.end()) {
          *mlayers[i] = itm->second;
        }
      }
    }
  }
  _layers.insert(_layers.end(), _mlayers.begin(), _mlayers.end());
  _topMetal = (static_cast<int>(_layers.size()) - 1);
  _layers.insert(_layers.end(), _vlayers.begin(), _vlayers.end());
  for (unsigned i = 0; i < _layers.size(); ++i) {
    _layers[i]->setIndex(i);
    LAYER_NAMES.push_back(_layers[i]->name());
    _layerIndex[_layers[i]->name()] = static_cast<int>(i);
    COUT << "layer : " << _layers[i]->name() << " index : " << i << '\n';
    if (_layers[i]->isVia()) {
      auto vl = static_cast<ViaLayer*>(_layers[i]);
      for (auto& it : vl->viaArray()) {
        COUT << "\t va : " << it._sw._space.first << ' ' << it._sw._space.second << ' ' << it._nx << ' ' << it._ny << '\n';
      }
      COUT << " cover : l: " << vl->coverlx() << ',' << vl->coverly() << " u: " << vl->coverux() << ',' << vl->coveruy() << '\n';
      auto lp = vl->layers();
      if (lp.first && lp.first->isVertical()) {
        vl->swapcover(false);
      }
      if (lp.second && lp.second->isVertical()) {
        vl->swapcover(true);
      }
    }
  }
  COUT << "top metal layer : " << LAYER_NAMES[_topMetal] << '\n';
  COUT << "signal routing layers : " << (_sbottom? _sbottom->name() : "unsp") << " : " << (_stop ? _stop->name() : "unsp") << "\n";
  COUT << "power  routing layers : " << (_pbottom? _pbottom->name() : "unsp") << " : " << (_ptop ? _ptop->name() : "unsp") << "\n";
  COUT << "clock  routing layers : " << (_cbottom? _cbottom->name() : "unsp") << " : " << (_ctop ? _ctop->name() : "unsp") << "\n";
  _populated = true;
}

LayerInfo::~LayerInfo()
{
  _vldn.clear();
  _vlup.clear();
  for (auto& v : _vlayers) delete v;
  for (auto& m : _mlayers) delete m;
}

};
