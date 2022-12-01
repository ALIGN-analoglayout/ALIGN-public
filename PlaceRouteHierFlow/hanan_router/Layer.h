#ifndef LAYER_H_
#define LAYER_H_

#include <string>
#include <vector>
#include <iostream>
#include <map>
#include "Geom.h"

namespace DRC {

using namespace std; 

enum class Direction {
  HORIZONTAL,
  VERTICAL,
  ORTHOGONAL
};

enum class LayerType {
  METAL,
  VIA
};

class Layer {
  private:
    const int _gdsNo;
    const std::string _name;
    const float _r[3]; // mean, -3\sigma, 3\sigma
    const LayerType _type;
    int _index;
  public:
    Layer(const int gdsNo, const std::string& name, const float mur, const float lr, const float ur, const LayerType type)
      : _gdsNo(gdsNo), _name(name), _r{mur, lr, ur}, _type{type}, _index{-1} {}
    int gdsNo() const { return _gdsNo; }
    const std::string& name() const { return _name; }
    float meanR() const { return _r[0]; }
    bool isMetal() const { return _type == LayerType::METAL; }
    bool isVia() const { return _type == LayerType::VIA; }
    void setIndex(const int i) { _index = i; }
    int index() const { return _index; }
    ~Layer()
    {
      //std::cout << "layer : " << _name << ' ' << _gdsNo << " {" << _r[0] << ',' << _r[1] << ',' << _r[2] << "}\n";
    }
};
typedef std::vector<Layer*> Layers;

class gdsDatatype {
  public:
    int _draw{0}, _pin{0}, _label{0}, _blockage{0};
};

class Grid {
  private:
    int _pitch, _offset;
  public:
    Grid(const int pitch = 0, const int offset = 0) : _pitch{pitch}, _offset{offset} {}
    void setPitchOffset(const int pitch, const int offset) { _pitch = pitch; _offset = offset; }
    const int snapUp(const int val) const {
      auto rem = (val - _offset) % _pitch;
      return rem ? (val + _offset - rem) : val;
    }
    const int snapDn(const int val) const {
      auto rem = (val - _offset) % _pitch;
      return val - ((val - _offset) % _pitch);
    }
    bool isPtOnGrid(const int val) const { return ((val - _offset) % _pitch) ? false : true; }
};

class MetalLayer : public Layer {
  private:
    int _pitch, _width, _minL, _maxL;
    int _e2e, _offset;
    float _c[3], _cc[3];
    Direction _dir;
    Grid _grid;
  public:
    MetalLayer(const int gdsNo, const std::string& name, const float mur, const float lr, const float ur)
      : Layer(gdsNo, name, mur, lr, ur, LayerType::METAL), _pitch(0), _width(0), _minL(0), _maxL(0), _e2e(0), _offset(0),
    _c{0,0,0}, _cc{0, 0, 0}, _dir(Direction::ORTHOGONAL) {}
    int pitch() const { return _pitch;}
    int width() const { return _width;}
    int space() const
    {
      return (_pitch > _width) ? (_pitch - _width) : _pitch;
    }
    int offset() const { return _offset; }
    void setPitch(const int p) {_pitch = p;}
    void setWidth(const int w) {_width = w;}
    void setMinL(const int l) {_minL = l;}
    void setMaxL(const int l) {_maxL = l;}
    void setE2E(const int e) {_e2e = e;}
    void setOffset(const int o) {_offset = o;}
    void setGrid() { _grid.setPitchOffset(_pitch, _offset); }
    void setDirection(const int dir) { _dir = (dir == 0 ? Direction::HORIZONTAL : (dir == 1 ? Direction::VERTICAL : Direction::ORTHOGONAL)); }
    void setC(const float muc, const float lc, const float uc) { _c[0] = muc; _c[1] = lc; _c[2] = uc; }
    void setCC(const float muc, const float lc, const float uc) { _cc[0] = muc; _cc[1] = lc; _cc[2] = uc; }
    bool isHorizontal() const { return _dir == Direction::HORIZONTAL || _dir == Direction::ORTHOGONAL; }
    bool isVertical() const { return _dir == Direction::VERTICAL || _dir == Direction::ORTHOGONAL; }
    ~MetalLayer()
    {
      //std::cout << _pitch << ' ' << _width << ' ' << _minL << ' ' << _maxL << ' ' << _e2e << ' ' << _offset << ' ';
      //std::cout << (_dir == Direction::HORIZONTAL ? "hor" : "ver") << ' ';
    }
    Geom::Rect snapToGrid(const Geom::Rect& r) const
    {
      if (isHorizontal()) {
        return Geom::Rect(_grid.snapDn(r.xmin()), r.ymin(),
            _grid.snapUp(r.xmax()), r.ymax());
      } else if (isVertical()) {
        return Geom::Rect(r.xmin(), _grid.snapDn(r.ymin()),
            r.xmax(), _grid.snapUp(r.ymax()));
      }
      return r;
    }
    const int snapUp(const int val) const { return _grid.snapUp(val); }
    const int snapDn(const int val) const { return _grid.snapDn(val); }

};
typedef std::vector<MetalLayer*> MetalLayers;

struct SpaceWidth {
  std::pair<int, int> _space, _width; // 0 : x, 1 : y
  SpaceWidth() : _space{0, 0}, _width{0, 0} {}
};
struct ViaArray {
  SpaceWidth _sw;
  int _nx, _ny;
  ViaArray() : _sw{}, _nx{0}, _ny{0} {}
  ViaArray(const int  wx, const int wy, const int sx, const int sy, const int nx, const int ny)
  {
    _sw._space = std::make_pair(sx, sy);
    _sw._width = std::make_pair(wx, wy);
    _nx = nx;
    _ny = ny;
  }
  const std::string str() const
  {
    return std::string(
        "w : " + std::to_string(_sw._width.first) + ", " + std::to_string(_sw._width.second) +
        "s : " + std::to_string(_sw._space.first) + ", " + std::to_string(_sw._space.second) +
        "n : " + std::to_string(_nx) + ", " + std::to_string(_ny)
        );
  }
};
typedef std::vector<ViaArray> ViaArrays;

class ViaLayer : public Layer {
  private:
    SpaceWidth _sw;
    std::pair<const MetalLayer*, const MetalLayer*> _layerPair; // first : lower, second : upper
    int _coverl[2], _coveru[2]; // 0 : low, 1 : high
    ViaArrays _va;
  public:
    ViaLayer(const int gdsNo, const std::string& name, const float mur, const float lr, const float ur)
      : Layer(gdsNo, name, mur, lr, ur, LayerType::VIA), _sw{}, _layerPair(nullptr, nullptr),
      _coverl{0, 0}, _coveru{0, 0} {}
    void setSpace(const int x, const int y) {_sw._space.first = x; _sw._space.second = y;}
    void setWidth(const int x, const int y) {_sw._width.first = x; _sw._width.second = y;}
    void setCoverL(const int x, const int y) {_coverl[0] = x; _coverl[1] = y;}
    void setCoverU(const int x, const int y) {_coveru[0] = x; _coveru[1] = y;}
    void setLayerPair(const MetalLayer* m1, const MetalLayer* m2) {_layerPair = std::make_pair(m1, m2); }
    void addViaArray(const int wx, const int wy, const int sx, const int sy, const int nx, const int ny)
    {
      _va.push_back(ViaArray(wx, wy, sx, sy, nx, ny));
    }
    ~ViaLayer()
    {
      //std::cout << _sw._space[0] << ' ' << _sw._space[1] << " -- " << _width[0] << ' ' << _width[1] << ' ';
      //std::cout << (_layerPair.first ? _layerPair.first->name() : " ") << ' ';
      //std::cout << (_layerPair.second ? _layerPair.second->name() : " ") << ' ';
      //std::cout << _coverl[0] << ' ' << _coverl[1] << " -- " << _coveru[0] << ' ' << _coveru[1] << ' ';
    }
    const std::vector<ViaArray>& viaArray() const { return _va; }
    const std::pair<const MetalLayer*, const MetalLayer*>& layers() const { return _layerPair; }
    int widthx() const { return _sw._width.first; }
    int widthy() const { return _sw._width.second; }
    int coverlx() const { return _coverl[0]; }
    int coverly() const { return _coverl[1]; }
    int coverux() const { return _coveru[0]; }
    int coveruy() const { return _coveru[1]; }
    void swapcover(bool up)
    {
      if (up) std::swap(_coveru[0], _coveru[1]); 
      else std::swap(_coverl[0], _coverl[1]); 
    }
    int spacex() const { return _sw._space.first; }
    int spacey() const { return _sw._space.second; }

};
typedef std::vector<ViaLayer*> ViaLayers;

class LayerInfo {
  private:
    MetalLayers _mlayers;
    ViaLayers _vlayers;
    Layers _layers;
    std::map<std::string, int> _layerIndex;
    std::map<const MetalLayer*, const ViaLayer*> _vldn, _vlup;
    std::map<std::string, MetalLayer*> _mlayerNameMap;
    MetalLayer *_sbottom, *_stop, *_cbottom, *_ctop, *_pbottom, *_ptop;
    int _topMetal;
    bool _populated;
  public:
    LayerInfo(const std::string& lj, const int uu);
    void print() const;
    ~LayerInfo();
    const std::string& getLayerName(const int i) const { return _layers[i]->name(); }
    int getLayerIndex(const std::string& name) const
    {
      auto it = _layerIndex.find(name);
      return ((it != _layerIndex.end()) ? it->second : -1);
    }
    int space(const int l, const bool x) const
    {
      int s(0);
      auto layer = (static_cast<unsigned>(l) < _layers.size()) ? _layers[l] : nullptr;
      if (layer) {
        if (layer->isMetal()) {
          return static_cast<MetalLayer*>(layer)->space();
        } else {
          return x ? static_cast<ViaLayer*>(layer)->spacex() :
            static_cast<ViaLayer*>(layer)->spacey();
        }
      }
      return s;
    }
    int spacex(const int l) const { return space(l, true); }
    int spacey(const int l) const { return space(l, false); }
    std::pair<int, int> getLayers(const ViaLayer* v) const
    {
      auto l = v->layers();
      if (l.first && l.second) return std::make_pair(l.first->index(), l.second->index());
      return std::make_pair(-1, -1);
    }
    const Layers& layers() const { return _layers; }
    int signalBottomLayer() const 
    {
      if (_sbottom) return _sbottom->index();
      for (int i = 0; i < static_cast<int>(_layers.size()); ++i) {
        if (_layers[i]->name() == "M1") return i;
      }
      return 0;
    }
    int signalTopLayer() const { return (_stop ? _stop->index() : _topMetal); }
    bool populated() const { return _populated; }
    bool isVertical(const int z) const
    {
      if (z < static_cast<int>(_layers.size()) && _layers[z]->isMetal()) {
        return static_cast<MetalLayer*>(_layers[z])->isVertical();
      }
      return true;
    }
    bool isHorizontal(const int z) const
    {
      if (z < static_cast<int>(_layers.size()) && _layers[z]->isMetal()) {
        return static_cast<MetalLayer*>(_layers[z])->isHorizontal();
      }
      return true;
    }
    Geom::Rect snapToGrid(const Geom::Rect& r, const int layer) const
    {
      if (layer < _mlayers.size()) return _mlayers[layer]->snapToGrid(r);
      return r;
    }
    Geom::Rect snapToGrid(const Geom::Rect& r, const int llayer, const int ulayer) const
    {
      if (_mlayers[llayer]->isHorizontal() && _mlayers[ulayer]->isVertical()) {
        return Geom::Rect(_mlayers[llayer]->snapDn(r.xmin()), _mlayers[ulayer]->snapDn(r.ymin()),
            _mlayers[llayer]->snapUp(r.xmax()), _mlayers[ulayer]->snapUp(r.ymax()));
      } else if (_mlayers[llayer]->isVertical() && _mlayers[ulayer]->isHorizontal()) {
        return Geom::Rect(_mlayers[ulayer]->snapDn(r.xmin()), _mlayers[llayer]->snapDn(r.ymin()),
            _mlayers[ulayer]->snapUp(r.xmax()), _mlayers[llayer]->snapUp(r.ymax()));
      }
      return r;
    }
};

}

#endif
