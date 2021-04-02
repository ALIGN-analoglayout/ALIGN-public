#include "IntPlot.h"

MatPlotGen::MatPlotGen(const string& name) : _cnt(0), _xmin(INT_MAX), _ymin(INT_MAX), _xmax(INT_MIN), _ymax(INT_MIN)
{
    _ofs = std::ofstream(name + "_detail_plot_gen.py");
    if (_ofs.is_open()) {
      _ofs << "import numpy as np\nimport matplotlib.pyplot as plt\nimport matplotlib.patches as patches\n";
      _ofs << "from matplotlib.widgets import Slider\nimport numpy.random as nr\n\n";

      _ofs << "fig = plt.figure()\n";

      _ofs << "coords = [\n";

    }
}

MatPlotGen::~MatPlotGen()
{
  if (_ofs.is_open()) {
    if (_cnt) {
      _ofs << "]\n";
      _ofs << "cells = [";
      for (auto& it : _cells) {
        _ofs << "'" << it << "', ";
      }
      _ofs << "]\n";
      _ofs << "ax = fig.add_subplot(211)\n";
      _ofs << "costHeader = [" << _costComp << "]\n";
      _ofs << "markers=['+', '*', '^', 's', 'p', 'h', '8']\n";
      _ofs << "colors=['red', 'green', 'blue', 'orange', 'cyan', 'magenta']\n";
      _ofs << "#ax.set_prop_cycle(marker=['o', 'v', '^', '+', 'x', '*', 'p', 's', 'h', 'd'], )\n";
      _ofs << "for k in range(4*len(cells), len(coords[0])):\n";
      _ofs << "\tax.plot([x[k] for x in coords], color = colors[(k-4*len(cells))%len(colors)], marker = markers[(k-4*len(cells))%len(markers)], label=costHeader[k-4*len(cells)])\n";
      _ofs << "ax.legend(loc=\"upper right\", bbox_to_anchor=(1.1, 1.0))\n";
      _ofs << "plt.xlabel('iter')\n";
      _ofs << "plt.ylabel('Cost')\n";
      _ofs << "ax.grid()\n\n";

      _ofs << "ax = fig.add_subplot(212)\n";
      _ofs << "iter = 0\n";
      _ofs << "plt.xlim([" << _xmin-2 << ", " << _xmax+2 << "])\n";
      _ofs << "plt.ylim([" << _ymin-2 << ", " << _ymax+2 << "])\n";
      _ofs << "for i in range(len(cells)):\n";
      _ofs << "\tj = 4*i;k=j + 1;l=k+1;m=l+1;\n";
      _ofs << "\tw = coords[iter][l]-coords[iter][j]\n";
      _ofs << "\th = coords[iter][m]-coords[iter][k]\n";
      _ofs << "\tr = patches.Rectangle((coords[iter][j], coords[iter][k]), w, h, ec='b', alpha=0.5, fill=False, lw=2)\n";
      _ofs << "\tax.add_patch(r)\n";
      _ofs << "\tax.text(coords[iter][j], coords[iter][k], cells[i])\n";
      _ofs << "sliderCoord = plt.axes([0.15, 0.02, 0.65, 0.02])\n";
      _ofs << "iterSlider = Slider(sliderCoord, 'Iter', 0, " << _cnt-1 <<", valinit=0, valstep=1.)\nax.autoscale_view()\n";
      _ofs << "def update(val):\n";
      _ofs << "\tax.patches = []\n";
      _ofs << "\tax.texts = []\n";
      _ofs << "\titer = int(iterSlider.val)\n";
      _ofs << "\tfor i in range(len(cells)):\n";
      _ofs << "\t\tj = 4*i;k=j + 1;l=k+1;m=l+1;\n";
      _ofs << "\t\tw = coords[iter][l]-coords[iter][j]\n";
      _ofs << "\t\th = coords[iter][m]-coords[iter][k]\n";
      _ofs << "\t\tr = patches.Rectangle((coords[iter][j], coords[iter][k]), w, h, ec='b', alpha=0.5, fill=False, lw=2)\n";
      _ofs << "\t\tax.add_patch(r)\n";
      _ofs << "\t\tax.text(coords[iter][j], coords[iter][k], cells[i])\n";
      _ofs << "\tfig.canvas.draw_idle()\n";
      _ofs << "iterSlider.on_changed(update)\n";
      _ofs << "plt.grid()\n";
      _ofs << "plt.show()" << std::endl;
    }
    _ofs.close();
  }
}

void MatPlotGen::addCells(const design& des)
{
  for (int i = 0; i < des.Blocks.size(); ++i) {
    _cells.insert(const_cast<design&>(des).GetBlockName(i));
  }
}

void MatPlotGen::addRow(const design& des, const SeqPair& curr_sp, const ILP_solver& ilp, const string& costStr)
{
  ++_cnt;
  if (_ofs.is_open()) {
    CellBoxMap coords;
    for (int i = 0; i < des.Blocks.size(); ++i) {
      PnRDB::bbox bbox(INT_MAX, INT_MAX, INT_MIN, INT_MIN);
      const vector<placerDB::point>& newp = des.Blocks[i][curr_sp.selected[i]].boundary.polygon;
      for (int it = 0; it < newp.size(); it++) {
        auto x = newp[it].x + ilp.Blocks[i].x;
        auto y = newp[it].y + ilp.Blocks[i].y;
        bbox.LL.x = std::min(x, bbox.LL.x);
        bbox.LL.y = std::min(y, bbox.LL.y);
        bbox.UR.x = std::max(x, bbox.UR.x);
        bbox.UR.y = std::max(y, bbox.UR.y);
      }
      coords[des.Blocks[i][curr_sp.selected[i]].name] = bbox;
    }
    _ofs << "[";
    for (auto& c : _cells) {
      auto it = coords.find(c);
      if (it != coords.end()) {
        _xmin = std::min(it->second.LL.x, _xmin);
        _ymin = std::min(it->second.LL.y, _ymin);
        _xmax = std::max(it->second.UR.x, _xmax);
        _ymax = std::max(it->second.UR.y, _ymax);
        _ofs << it->second.LL.x << ", " << it->second.LL.y << ", ";
        _ofs << it->second.UR.x << ", " << it->second.UR.y << ", ";
      }
    }
    _ofs << costStr << "],\n";
  }
}
