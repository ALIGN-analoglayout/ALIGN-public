#ifndef CAPPLACERIFC_h_
#define CAPPLACERIFC_h_

class Placer_Router_Cap;

class Placer_Router_Cap_Ifc
{
 private:
    Placer_Router_Cap *_ptr;
 public:
    Placer_Router_Cap_Ifc(const string& opath, const string& fpath, PnRDB::hierNode & current_node, PnRDB::Drc_info &drc_info, const map<string, PnRDB::lefMacro> &lefData, bool aspect_ratio, int num_aspect);
    ~Placer_Router_Cap_Ifc();
    Placer_Router_Cap *get() const { return _ptr;}
};

#endif
