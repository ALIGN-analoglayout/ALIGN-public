#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <pybind11/stl_bind.h>
#include <pybind11/iostream.h>

namespace py = pybind11;
using namespace pybind11::literals;

#include "spdlog/spdlog.h"
#include "spdlog/sinks/base_sink.h"
#include <spdlog/details/null_mutex.h>
#include <mutex>

#include "PnRDB/PnRdatabase.h"
#include "cap_placer/CapPlacerIfc.h"
#include "placer/PlacerIfc.h"
#include "guard_ring/GuardRingIfc.h"
#include "router/Router.h"
#include "MNA/MNASimulationIfc.h"
//#include "toplevel.h"

using namespace PnRDB;
using std::string;

template<typename Mutex>
class align_sink : public spdlog::sinks::base_sink <Mutex>
{
protected:

    void sink_it_(const spdlog::details::log_msg& msg) override
    {
      auto pylogger = py::module_::import("logging").attr("getLogger")(
        std::string("PnR.") + fmt::to_string(msg.logger_name)
      );
      spdlog::memory_buf_t formatted;
      spdlog::sinks::base_sink<Mutex>::formatter_->format(msg, formatted);
      // HACK: python.logging log-level is currently 10x of sequivalent spdlog level
      //       May need to be changed if spdlog or python.logging changes
      pylogger.attr("log")(static_cast<int>(msg.level)*10, fmt::to_string(msg.payload));
    }

    void flush_() override
    {
      std::cout << std::flush;
    }
};

using align_sink_mt = align_sink<std::mutex>;
using align_sink_st = align_sink<spdlog::details::null_mutex>;

void _bind_spdlog_to_python_logger() {
  // Set up logging defaults before doing anything else
  int pylevel = py::cast<int>(py::module_::import("logging").attr("getLogger")().attr("level"));
  spdlog::set_default_logger(std::make_shared<spdlog::logger>("default", std::make_shared<align_sink_mt>()));
  spdlog::set_level(static_cast<spdlog::level::level_enum>(pylevel/ 10));
  spdlog::set_error_handler([](const std::string& msg) {
		std::cerr << msg << std::endl;
	});
}

PYBIND11_MODULE(PnR, m) {

  _bind_spdlog_to_python_logger();

  m.doc() = "pybind11 plugin for PnR";

  py::class_<point>( m, "point")
    .def( py::init<>())
    .def( py::init<int, int>())
    .def_readwrite("x", &point::x)
    .def_readwrite("y", &point::y);
  py::class_<bbox>( m, "bbox")
    .def( py::init<>())
    .def( py::init<int, int, int, int>())
    .def( py::init<const bbox&>())
    .def( py::init<const point&, const point&>())
    .def( py::init<const point&, const point&>())
    .def( "center", &bbox::center)
    .def_readwrite("LL", &bbox::LL)
    .def_readwrite("UR", &bbox::UR);
  py::class_<contact>( m, "contact")
    .def( py::init<>())
    .def( py::init<const contact&>())
    .def_readwrite("metal", &contact::metal)
    .def_readwrite("originBox", &contact::originBox)
    .def_readwrite("placedBox", &contact::placedBox)
    .def_readwrite("originCenter", &contact::originCenter)
    .def_readwrite("placedCenter", &contact::placedCenter);
  py::class_<tileEdge>( m, "tileEdge")
    .def( py::init<>())
    .def_readwrite("next", &tileEdge::next)
    .def_readwrite("capacity", &tileEdge::capacity);
  py::class_<tile>( m, "tile")
    .def( py::init<>())
    .def_readwrite("x", &tile::x)
    .def_readwrite("y", &tile::y)
    .def_readwrite("width", &tile::width)
    .def_readwrite("height", &tile::height)
    .def_readwrite("metal", &tile::metal)
    .def_readwrite("tileLayer", &tile::tileLayer)
    .def_readwrite("index", &tile::index)
    .def_readwrite("Yidx", &tile::Yidx)
    .def_readwrite("Xidx", &tile::Xidx)
    .def_readwrite("north", &tile::north)
    .def_readwrite("south", &tile::south)
    .def_readwrite("east", &tile::east)
    .def_readwrite("west", &tile::west)
    .def_readwrite("down", &tile::down)
    .def_readwrite("up", &tile::up);
  py::class_<connectNode>( m, "connectNode")
    .def( py::init<>())
    .def_readwrite("type", &connectNode::type)
    .def_readwrite("iter", &connectNode::iter)
    .def_readwrite("iter2", &connectNode::iter2);
  py::class_<globalContact>( m, "globalContact")
    .def( py::init<>())
    .def_readwrite("conTact", &globalContact::conTact)
    .def_readwrite("metalIdx", &globalContact::metalIdx);
  py::class_<net>( m, "net")
    .def( py::init<>())
    .def_readwrite("name", &net::name)
    .def_readwrite("shielding", &net::shielding)
    .def_readwrite("sink2Terminal", &net::sink2Terminal)
    .def_readwrite("degree", &net::degree)
    .def_readwrite("symCounterpart", &net::symCounterpart)
    .def_readwrite("iter2SNetLsit", &net::iter2SNetLsit)
    .def_readwrite("connected", &net::connected)
    .def_readwrite("priority", &net::priority)
    .def_readwrite("segments", &net::segments)
    .def_readwrite("interVias", &net::interVias)
    .def_readwrite("path_metal", &net::path_metal)
    .def_readwrite("GcellGlobalRouterPath", &net::GcellGlobalRouterPath)
    .def_readwrite("path_via", &net::path_via)
    .def_readwrite("axis_dir", &net::axis_dir)
    .def_readwrite("axis_coor", &net::axis_coor)
    .def_readwrite("connectedTile", &net::connectedTile);
  py::class_<Metal>( m, "Metal")
    .def( py::init<>())
    .def_readwrite("MetalIdx", &Metal::MetalIdx)
    .def_readwrite("LinePoint", &Metal::LinePoint)
    .def_readwrite("width", &Metal::width)
    .def_readwrite("MetalRect", &Metal::MetalRect);
  py::class_<pin>( m, "pin")
    .def( py::init<>())
    .def_readwrite("name", &pin::name)
    .def_readwrite("type", &pin::type)
    .def_readwrite("use", &pin::use)
    .def_readwrite("netIter", &pin::netIter)
    .def_readwrite("pinContacts", &pin::pinContacts)
    .def_readwrite("pinVias", &pin::pinVias);
  py::class_<Via>( m, "Via")
    .def( py::init<>())
    .def_readwrite("model_index", &Via::model_index)
    .def_readwrite("originpos", &Via::originpos)
    .def_readwrite("placedpos", &Via::placedpos)
    .def_readwrite("UpperMetalRect", &Via::UpperMetalRect)
    .def_readwrite("LowerMetalRect", &Via::LowerMetalRect)
    .def_readwrite("ViaRect", &Via::ViaRect);
  py::class_<PowerNet>( m, "PowerNet")
    .def( py::init<>())
    .def_readwrite("name", &PowerNet::name)
    .def_readwrite("power", &PowerNet::power)
    .def_readwrite("Pins", &PowerNet::Pins)
    .def_readwrite("connected", &PowerNet::connected)
    .def_readwrite("dummy_connected", &PowerNet::dummy_connected)
    .def_readwrite("path_metal", &PowerNet::path_metal)
    .def_readwrite("path_via", &PowerNet::path_via);
  py::class_<block>( m, "block")
    .def( py::init<>())
    .def_readwrite("name", &block::name)
    .def_readwrite("master", &block::master)
    .def_readwrite("lefmaster", &block::lefmaster)
    .def_readwrite("type", &block::type)
    .def_readwrite("width", &block::width)
    .def_readwrite("height", &block::height)
    .def_readwrite("isLeaf", &block::isLeaf)
    .def_readwrite("originBox", &block::originBox)
    .def_readwrite("originCenter", &block::originCenter)
    .def_readwrite("gdsFile", &block::gdsFile)
    .def_readwrite("orient", &block::orient)
    .def_readwrite("placedBox", &block::placedBox)
    .def_readwrite("placedCenter", &block::placedCenter)
    .def_readwrite("PowerNets", &block::PowerNets)
    .def_readwrite("blockPins", &block::blockPins)
    .def_readwrite("interMetals", &block::interMetals)
    .def_readwrite("dummy_power_pin", &block::dummy_power_pin);
  py::class_<terminal>( m, "terminal")
    .def( py::init<>())
    .def_readwrite("name", &terminal::name)
    .def_readwrite("type", &terminal::type)
    .def_readwrite("netIter", &terminal::netIter)
    .def_readwrite("termContacts", &terminal::termContacts);
  py::class_<blockComplex>( m, "blockComplex")
    .def( py::init<>())
    .def_readwrite("instance", &blockComplex::instance)
    .def_readwrite("selectedInstance", &blockComplex::selectedInstance)
    .def_readwrite("child", &blockComplex::child)
    .def_readwrite("instNum", &blockComplex::instNum);
  py::class_<PowerGrid>( m, "PowerGrid")
    .def( py::init<>())
    .def_readwrite("name", &PowerGrid::name)
    .def_readwrite("metals", &PowerGrid::metals)
    .def_readwrite("vias", &PowerGrid::vias);
  py::class_<layoutAS>( m, "layoutAS")
    .def( py::init<>())
    .def_readwrite("width", &layoutAS::width)
    .def_readwrite("height", &layoutAS::height)
    .def_readwrite("HPWL", &layoutAS::HPWL)
    .def_readwrite("HPWL_extend", &layoutAS::HPWL_extend)
    .def_readwrite("gdsFile", &layoutAS::gdsFile)
    .def_readwrite("Blocks", &layoutAS::Blocks)
    .def_readwrite("Nets", &layoutAS::Nets)
    .def_readwrite("Terminals", &layoutAS::Terminals)
    .def_readwrite("LL", &layoutAS::LL)
    .def_readwrite("UR", &layoutAS::UR);
  py::class_<hierNode>( m, "hierNode")
      .def( py::init<>())
      .def( py::init<hierNode>())
      .def_readwrite("isCompleted", &hierNode::isCompleted)
      .def_readwrite("isTop", &hierNode::isTop)
      .def_readwrite("isIntelGcellGlobalRouter", &hierNode::isIntelGcellGlobalRouter)
      .def_readwrite("width", &hierNode::width)
      .def_readwrite("height", &hierNode::height)
      .def_readwrite("LL", &hierNode::LL)
      .def_readwrite("UR", &hierNode::UR)
      .def_readwrite("abs_orient", &hierNode::abs_orient)
      .def_readwrite("n_copy", &hierNode::n_copy)
      .def_readwrite("numPlacement", &hierNode::numPlacement)
      .def_readwrite("name", &hierNode::name)
      .def_readwrite("concrete_name", &hierNode::concrete_name)
      .def_readwrite("gdsFile", &hierNode::gdsFile)
      .def_readwrite("parent", &hierNode::parent)
      .def_readwrite("Blocks", &hierNode::Blocks)
      .def_readwrite("tiles_total", &hierNode::tiles_total)
      .def_readwrite("Nets", &hierNode::Nets)
      .def_readwrite("Terminals", &hierNode::Terminals)
      .def_readwrite("Vdd", &hierNode::Vdd)
      .def_readwrite("Gnd", &hierNode::Gnd)
      .def_readwrite("PowerNets", &hierNode::PowerNets)
      .def_readwrite("blockPins", &hierNode::blockPins)
      .def_readwrite("interMetals", &hierNode::interMetals)
      .def_readwrite("interVias", &hierNode::interVias)
      .def_readwrite("PnRAS", &hierNode::PnRAS)
      .def_readwrite("SNets", &hierNode::SNets)
      .def_readwrite("SPBlocks", &hierNode::SPBlocks)
      .def_readwrite("Preplace_blocks", &hierNode::Preplace_blocks)
      .def_readwrite("Alignment_blocks", &hierNode::Alignment_blocks)
      .def_readwrite("Match_blocks", &hierNode::Match_blocks)
      .def_readwrite("CC_Caps", &hierNode::CC_Caps)
      .def_readwrite("R_Constraints", &hierNode::R_Constraints)
      .def_readwrite("C_Constraints", &hierNode::C_Constraints)
      .def_readwrite("Port_Location", &hierNode::Port_Location)
      .def_readwrite("Guardring_Consts", &hierNode::Guardring_Consts)
      .def_readwrite("bias_Hgraph", &hierNode::bias_Hgraph)
      .def_readwrite("bias_Vgraph", &hierNode::bias_Vgraph)
      .def_readwrite("compact_style", &hierNode::compact_style)
      .def_readwrite("router_report", &hierNode::router_report)
      .def_readwrite("Block_name_map", &hierNode::Block_name_map)
      .def_readonly("HPWL", &hierNode::HPWL)
      .def_readonly("HPWL_extend", &hierNode::HPWL_extend)
      .def_readonly("HPWL_norm", &hierNode::HPWL_norm)
      .def_readonly("area_norm", &hierNode::area_norm)
      .def_readonly("cost", &hierNode::cost)
      .def_readonly("constraint_penalty", &hierNode::constraint_penalty)
      .def_readwrite("GuardRings", &hierNode::GuardRings);
  py::class_<Guardring_Const>( m, "Guardring_Const")
    .def( py::init<>())
    .def_readwrite("block_name", &Guardring_Const::block_name)
    .def_readwrite("guard_ring_primitives", &Guardring_Const::guard_ring_primitives)
    .def_readwrite("global_pin", &Guardring_Const::global_pin)
    ;
  py::class_<SymmNet>( m, "SymmNet")
    .def( py::init<>())
    .def_readwrite("net1", &SymmNet::net1)
    .def_readwrite("net2", &SymmNet::net2)
    .def_readwrite("iter1", &SymmNet::iter1)
    .def_readwrite("iter2", &SymmNet::iter2);
  py::class_<SymmPairBlock>( m, "SymmPairBlock")
    .def( py::init<>())
    .def_readwrite("sympair", &SymmPairBlock::sympair)
    .def_readwrite("selfsym", &SymmPairBlock::selfsym);
  py::class_<Preplace>( m, "Preplace")
    .def( py::init<>())
    .def_readwrite("blockid1", &Preplace::blockid1)
    .def_readwrite("blockid2", &Preplace::blockid2)
    .def_readwrite("conner", &Preplace::conner)
    .def_readwrite("distance", &Preplace::distance)
    .def_readwrite("horizon", &Preplace::horizon);
  py::class_<Alignment>( m, "Alignment")
    .def( py::init<>())
    .def_readwrite("blockid1", &Alignment::blockid1)
    .def_readwrite("blockid2", &Alignment::blockid2)
    .def_readwrite("distance", &Alignment::distance)
    .def_readwrite("horizon", &Alignment::horizon);
  py::class_<MatchBlock>( m, "MatchBlock")
    .def( py::init<>())
    .def_readwrite("blockid1", &MatchBlock::blockid1)
    .def_readwrite("blockid2", &MatchBlock::blockid2);
  py::class_<AlignBlock>( m, "AlignBlock")
    .def( py::init<>())
    .def_readwrite("blocks", &AlignBlock::blocks)
    .def_readwrite("horizon", &AlignBlock::horizon)
    .def_readwrite("line", &AlignBlock::line);
  py::class_<PortPos>( m, "PortPos")
    .def( py::init<>())
    .def_readwrite("tid", &PortPos::tid)
    .def_readwrite("pos", &PortPos::pos);
  py::class_<CCCap>( m, "CCCap")
    .def( py::init<>())
    .def_readwrite("size", &CCCap::size)
    .def_readwrite("CCCap_name", &CCCap::CCCap_name)
    .def_readwrite("Unit_capacitor", &CCCap::Unit_capacitor)
    .def_readwrite("cap_ratio", &CCCap::cap_ratio)
    .def_readwrite("cap_r", &CCCap::cap_r)
    .def_readwrite("cap_s", &CCCap::cap_s)
    .def_readwrite("dummy_flag", &CCCap::dummy_flag);
  py::class_<R_const>( m, "R_const")
    .def( py::init<>())
    .def_readwrite("net_name", &R_const::net_name)
    .def_readwrite("start_pin", &R_const::start_pin)
    .def_readwrite("end_pin", &R_const::end_pin)
    .def_readwrite("R", &R_const::R);
  py::class_<C_const>( m, "C_const")
    .def( py::init<>())
    .def_readwrite("net_name", &C_const::net_name)
    .def_readwrite("start_pin", &C_const::start_pin)
    .def_readwrite("end_pin", &C_const::end_pin)
    .def_readwrite("C", &C_const::C);


  py::class_<lefMacro>( m, "lefMacro")
    .def( py::init<>())
    .def_readwrite("width", &lefMacro::width)
    .def_readwrite("height", &lefMacro::height)
    .def_readwrite("name", &lefMacro::name)
    .def_readwrite("macroPins", &lefMacro::macroPins)
    .def_readwrite("interMetals", &lefMacro::interMetals)
    .def_readwrite("interVias", &lefMacro::interVias)
    .def_readwrite("master", &lefMacro::master);

  py::class_<designRule>( m, "designRule")
    .def( py::init<>())
    .def_readwrite("MinWidth", &designRule::MinWidth)
    .def_readwrite("MaxSpace", &designRule::MaxSpace)
    .def_readwrite("EnMax", &designRule::EnMax)
    .def_readwrite("TrkSpacing", &designRule::TrkSpacing)
    .def_readwrite("grid_unit_x", &designRule::grid_unit_x)
    .def_readwrite("grid_unit_y", &designRule::grid_unit_y);

  py::class_<ViaModel>( m, "ViaModel")
    .def( py::init<>())
    .def_readwrite("name", &ViaModel::name)
    .def_readwrite("ViaIdx", &ViaModel::ViaIdx)
    .def_readwrite("LowerIdx", &ViaModel::LowerIdx)
    .def_readwrite("UpperIdx", &ViaModel::UpperIdx)
    .def_readwrite("ViaRect", &ViaModel::ViaRect)
    .def_readwrite("LowerRect", &ViaModel::LowerRect)
    .def_readwrite("UpperRect", &ViaModel::UpperRect)
    .def_readwrite("R", &ViaModel::R);

  py::class_<design_info>( m, "design_info")
    .def( py::init<>())
    .def_readwrite("Hspace", &design_info::Hspace)
    .def_readwrite("Vspace", &design_info::Vspace)
    .def_readwrite("signal_routing_metal_l", &design_info::signal_routing_metal_l)
    .def_readwrite("signal_routing_metal_u", &design_info::signal_routing_metal_u)
    .def_readwrite("power_grid_metal_l", &design_info::power_grid_metal_l)
    .def_readwrite("power_grid_metal_u", &design_info::power_grid_metal_u)
    .def_readwrite("power_routing_metal_l", &design_info::power_routing_metal_l)
    .def_readwrite("power_routing_metal_u", &design_info::power_routing_metal_u)
    .def_readwrite("h_skip_factor", &design_info::h_skip_factor)
    .def_readwrite("v_skip_factor", &design_info::v_skip_factor)
    .def_readwrite("compact_style", &design_info::compact_style)
    ;

  py::class_<guardring_info>( m, "guardring_info")
    .def( py::init<>())
    .def_readwrite("path", &guardring_info::path)
    ;

  py::class_<Drc_info>( m, "Drc_info")
    .def( py::init<>())
    .def_readwrite("MaxLayer", &Drc_info::MaxLayer)
    .def_readwrite("Metalmap", &Drc_info::Metalmap)
    .def_readwrite("Viamap", &Drc_info::Viamap)
    .def_readwrite("Metal_info", &Drc_info::Metal_info)
    .def_readwrite("Via_info", &Drc_info::Via_info)
    .def_readwrite("metal_weight", &Drc_info::metal_weight)
    .def_readwrite("Via_model", &Drc_info::Via_model)
    .def_readwrite("MaskID_Metal", &Drc_info::MaskID_Metal)
    .def_readwrite("MaskID_Via", &Drc_info::MaskID_Via)
    .def_readwrite("top_boundary", &Drc_info::top_boundary)
    .def_readwrite("Guardring_info", &Drc_info::Guardring_info)
    .def_readwrite("Design_info", &Drc_info::Design_info)
  ;

  py::enum_<NType>(m,"NType")
    .value("Block",Block)
    .value("Terminal",Terminal)
    .export_values();

  py::enum_<Omark>(m,"Omark")
    .value("N",N)
    .value("S",S)
    .value("W",W)
    .value("E",E)
    .value("FN",FN)
    .value("FS",FS)
    .value("FW",FW)
    .value("FE",FE)
    .export_values();

  py::enum_<Smark>(m,"Smark")
    .value("H",H)
    .value("V",V)
    .export_values();

  py::enum_<Bmark>(m,"Bmark")
    .value("TL",TL)
    .value("TC",TC)
    .value("TR",TR)
    .value("RT",RT)
    .value("RC",RC)
    .value("RB",RB)
    .value("BR",BR)
    .value("BC",BC)
    .value("BL",BL)
    .value("LB",LB)
    .value("LC",LC)
    .value("LT",LT)
    .export_values();

  py::enum_<TransformType>(m,"TransformType")
    .value("Forward",Forward)
    .value("Backward",Backward)
    .export_values();

  py::class_<PnRdatabase>( m, "PnRdatabase")
    .def( py::init<>())
    .def( "semantic0", &PnRdatabase::semantic0)
    .def( "semantic1", &PnRdatabase::semantic1)
    .def( "semantic2", &PnRdatabase::semantic2)
    .def( "TraverseHierTree", &PnRdatabase::TraverseHierTree)
    .def( "CheckoutHierNode", &PnRdatabase::CheckoutHierNode)
    .def( "PrintHierNode", &PnRdatabase::PrintHierNode)
    .def( "PrintHierTree", &PnRdatabase::PrintHierTree)
    .def( "ReadPDKJSON", &PnRdatabase::ReadPDKJSON)
    .def( "ReadLEF", &PnRdatabase::ReadLEF)
    .def( "ReadLEFFromString", &PnRdatabase::ReadLEFFromString)
    .def( "getDrc_info", &PnRdatabase::getDrc_info)
    .def( "checkoutSingleLEF", &PnRdatabase::checkoutSingleLEF)
    .def( "AddingPowerPins", &PnRdatabase::AddingPowerPins)
    .def( "Extract_RemovePowerPins", &PnRdatabase::Extract_RemovePowerPins)
    .def( "CheckinHierNode", &PnRdatabase::CheckinHierNode)
    .def( "TransformNode", &PnRdatabase::TransformNode)
    .def( "TransformBbox", &PnRdatabase::TransformBbox)
    .def( "TransformPoint", &PnRdatabase::TransformPoint)
    .def( "RelOrt2AbsOrt", &PnRdatabase::RelOrt2AbsOrt)
    .def( "ExtractPinsToPowerPins", &PnRdatabase::ExtractPinsToPowerPins)
    .def( "CheckinChildnodetoBlock", &PnRdatabase::CheckinChildnodetoBlock)
    .def( "AppendToHierTree", &PnRdatabase::AppendToHierTree)
    .def( "WriteJSON", &PnRdatabase::WriteJSON)
    .def( "WriteLef", &PnRdatabase::WriteLef)
    .def( "Write_Router_Report", &PnRdatabase::Write_Router_Report)
    .def( "WriteGcellGlobalRoute", &PnRdatabase::WriteGcellGlobalRoute)
    .def( "Write_Current_Workload", &PnRdatabase::Write_Current_Workload)
    .def( "Write_Power_Mesh_Conf", &PnRdatabase::Write_Power_Mesh_Conf)
    .def( "ReadConstraint_Json", &PnRdatabase::ReadConstraint_Json)
    .def( "ReadPrimitiveOffsetPitch", &PnRdatabase::ReadPrimitiveOffsetPitch)
    .def_readwrite("hierTree", &PnRdatabase::hierTree)
    .def_readwrite("topidx", &PnRdatabase::topidx)
    .def_readwrite("gdsData2", &PnRdatabase::gdsData2)
    .def_readwrite("lefData", &PnRdatabase::lefData)
    .def_readwrite("DRC_info", &PnRdatabase::DRC_info)
    .def_readwrite("ScaleFactor", &PnRdatabase::ScaleFactor)
  ;

  py::class_<Placer_Router_Cap_Ifc>( m, "Placer_Router_Cap_Ifc")
    .def( py::init<string, string, hierNode&, Drc_info&, map<string, lefMacro>&, bool, int>());    

  py::class_<PlacerHyperparameters>( m, "PlacerHyperparameters")
    .def( py::init<>())
    .def_readwrite("T_INT", &PlacerHyperparameters::T_INT)
    .def_readwrite("T_MIN", &PlacerHyperparameters::T_MIN)
    .def_readwrite("ALPHA", &PlacerHyperparameters::ALPHA)
    .def_readwrite("SEED", &PlacerHyperparameters::SEED)
    .def_readwrite("COUNT_LIMIT", &PlacerHyperparameters::COUNT_LIMIT)
    .def_readwrite("LAMBDA", &PlacerHyperparameters::LAMBDA)
    .def_readwrite("use_analytical_placer", &PlacerHyperparameters::use_analytical_placer)
    .def_readwrite("placement_info_json", &PlacerHyperparameters::placement_info_json)
    .def_readwrite("use_external_placement_info", &PlacerHyperparameters::use_external_placement_info)
    .def_readwrite("max_init_trial_count", &PlacerHyperparameters::max_init_trial_count)
    .def_readwrite("max_cache_hit_count", &PlacerHyperparameters::max_cache_hit_count)
    .def_readwrite("select_in_ILP", &PlacerHyperparameters::select_in_ILP) // select variant of blocks in SA using ILP used for compaction
    .def_readwrite("use_ILP_placer", &PlacerHyperparameters::use_ILP_placer) // Use ILP to place blocks instead of SA
    .def_readwrite("ilp_solver", &PlacerHyperparameters::ilp_solver) // choice of solver used in SA : 0 - SYMPHONY, 1 - LpSolve
    .def_readwrite("NUM_THREADS", &PlacerHyperparameters::NUM_THREADS)
    .def_readwrite("place_on_grid_constraints_json", &PlacerHyperparameters::place_on_grid_constraints_json)
    ;

  py::class_<PlacerIfc>( m, "PlacerIfc")
    .def( py::init<hierNode&, int, string, int, Drc_info&, const PlacerHyperparameters&>())
    .def( "getNodeVecSize", &PlacerIfc::getNodeVecSize)
    .def( "getNode", &PlacerIfc::getNode);

  py::class_<GuardRingIfc>( m, "GuardRingIfc")
    .def( py::init<hierNode&, const map<string, lefMacro>&, const Drc_info&, const string&>());

  py::class_<MNASimulationIfc>( m, "MNASimulationIfc")
    .def( py::init<hierNode&, Drc_info&, string&, string&, string&>())
    .def( "Return_Worst_Voltage", &MNASimulationIfc::Return_Worst_Voltage)
    .def( "Clear_Power_Grid", &MNASimulationIfc::Clear_Power_Grid);

  py::class_<Router>( m, "Router")
    .def( py::init<>())
    .def( "RouteWork", &Router::RouteWork);

  /*
  m.def("save_state", &save_state, "helper function to save_state");
  m.def("route_single_variant", &route_single_variant, "helper function to route a single variant");
  m.def("route_top_down", &route_top_down, "helper function to perform top-down routing");

  m.def("toplevel", &toplevel, py::return_value_policy::take_ownership, "helper function to perform the whole C++ flow");
  */
};
