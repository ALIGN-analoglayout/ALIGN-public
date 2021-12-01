set(headers
     Aplace.h
     ILP_solver.h
     Placer.h
     PlacerHyperparameters.h
     Preadfile.h
     design.h
     ConstGraph.h
     Pdatatype.h
     PlacerIfc.h
     SeqPair.h)

set(sources
     Aplace.cpp
     ILP_solver.cpp
     PlacerIfc.cpp
     SeqPair.cpp
     ConstGraph.cpp
     Placer.cpp
     Preadfile.cpp
     design.cpp)

ExternalProject_Get_Property(symphony binary_dir)
ExternalProject_Get_Property(symphony source_dir)
include_directories(${source_dir}/SYMPHONY/include)
add_library(placer STATIC ${sources} ${headers})

add_dependencies(placer symphony Clp Cgl CoinUtils Osi OsiSym OsiClp)

#  add_library (libSym STATIC IMPORTED GLOBAL)
#    set_target_properties (libSym PROPERTIES
#        IMPORTED_LOCATION ${binary_dir}/lib/libSym.a)
#
#  add_library (libClp STATIC IMPORTED GLOBAL)
#  set_target_properties (libClp PROPERTIES
#      IMPORTED_LOCATION ${binary_dir}/lib/libClp.a)
#
#  add_library (libCgl STATIC IMPORTED GLOBAL)
#  set_target_properties (libCgl PROPERTIES
#      IMPORTED_LOCATION ${binary_dir}/lib/libCgl.a)
#
#  add_library (libCoinUtils STATIC IMPORTED GLOBAL)
#  set_target_properties (libCoinUtils PROPERTIES
#      IMPORTED_LOCATION ${binary_dir}/lib/libCoinUtils.a)
#
#  add_library (libOsi STATIC IMPORTED GLOBAL)
#  set_target_properties (libOsi PROPERTIES
#      IMPORTED_LOCATION ${binary_dir}/lib/libOsi.a)
#
#  add_library (libOsiSym STATIC IMPORTED GLOBAL)
#  set_target_properties (libOsiSym PROPERTIES
#      IMPORTED_LOCATION ${binary_dir}/lib/libOsiSym.a)
#
#  add_library (libOsiClp STATIC IMPORTED GLOBAL)
#  set_target_properties (libOsiClp PROPERTIES
#      IMPORTED_LOCATION ${binary_dir}/lib/libOsiClp.a)
#
#  add_library (libClpSolver STATIC IMPORTED GLOBAL)
#  set_target_properties (libClpSolver PROPERTIES
#      IMPORTED_LOCATION ${binary_dir}/lib/libClpSolver.a)
#
#  add_library (libOsiCommonTests STATIC IMPORTED GLOBAL)
#  set_target_properties (libOsiCommonTests PROPERTIES
#      IMPORTED_LOCATION ${binary_dir}/lib/libOsiCommonTests.a)



target_link_libraries(
     placer PRIVATE
     spdlog::spdlog
     lpsolve::lpsolve55
     Boost::boost
     nlohmann_json::nlohmann_json
     ${symphony_LIBRARIES}
     )

target_code_coverage(placer)
