set(headers
     ILP_solver.h
     Placer.h
     PlacerHyperparameters.h
     Preadfile.h
     design.h
     Pdatatype.h
     PlacerIfc.h
     SeqPair.h)

set(sources
     ILP_solver.cpp
     ILP_Place.cpp
     PlacerIfc.cpp
     SeqPair.cpp
     Placer.cpp
     Preadfile.cpp
     design.cpp)

ExternalProject_Get_Property(cbc binary_dir)
ExternalProject_Get_Property(cbc source_dir)
include_directories(${source_dir}/Cbc/src)
include_directories(${source_dir}/Cgl/src)
include_directories(${source_dir}/Clp/src)
include_directories(${source_dir}/Clp/src/OsiClp)
include_directories(${source_dir}/Osi/src/Osi)
include_directories(${source_dir}/CoinUtils/src)
add_library(placer STATIC ${sources} ${headers})

target_link_libraries(
     placer PRIVATE
     spdlog::spdlog
     lpsolve::lpsolve55
     Boost::boost
     nlohmann_json::nlohmann_json
     HiGHS
     ${cbc_LIBRARIES}
     ${highs_LIBRARIES}
     )

target_code_coverage(placer)
