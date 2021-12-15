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

target_link_libraries(
     placer PRIVATE
     spdlog::spdlog
     lpsolve::lpsolve55
     Boost::boost
     nlohmann_json::nlohmann_json
     ${symphony_LIBRARIES}
     )

target_code_coverage(placer)
