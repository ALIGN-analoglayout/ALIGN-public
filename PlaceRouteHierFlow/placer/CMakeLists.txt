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

include_directories(${highs_BINARY_DIR}/)
include_directories(${highs_SOURCE_DIR}/src/)
add_library(placer STATIC ${sources} ${headers})

target_link_libraries(
     placer PRIVATE
     spdlog::spdlog
     lpsolve::lpsolve55
     Boost::boost
     nlohmann_json::nlohmann_json
     HiGHS
     )

target_code_coverage(placer)
