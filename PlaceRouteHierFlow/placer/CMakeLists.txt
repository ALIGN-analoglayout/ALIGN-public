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
     PT_Place.cpp
     PlacerIfc.cpp
     SeqPair.cpp
     Placer.cpp
     Preadfile.cpp
     design.cpp)

add_library(placer STATIC ${sources} ${headers})

target_link_libraries(
     placer PRIVATE
     spdlog::spdlog
     lpsolve::lpsolve55
     Boost::boost
     nlohmann_json::nlohmann_json
     ilp_solver::ilp_solver
     )

target_code_coverage(placer)
