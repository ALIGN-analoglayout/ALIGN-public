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

add_library(placer STATIC ${sources} ${headers})

target_link_libraries(
     placer PRIVATE
     spdlog::spdlog
     lpsolve::lpsolve55
     Sym::Sym
     Osi::Osi
     Clp::Clp
     Cgl::Cgl
     CoinUtils::CoinUtils
     OsiClp::OsiClp
     OsiSym::OsiSym
     Boost::boost
     nlohmann_json::nlohmann_json
)
target_code_coverage(placer)
