set(headers
     MNASimulationIfc.h
     MNASimulation.h
     Mdatatype.h
)

set(sources
     MNASimulationIfc.cpp
     MNASimulation.cpp
)

add_library(MNA STATIC ${sources} ${headers})

target_link_libraries(
     MNA PRIVATE
     spdlog::spdlog
     superlu
     Boost::boost
)
target_code_coverage(MNA)
