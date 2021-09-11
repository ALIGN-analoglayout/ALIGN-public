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


target_include_directories(MNA PRIVATE "/opt/homebrew/include")

target_link_directories(MNA PRIVATE "/opt/homebrew/lib")

target_link_libraries(
     MNA PRIVATE
     spdlog
     superlu
)
target_code_coverage(MNA)
