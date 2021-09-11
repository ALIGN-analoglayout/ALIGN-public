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


target_include_directories(placer PRIVATE "/opt/homebrew/include")

target_link_directories(placer PRIVATE "/opt/homebrew/lib")

target_link_libraries(
     placer PRIVATE
     spdlog
     lpsolve55
)
target_code_coverage(placer)
