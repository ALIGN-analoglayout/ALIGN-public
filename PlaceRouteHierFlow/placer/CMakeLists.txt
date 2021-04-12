set(headers
     Aplace.h
     ILP_solver.h
     Placer.h
     Preadfile.h
     design.h
     ConstGraph.h
     Pdatatype.h
     PlacerIfc.h
     SeqPair.h
     TapRemoval.h
	  )

set(sources
     Aplace.cpp
     ILP_solver.cpp
     PlacerIfc.cpp
     SeqPair.cpp
     ConstGraph.cpp
     Placer.cpp
     Preadfile.cpp
     design.cpp
     TapRemoval.cpp
	)

add_library(placer STATIC ${sources} ${headers})

target_link_libraries(
     placer PRIVATE
     spdlog::spdlog
     lpsolve::lpsolve55
     Boost::boost
)
target_code_coverage(placer)
