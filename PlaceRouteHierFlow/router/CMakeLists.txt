set(headers
     A_star.h
     GcellGlobalRouter.h
     GlobalRouter.h
     PowerRouter.h
     Router.h
     DetailRouter.h
     GlobalGraph.h
     Graph.h
     RawRouter.h
     GcellDetailRouter.h
     GlobalGrid.h
     Grid.h
     HananRouter.h
     Rdatatype.h
)

set(sources
     A_star.cpp
     GlobalGraph.cpp
     Grid.cpp
     DetailRouter.cpp
     GlobalGrid.cpp
     PowerRouter.cpp
     GcellDetailRouter.cpp
     GlobalRouter.cpp
     RawRouter.cpp
     GcellGlobalRouter.cpp
     Graph.cpp
     HananRouter.cpp
     Router.cpp
)

add_library(router STATIC ${sources} ${headers})
target_include_directories(router PRIVATE "/opt/homebrew/include")
target_link_directories(router PRIVATE "/opt/homebrew/lib")
target_link_libraries(
     router PRIVATE
     lpsolve55
     spdlog
)
target_code_coverage(router)
