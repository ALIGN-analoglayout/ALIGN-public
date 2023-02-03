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
     Router.cpp
)

add_library(router STATIC ${sources} ${headers})
target_link_libraries(
     router PRIVATE
     ilp_solver::ilp_solver
     nlohmann_json::nlohmann_json
     spdlog::spdlog
)
target_code_coverage(router)
