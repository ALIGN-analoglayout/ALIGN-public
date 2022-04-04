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
     PlacerIfc.cpp
     SeqPair.cpp
     Placer.cpp
     Preadfile.cpp
     design.cpp)

include_directories(${cbc_SOURCE_DIR}/Cbc/src)
include_directories(${cbc_SOURCE_DIR}/Cgl/src)
include_directories(${cbc_SOURCE_DIR}/Clp/src)
include_directories(${cbc_SOURCE_DIR}/Clp/src/OsiClp)
include_directories(${cbc_SOURCE_DIR}/Osi/src/Osi)
include_directories(${cbc_SOURCE_DIR}/CoinUtils/src)
include_directories(${symphony_SOURCE_DIR}/SYMPHONY/include)
add_library(placer STATIC ${sources} ${headers})

target_link_libraries(
     placer PRIVATE
     spdlog::spdlog
     lpsolve::lpsolve55
     Boost::boost
     nlohmann_json::nlohmann_json
     ${symphony_LIBRARIES}
     ${cbc_LIBRARIES}
     )

target_code_coverage(placer)
