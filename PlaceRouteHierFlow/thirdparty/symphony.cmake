FetchContent_Declare(
  symphony
  URL https://www.coin-or.org/download/source/SYMPHONY/SYMPHONY-5.6.17.tgz
  URL_HASH MD5=59fe0fa58c8bef019967766c86247b9d
)
find_library(
    Sym_lib
    NAMES libSym.so
    )
find_library(
    Cgl_lib
    NAMES libCgl.so
    )
find_library(
    Clp_lib
    NAMES libClp.so
    )
find_library(
    OsiClp_lib
    NAMES libOsiClp.so
    )
find_library(
    OsiSym_lib
    NAMES libOsiSym.so
    )
find_library(
    CoinUtils_lib
    NAMES libCoinUtils.so
    )
find_library(
    Osi_lib
    NAMES libOsi.so
    )
if(NOT Sym_lib)
  message(STATUS "Sym library file not found. Building from source.")
  FetchContent_GetProperties(symphony)
  if(NOT symphony_POPULATED)
    FetchContent_Populate(symphony)
    message(STATUS "Sym src in ${symphony_SOURCE_DIR} ${symphony_BINARY_DIR}")
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CMakeLists.Sym
      ${symphony_SOURCE_DIR}/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/CMakeLists.Sym
      ${symphony_SOURCE_DIR}/SYMPHONY/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/CMakeLists.Cgl
      ${symphony_SOURCE_DIR}/Cgl/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/CMakeLists.Clp
      ${symphony_SOURCE_DIR}/Clp/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/CMakeLists.CoinUtils
      ${symphony_SOURCE_DIR}/CoinUtils/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/CMakeLists.Osi
      ${symphony_SOURCE_DIR}/Osi/src/Osi/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/CMakeLists.OsiSym
      ${symphony_SOURCE_DIR}/SYMPHONY/src/OsiSym/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/CMakeLists.OsiClp
      ${symphony_SOURCE_DIR}/Clp/src/OsiClp/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/Sym_include/config.h.in
      ${symphony_SOURCE_DIR}/SYMPHONY/include/config.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/Sym_include/config_sym.h.in
      ${symphony_SOURCE_DIR}/SYMPHONY/include/config_sym.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/Clp_include/config.h.in
      ${symphony_SOURCE_DIR}/Clp/include/config.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/Clp_include/config_clp.h.in
      ${symphony_SOURCE_DIR}/Clp/include/config_clp.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/Cgl_include/config.h.in
      ${symphony_SOURCE_DIR}/Cgl/include/config.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/Cgl_include/config_cgl.h.in
      ${symphony_SOURCE_DIR}/Cgl/include/config_cgl.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/CoinUtils_include/config.h.in
      ${symphony_SOURCE_DIR}/CoinUtils/include/config.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/CoinUtils_include/config_coinutils.h.in
      ${symphony_SOURCE_DIR}/CoinUtils/include/config_coinutils.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/Osi_include/config.h.in
      ${symphony_SOURCE_DIR}/Osi/src/Osi/include/config.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/Osi_include/config_osi.h.in
      ${symphony_SOURCE_DIR}/Osi/src/Osi/include/config_osi.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/SymCMakeFiles/Osi_include/config_osi.h.in
      ${symphony_SOURCE_DIR}/Osi/src/Osi/include/config_osicommontest.h.in
      COPYONLY)
    add_subdirectory(${symphony_SOURCE_DIR} ${symphony_BINARY_DIR})
    target_include_directories(libSym INTERFACE ${symphony_SOURCE_DIR}/SYMPHONY/include)
    target_include_directories(libCgl INTERFACE ${symphony_SOURCE_DIR}/Cgl/src
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglAllDifferent
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglClique
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglDuplicateRow
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglFlowCover
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglGMI
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglGomory
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglKnapsackCover
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglLandP
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglLiftAndProject
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglMixedIntegerRounding
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglMixedIntegerRounding2
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglOddHole
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglPreProcess
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglProbing
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglRedSplit
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglRedSplit2
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglResidualCapacity
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglSimpleRounding
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglTwomir
                                                ${symphony_SOURCE_DIR}/Cgl/src/CglZeroHalf)

    target_include_directories(libClp INTERFACE ${symphony_SOURCE_DIR}/Clp/src)
    target_include_directories(libOsi INTERFACE ${symphony_SOURCE_DIR}/Osi/src/Osi)
    target_include_directories(libOsiClp INTERFACE ${symphony_SOURCE_DIR}/Clp/src/OsiClp)
    target_include_directories(libOsiSym INTERFACE ${symphony_SOURCE_DIR}/SYMPHONY/src/OsiSym)
    target_include_directories(libCoinUtils INTERFACE ${symphony_SOURCE_DIR}/CoinUtils/src)
  endif()
  add_library(Sym::Sym ALIAS libSym)
  add_library(Cgl::Cgl ALIAS libCgl)
  add_library(Clp::Clp ALIAS libClp)
  add_library(Osi::Osi ALIAS libOsi)
  add_library(CoinUtils::CoinUtils ALIAS libCoinUtils)
  add_library(OsiClp::OsiClp ALIAS libOsiClp)
  add_library(OsiSym::OsiSym ALIAS libOsiSym)
else()
  message(STATUS "Sym library file found. Using headers from source distribution.")
  FetchContent_GetProperties(symphony)
  if(NOT SYM_POPULATED)
    FetchContent_Populate(symphony)
    add_library(Sym SHARED IMPORTED)
    #target_include_directories(Sym INTERFACE ${symphony_SOURCE_DIR})
    set_property( TARGET Sym PROPERTY IMPORTED_LOCATION ${Sym_lib})
    add_library(Cgl SHARED IMPORTED)
    set_property( TARGET Cgl PROPERTY IMPORTED_LOCATION ${Cgl_lib})
    add_library(Clp SHARED IMPORTED)
    set_property( TARGET Clp PROPERTY IMPORTED_LOCATION ${Clp_lib})
    add_library(Osi SHARED IMPORTED)
    set_property( TARGET Osi PROPERTY IMPORTED_LOCATION ${Osi_lib})
    add_library(OsiClp SHARED IMPORTED)
    set_property( TARGET OsiClp PROPERTY IMPORTED_LOCATION ${OsiClp_lib})
    add_library(OsiSym SHARED IMPORTED)
    set_property( TARGET OsiSym PROPERTY IMPORTED_LOCATION ${OsiSym_lib})
    add_library(CoinUtils SHARED IMPORTED)
    set_property( TARGET CoinUtils PROPERTY IMPORTED_LOCATION ${CoinUtils_lib})
  endif()
  add_library(Sym::Sym ALIAS Sym)
  target_include_directories(Sym INTERFACE ${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_INCLUDEDIR}/coin)
  add_library(Cgl::Cgl ALIAS Cgl)
  add_library(Clp::Clp ALIAS Clp)
  add_library(Osi::Osi ALIAS Osi)
  add_library(CoinUtils::CoinUtils ALIAS CoinUtils)
  add_library(OsiClp::OsiClp ALIAS OsiClp)
  add_library(OsiSym::OsiSym ALIAS OsiSym)
endif()
