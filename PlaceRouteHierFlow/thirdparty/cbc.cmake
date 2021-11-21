# cbc-2.10.5
FetchContent_Declare(
  Cbc
  URL https://www.coin-or.org/download/source/Cbc/Cbc-2.10.5.tgz
  URL_HASH MD5=46277180c0fc67f750e2de1836333189
)
find_library(
    Cbc_lib
    NAMES libCbc.so
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
    OsiCbc_lib
    NAMES libOsiCbc.so
    )
find_library(
    CoinUtils_lib
    NAMES libCoinUtils.so
    )
find_library(
    Osi_lib
    NAMES libOsi.so
    )
if(NOT Cbc_lib)
  message(STATUS "Cbc library file not found. Building from source.")
  FetchContent_GetProperties(Cbc)
  if(NOT Cbc_POPULATED)
    FetchContent_Populate(Cbc)
    message(STATUS "Cbc src in ${cbc_SOURCE_DIR} ${cbc_BINARY_DIR}")
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CMakeLists.Cbc
      ${cbc_SOURCE_DIR}/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/CMakeLists.Cbc
      ${cbc_SOURCE_DIR}/Cbc/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/CMakeLists.Cgl
      ${cbc_SOURCE_DIR}/Cgl/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/CMakeLists.Clp
      ${cbc_SOURCE_DIR}/Clp/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/CMakeLists.CoinUtils
      ${cbc_SOURCE_DIR}/CoinUtils/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/CMakeLists.Osi
      ${cbc_SOURCE_DIR}/Osi/src/Osi/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/CMakeLists.OsiCbc
      ${cbc_SOURCE_DIR}/Cbc/src/OsiCbc/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/CMakeLists.OsiClp
      ${cbc_SOURCE_DIR}/Clp/src/OsiClp/CMakeLists.txt
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/Cbc_include/config.h.in
      ${cbc_SOURCE_DIR}/Cbc/include/config.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/Cbc_include/config_cbc.h.in
      ${cbc_SOURCE_DIR}/Cbc/include/config_cbc.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/Clp_include/config.h.in
      ${cbc_SOURCE_DIR}/Clp/include/config.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/Clp_include/config_clp.h.in
      ${cbc_SOURCE_DIR}/Clp/include/config_clp.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/Cgl_include/config.h.in
      ${cbc_SOURCE_DIR}/Cgl/include/config.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/Cgl_include/config_cgl.h.in
      ${cbc_SOURCE_DIR}/Cgl/include/config_cgl.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/CoinUtils_include/config.h.in
      ${cbc_SOURCE_DIR}/CoinUtils/include/config.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/CoinUtils_include/config_coinutils.h.in
      ${cbc_SOURCE_DIR}/CoinUtils/include/config_coinutils.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/Osi_include/config.h.in
      ${cbc_SOURCE_DIR}/Osi/src/Osi/include/config.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/Osi_include/config_osi.h.in
      ${cbc_SOURCE_DIR}/Osi/src/Osi/include/config_osi.h.in
      COPYONLY)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CbcCMakeFiles/Osi_include/config_osi.h.in
      ${cbc_SOURCE_DIR}/Osi/src/Osi/include/config_osicommontest.h.in
      COPYONLY)
    add_subdirectory(${cbc_SOURCE_DIR} ${cbc_BINARY_DIR})
     #target_include_directories(libCbc INTERFACE ${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_INCLUDEDIR})
    target_include_directories(libCbc INTERFACE ${cbc_SOURCE_DIR}/Cbc/src)
    target_include_directories(libCgl INTERFACE ${cbc_SOURCE_DIR}/Cgl/src)
    target_include_directories(libClp INTERFACE ${cbc_SOURCE_DIR}/Clp/src)
    target_include_directories(libOsi INTERFACE ${cbc_SOURCE_DIR}/Osi/src/Osi)
    target_include_directories(libOsiClp INTERFACE ${cbc_SOURCE_DIR}/Clp/src/OsiClp)
    target_include_directories(libOsiCbc INTERFACE ${cbc_SOURCE_DIR}/Cbc/src/OsiCbc)
    target_include_directories(libCoinUtils INTERFACE ${cbc_SOURCE_DIR}/CoinUtils/src)
  endif()
  add_library(Cbc::Cbc ALIAS libCbc)
  add_library(Cgl::Cgl ALIAS libCgl)
  add_library(Clp::Clp ALIAS libClp)
  add_library(Osi::Osi ALIAS libOsi)
  add_library(CoinUtils::CoinUtils ALIAS libCoinUtils)
  add_library(OsiClp::OsiClp ALIAS libOsiClp)
  add_library(OsiCbc::OsiCbc ALIAS libOsiCbc)
else()
  message(STATUS "Cbc library file found. Using headers from source distribution.")
  FetchContent_GetProperties(Cbc)
  if(NOT Cbc_POPULATED)
    FetchContent_Populate(Cbc)
    add_library(Cbc SHARED IMPORTED)
    #target_include_directories(Cbc INTERFACE ${Cbc_SOURCE_DIR})
    set_property( TARGET Cbc PROPERTY IMPORTED_LOCATION ${Cbc_lib})
    add_library(Cgl SHARED IMPORTED)
    set_property( TARGET Cgl PROPERTY IMPORTED_LOCATION ${Cgl_lib})
    add_library(Clp SHARED IMPORTED)
    set_property( TARGET Clp PROPERTY IMPORTED_LOCATION ${Clp_lib})
    add_library(Osi SHARED IMPORTED)
    set_property( TARGET Osi PROPERTY IMPORTED_LOCATION ${Osi_lib})
    add_library(OsiClp SHARED IMPORTED)
    set_property( TARGET OsiClp PROPERTY IMPORTED_LOCATION ${OsiClp_lib})
    add_library(OsiCbc SHARED IMPORTED)
    set_property( TARGET OsiCbc PROPERTY IMPORTED_LOCATION ${OsiCbc_lib})
    add_library(CoinUtils SHARED IMPORTED)
    set_property( TARGET CoinUtils PROPERTY IMPORTED_LOCATION ${CoinUtils_lib})
  endif()
  add_library(Cbc::Cbc ALIAS Cbc)
  target_include_directories(Cbc INTERFACE ${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_INCLUDEDIR})
  add_library(Cgl::Cgl ALIAS Cgl)
  add_library(Clp::Clp ALIAS Clp)
  add_library(Osi::Osi ALIAS Osi)
  add_library(CoinUtils::CoinUtils ALIAS CoinUtils)
  add_library(OsiClp::OsiClp ALIAS OsiClp)
  add_library(OsiCbc::OsiCbc ALIAS OsiCbc)
endif()
