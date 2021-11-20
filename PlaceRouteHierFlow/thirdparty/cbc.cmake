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
    target_include_directories(libCbc INTERFACE ${cbc_SOURCE_DIR})
  endif()
  add_library(Cbc::Cbc ALIAS libCbc)
endif()
