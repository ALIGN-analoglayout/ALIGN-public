# lpsolve 5.5.2.11
FetchContent_Declare(
  lpsolve
  URL https://sourceforge.net/projects/lpsolve/files/lpsolve/5.5.2.11/lp_solve_5.5.2.11_source.tar.gz/download
  URL_HASH MD5=a829a8d9c60ff81dc72ff52363703886
)
find_library(
  lpsolve_lib
  NAMES liblpsolve55.so
  PATH_SUFFIXES lpsolve lp_solve)
if (NOT lpsolve_lib)
  message(STATUS "lpsolve library file not found. Building from source.")
  FetchContent_GetProperties(lpsolve)
  if(NOT lpsolve_POPULATED)
    FetchContent_Populate(lpsolve)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CMakeLists.lpsolve
      ${lpsolve_SOURCE_DIR}/CMakeLists.txt
      COPYONLY)
    add_subdirectory(${lpsolve_SOURCE_DIR} ${lpsolve_BINARY_DIR})
    target_include_directories(lpsolve55 INTERFACE ${lpsolve_SOURCE_DIR})
  endif()
  add_library(lpsolve::lpsolve55 ALIAS lpsolve55)
else()
  message(STATUS "lpsolve library file found. Using headers from source distribution.")
  FetchContent_GetProperties(lpsolve)
  if(NOT lpsolve_POPULATED)
    FetchContent_Populate(lpsolve)
    add_library(lpsolve SHARED IMPORTED)
    target_include_directories(lpsolve INTERFACE ${lpsolve_SOURCE_DIR})
    set_property(
      TARGET lpsolve
      PROPERTY IMPORTED_LOCATION ${lpsolve_lib})
  endif()
  add_library(lpsolve::lpsolve55 ALIAS lpsolve)
endif()
