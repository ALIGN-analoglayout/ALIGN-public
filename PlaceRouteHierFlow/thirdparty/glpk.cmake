# glpk 5.0
FetchContent_Declare(
  glpk
  URL http://ftp.gnu.org/gnu/glpk/glpk-5.0.tar.gz
  URL_HASH MD5=91499dc0c139b221846cae60e5c7d222
)
find_library(
  glpk
  NAMES libglpk.so
)
if (NOT glpk)
  message(STATUS "glpk library file not found. Building from source.")
  FetchContent_GetProperties(glpk)
  if(NOT glpk_POPULATED)
    FetchContent_Populate(glpk)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CMakeLists.glpk
      ${glpk_SOURCE_DIR}/CMakeLists.txt
      COPYONLY)
    add_subdirectory(${glpk_SOURCE_DIR} ${glpk_BINARY_DIR})
    target_include_directories(glpk INTERFACE ${glpk_SOURCE_DIR}/src)
  endif()
  add_library(glpk::glpk ALIAS glpk)
else()
  message(STATUS "glpk library file found. Using headers from source distribution.")
  FetchContent_GetProperties(glpk)
  if(NOT glpk_POPULATED)
    FetchContent_Populate(glpk)
    add_library(glpk SHARED IMPORTED)
    target_include_directories(glpk INTERFACE ${glpk_SOURCE_DIR}/src)
    set_property(
      TARGET glpk
      PROPERTY IMPORTED_LOCATION ${glpk_lib})
  endif()
  add_library(glpk::glpk ALIAS glpk)
endif()
