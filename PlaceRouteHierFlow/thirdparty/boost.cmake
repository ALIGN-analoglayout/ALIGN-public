# Boost v1.75.0 (header-only Boost::boost)
find_package(Boost QUIET COMPONENTS boost)
if (NOT TARGET Boost::boost)
  message(STATUS "Boost not found on host system. Downloading headers.")
  FetchContent_Declare(
    boost
    GIT_REPOSITORY https://github.com/boostorg/boost.git
    GIT_TAG b7b1371294b4bdfc8d85e49236ebced114bc1d8f # boost-1.75.0
  )
  FetchContent_GetProperties(boost)
  if(NOT boost_POPULATED)
      FetchContent_Populate(boost)
      add_library(boost INTERFACE)
      target_include_directories(boost INTERFACE ${boost_SOURCE_DIR})
  endif()
  add_library(Boost::boost ALIAS boost)
endif()
