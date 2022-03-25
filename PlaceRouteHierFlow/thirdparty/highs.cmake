FetchContent_Declare(
  HiGHS
  GIT_REPOSITORY https://github.com/coin-or/HiGHS.git
  GIT_TAG v1.2.1
)
#FetchContent_MakeAvailable(HiGHS)
FetchContent_GetProperties(HiGHS)
if(NOT HiGHS_POPULATED)
    option (SHARED "Build shared libraries" OFF)
    set (SHARED OFF)
    FetchContent_Populate(HiGHS)
    message(STATUS "HiGHS src in ${highs_SOURCE_DIR} ${highs_BINARY_DIR}")
    set(highs_LIBRARIES
    ${HiGHS_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}OsiHighs${CMAKE_STATIC_LIBRARY_SUFFIX}
    ${HiGHS_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}highs${CMAKE_STATIC_LIBRARY_SUFFIX}
    )
endif()
