FetchContent_Declare(
  HiGHS
  GIT_REPOSITORY https://github.com/coin-or/HiGHS.git
  GIT_TAG v1.2.1
)
option (SHARED "Build shared libraries" OFF)
set (SHARED OFF)
set (CMAKE_Fortran_COMPILER "")
FetchContent_MakeAvailable(HiGHS)
#FetchContent_GetProperties(HiGHS)
message(STATUS "HiGHS src in ${highs_SOURCE_DIR} ${highs_BINARY_DIR}")
set(highs_LIBRARIES
    ${highs_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}highs${CMAKE_STATIC_LIBRARY_SUFFIX}
    ${highs_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}ipx${CMAKE_STATIC_LIBRARY_SUFFIX}
    ${highs_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}basiclu${CMAKE_STATIC_LIBRARY_SUFFIX}
)
message(STATUS "HiGHS bin in ${highs_LIBRARIES}")
