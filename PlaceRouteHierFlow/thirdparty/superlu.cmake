# superlu v6.0.0
#
# If ALIGN_SUPERLU_PATH points to a prebuilt bundle produced by ci/build_cpp_deps.sh
# (layout: lib/libsuperlu.a [lib/libblas.a]  include/*.h) we import those instead
# of cloning + building from source.  This is the hot path in CI; the from-source
# path below is the fallback.
if (DEFINED ENV{ALIGN_SUPERLU_PATH})
  find_library(
    superlu_prebuilt_lib
    NAMES libsuperlu.a
    PATHS $ENV{ALIGN_SUPERLU_PATH}/lib
    NO_DEFAULT_PATH)
  if (superlu_prebuilt_lib)
    message(STATUS "SuperLU prebuilt library found at ${superlu_prebuilt_lib}.")
    add_library(superlu STATIC IMPORTED GLOBAL)
    set_property(TARGET superlu PROPERTY IMPORTED_LOCATION ${superlu_prebuilt_lib})
    target_include_directories(superlu INTERFACE $ENV{ALIGN_SUPERLU_PATH}/include)
    # Bundle may also ship the internal CBLAS; link it if present.
    find_library(
      superlu_blas_lib
      NAMES libblas.a
      PATHS $ENV{ALIGN_SUPERLU_PATH}/lib
      NO_DEFAULT_PATH)
    if (superlu_blas_lib)
      add_library(superlu_blas STATIC IMPORTED GLOBAL)
      set_property(TARGET superlu_blas PROPERTY IMPORTED_LOCATION ${superlu_blas_lib})
      target_link_libraries(superlu INTERFACE superlu_blas)
    endif()
  else()
    message(WARNING "ALIGN_SUPERLU_PATH set but libsuperlu.a not found; building from source.")
    unset(ENV{ALIGN_SUPERLU_PATH})
  endif()
endif()

if (NOT TARGET superlu)
  FetchContent_Declare(
      superlu
      GIT_REPOSITORY https://github.com/xiaoyeli/superlu.git
      GIT_TAG        v6.0.0
  )
  FetchContent_GetProperties(superlu)
  if(NOT superlu_POPULATED)
      FetchContent_Populate(superlu)
      configure_file(
          ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CMakeLists.superlu
          ${superlu_SOURCE_DIR}/CMakeLists.txt
          COPYONLY)
      add_subdirectory(${superlu_SOURCE_DIR} ${superlu_BINARY_DIR})
  endif()
endif()
