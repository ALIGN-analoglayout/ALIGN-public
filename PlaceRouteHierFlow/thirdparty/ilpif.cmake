FetchContent_Declare(
  ilpsolverif
  GIT_REPOSITORY https://github.com/ALIGN-analoglayout/ILPSolverInterface.git
  GIT_TAG 57de83f43dd1d05fa63295d7d55f58da2edf632c
)
include(ProcessorCount)
ProcessorCount(N)
if (N GREATER 8)
  set (N 8)
endif ()
FetchContent_GetProperties(ilpsolverif)
if(NOT ilpsolverif_POPULATED)
  FetchContent_Populate(ilpsolverif)
  set (solver_search_path ${ilpsolverif_SOURCE_DIR}/lib)
  if (DEFINED ENV{BUILD_PLATFORM})
    set (solver_search_path ${ilpsolverif_SOURCE_DIR}/$ENV{BUILD_PLATFORM}/lib)
  elseif(DEFINED ENV{ALIGN_ILP_PATH})
    set (solver_search_path $ENV{ALIGN_ILP_PATH}/lib)
  endif()
  find_library(
    ilp_solver_lib
    NAMES libILPSolverIf.a
    PATHS ${solver_search_path})
  if (NOT ilp_solver_lib)
    message(STATUS "Building ILP solver interface from source.")
    if(APPLE)
      # cbc.cmake hardcodes Linux-style versioned dylib symlinks (libCbc.dylib.3.10.5
      # etc.) in cbc_LIBRARIES.  macOS libtool creates libCbc.3.10.5.dylib instead,
      # so those paths never exist.  Append a one-line filter to cbc.cmake so that
      # cbc_LIBRARIES is clean everywhere it is used: target_link_libraries,
      # install(FILES ...), and the new ILPSolverIf_shared PRIVATE entry below.
      set(_ilpif_cbc_cmake "${ilpsolverif_SOURCE_DIR}/ILPSolverIf/cbc.cmake")
      file(READ "${_ilpif_cbc_cmake}" _ilpif_cbc_content)
      string(APPEND _ilpif_cbc_content [=[
if(APPLE)
  list(FILTER cbc_LIBRARIES EXCLUDE REGEX ".*\\.dylib\\.[0-9]")
endif()
]=])
      file(WRITE "${_ilpif_cbc_cmake}" "${_ilpif_cbc_content}")

      # ILPSolverIf/CMakeLists.txt adds a build dep on cbc for ILPSolverIf_shared
      # but never calls target_link_libraries for it.  macOS ld requires all
      # symbols resolved at shared-lib link time.
      set(_ilpif_cmake "${ilpsolverif_SOURCE_DIR}/ILPSolverIf/CMakeLists.txt")
      file(READ "${_ilpif_cmake}" _ilpif_content)
      string(REPLACE
        [=[target_link_libraries(ILPSolverIf INTERFACE ${cbc_LIBRARIES})]=]
        [=[target_link_libraries(ILPSolverIf INTERFACE ${cbc_LIBRARIES})
target_link_libraries(ILPSolverIf_shared PRIVATE ${cbc_LIBRARIES})]=]
        _ilpif_content "${_ilpif_content}")
      file(WRITE "${_ilpif_cmake}" "${_ilpif_content}")
    endif()
    add_subdirectory(${ilpsolverif_SOURCE_DIR} ${ilpsolverif_BINARY_DIR})
    target_include_directories(ILPSolverIf INTERFACE ${ilpsolverif_SOURCE_DIR}/ILPSolverIf)
    target_include_directories(ILPSolverIf INTERFACE ${ilpsolverif_LIBRARY_DIR})
    add_library(ilp_solver::ilp_solver ALIAS ILPSolverIf)
  else()
    message(STATUS "ILP solver lib found in ${ilp_solver_lib}")
    add_library(ilp_solver_if STATIC IMPORTED)
    add_library(cbc_if STATIC IMPORTED)
    add_library(clp_if STATIC IMPORTED)
    add_library(cgl_if STATIC IMPORTED)
    add_library(osi_if STATIC IMPORTED)
    add_library(osiclp_if STATIC IMPORTED)
    add_library(osicbc_if STATIC IMPORTED)
    add_library(coinutils_if STATIC IMPORTED)
    add_library(clpsolver_if STATIC IMPORTED)
    add_library(cbcsolver_if STATIC IMPORTED)
    add_library(sym_if STATIC IMPORTED)
    add_library(osisym_if STATIC IMPORTED)
    set_property(TARGET ilp_solver_if PROPERTY IMPORTED_LOCATION ${ilp_solver_lib})
    target_include_directories(ilp_solver_if INTERFACE ${ilpsolverif_SOURCE_DIR}/ILPSolverIf)
    target_include_directories(ilp_solver_if INTERFACE ${solver_search_path})
    find_library(cbc_lib NAMES libCbc.a PATHS ${solver_search_path})
    set_property(TARGET cbc_if PROPERTY IMPORTED_LOCATION ${cbc_lib})
    find_library(cbcsolver_lib NAMES libCbcSolver.a PATHS ${solver_search_path})
    set_property(TARGET cbcsolver_if PROPERTY IMPORTED_LOCATION ${cbcsolver_lib})
    find_library(clp_lib NAMES libClp.a PATHS ${solver_search_path})
    set_property(TARGET clp_if PROPERTY IMPORTED_LOCATION ${clp_lib})
    find_library(cgl_lib NAMES libCgl.a PATHS ${solver_search_path})
    set_property(TARGET cgl_if PROPERTY IMPORTED_LOCATION ${cgl_lib})
    find_library(osi_lib NAMES libOsi.a PATHS ${solver_search_path})
    set_property(TARGET osi_if PROPERTY IMPORTED_LOCATION ${osi_lib})
    find_library(osiclp_lib NAMES libOsiClp.a PATHS ${solver_search_path})
    set_property(TARGET osiclp_if PROPERTY IMPORTED_LOCATION ${osiclp_lib})
    find_library(coinutils_lib NAMES libCoinUtils.a PATHS ${solver_search_path})
    set_property(TARGET coinutils_if PROPERTY IMPORTED_LOCATION ${coinutils_lib})
    find_library(clpsolver_lib NAMES libClpSolver.a PATHS ${solver_search_path})
    set_property(TARGET clpsolver_if PROPERTY IMPORTED_LOCATION ${clpsolver_lib})
    find_library(osicbc_lib NAMES libOsiCbc.a PATHS ${solver_search_path})
    set_property(TARGET osicbc_if PROPERTY IMPORTED_LOCATION ${osicbc_lib})
    find_library(sym_lib NAMES libSym.a PATHS ${solver_search_path})
    set_property(TARGET sym_if PROPERTY IMPORTED_LOCATION ${sym_lib})
    find_library(osisym_lib NAMES libOsiSym.a PATHS ${solver_search_path})
    set_property(TARGET osisym_if PROPERTY IMPORTED_LOCATION ${osisym_lib})

    add_library(ilp_solver INTERFACE)
    target_link_libraries(ilp_solver INTERFACE ilp_solver_if sym_if osicbc_if cbcsolver_if cbc_if cgl_if osisym_if osiclp_if clpsolver_if clp_if osi_if coinutils_if)
    add_library(ilp_solver::ilp_solver ALIAS ilp_solver)
  endif()
endif()
