get_ac_init_version(${Clp_DIR}/configure.ac CLP)

option(CLP_BUILD_EXAMPLES "Enable the building of examples" OFF)

if (CLP_MAJOR_VERSION STREQUAL "devel")
  set(CLP_VERSION_MAJOR   "1"      CACHE STRING "The CLP major version number" FORCE)
  set(CLP_VERSION_MINOR   "17"     CACHE STRING "The CLP minor version number" FORCE)
  set(CLP_VERSION_RELEASE "6"      CACHE STRING "The CLP patch version number" FORCE)
  set(CLP_VERSION         "1.17.6" CACHE STRING "The CLP version" FORCE)
else ()
  set(CLP_VERSION_MAJOR   "${CLP_MAJOR_VERSION}"  CACHE STRING "The CLP major version number" FORCE)
  set(CLP_VERSION_MINOR   "${CLP_MINOR_VERSION}"  CACHE STRING "The CLP minor version number" FORCE)
  set(CLP_VERSION_RELEASE "${CLP_PATCH_VERSION}"  CACHE STRING "The CLP patch version number" FORCE)
  set(CLP_VERSION         "${CLP_VERSION_STRING}" CACHE STRING "The CLP version" FORCE)
endif ()

message(STATUS "Current CLP revision is ${CLP_WC_REVISION}")
set(CLP_SVN_REV "${CLP_WC_REVISION}" CACHE STRING "The CLP subversion revision" PARENT_SCOPE)

mark_as_advanced(CLP_VERSION_MAJOR
                 CLP_VERSION_MINOR
                 CLP_VERSION_RELEASE
                 CLP_VERSION
                 CLP_SVN_REV)

add_definitions(-DCLPLIB_BUILD)

if (CMAKE_COMPILER_IS_GNUCXX)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pedantic-errors -Wparentheses -Wreturn-type -Wcast-qual -Wall -Wpointer-arith -Wwrite-strings -Wconversion -Wno-unknown-pragmas -Wno-long-long")
endif ()

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/include/config.h.in        ${CMAKE_BINARY_DIR}/Clp/include/config.h)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/include/config_clp.h.in    ${CMAKE_BINARY_DIR}/Clp/include/config_clp.h)

#
# pkg-config file generation
#

set(prefix           "${CMAKE_INSTALL_PREFIX}")
set(exec_prefix      "\${prefix}")
set(libdir           "${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_LIBDIR}")
set(includedir       "${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_INCLUDEDIR}")
set(CLPLIB_PCLIBS     "")
set(CLPLIB_PCREQUIRES "coinutils")
set(PACKAGE_VERSION   "${CLP_VERSION}")

set(libdir         "${Clp_DIR}")
set(abs_source_dir "${CMAKE_BINARY_DIR}/bin")

#
# Build
#

set(Clp_SRC_LIST ${Clp_DIR}/src/ClpCholeskyBase.cpp
                 ${Clp_DIR}/src/ClpCholeskyDense.cpp
                 ${Clp_DIR}/src/ClpConstraint.cpp
                 ${Clp_DIR}/src/ClpConstraintLinear.cpp
                 ${Clp_DIR}/src/ClpConstraintQuadratic.cpp
                 ${Clp_DIR}/src/Clp_C_Interface.cpp
                 ${Clp_DIR}/src/ClpDualRowDantzig.cpp
                 ${Clp_DIR}/src/ClpDualRowPivot.cpp
                 ${Clp_DIR}/src/ClpDualRowSteepest.cpp
                 ${Clp_DIR}/src/ClpDummyMatrix.cpp
                 ${Clp_DIR}/src/ClpDynamicExampleMatrix.cpp
                 ${Clp_DIR}/src/ClpDynamicMatrix.cpp
                 ${Clp_DIR}/src/ClpEventHandler.cpp
                 ${Clp_DIR}/src/ClpFactorization.cpp
                 ${Clp_DIR}/src/ClpGubDynamicMatrix.cpp
                 ${Clp_DIR}/src/ClpGubMatrix.cpp
                 ${Clp_DIR}/src/ClpHelperFunctions.cpp
                 ${Clp_DIR}/src/ClpInterior.cpp
                 ${Clp_DIR}/src/ClpLinearObjective.cpp
                 ${Clp_DIR}/src/ClpMatrixBase.cpp
                 ${Clp_DIR}/src/ClpMessage.cpp
                 ${Clp_DIR}/src/ClpModel.cpp
                 ${Clp_DIR}/src/ClpNetworkBasis.cpp
                 ${Clp_DIR}/src/ClpNetworkMatrix.cpp
                 ${Clp_DIR}/src/ClpNonLinearCost.cpp
                 ${Clp_DIR}/src/ClpNode.cpp
                 ${Clp_DIR}/src/ClpObjective.cpp
                 ${Clp_DIR}/src/ClpPackedMatrix.cpp
                 ${Clp_DIR}/src/ClpPlusMinusOneMatrix.cpp
                 ${Clp_DIR}/src/ClpPredictorCorrector.cpp
                 ${Clp_DIR}/src/ClpPdco.cpp
                 ${Clp_DIR}/src/ClpPdcoBase.cpp
                 ${Clp_DIR}/src/ClpLsqr.cpp
                 ${Clp_DIR}/src/ClpPresolve.cpp
                 ${Clp_DIR}/src/ClpPrimalColumnDantzig.cpp
                 ${Clp_DIR}/src/ClpPrimalColumnPivot.cpp
                 ${Clp_DIR}/src/ClpPrimalColumnSteepest.cpp
                 ${Clp_DIR}/src/ClpQuadraticObjective.cpp
                 ${Clp_DIR}/src/ClpSimplex.cpp
                 ${Clp_DIR}/src/ClpSimplexDual.cpp
                 ${Clp_DIR}/src/ClpSimplexNonlinear.cpp
                 ${Clp_DIR}/src/ClpSimplexOther.cpp
                 ${Clp_DIR}/src/ClpSimplexPrimal.cpp
                 ${Clp_DIR}/src/ClpSolve.cpp
                 ${Clp_DIR}/src/Idiot.cpp
                 ${Clp_DIR}/src/IdiSolve.cpp
                 ${Clp_DIR}/src/ClpPEPrimalColumnSteepest.cpp
                 ${Clp_DIR}/src/ClpPESimplex.cpp
                 ${Clp_DIR}/src/ClpPEDualRowSteepest.cpp
                 ${Clp_DIR}/src/ClpPEDualRowDantzig.cpp
                 ${Clp_DIR}/src/ClpPEPrimalColumnDantzig.cpp)

set(ClpSolver_SRC_LIST ${Clp_DIR}/src/ClpSolver.cpp
                       ${Clp_DIR}/src/CbcOrClpParam.cpp
                       ${Clp_DIR}/src/MyEventHandler.cpp
                       ${Clp_DIR}/src/MyMessageHandler.cpp
                       ${Clp_DIR}/src/unitTest.cpp)

if (COIN_HAS_ASL)
  set(ClpSolver_SRC_LIST ${ClpSolver_SRC_LIST}
                         ${Clp_DIR}/src/Clp_ampl.cpp)
endif ()

if (COIN_HAS_ABC)
  set(Clp_SRC_LIST ${Clp_SRC_LIST}
                   ${Clp_DIR}/src/AbcDualRowDantzig.cpp
                   ${Clp_DIR}/src/AbcDualRowPivot.cpp
                   ${Clp_DIR}/src/AbcDualRowSteepest.cpp
                   ${Clp_DIR}/src/AbcMatrix.cpp
                   ${Clp_DIR}/src/AbcNonLinearCost.cpp
                   ${Clp_DIR}/src/AbcPrimalColumnDantzig.cpp
                   ${Clp_DIR}/src/AbcPrimalColumnPivot.cpp
                   ${Clp_DIR}/src/AbcPrimalColumnSteepest.cpp
                   ${Clp_DIR}/src/AbcSimplex.cpp
                   ${Clp_DIR}/src/AbcSimplexDual.cpp
                   ${Clp_DIR}/src/AbcSimplexPrimal.cpp
                   ${Clp_DIR}/src/AbcSimplexParallel.cpp
                   ${Clp_DIR}/src/AbcSimplexFactorization.cpp
                   ${Clp_DIR}/src/AbcWarmStart.cpp
                   ${Clp_DIR}/src/CoinAbcBaseFactorization1.cpp
                   ${Clp_DIR}/src/CoinAbcBaseFactorization2.cpp
                   ${Clp_DIR}/src/CoinAbcBaseFactorization3.cpp
                   ${Clp_DIR}/src/CoinAbcBaseFactorization4.cpp
                   ${Clp_DIR}/src/CoinAbcBaseFactorization5.cpp
                   ${Clp_DIR}/src/CoinAbcDenseFactorization.cpp
                   ${Clp_DIR}/src/CoinAbcFactorization1.cpp
                   ${Clp_DIR}/src/CoinAbcFactorization2.cpp
                   ${Clp_DIR}/src/CoinAbcFactorization3.cpp
                   ${Clp_DIR}/src/CoinAbcFactorization4.cpp
                   ${Clp_DIR}/src/CoinAbcFactorization5.cpp
                   ${Clp_DIR}/src/CoinAbcHelperFunctions.cpp
                   ${Clp_DIR}/src/CoinAbcOrderedFactorization1.cpp
                   ${Clp_DIR}/src/CoinAbcOrderedFactorization2.cpp
                   ${Clp_DIR}/src/CoinAbcOrderedFactorization3.cpp
                   ${Clp_DIR}/src/CoinAbcOrderedFactorization4.cpp
                   ${Clp_DIR}/src/CoinAbcOrderedFactorization5.cpp
                   ${Clp_DIR}/src/CoinAbcSmallFactorization1.cpp
                   ${Clp_DIR}/src/CoinAbcSmallFactorization2.cpp
                   ${Clp_DIR}/src/CoinAbcSmallFactorization3.cpp
                   ${Clp_DIR}/src/CoinAbcSmallFactorization4.cpp
                   ${Clp_DIR}/src/CoinAbcSmallFactorization5.cpp)
endif ()
           
if (COIN_HAS_AMD OR COIN_HAS_CHOLMOD OR COIN_HAS_GLPK)
  set(Clp_SRC_LIST ${Clp_SRC_LIST}
                   ${Clp_DIR}/src/ClpCholeskyUfl.cpp)
endif ()
if (COIN_HAS_MUMPS)
  set(Clp_SRC_LIST ${Clp_SRC_LIST}
                   ${Clp_DIR}/src/ClpCholeskyMumps.cpp)
endif ()
if (COIN_HAS_WSMP)
  set(Clp_SRC_LIST ${Clp_SRC_LIST}
                   ${Clp_DIR}/src/ClpCholeskyWssmp.cpp
                   ${Clp_DIR}/src/ClpCholeskyWssmpKKT.cpp)
endif ()

set(Clp_MAIN_SRC_LIST ${Clp_DIR}/src/ClpMain.cpp)

set(Clp_SRC_LIST_Headers ${Clp_DIR}/src/Clp_C_Interface.h
                         ${Clp_DIR}/src/ClpCholeskyBase.hpp
                         ${Clp_DIR}/src/ClpCholeskyDense.hpp
                         ${Clp_DIR}/src/ClpConstraint.hpp
                         ${Clp_DIR}/src/ClpConstraintLinear.hpp
                         ${Clp_DIR}/src/ClpConstraintQuadratic.hpp
                         ${Clp_DIR}/src/ClpDualRowDantzig.hpp
                         ${Clp_DIR}/src/ClpDualRowPivot.hpp
                         ${Clp_DIR}/src/ClpDualRowSteepest.hpp
                         ${Clp_DIR}/src/ClpDummyMatrix.hpp
                         ${Clp_DIR}/src/ClpDynamicExampleMatrix.hpp
                         ${Clp_DIR}/src/ClpDynamicMatrix.hpp
                         ${Clp_DIR}/src/ClpEventHandler.hpp
                         ${Clp_DIR}/src/ClpFactorization.hpp
                         ${Clp_DIR}/src/ClpGubDynamicMatrix.hpp
                         ${Clp_DIR}/src/ClpGubMatrix.hpp
                         ${Clp_DIR}/src/ClpInterior.hpp
                         ${Clp_DIR}/src/ClpLinearObjective.hpp
                         ${Clp_DIR}/src/ClpMatrixBase.hpp
                         ${Clp_DIR}/src/ClpMessage.hpp
                         ${Clp_DIR}/src/ClpModel.hpp
                         ${Clp_DIR}/src/ClpNetworkMatrix.hpp
                         ${Clp_DIR}/src/ClpNonLinearCost.hpp
                         ${Clp_DIR}/src/ClpNode.hpp
                         ${Clp_DIR}/src/ClpObjective.hpp
                         ${Clp_DIR}/src/ClpPackedMatrix.hpp
                         ${Clp_DIR}/src/ClpPdcoBase.hpp
                         ${Clp_DIR}/src/ClpPlusMinusOneMatrix.hpp
                         ${Clp_DIR}/src/ClpParameters.hpp
                         ${Clp_DIR}/src/ClpPresolve.hpp
                         ${Clp_DIR}/src/ClpPrimalColumnDantzig.hpp
                         ${Clp_DIR}/src/ClpPrimalColumnPivot.hpp
                         ${Clp_DIR}/src/ClpPrimalColumnSteepest.hpp
                         ${Clp_DIR}/src/ClpQuadraticObjective.hpp
                         ${Clp_DIR}/src/ClpSimplex.hpp
                         ${Clp_DIR}/src/ClpSimplexNonlinear.hpp
                         ${Clp_DIR}/src/ClpSimplexOther.hpp
                         ${Clp_DIR}/src/ClpSimplexDual.hpp
                         ${Clp_DIR}/src/ClpSimplexPrimal.hpp
                         ${Clp_DIR}/src/ClpSolve.hpp
                         ${Clp_DIR}/src/CbcOrClpParam.hpp
                         ${Clp_DIR}/src/Idiot.hpp
                         ${Clp_DIR}/src/ClpPEPrimalColumnDantzig.hpp
                         ${Clp_DIR}/src/ClpPEPrimalColumnSteepest.hpp
                         ${Clp_DIR}/src/ClpPESimplex.hpp
                         ${Clp_DIR}/src/ClpPEDualRowSteepest.hpp
                         ${Clp_DIR}/src/ClpPEDualRowDantzig.hpp)

if (COIN_HAS_ABC)
  set(Clp_SRC_LIST_Headers ${Clp_SRC_LIST_Headers}
                           ${Clp_DIR}/src/AbcSimplex.hpp
                           ${Clp_DIR}/src/CoinAbcCommon.hpp
                           ${Clp_DIR}/src/AbcCommon.hpp)
endif ()

# if AMD, CHOLMOD, or GLPK is available, then install ClpCholeskyUfl.hpp (for advanced users)
if (COIN_HAS_AMD OR COIN_HAS_CHOLMOD OR COIN_HAS_GLPK)
  set(Clp_SRC_LIST_Headers ${Clp_SRC_LIST_Headers}
                           ${Clp_DIR}/src/ClpCholeskyUfl.hpp)
endif ()
if (COIN_HAS_MUMPS)
  set(Clp_SRC_LIST_Headers ${Clp_SRC_LIST_Headers}
                           ${Clp_DIR}/src/ClpCholeskyMumps.hpp)
endif ()

if (COIN_HAS_WSMP)
  set(Clp_SRC_LIST_Headers ${Clp_SRC_LIST_Headers}
                           ${Clp_DIR}/src/ClpCholeskyWssmp.hpp
                           ${Clp_DIR}/src/ClpCholeskyWssmpKKT.hpp)
endif ()

if (CMAKE_COMPILER_IS_GNUCXX AND ((CMAKE_CXX_COMPILER_VERSION VERSION_GREATER 4.4) OR (CMAKE_CXX_COMPILER_VERSION VERSION_EQUAL 4.4)))
  set_source_files_properties(${Clp_DIR}/src/CbcOrClpParam.cpp PROPERTIES COMPILE_FLAGS -fno-var-tracking-assignments)
endif ()

add_definitions(-DCOIN_HAS_CLP)

if (COIN_HAS_AMD AND (NOT COIN_HAS_AMD_INCLUDE_PATH STREQUAL "None"))
  include_directories(${COIN_HAS_AMD_INCLUDE_PATH})
endif ()
if (COIN_HAS_CHOLMOD AND (NOT COIN_HAS_CHOLMOD_INCLUDE_PATH STREQUAL "None"))
  include_directories(${COIN_HAS_CHOLMOD_INCLUDE_PATH})
endif ()
if (COIN_HAS_GLPK AND (NOT COIN_HAS_GLPK_INCLUDE_PATH STREQUAL "None"))
  include_directories(${COIN_HAS_GLPK_INCLUDE_PATH})
endif ()
if (COIN_HAS_MUMPS AND (NOT COIN_HAS_MUMPS_INCLUDE_PATH STREQUAL "None"))
  include_directories(${COIN_HAS_MUMPS_INCLUDE_PATH})
endif ()
if (COIN_HAS_WSMP AND (NOT COIN_HAS_WSMP_INCLUDE_PATH STREQUAL "None"))
  include_directories(${COIN_HAS_WSMP_INCLUDE_PATH})
endif ()

include_directories(${CMAKE_SOURCE_DIR}/src)
include_directories(${BuildTools_DIR}/headers)
include_directories(SYSTEM ${CoinUtils_DIR}/src)
include_directories(${Clp_DIR}/src)
include_directories(${Clp_DIR}/src/OsiClp)
if (COIN_ENABLE_DOWNLOAD_ASL OR COIN_USE_ASL)
  include_directories(${CMAKE_BINARY_DIR}/Dependencies/${CMAKE_CFG_INTDIR}/include/ampl)
endif ()

macro(set_include_directories TARGET)
  target_include_directories(${TARGET} BEFORE PRIVATE ${CMAKE_BINARY_DIR}/CoinUtils/include)
  target_include_directories(${TARGET} BEFORE PRIVATE ${CMAKE_BINARY_DIR}/Osi/include)
  target_include_directories(${TARGET} BEFORE PRIVATE ${CMAKE_BINARY_DIR}/Clp/include)
endmacro ()

if (WIN32)
  add_definitions(-D_CRT_SECURE_NO_WARNINGS -D_CRT_SECURE_NO_DEPRECATE)
endif ()

remove_definitions(-DCBC_THREAD)

if (ENABLE_SHARED_LIBRARIES)
  add_library(libClp SHARED ${Clp_SRC_LIST})
else ()
  add_library(libClp STATIC ${Clp_SRC_LIST})
endif ()
if (COIN_COMPILE_LTO)
  set_target_properties(libClp PROPERTIES INTERPROCEDURAL_OPTIMIZATION true)
endif ()
if (NOT WIN32 OR MINGW)
  set_target_properties(libClp PROPERTIES PREFIX "")
endif ()

if (COIN_HAS_AMD AND (NOT COIN_HAS_AMD_LIBRARY_PATH STREQUAL "None"))
  link_directories(${COIN_HAS_AMD_LIBRARY_PATH})
endif ()
if (COIN_HAS_CHOLMOD AND (NOT COIN_HAS_CHOLMOD_LIBRARY_PATH STREQUAL "None"))
  link_directories(${COIN_HAS_CHOLMOD_LIBRARY_PATH})
endif ()
if (COIN_HAS_GLPK AND (NOT COIN_HAS_GLPK_LIBRARY_PATH STREQUAL "None"))
  link_directories(${COIN_HAS_GLPK_LIBRARY_PATH})
endif ()
if (COIN_HAS_MUMPS AND (NOT COIN_HAS_MUMPS_LIBRARY_PATH STREQUAL "None"))
  link_directories(${COIN_HAS_MUMPS_LIBRARY_PATH})
endif ()
if (COIN_HAS_WSMP AND (NOT COIN_HAS_WSMP_LIBRARY_PATH STREQUAL "None"))
  link_directories(${COIN_HAS_WSMP_LIBRARY_PATH})
endif ()
set_include_directories(libClp)

install(TARGETS libClp 
        CONFIGURATIONS Release
        RUNTIME DESTINATION ${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_BINDIR}
        LIBRARY DESTINATION ${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_LIBDIR}
        ARCHIVE DESTINATION ${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_LIBDIR}/static)

#install(FILES ${Clp_SRC_LIST_Headers} 
#        DESTINATION ${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_INCLUDEDIR}/coin)
#
#install(FILES ${CMAKE_BINARY_DIR}/Clp/include/config_clp.h
#        DESTINATION ${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_INCLUDEDIR}/coin
#        RENAME ClpConfig.h)
#
#install(FILES ${CMAKE_BINARY_DIR}/Clp/include/config_clp.h
#        DESTINATION ${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_INCLUDEDIR}/coin)
