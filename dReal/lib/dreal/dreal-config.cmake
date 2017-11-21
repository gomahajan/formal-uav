
####### Expanded from @PACKAGE_INIT@ by configure_package_config_file() #######
####### Any changes to this file will be overwritten by the next CMake run ####
####### The input file was dreal-config.cmake.in                            ########

get_filename_component(PACKAGE_PREFIX_DIR "${CMAKE_CURRENT_LIST_DIR}/../../" ABSOLUTE)

macro(set_and_check _var _file)
  set(${_var} "${_file}")
  if(NOT EXISTS "${_file}")
    message(FATAL_ERROR "File or directory ${_file} referenced by variable ${_var} does not exist !")
  endif()
endmacro()

####################################################################################

set(DREAL_VERSION 3.16.09.01)
set_and_check(DREAL_INCLUDE_DIRS ${PACKAGE_PREFIX_DIR}/include/dreal
set_and_check(DREAL_LIBRARY_DIRS ${PACKAGE_PREFIX_DIR}/lib/dreal)
set(DREAL_LIBRARIES dreal;ibex;ClpSolver;Clp;CoinUtils;capd;adept;nlopt;glpk;prim;picosat;-lpthread;m)
