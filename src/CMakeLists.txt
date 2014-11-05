cmake_minimum_required(VERSION 2.8.7)
project(PREAL C CXX)
set(PREAL_VERSION_MAJOR 0)
set(PREAL_VERSION_MINOR 0)
set(PREAL_VERSION_PATCH 0)
set(PACKAGE_NAME pReal)
set(PACKAGE_VERSION "${PREAL_VERSION_MAJOR}.${PREAL_VERSION_MINOR}.${PREAL_VERSION_PATCH}")
set(PACKAGE_STRING "${PACKAGE_NAME} ${PACKAGE_VERSION}")
set(PACKAGE_BUGREPORT "http://github.com/dreal/dreal/issues")
set(BUG_REPORT_URL "${PACKAGE_BUGREPORT}" CACHE STRING "Default URL where bug reports are to be submitted.")

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

option(REQUIRE_ODE "REQUIRE_ODE" OFF)
option(STATIC      "STATIC"      OFF)

# Added for CTest
include(CTest)
# Added for External Projects
include(ExternalProject)

set(PREAL_EXTRA_LINKER_FLAGS "")
set(PREAL_EXTRA_CXX_FLAGS "")

################################################################
# Set Module Path
################################################################
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules/")

################################################################
# Static Build
################################################################
if("${STATIC}" MATCHES "ON")
  if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    message(STATUS "Static linking of user binaries is not supported on Mac OS X. See https://developer.apple.com/library/mac/qa/qa1118/_index.html")
    set(PREAL_EXTRA_LINKER_FLAGS "${PREAL_EXE_EXTRA_LINKER_FLAGS} -static-libgcc -static-libstdc++")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -static-libgcc -static-libstdc++")
  else()
    set(PREAL_EXTRA_LINKER_FLAGS "${PREAL_EXTRA_LINKER_FLAGS} -static -static-libgcc -static-libstdc++")
    #  set(PREAL_EXTRA_CXX_FLAGS "${PREAL_EXTRA_CXX_FLAGS} -static -static-libgcc -static-libstdc++")
    message(STATUS "Creating a static executable")
  endif()
endif()

################################################################
# Initialize CXXFLAGS.
################################################################
set(CMAKE_CXX_FLAGS                "-Wall -Wextra -std=c++11 ${PREAL_EXTRA_CXX_FLAGS}")
set(CMAKE_CXX_FLAGS_DEBUG          "-g -DPREAL_DEBUG -DPREAL_TRACE -fno-inline")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")

################################################################
# Test coverage
################################################################
if("${TESTCOV}" MATCHES "ON")
  include(CodeCoverage)
  message(STATUS "Enable test-coverage")
  set(CMAKE_CXX_FLAGS_DEBUG        "${CMAKE_CXX_FLAGS_DEBUG} -O0 -fprofile-arcs -ftest-coverage --coverage")
  setup_target_for_coverage(cov ${PREAL_SOURCE_DIR}/script/run_tests.sh coverage)
endif()

################################################################
# Compiler-specific C++11 activation.
################################################################
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
  execute_process(
    COMMAND ${CMAKE_CXX_COMPILER} -dumpversion OUTPUT_VARIABLE GCC_VERSION)
  if (NOT (GCC_VERSION VERSION_GREATER 4.8 OR GCC_VERSION VERSION_EQUAL 4.8))
    message(FATAL_ERROR "${PROJECT_NAME} requires g++ 4.8 or greater.")
  endif ()
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-mismatched-tags -Qunused-arguments")
  if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    # In OSX, clang requires "-stdlib=libc++" to support C++11
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
    set(PREAL_EXTRA_LINKER_FLAGS "-stdlib=libc++")
  endif ()
else ()
  message(FATAL_ERROR "Your C++ compiler does not support C++11.")
endif ()

################################################################
# Fix Paths
################################################################
SET(CMAKE_SYSTEM_INCLUDE_PATH ${CMAKE_SYSTEM_INCLUDE_PATH}
  /usr/local/include /opt/local/include
  /usr/include/w32api
  /usr/X11R6/include /usr/include/X11
  /usr/pkg/include
  /opt/csw/include /opt/include
  /usr/include /include
  )
SET(CMAKE_SYSTEM_LIBRARY_PATH ${CMAKE_SYSTEM_LIBRARY_PATH}
  $ENV{LD_LIBRARY_PATH}
  /usr/local/lib /opt/local/lib
  /usr/lib/w32api
  /usr/X11R6/lib /usr/lib/X11
  /usr/pkg/lib
  /opt/csw/lib /opt/lib
  /usr/lib /lib
  )
SET(CMAKE_SYSTEM_PROGRAM_PATH ${CMAKE_SYSTEM_PROGRAM_PATH}
  /usr/local/bin /usr/pkg/bin /usr/bin /sbin /bin
  )
SET(CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES
  ${CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES}
  /usr/lib64 /usr/lib32 /usr/lib /lib
  )

################################################################
# Packages
################################################################
# Git & Bison & Flex
find_package(GIT REQUIRED)
find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

function(JOIN VALUES GLUE OUTPUT)
  string (REGEX REPLACE "([^\\]|^);" "\\1${GLUE}" _TMP_STR "${VALUES}")
  string (REGEX REPLACE "[\\](.)" "\\1" _TMP_STR "${_TMP_STR}") #fixes escaping
  set (${OUTPUT} "${_TMP_STR}" PARENT_SCOPE)
endfunction()

JOIN("${CMAKE_CXX_FLAGS}" "," EXTERNAL_CXX_FLAGS)
JOIN("${PREAL_EXTRA_LINKER_FLAGS}" "," EXTERNAL_LD_FLAGS)

################################################################
# External: VAL
################################################################
ExternalProject_Add(VAL
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/danbryce/VAL
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND make clean
  BUILD_COMMAND make -j libVal.a CXX=${CMAKE_CXX_COMPILER} CC=${CMAKE_C_COMPILER}
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND ln -s -F ${CMAKE_CURRENT_BINARY_DIR}/external/src/VAL/include ${CMAKE_CURRENT_BINARY_DIR}/include/val && ln -s -F ${CMAKE_CURRENT_BINARY_DIR}/external/src/VAL/libVal.a ${CMAKE_CURRENT_BINARY_DIR}/lib/
)

################################################################
# External: gflags (Google Flags)
################################################################
ExternalProject_Add(GFLAGS
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/soonhokong/gflags.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND cmake -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER} "-DCMAKE_CXX_FLAGS=${EXTERNAL_CXX_FLAGS} -fPIC -DNDEBUG -w" -DCMAKE_INSTALL_PREFIX:PATH=${CMAKE_CURRENT_BINARY_DIR} ./
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make install
)
set(EXTRA_LIBS ${EXTRA_LIBS} "gflags")

################################################################
# External: glog (Google Log)
################################################################
ExternalProject_Add(GLOG
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/soonhokong/glog.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} --disable-shared "CXX_FLAGS=-DNDEBUG ${EXTERNAL_CXX_FLAGS}" CFLAGS=-DNDEBUG "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} --with-gflags=${CMAKE_CURRENT_BINARY_DIR}
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make install
)
set(EXTRA_LIBS ${EXTRA_LIBS} "glog")

################################################################
# External: googletest (Google Test)
################################################################
ExternalProject_Add(GTEST
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/soonhokong/googletest.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND cmake -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER} "-DCMAKE_CXX_FLAGS=${EXTERNAL_CXX_FLAGS} -w" -DCMAKE_INSTALL_PREFIX:PATH=${CMAKE_CURRENT_BINARY_DIR} ./
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make install
)
set(EXTRA_LIBS ${EXTRA_LIBS} "gtest")

################################################################
# External: set up include dir and libpath
################################################################
include_directories(${CMAKE_CURRENT_BINARY_DIR}/include)
set(EXTERNAL_LD_FLAGS "-L${CMAKE_CURRENT_BINARY_DIR}/lib")

################################################################
# CXX Flags
################################################################
set(PREAL_EXTRA_CXX_FLAGS "${PREAL_EXTRA_CXX_FLAGS} -mfpmath=sse -msse -msse2 -ffloat-store")

if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
  set(PREAL_EXTRA_CXX_FLAGS "${PREAL_EXTRA_CXX_FLAGS} -frounding-math")
endif()

################################################################
# VAL LIB
################################################################
set(EXTRA_LIBS ${EXTRA_LIBS} "-lVal")
set(EXTRA_LIBS ${EXTRA_LIBS} "-lfl")


################################################################
# EGLIBC (Optional)
################################################################
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  if("${EGLIBCPATH}" MATCHES ".+")
    message(STATUS "Use EGLIBC Installed at ${EGLIBCPATH}")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--rpath=${EGLIBCPATH}:/usr/lib/gcc/x86_64-linux-gnu/4.8:/usr/lib:/usr/lib/x86_64-linux-gnu/")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--dynamic-linker=${EGLIBCPATH}/lib/ld-linux-x86-64.so.2")
  else()
    message(STATUS "Use built-in EGLIBC.")
  endif()
endif()

################################################################
# Include Directories
################################################################
include_directories(${PREAL_SOURCE_DIR})
configure_file("${PREAL_SOURCE_DIR}/version.h.in" "${PREAL_BINARY_DIR}/version.h")
configure_file("${PREAL_SOURCE_DIR}/config.h.in" "${PREAL_BINARY_DIR}/config.h")
include_directories("${PREAL_BINARY_DIR}")
add_subdirectory(util)
set(PREAL_LIBS ${PREAL_LIBS} util)





set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${PREAL_EXTRA_LINKER_FLAGS} ${EXTERNAL_LD_FLAGS}")
set(CMAKE_EXE_LINKER_FLAGS_TESTCOV "${CMAKE_EXE_LINKER_FLAGS} -fprofile-arcs -ftest-coverage")

set(EXTRA_LIBS ${PREAL_LIBS} ${EXTRA_LIBS})
add_executable(pReal main.cpp translate.cpp smtWriteController.cpp)
target_link_libraries(pReal ${EXTRA_LIBS})

#add tests
#add_subdirectory(tests/nra)
#add_subdirectory(tests/nra_ode)
#add_subdirectory(tests/capd3)
#add_subdirectory(tests/realpaver)

#dependencies
add_dependencies(GLOG GFLAGS)
add_dependencies(util GLOG)
add_dependencies(util GFLAGS)
#add_dependencies(dsolvers JSON11)
#add_dependencies(dsolvers realpaver)
#add_dependencies(dsolvers CAPD3)
#add_dependencies(realpaver GFLAGS)
#add_dependencies(realpaver CAPD3)
add_dependencies(VAL VAL)
#add_dependencies(realpaver util)



# Include style check
include(StyleCheck)
file(GLOB_RECURSE PREAL_SOURCES
  #${PREAL_SOURCE_DIR}/*.cpp       ${PREAL_SOURCE_DIR}/*.h
 # ${PREAL_SOURCE_DIR}/dsolvers/*.cpp   ${PREAL_SOURCE_DIR}/dsolvers/*.h
 # ${PREAL_SOURCE_DIR}/tests/*.cpp      ${PREAL_SOURCE_DIR}/tests/*.h
  )
add_style_check_target(style "${PREAL_SOURCES}")
add_test(NAME style_check COMMAND ${PREAL_SOURCE_DIR}/cmake/Modules/cpplint.py ${PREAL_SOURCES})

ADD_CUSTOM_COMMAND(TARGET pReal
          POST_BUILD
          COMMAND ${CMAKE_COMMAND} -E make_directory ${PREAL_SOURCE_DIR}/../bin
          COMMAND ${CMAKE_COMMAND} -E copy ${PREAL_BINARY_DIR}/pReal ${PREAL_SOURCE_DIR}/../bin/
)

#########################################
# CPack
#########################################
set(CPACK_PACKAGE_NAME pReal)
string(TOLOWER ${CMAKE_SYSTEM_NAME} LOWER_SYSTEM_NAME)
set(CPACK_PACKAGE_FILE_NAME "pReal-${PREAL_VERSION_MAJOR}.${PREAL_VERSION_MINOR}.${PREAL_VERSION_PATCH}-${LOWER_SYSTEM_NAME}")
set(CPACK_STRIP_FILES TRUE)
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  SET(CPACK_GENERATOR TGZ)
else()
  SET(CPACK_GENERATOR ZIP)
endif()
include(CPack)

install(TARGETS pReal DESTINATION bin)

