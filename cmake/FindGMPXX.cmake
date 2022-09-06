# Tries to find the GMP C++ library.
#
# Parameter Variables:
#
# GMPXX_ROOT_DIR
#   Root directory of GMP installation.
# GMPXX_USE_STATIC_LIBS
#   Set to TRUE for linking with static library.
#
# Defines Variables:
#
# GMPXX_FOUND
#   True if GMPXX was found.
# GMPXX_INCLUDE_DIRS
#   Directory where gmpxx.h resides.
# GMPXX_LIBRARIES
#   Path of GMP Library.
# GMPXX_VERSION
#   Version found.
#
# Author:
#
# Matthias Walter <matthias@matthiaswalter.org>
#
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file BOOST_LICENSE_1_0.txt or copy at
#  http://www.boost.org/LICENSE_1_0.txt)

# Dependency.
if(GMPXX_FIND_REQUIRED)
  find_package(GMP REQUIRED)
else()
  find_package(GMP)
endif()

# Handle GMPXX_ROOT_DIR.
set(_GMPXX_ROOT_HINTS ${GMPXX_ROOT_DIR} ENV GMPXX_ROOT_DIR)

# Handle GMPXX_USE_STATIC_LIBS.
if(GMPXX_USE_STATIC_LIBS)
  set(_GMPXX_ORIG_CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES})
  if(WIN32)
    set(CMAKE_FIND_LIBRARY_SUFFIXES .lib .a ${CMAKE_FIND_LIBRARY_SUFFIXES})
  else()
    set(CMAKE_FIND_LIBRARY_SUFFIXES .a )
  endif()
endif()

# Find header.
find_path(GMPXX_INCLUDE_DIR NAMES gmpxx.h HINTS ${_GMPXX_ROOT_HINTS})
set(GMPXX_INCLUDE_DIRS ${GMP_INCLUDE_DIRS} ${GMPXX_INCLUDE_DIR})

# Get version number from GMP.
set(GMPXX_VERSION_MAJOR ${GMP_VERSION_MAJOR})
set(GMPXX_VERSION_MINOR ${GMP_VERSION_MINOR})
set(GMPXX_VERSION_PATCH ${GMP_VERSION_PATCH})
set(GMPXX_VERSION ${GMP_VERSION})

# Find library.
find_library(GMPXX_LIBRARY NAMES gmpxx HINTS ${_GMPXX_ROOT_HINTS})
set(GMPXX_LIBRARIES ${GMPXX_LIBRARY} ${GMP_LIBRARIES})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(GMPXX REQUIRED_VARS GMPXX_INCLUDE_DIR GMPXX_LIBRARY GMP_FOUND VERSION_VAR GMPXX_VERSION)

# Restore the original find_library ordering.
if(GMPXX_USE_STATIC_LIBS)
  set(CMAKE_FIND_LIBRARY_SUFFIXES ${_GMPXX_ORIG_CMAKE_FIND_LIBRARY_SUFFIXES})
endif()
