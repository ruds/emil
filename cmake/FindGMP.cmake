# Tries to find the GMP library.
#
# Parameter Variables:
#
# GMP_ROOT_DIR
#   Root directory of GMP installation.
# GMP_USE_STATIC_LIBS
#   Set to TRUE for linking with static library.
#
# Defines Variables:
#
# GMP_FOUND
#   True if GMP was found.
# GMP_INCLUDE_DIRS
#   Directory where gmp.h resides.
# GMP_LIBRARIES
#   Path of Library.
# GMP_VERSION
#   Version found.
#
# Author:
#
# Matthias Walter <matthias@matthiaswalter.org>
#
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file BOOST_LICENSE_1_0.txt or copy at
#  http://www.boost.org/LICENSE_1_0.txt)

# Handle GMP_ROOT_DIR.
set(_GMP_ROOT_HINTS ${GMP_ROOT_DIR} ENV GMP_ROOT_DIR)

# Handle GMP_USE_STATIC_LIBS.
if(GMP_USE_STATIC_LIBS)
  set(_GMP_ORIG_CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES})
  if(WIN32)
    set(CMAKE_FIND_LIBRARY_SUFFIXES .lib .a ${CMAKE_FIND_LIBRARY_SUFFIXES})
  else()
    set(CMAKE_FIND_LIBRARY_SUFFIXES .a )
  endif()
endif()

# Find header.
find_path(GMP_INCLUDE_DIR NAMES gmp.h HINTS ${_GMP_ROOT_HINTS})
set(GMP_INCLUDE_DIRS ${GMP_INCLUDE_DIR})

# Extract version number.
file(STRINGS "${GMP_INCLUDE_DIR}/gmp.h" _GMP_VERSION_MAJOR REGEX "^#define[\t ]+__GNU_MP_VERSION[\t ]+[0-9].*")
string(REGEX REPLACE "^.*__GNU_MP_VERSION[\t ]+([0-9]).*$" "\\1" GMP_VERSION_MAJOR "${_GMP_VERSION_MAJOR}")
file(STRINGS "${GMP_INCLUDE_DIR}/gmp.h" _GMP_VERSION_MINOR REGEX "^#define[\t ]+__GNU_MP_VERSION_MINOR[\t ]+[0-9].*")
string(REGEX REPLACE "^.*__GNU_MP_VERSION_MINOR[\t ]+([0-9]).*$" "\\1" GMP_VERSION_MINOR "${_GMP_VERSION_MINOR}")
file(STRINGS "${GMP_INCLUDE_DIR}/gmp.h" _GMP_VERSION_PATCH REGEX "^#define[\t ]+__GNU_MP_VERSION_PATCHLEVEL[\t ]+[0-9].*")
string(REGEX REPLACE "^.*__GNU_MP_VERSION_PATCHLEVEL[\t ]+([0-9]).*$" "\\1" GMP_VERSION_PATCH "${_GMP_VERSION_PATCH}")
set(GMP_VERSION "${GMP_VERSION_MAJOR}.${GMP_VERSION_MINOR}.${GMP_VERSION_PATCH}")

# Find library.
find_library(GMP_LIBRARY NAMES gmp HINTS ${_GMP_ROOT_HINTS})
set(GMP_LIBRARIES ${GMP_LIBRARY})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(GMP REQUIRED_VARS GMP_INCLUDE_DIRS GMP_LIBRARIES VERSION_VAR GMP_VERSION)

# Restore the original find_library ordering.
if(GMP_USE_STATIC_LIBS)
  set(CMAKE_FIND_LIBRARY_SUFFIXES ${_GMP_ORIG_CMAKE_FIND_LIBRARY_SUFFIXES})
endif()
