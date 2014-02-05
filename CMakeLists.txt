cmake_minimum_required(VERSION 2.8)

project(ngp)

FIND_PACKAGE(Curses REQUIRED)

FIND_PATH(LIBCONFIG_INCLUDE_DIR libconfig.h)
FIND_LIBRARY(LIBCONFIG_LIBRARIES libconfig.a)

set(NGP_INCLUDES ${LIBCONFIG_INCLUDE_DIR} ${CURSES_INCLUDE_DIR})

include_directories(${NGP_INCLUDES})

add_executable(ngp "ngp.c")

target_link_libraries(ngp ${CURSES_LIBRARIES} ${LIBCONFIG_LIBRARIES} pthread)

install(TARGETS ngp
  DESTINATION /usr/local/bin)

install(FILES "${CMAKE_SOURCE_DIR}/ngprc"
  DESTINATION /etc)