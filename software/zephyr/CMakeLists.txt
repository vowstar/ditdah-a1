# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
cmake_minimum_required(VERSION 3.20.0)
list(APPEND BOARD_ROOT ${CMAKE_CURRENT_SOURCE_DIR})
list(APPEND SOC_ROOT ${CMAKE_CURRENT_SOURCE_DIR})
list(APPEND DTS_ROOT ${CMAKE_CURRENT_SOURCE_DIR})
find_package(Zephyr REQUIRED HINTS $ENV{ZEPHYR_BASE})
project(ditdah_a1_software)
target_sources(app PRIVATE src/main.c)
zephyr_link_libraries(-Wl,--defsym=_start=__start)
