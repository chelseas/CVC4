/*********************                                                        */
/*! \file safe_print.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Print functions that are safe to use in a signal handler.
 **
 ** Signal handlers only allow a very limited set of operations, e.g. dynamic
 ** memory allocation is not possible. This set of functions can be used to
 ** print information from a signal handler.
 **/

#pragma once

#include <unistd.h>

#include "lib/clock_gettime.h"
#include "util/result.h"

/* Computes the length of a string. Safe to use in a signal handler. */
size_t safe_strlen(const char* str);

/* Prints an integer in hexadecimal. */
void safe_print_hex(int fd, uint64_t i);

void safe_print_right_aligned(int fd, uint64_t i, size_t width);

/* Safe printing functions */
template<typename T>
void safe_print(int fd, T msg);
