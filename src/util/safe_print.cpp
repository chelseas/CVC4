/*********************                                                        */
/*! \file safe_print.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "safe_print.h"

#include <unistd.h>

/* Size of buffers used */
#define BUFFER_SIZE 20

size_t safe_strlen(const char* str) {
  size_t l = 0;
  while (*str) {
    str++;
    l++;
  }
  return l;
}

template<>
void safe_print(int fd, const char* msg) {
  write(fd, msg, safe_strlen(msg));
}

template<>
void safe_print(int fd, int64_t i) {
  char buf[BUFFER_SIZE];

  if (i == 0) {
    safe_print(fd, "0");
    return;
  } else if (i < 0) {
    safe_print(fd, "-");
  }

  size_t idx = BUFFER_SIZE - 1;
  while(i != 0 && idx != 0) {
    buf[idx] = '0' + i % 10;
    i /= 10;
    idx--;
  }
  write(fd, buf + idx + 1, BUFFER_SIZE - idx - 1);
}

template<>
void safe_print(int fd, int32_t i) {
  safe_print<long long>(fd, i);
}

template<>
void safe_print(int fd, uint64_t i) {
  char buf[BUFFER_SIZE];

  if (i == 0) {
    safe_print(fd, "0");
    return;
  }

  size_t idx = BUFFER_SIZE - 1;
  while(i != 0 && idx != 0) {
    buf[idx] = '0' + i % 10;
    i /= 10;
    idx--;
  }
  write(fd, buf + idx + 1, BUFFER_SIZE - idx - 1);
}

template<>
void safe_print(int fd, uint32_t i) {
  safe_print<uint64_t>(fd, i);
}

template<>
void safe_print(int fd, double d) {
  char buf[BUFFER_SIZE];
  size_t i = 0;
  int64_t v = (int64_t) d;
  safe_print<int64_t>(fd, v);
  safe_print(fd, ".");
  while (d > 0.0 && i < BUFFER_SIZE) {
    char c = (char) d;
    buf[i] = '0' + c;
    d -= c;
    d *= 10.0;
    i++;
  }
  if (i == 0) {
    safe_print(fd, "0");
  } else {
    write(fd, buf, i);
  }
}

template<>
void safe_print(int fd, float f) {
  safe_print<double>(fd, (double) f);
}

template<>
void safe_print(int fd, bool b) {
  safe_print(fd, b ? "true" : "false");
}

template<>
void safe_print(int fd, void* addr) {
  safe_print_hex(fd, (unsigned long long) addr);
}

void safe_print_hex(int fd, unsigned long long i) {
  char buf[BUFFER_SIZE];

  safe_print(fd, "0x");
  if (i == 0) {
    safe_print(fd, "0");
    return;
  }

  size_t idx = BUFFER_SIZE - 1;
  while(i != 0 && idx != 0) {
    char current = i % 16;
    if (current <= 9) {
      buf[idx] = '0' + current;
    } else {
      buf[idx] = 'a' + current - 10;
    }
    i /= 10;
    idx--;
  }
  write(fd, buf + idx + 1, BUFFER_SIZE - idx - 1);
}

void safe_print_right_aligned(int fd, uint64_t i, size_t width) {
  char buf[BUFFER_SIZE];

  // Make sure that the result fits in the buffer
  width = (width < BUFFER_SIZE) ? width : BUFFER_SIZE;

  for(size_t j = 0; j < width; j++) {
    buf[j] = '0';
  }

  if (i == 0) {
    write(fd, buf, width);
    return;
  }

  size_t idx = width - 1;
  while(i != 0 && idx != 0) {
    buf[idx] = '0' + i % 10;
    i /= 10;
    idx--;
  }
  write(fd, buf, width);
}

template<>
void safe_print(int fd, const timespec t) {
  safe_print<uint64_t>(fd, t.tv_sec);
  safe_print(fd, ".");
  safe_print_right_aligned(fd, t.tv_nsec, 9);
}

template<>
void safe_print(int fd, CVC4::Result r) {
  // ReferenceStat<Result> is only used at the end, so we do not need this in
  // signal handlers.
  safe_print(fd, "<unsupported>");
}
