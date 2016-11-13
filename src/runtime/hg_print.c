/*--------------------------------------------------------------------*/
/*--- HerbGrind: a valgrind tool for Herbie             hg_print.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of HerbGrind, a valgrind tool for diagnosing
   floating point accuracy problems in binary programs and extracting
   problematic expressions.

   Copyright (C) 2016 Alex Sanchez-Stern

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 3 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

#include "hg_print.h"
#include <float.h>
#include "pub_tool_libcprint.h"

#define NUM_DIGITS 6

void printFloat(double number){
  if (number == 0){
    VG_(printf)("0.0");
    return;
  } else if (number != number){
    VG_(printf)("NaN");
    return;
  } else if (number > DBL_MAX){
    VG_(printf)("+Inf");
    return;
  } else if (number < -DBL_MAX){
    VG_(printf)("-Inf");
    return;
  }
  double normalized_number = number;
  int exponent = 0;
  for (int i = 0; i < 400; ++i){
    if (normalized_number < 10) break;
    normalized_number /= 10;
    exponent++;
  }
  if (normalized_number >= 10){
    VG_(printf)("+INF");
  }
  for (int i = 0; i < 400; ++i){
    if (normalized_number >= 1) break;
    normalized_number *= 10;
    exponent--;
  }
  if (normalized_number < 1){
    VG_(printf)("-INF");
    return;
  }
  double digified_number = normalized_number - (int)normalized_number;
  for (int i = 0; i < NUM_DIGITS; ++i){
    digified_number *= 10;
  }
  VG_(printf)("%d.%de%d",
              (int)normalized_number,
              (int)digified_number,
              exponent);
}

void snprintFloat(HChar* buf, Int size, double number){
  if (number == 0){
    VG_(snprintf)(buf, size, "0.0");
    return;
  } else if (number != number){
    VG_(snprintf)(buf, size, "NaN");
    return;
  } else if (number > DBL_MAX){
    VG_(snprintf)(buf, size, "+Inf");
    return;
  } else if (number < -DBL_MAX){
    VG_(snprintf)(buf, size, "-Inf");
    return;
  }
  double normalized_number = number;
  int exponent = 0;
  for (int i = 0; i < 400; ++i){
    if (normalized_number < 10) break;
    normalized_number /= 10;
    exponent++;
  }
  if (normalized_number >= 10){
    VG_(snprintf)(buf, size, "+INF");
  }
  for (int i = 0; i < 400; ++i){
    if (normalized_number >= 1) break;
    normalized_number *= 10;
    exponent--;
  }
  if (normalized_number < 1){
    VG_(snprintf)(buf, size, "-INF");
    return;
  }
  double digified_number = normalized_number - (int)normalized_number;
  for (int i = 0; i < NUM_DIGITS; ++i){
    digified_number *= 10;
  }
  VG_(snprintf)(buf, size,
                "%d.%de%d",
                (int)normalized_number,
                (int)digified_number,
                exponent);
}
