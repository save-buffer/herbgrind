/*--------------------------------------------------------------------*/
/*--- Herbgrind: a valgrind tool for Herbie                range.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Herbgrind, a valgrind tool for diagnosing
   floating point accuracy problems in binary programs and extracting
   problematic expressions.

   Copyright (C) 2016-2017 Alex Sanchez-Stern

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

#include "range.h"
#include <math.h>
#include "../../options.h"
#include "pub_tool_mallocfree.h"

void initRangeRecord(RangeRecord* record){
  initRange(&(record->pos_range));
  initRange(&(record->neg_range));
}

void initRange(Range* range){
  range->min = INFINITY;
  range->max = -INFINITY;
}

void updateRangeRecord(RangeRecord* range, double value){
  if (value > 0 || !detailed_ranges){
    if (range->pos_range.min > value){
      range->pos_range.min = value;
    }
    if (range->pos_range.max < value){
      range->pos_range.max = value;
    }
  } else {
    if (range->neg_range.min > value){
      range->neg_range.min = value;
    }
    if (range->neg_range.max < value){
      range->neg_range.max = value;
    }
  }
}

RangeRecord* copyRangeRecord(RangeRecord* record){
  RangeRecord* result = VG_(malloc)("range record", sizeof(RangeRecord));
  copyRangeRecordInPlace(result, record);
  return result;
}

void copyRangeRecordInPlace(RangeRecord* dest, RangeRecord* src){
  dest->pos_range.min = src->pos_range.min;
  dest->pos_range.max = src->pos_range.max;
  dest->neg_range.min = src->neg_range.min;
  dest->neg_range.max = src->neg_range.max;
}
