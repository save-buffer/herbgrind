/*--------------------------------------------------------------------*/
/*--- HerbGrind: a valgrind tool for Herbie          hg_evaluate.c ---*/
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

#include "hg_evaluate.h"
#include "hg_runtime.h"
#include "../types/hg_stemtea.h"
#include "../include/hg_options.h"
#include "hg_output.h"
#include "hg_print.h"

#include "pub_tool_libcassert.h"

#include <math.h>
#include <float.h>

void evaluateOpError(ShadowValue* shadowVal, double actualVal,
                     Op_Info* opinfo, double localResult,
                     Bool force){
  if (!running) return;

  double oldMaxLocal = opinfo->evalinfo.max_local;
  double oldMaxError = opinfo->evalinfo.max_error;

  evaluateError_bare(shadowVal, &(opinfo->evalinfo), actualVal);
  evaluateError_local(shadowVal, &(opinfo->evalinfo), localResult);

  if (report_exprs &&
      ((opinfo->evalinfo.max_local >= error_threshold &&
        opinfo->evalinfo.max_local > oldMaxLocal &&
        localize) ||
       (opinfo->evalinfo.max_error >= error_threshold &&
        opinfo->evalinfo.max_error > oldMaxError &&
        !localize) ||
       force)){
    updateTea(opinfo, shadowVal->stem);
  }
  if ((opinfo->evalinfo.max_error >= error_threshold &&
       oldMaxError < error_threshold && !localize) ||
      (opinfo->evalinfo.max_local >= error_threshold &&
       oldMaxLocal < error_threshold && localize) ||
      force){
    trackValueExpr(shadowVal, actualVal);
  }

  if (print_errors || print_errors_long){
    VG_(printf)("(Operation at %lX)\n", opinfo->debuginfo.addr);
    if (opinfo->debuginfo.src_filename != NULL)
      VG_(printf)("%s at %s:%u in %s\n",
                  opinfo->debuginfo.plain_opname,
                  opinfo->debuginfo.src_filename,
                  opinfo->debuginfo.src_line,
                  opinfo->debuginfo.fnname);
    VG_(printf)("\n");
  }
}

void evaluateError_bare(ShadowValue* shadowVal,
                        Eval_Info* evalinfo,
                        double computedValue){
  // We're going to do the log in mpfr since that way we don't have to
  // worry about pulling in the normal math library, which is
  // non-trivial in a valgrind tool. But, we can't get ulps from an
  // mpfr value, so we have to first bring both values into doubles,
  // get their ulps, move the ulps into MPFR, get the +1log (which is
  // the number of bits), then finally convert that to double.
  unsigned long long ulpsError;
  double bitsError, shadowValD;
  mpfr_t ulpsErrorM, bitsErrorM;

  shadowValD = mpfr_get_d(shadowVal->value, MPFR_RNDN);

  ulpsError = ulpd(shadowValD, computedValue);
  // To calculate bits error, we take the log2 of the ulps error +
  // 1. This means that 0 ulps (same value) has log2(1) = 0 bits of
  // error, 1 ulp (values that are as close as they can be but still
  // different) has log2(2) = 1 bit of error, and we scale
  // logarithmically from there.
  mpfr_init2(ulpsErrorM, precision);
  mpfr_set_ui(ulpsErrorM, (unsigned long int)(ulpsError + 1), MPFR_RNDN);
  mpfr_init2(bitsErrorM, 64);
  mpfr_log2(bitsErrorM, ulpsErrorM, MPFR_RNDN);
  bitsError = mpfr_get_d(bitsErrorM, MPFR_RNDN);

  mpfr_clears(ulpsErrorM, bitsErrorM, NULL);

  if (bitsError > evalinfo->max_error){
    evalinfo->max_error = bitsError;
  }
  evalinfo->total_error += bitsError;
  evalinfo->num_calls++;

  // For printing
  if (print_errors_long || print_errors){
    if (print_errors_long){
      char* shadowValstr;
      mpfr_exp_t shadowValexpt;

      shadowValstr = mpfr_get_str(NULL, &shadowValexpt, 10, longprint_len, shadowVal->value, MPFR_RNDN);

      VG_(printf)("The shadowed val is %se%ld, "
                  "and the actual (computed) val is ",
                  shadowValstr, shadowValexpt);
      printFloat(computedValue);
      VG_(printf)(".\n");
      mpfr_free_str(shadowValstr);
    }
    else if (print_errors){
      VG_(printf)("The shadowed val is ");
      printFloat(shadowValD);
      VG_(printf)(", and the actual (computed) val is ");
      printFloat(computedValue);
      VG_(printf)(".\n");
    }
  
    VG_(printf)("The bits error of that operation was: %f (%llu ulps).\n",
                bitsError, ulpsError);
  }
}

void evaluateError_local(ShadowValue* shadowVal,
                         Eval_Info* evalinfo,
                         double localResult){
  // We're going to do the log in mpfr since that way we don't have to
  // worry about pulling in the normal math library, which is
  // non-trivial in a valgrind tool. But, we can't get ulps from an
  // mpfr value, so we have to first bring both values into doubles,
  // get their ulps, move the ulps into MPFR, get the +1log (which is
  // the number of bits), then finally convert that to double.
  unsigned long long ulpsLocal;
  double bitsLocal, shadowValD;

  mpfr_t ulpsLocalM, bitsLocalM;

  shadowValD = mpfr_get_d(shadowVal->value, MPFR_RNDN);
  ulpsLocal = ulpd(shadowValD, localResult);

  mpfr_init2(ulpsLocalM, precision);
  mpfr_set_ui(ulpsLocalM, (unsigned long int)(ulpsLocal + 1), MPFR_RNDN);
  mpfr_init2(bitsLocalM, 64);
  mpfr_log2(bitsLocalM, ulpsLocalM, MPFR_RNDN);
  bitsLocal = mpfr_get_d(bitsLocalM, MPFR_RNDN);

  mpfr_clears(ulpsLocalM, bitsLocalM, NULL);

  if (bitsLocal > evalinfo->max_local){
    evalinfo->max_local = bitsLocal;
  }
  evalinfo->total_local += bitsLocal;

  if (print_errors_long || print_errors){
    VG_(printf)("The locally approximate value is ");
    printFloat(localResult);
    VG_(printf)("\n");
    VG_(printf)("Local error was: %f (%llu ulps).\n",
                bitsLocal, ulpsLocal);
  }
}

void evaluateOpError_helper(ShadowValue* shadowVal, LocType bytestype, int el_index, Op_Info* opinfo, double localResult){
  switch(bytestype){
  case Lt_Float:
  case Lt_Floatx2:
  case Lt_Floatx4:
  case Lt_Floatx8:
    evaluateOpError(shadowVal, ((float*)(opinfo->dest_value))[el_index], opinfo, localResult, False);
    break;
  case Lt_Double:
  case Lt_Doublex2:
  case Lt_Doublex4:
    evaluateOpError(shadowVal, ((double*)(opinfo->dest_value))[el_index], opinfo, localResult, False);
    break;
  default:
    VG_(dmsg)("Hey, those are some big floats! We can't handle those floats!");
    tl_assert(0);
    break;
  }
}

unsigned long long ulpd(double x, double y) {
  if (x == 0) x = 0; // -0 == 0
  if (y == 0) y = 0; // -0 == 0

  if (x != x && y != y) return 0;
  if (x != x) return ULLONG_MAX - 1; // Maximum error
  if (y != y) return ULLONG_MAX - 1; // Maximum error

  long long xx = *((long long*) &x);
  xx = xx < 0 ? LLONG_MIN - xx : xx;

  long long yy = *((long long*) &y);
  yy = yy < 0 ? LLONG_MIN - yy : yy;

  return xx >= yy ? xx - yy : yy - xx;
}

void updateRegimes(double** regimes_data, SizeT arity, ...){
  va_list args;
  va_start(args, arity);
  for (int i = 0; i < arity; ++i){
    double coord = va_arg(args, double);
    if (coord != coord || coord == INFINITY || coord == -INFINITY){
      continue;
    }
    unsigned long long bucket_size = (ULLONG_MAX - 1) / max_num_regimes;
    int bucket = (*((long long*) &coord)) / bucket_size;
    if (regimes_data[i][bucket] != regimes_data[i][bucket]){
      regimes_data[i][bucket] = coord;
    }
    if (regimes_data[i][bucket + 1] != regimes_data[i][bucket + 1]){
      regimes_data[i][bucket + 1] = coord;
    }
  }
  va_end(args);
}
