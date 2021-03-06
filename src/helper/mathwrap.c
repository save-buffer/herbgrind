/*--------------------------------------------------------------------*/
/*--- Herbgrind: a valgrind tool for Herbie             mathwrap.c ---*/
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

#include "pub_tool_clreq.h"
#include "pub_tool_redir.h"

#include <stdio.h>
#include <complex.h>

#include "../include/herbgrind.h"
#include "../include/mathreplace-funcs.h"

#define LIBM libmZdsoZa
#define LIBM_CPP libmZhZaZdsoZa

// This file instructs valgrind to capture calls to the math functions
// listed in hg_mathreplace_funcs.h, and redirect them to the
// appropriate funciton here instead. From here, we pass them through
// the client call mechanism to the valgrind tool code, which captures
// each operation and executes them directly in MPFR, instead of using
// whatever special bit twiddling function the standard math library
// provides. This means we can shadow the function properly, with the
// mpfr equivalent, instead of shadowing the arithmetic in libm that's
// only accurate to 64 bits.


/*----------------------------
====== Unary Ops =============
----------------------------*/

#define WRAP_UNARY(fnname, opname)                         \
  double VG_REPLACE_FUNCTION_ZU(LIBM, fnname)(double x);   \
  double VG_REPLACE_FUNCTION_ZU(LIBM, fnname)(double x){   \
    double result;                                         \
    double args[1];                                        \
    args[0] = x;                                           \
    HERBGRIND_PERFORM_OP(opname, &result, args);           \
    return result;                                         \
  }                                                        \
  double VG_REPLACE_FUNCTION_ZU(LIBM_CPP, fnname)(double x);    \
  double VG_REPLACE_FUNCTION_ZU(LIBM_CPP, fnname)(double x){    \
    double result;                                         \
    double args[1];                                        \
    args[0] = x;                                           \
    HERBGRIND_PERFORM_OP(opname, &result, args);           \
    return result;                                         \
  }                                                             \
  double VG_REPLACE_FUNCTION_ZU(NONE, fnname)(double x);    \
  double VG_REPLACE_FUNCTION_ZU(NONE, fnname)(double x){    \
    double result;                                         \
    double args[1];                                        \
    args[0] = x;                                           \
    HERBGRIND_PERFORM_OP(opname, &result, args);           \
    return result;                                         \
  }

// This macro is defined in include/hg_mathreplace_funcs.h, and
// invokes the above macro for each unary operation that needs to be
// wrapped.
#ifndef DONT_WRAP
WRAP_UNARY_OPS
#endif

/*----------------------------
====== Binary Ops ============
----------------------------*/

#define WRAP_BINARY(fnname, opname)                             \
  double VG_REPLACE_FUNCTION_ZU(LIBM, fnname)(double x, double y);  \
  double VG_REPLACE_FUNCTION_ZU(LIBM, fnname)(double x, double y){  \
    double result;                                               \
    double args[2];                                              \
    args[0] = x;                                                 \
    args[1] = y;                                                 \
    HERBGRIND_PERFORM_OP(opname, &result, args);                 \
    return result;                                               \
  }                                                                     \
  double VG_REPLACE_FUNCTION_ZU(LIBM_CPP, fnname)(double x, double y);  \
  double VG_REPLACE_FUNCTION_ZU(LIBM_CPP, fnname)(double x, double y){  \
    double result;                                               \
    double args[2];                                              \
    args[0] = x;                                                 \
    args[1] = y;                                                 \
    HERBGRIND_PERFORM_OP(opname, &result, args);                 \
    return result;                                               \
  }                                                                 \
  double VG_REPLACE_FUNCTION_ZU(NONE, fnname)(double x, double y);  \
  double VG_REPLACE_FUNCTION_ZU(NONE, fnname)(double x, double y){  \
    double result;                                               \
    double args[2];                                              \
    args[0] = x;                                                 \
    args[1] = y;                                                 \
    HERBGRIND_PERFORM_OP(opname, &result, args);                 \
    return result;                                               \
  }

// This macro is defined in include/hg_mathreplace_funcs.h, and
// invokes the above macro for each binary operation that needs to be
// wrapped.
#ifndef DONT_WRAP
WRAP_BINARY_OPS
#endif

/*----------------------------
====== Ternary Ops ===========
----------------------------*/

#define WRAP_TERNARY(fnname, opname)                                    \
  double VG_REPLACE_FUNCTION_ZU(LIBM, fnname)(double x, double y, double z); \
  double VG_REPLACE_FUNCTION_ZU(LIBM, fnname)(double x, double y, double z){ \
    double result;                                                      \
    double args[3];                                                     \
    args[0] = x;                                                        \
    args[1] = y;                                                        \
    args[2] = z;                                                        \
    HERBGRIND_PERFORM_OP(opname, &result, args);                        \
    return result;                                                      \
  }                                                                     \
  double VG_REPLACE_FUNCTION_ZU(LIBM_CPP, fnname)(double x, double y, double z); \
  double VG_REPLACE_FUNCTION_ZU(LIBM_CPP, fnname)(double x, double y, double z){ \
    double result;                                                      \
    double args[3];                                                     \
    args[0] = x;                                                        \
    args[1] = y;                                                        \
    args[2] = z;                                                        \
    HERBGRIND_PERFORM_OP(opname, &result, args);                        \
    return result;                                                      \
  }                                                                     \
  double VG_REPLACE_FUNCTION_ZU(NONE, fnname)(double x, double y, double z); \
  double VG_REPLACE_FUNCTION_ZU(NONE, fnname)(double x, double y, double z){ \
    double result;                                                      \
    double args[3];                                                     \
    args[0] = x;                                                        \
    args[1] = y;                                                        \
    args[2] = z;                                                        \
    HERBGRIND_PERFORM_OP(opname, &result, args);                        \
    return result;                                                      \
  }

// This macro is defined in include/hg_mathreplace_funcs.h, and
// invokes the above macro for each ternary operation that needs to be
// wrapped.
#ifndef DONT_WRAP
WRAP_TERNARY_OPS
#endif

#ifndef DONT_WRAP
// This is a special wrap
void VG_REPLACE_FUNCTION_ZU(LIBM_CPP, sincos)(double x, double* p_sin, double* p_cos);
void VG_REPLACE_FUNCTION_ZU(LIBM_CPP, sincos)(double x, double* p_sin, double* p_cos){
  double args[1];
  args[0] = x;
  HERBGRIND_PERFORM_SPECIAL_OP(OP_SINCOS, args, p_sin, p_cos);
}
void VG_REPLACE_FUNCTION_ZU(LIBM, sincos)(double x, double* p_sin, double* p_cos);
void VG_REPLACE_FUNCTION_ZU(LIBM, sincos)(double x, double* p_sin, double* p_cos){
  double args[1];
  args[0] = x;
  HERBGRIND_PERFORM_SPECIAL_OP(OP_SINCOS, args, p_sin, p_cos);
}

complex double VG_REPLACE_FUNCTION_ZU(LIBM, cexp)(complex double x);
complex double VG_REPLACE_FUNCTION_ZU(LIBM, cexp)(complex double x){
  double sinCosArgs[1];
  double expArgs[1];
  sinCosArgs[0] = cimag(x);
  expArgs[0] = creal(x);
  double sinResult, cosResult, expResult;
  HERBGRIND_PERFORM_OP(OP_SIN, &sinResult, sinCosArgs);
  HERBGRIND_PERFORM_OP(OP_COS, &cosResult, sinCosArgs);
  HERBGRIND_PERFORM_OP(OP_EXP, &expResult, expArgs);
  return (expResult * cosResult) + (expResult * sinResult * I);
}
complex double VG_REPLACE_FUNCTION_ZU(LIBM, clog)(complex double x);
complex double VG_REPLACE_FUNCTION_ZU(LIBM, clog)(complex double x){
  double sqrtArgs[1];
  double logArgs[1];
  double atan2Args[2];
  double sqrtResult, logResult, atan2Result;

  // Real part
  sqrtArgs[0] = creal(x) * creal(x) + cimag(x) * cimag(x);
  HERBGRIND_PERFORM_OP(OP_SQRT, &sqrtResult, sqrtArgs);
  logArgs[0] = sqrtResult;
  HERBGRIND_PERFORM_OP(OP_LOG, &logResult, logArgs);

  // Imaginary part
  atan2Args[0] = cimag(x);
  atan2Args[1] = creal(x);
  HERBGRIND_PERFORM_OP(OP_ATAN2, &atan2Result, atan2Args);

  return logResult + I * atan2Result;
}

complex float VG_REPLACE_FUNCTION_ZU(LIBM, __mulsc3)(complex float x, complex float y);
complex float VG_REPLACE_FUNCTION_ZU(LIBM, __mulsc3)(complex float x, complex float y){
  return x * y;
}
complex double VG_REPLACE_FUNCTION_ZU(LIBM, __muldc3)(complex double x, complex double y);
complex double VG_REPLACE_FUNCTION_ZU(LIBM, __muldc3)(complex double x, complex double y){
  return x * y;
}
complex double VG_REPLACE_FUNCTION_ZU(LIBM, __multc3)(complex double x, complex double y);
complex double VG_REPLACE_FUNCTION_ZU(LIBM, __multc3)(complex double x, complex double y){
  return x * y;
}
complex double VG_REPLACE_FUNCTION_ZU(LIBM, __mulxc3)(complex double x, complex double y);
complex double VG_REPLACE_FUNCTION_ZU(LIBM, __mulxc3)(complex double x, complex double y){
  return x * y;
}

complex float VG_REPLACE_FUNCTION_ZU(LIBM, __divsc3)(complex float x, complex float y);
complex float VG_REPLACE_FUNCTION_ZU(LIBM, __divsc3)(complex float x, complex float y){
  return x / y;
}
complex double VG_REPLACE_FUNCTION_ZU(LIBM, __divdc3)(complex double x, complex double y);
complex double VG_REPLACE_FUNCTION_ZU(LIBM, __divdc3)(complex double x, complex double y){
  return x / y;
}
complex double VG_REPLACE_FUNCTION_ZU(LIBM, __divtc3)(complex double x, complex double y);
complex double VG_REPLACE_FUNCTION_ZU(LIBM, __divtc3)(complex double x, complex double y){
  return x / y;
}
complex double VG_REPLACE_FUNCTION_ZU(LIBM, __divxc3)(complex double x, complex double y);
complex double VG_REPLACE_FUNCTION_ZU(LIBM, __divxc3)(complex double x, complex double y){
  return x / y;
}

#endif
