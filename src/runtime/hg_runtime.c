
/*--------------------------------------------------------------------*/
/*--- HerbGrind: a valgrind tool for Herbie           hg_runtime.c ---*/
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

#include "hg_runtime.h"

#include "hg_mathreplace.h"
#include "../include/hg_options.h"
#include "hg_lci.h"

// Pull in this header file so that we can set the strlen, strcpy,
// memmove, memcmp, and memset functions of mpfr to their valgrind
// library equivalents.
#include "pub_tool_libcbase.h"

// Whether or not the tool is currently "turned on".
Bool running = True;

// This disables the instrumentation of this tool.
void stopHerbGrind(void){ running = False; }

// This enables the instrumentation of this tool.
void startHerbGrind(void){ running = True; }

// Some memory allocation functions for gmp support
void* gmp_alloc(size_t t){ return VG_(malloc)("hg.gmp_alloc.1", t); }
void* gmp_realloc(void* p, size_t t1, size_t t2){ return VG_(realloc)("hg.gmp_realloc.1", p, t2); }
void gmp_free(void* p, size_t t){ VG_(free)(p); }

// We wrap these functions because they require slightly different
// types, and we want the coercions to work out.
size_t mpfr_strlen(const char* str){ return VG_(strlen)(str); }
long int mpfr_strtol(const char* str, char** endptr, int _base) {
  // Ignoring the base. This works everywhere we care about for now.
  return VG_(strtoll10)(str, endptr);
}
int mpfr_isspace(int c){ return VG_(isspace)(c); }
void* mpfr_memmove(void* dest, const void* src, size_t len){ return VG_(memmove)(dest, src, len); }
int mpfr_memcmp(const void* ptr1, const void* ptr2, size_t len){ return VG_(memcmp)(ptr1, ptr2, len); }
void* mpfr_memset(void* dest, int val, size_t size){ return VG_(memset)(dest, val, size); }

void init_runtime(void){
  mpfr_set_default_prec(precision);
  // Set up the shadow memory, thread state, and temporaries.
  initStorage();
  // Set up the wrapping function table
  callToOpInfoMap = VG_(HT_construct)("callToOpInfoMap");
  lciGlobalInit();
}
void cleanup_runtime(void){
  // Clean up the mpfr cache
  mpfr_free_cache();
  cleanupStorage();
  lciGlobalTeardown();
}
