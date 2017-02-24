/*--------------------------------------------------------------------*/
/*--- HerbGrind: a valgrind tool for Herbie           floattypes.h ---*/
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

#ifndef _FLOATTYPES_H
#define _FLOATTYPES_H

#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_hashtable.h"

#define MAX_TEMPS 1000
#define MAX_REGISTERS 1000

typedef enum {
  Ft_Unknown,
  Ft_NonFloat,
  Ft_Unshadowed,
  Ft_Single,
  Ft_Double
} FloatType;

FloatType argPrecision(IROp op_code);
FloatType resultPrecision(IROp op_code);

int isFloatType(IRType type);
int isFloat(IRTypeEnv* env, IRTemp temp);

void ppFloatType(FloatType type);

int valueSize(IRSB* sbOut, int idx);
int numTempValues(IRSB* sbOut, int idx);
int exprSize(IRTypeEnv* tyenv, IRExpr* expr);
int typeSize(IRType type);
#endif
