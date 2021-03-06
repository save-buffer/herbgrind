/*--------------------------------------------------------------------*/
/*--- Herbgrind: a valgrind tool for Herbie          symbolic-op.h ---*/
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

#ifndef _SYMBOLIC_OP_H
#define _SYMBOLIC_OP_H

#include "../value-shadowstate/exprs.h"
#include "../value-shadowstate/shadowval.h"
#include "../value-shadowstate/pos-tree.h"
#include "../op-shadowstate/shadowop-info.h"

#include "pub_tool_basics.h"
#include "pub_tool_hashtable.h"

typedef struct _varMapEntry {
  struct _varMapEntry* next;
  UWord positionHash;
  NodePos position;
  UWord varIdx;
} VarMapEntry;

typedef struct _valMapEntry {
  struct _valMapEntry* next;
  UWord valHash;
  double val;
  UWord groupIdx;
} ValMapEntry;

typedef struct _rangeMapEntry {
  struct _rangeMapEntry* next;
  UWord positionHash;
  NodePos position;
  RangeRecord range_rec;
} RangeMapEntry;
typedef struct _exampleMapEntry {
  struct _exampleMapEntry* next;
  UWord positionHash;
  NodePos position;
  double value;
} ExampleMapEntry;

void execSymbolicOp(ShadowOpInfo* opinfo, ConcExpr** result,
                    double computedResult, ShadowValue** args,
                    Bool problematic);
void generalizeSymbolicExpr(SymbExpr** symexpr, ConcExpr* cexpr);

void generalizeStructure(SymbExpr* symbexpr, ConcExpr* concExpr,
                         int depth);
void intersectEqualities(SymbExpr* symbexpr, ConcExpr* concExpr);
GroupList getExprsEquivGroups(ConcExpr* concExpr, SymbExpr* symbExpr);
GroupList dedupGroups(GroupList list);
GroupList pruneSingletonGroups(GroupList list);
GroupList groupsWithoutNonVars(SymbExpr* structure, GroupList list,
                               int max_depth);

VarMap* mkVarMap(GroupList groups);
int lookupVar(VarMap* map, NodePos pos);
void freeVarMap(VarMap* map);

void addValEntry(VgHashTable* valmap, double val, int groupIdx);
int lookupVal(VgHashTable* valmap, double val);
UWord hashValue(double val);
Word cmp_value(const void* node1, const void* node2);

ConcExpr* concExprPosGet(ConcExpr* expr, NodePos pos);
SymbExpr* symbExprPosGet(SymbExpr* expr, NodePos pos);
SymbExpr** symbExprPosGetRef(SymbExpr** expr, NodePos pos);
Word cmp_position(const void* node1, const void* node2);
#endif
