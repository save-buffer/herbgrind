/*--------------------------------------------------------------------*/
/*--- Herbgrind: a valgrind tool for Herbie          semantic-op.h ---*/
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

#ifndef _SEMANTIC_OP_H
#define _SEMANTIC_OP_H

#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"

#include "../runtime/value-shadowstate/shadowval.h"
#include "../runtime/op-shadowstate/shadowop-info.h"

void instrumentSemanticOp(IRSB* sbOut, IROp op_code,
                          int nargs, IRExpr** argExprs,
                          Addr curAddr, Addr blockAddr,
                          IRTemp dest);
void instrumentPossibleNegate(IRSB* sbOut,
                              IRExpr** argExprs, IRTemp dest,
                              Addr curAddr, Addr blockAddr);

IRExpr* runShadowOp(IRSB* sbOut, IRExpr* guard,
                    IROp op_code,
                    Addr curAddr, Addr block_addr,
                    int nargs, IRExpr** argsExprs,
                    IRExpr* result);
ShadowOpInfoInstance* getSemanticOpInfoInstance(Addr callAddr, Addr block_addr,
                                                IROp op_code,
                                                int nargs, IRExpr** argExprs);
long int cmpSemOpInfoEntry(const void* node1, const void* node2);
#endif
