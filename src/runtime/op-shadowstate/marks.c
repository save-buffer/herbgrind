/*--------------------------------------------------------------------*/
/*--- Herbgrind: a valgrind tool for Herbie                marks.c ---*/
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

#include "marks.h"
#include "../../helper/runtime-util.h"
#include "../value-shadowstate/shadowval.h"
#include "../shadowop/error.h"
#include "../shadowop/influence-op.h"
#include "pub_tool_libcprint.h"

List_Impl(MarkInfo, MarkList);

VgHashTable* markMap = NULL;

void markImportant(Addr varAddr){
  Addr callAddr = getCallAddr();
  MarkInfo* info = getMarkInfo(callAddr);
  tl_assert(info != NULL);
  ShadowValue* val = getMemShadow(varAddr);
  if (val == NULL){
    VG_(umsg)("This mark couldn't find a shadow value! This means either it lost the value, or there were no floating point operations on this value prior to hitting this mark.\n");
    if (info->eagg->max_error < 0){
      info->eagg->max_error = 0;
    }
    info->eagg->num_evals += 1;
    return;
  }
  addInfluencesToMark(info, val->influences);
  if (print_errors || print_errors_long){
    printMarkInfo(info);
  }
  updateError(&(info->eagg), val->real, *(double*)varAddr);
}

MarkInfo* getMarkInfo(Addr callAddr){
  MarkInfo* markInfo = VG_(HT_lookup)(markMap, callAddr);
  if (markInfo == NULL){
    markInfo = VG_(perm_malloc)(sizeof(MarkInfo), vg_alignof(MarkInfo));
    markInfo->addr = callAddr;
    markInfo->influences = NULL;
    markInfo->eagg.max_error = -1;
    markInfo->eagg.total_error = 0;
    markInfo->eagg.num_evals = 0;
    VG_(HT_add_node)(markMap, markInfo);
  }
  return markInfo;
}

void addInfluencesToMark(MarkInfo* info, InfluenceList influences){
  for(InfluenceList curNode = influences; curNode != NULL;
      curNode = curNode->next){
    dedupAddInfluenceToList(&(info->influences), curNode->item);
  }
}

void printMarkInfo(MarkInfo* info){
  VG_(printf)("At ");
  ppAddr(info->addr);
}

int isSubexpr(SymbExpr* needle, SymbExpr* haystack, int depth){
  if (needle == haystack) return 1;
  else if (haystack->type == Node_Leaf) return 0;
  else {
    for(int i = 0; i < haystack->branch.nargs; ++i){
      if (isSubexpr(needle, haystack->branch.args[i], depth - 1)) return 1;
    }
    return 0;
  }
}

InfluenceList filterInfluenceSubexprs(InfluenceList influences){
  InfluenceList result = NULL;
  for(InfluenceList curNode = influences;
      curNode != NULL;
      curNode = curNode->next){
    ShadowOpInfo* influence = curNode->item;
    for(InfluenceList otherNode = influences;
        otherNode != NULL;
        otherNode = otherNode->next){
      ShadowOpInfo* otherInfluence = otherNode->item;
      if (otherInfluence == influence){
        continue;
      }
      if (isSubexpr(influence->expr, otherInfluence->expr, MAX_EXPR_IMPRECISE_BLOCK_DEPTH)){
        goto dont_keep_influence;
      }
    }
    lpush(InfluenceList)(&result, influence);
  dont_keep_influence:;
  }
  return result;
}
