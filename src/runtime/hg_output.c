/*--------------------------------------------------------------------*/
/*--- HerbGrind: a valgrind tool for Herbie            herbgrind.h ---*/
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
#include "hg_output.h"
#include "hg_runtime.h"
#include "../types/hg_stemtea.h"
#include "../types/hg_queue.h"
#include "pub_tool_libcassert.h"
#include "../include/hg_macros.h"
#include "hg_mathreplace.h"

#include "pub_tool_vki.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_stacktrace.h"
#include "pub_tool_threadstate.h"

XArray* marks;
Op_Info* influencesTable[128];

// How many characters are going to be allowed in each entry.
#define ENTRY_BUFFER_SIZE 2048

#define NCALLFRAMES 5

OutputMark* mkMark(Op_Info* op, Addr curAddr){
  OutputMark* mark;
  ALLOC(mark, "output mark", 1, sizeof(OutputMark));
  mark->op = op;

  mark->debuginfo.addr = curAddr;
  tl_assert2(VG_(get_filename_linenum)(curAddr,
                                       &(mark->debuginfo.src_filename),
                                       NULL,
                                       &(mark->debuginfo.src_line)) &&
             VG_(get_fnname)(curAddr, &(mark->debuginfo.fnname)),
             "Couldn't find debug info! Please compile with debug info.");

  mark->influences = VG_(newXA)(VG_(malloc), "influence tracker",
                                VG_(free), sizeof(Op_Info*));

  return mark;
}

void markValueImportant(ShadowValue* shadowVal, Op_Info* op, InfluenceBits lciBits,
                        double computedValue){
  if (marks == NULL){
    marks = VG_(newXA)(VG_(malloc), "op tracker",
                       VG_(free), sizeof(OutputMark*));
  }

  // Get the current client PC
  Addr curAddr = getCallAddr();
  // See if we've already hit this mark. If so, use existing mark
  // data.
  OutputMark* curMark = NULL;
  for (int i = 0; i < VG_(sizeXA)(marks); ++i){
    if ((*(OutputMark**)VG_(indexXA)(marks, i))->debuginfo.addr ==
        curAddr){
      curMark = *(OutputMark**)VG_(indexXA)(marks, i);
      break;
    }
  }
  if (curMark == NULL){
    if (shadowVal){
      curMark = mkMark(op, curAddr);
    } else {
      curMark = mkMark(NULL, curAddr);
    }
    VG_(addToXA)(marks, &curMark);
  }
  compoundAssignOr(&(curMark->lciBits), lciBits);

  if (shadowVal){
    for (int i = 0; i < VG_(sizeXA)(shadowVal->tracked_influences); ++i){
      Op_Info* new_influence =
        *(Op_Info**)VG_(indexXA)(shadowVal->tracked_influences, i);
      dedupAdd(curMark->influences, new_influence);
    }
    evaluateError_bare(shadowVal, &(curMark->evalinfo), computedValue);
  }
}
void trackValueExpr(ShadowValue* val, Op_Info* op, double computedValue){
  dedupAdd(val->tracked_influences, op);

  int tableIndex = addInfluenceToTableDedup(op);
  setBitOn(&(tempInfluences[op->dest_tmp]), tableIndex);

  if (report_all){
    markValueImportant(val, op, getMaskTemp(op->dest_tmp),
                       computedValue);
  }
}
void propagateInfluences(ShadowValue* dest, int nargs, ...){
  va_list args;
  va_start(args, nargs);
  for(SizeT i = 0; i < nargs; ++i){
    ShadowValue* argVal = va_arg(args, ShadowValue*);
    for (SizeT j = 0; j < VG_(sizeXA)(argVal->tracked_influences); ++j){
      Op_Info* new_influence =
        *(Op_Info**)VG_(indexXA)(argVal->tracked_influences, j);
      dedupAdd(dest->tracked_influences, new_influence);
    }
  }
  va_end(args);
}

// Assumes no duplicates. Will result in NULL's in the tracked ops
// list, does not actually remove from the list, just sets matching op
// to NULL.
void clearInfluence(Op_Info* opinfo, XArray* influences){
  for(int i = 0; i < VG_(sizeXA)(influences); ++i){
    Op_Info** entry = VG_(indexXA)(influences, i);
    if (*entry == NULL) continue;
    if (*entry == opinfo){
      *entry = NULL;
      return;
    }
  }
}
typedef struct _cEntry {
  TeaNode* node;
  SizeT depth;
} cEntry;
cEntry* mkCEntry(TeaNode* node, SizeT depth);
cEntry* mkCEntry(TeaNode* node, SizeT depth){
  cEntry* entry;
  ALLOC(entry, "clear argument entry",
        1, sizeof(cEntry));
  entry->node = node;
  entry->depth = depth;
  return entry;
}
void recursivelyClearChildren(TeaNode* _node, XArray* influences){
  Queue* clearQueue = mkQueue();
  queue_push(clearQueue, mkCEntry(_node, 0));
  while (! queue_empty(clearQueue)){
    cEntry* entry = queue_pop(clearQueue);
    TeaNode* node = entry->node;
    if (node->type == Node_Branch && entry->depth < max_tea_track_depth){
      for(int i = 0; i < node->branch.nargs; ++i){
        TeaNode* child = node->branch.args[i];
        if (child == _node) continue;
        if (child != NULL && child->type == Node_Branch){
          queue_push(clearQueue, mkCEntry(child, entry->depth + 1));
          clearInfluence(child->branch.op, influences);
        }
      }
    }
    VG_(free)(entry);
  }
  freeQueue(clearQueue);
}

Word cmp_debuginfo(const Op_Info** a, const Op_Info** b){
  if (*a == NULL && *b == NULL){
    return 0;
  } else if (*a == NULL){
    return 1;
  } else if (*b == NULL){
    return -1;
  }
  double aMax = (*a)->evalinfo.max_error;
  double bMax = (*b)->evalinfo.max_error;
  if (aMax > bMax){
    return -1;
  } else if (aMax < bMax){
    return 1;
  } else {
    return 0;
  }
}

void writeReport(const char* filename){
  VG_(printf)("Writing report...\n");
  // Try to open the filename they gave us.
  SysRes file_result = VG_(open)(filename,
                                 VKI_O_CREAT | VKI_O_TRUNC | VKI_O_WRONLY,
                                 VKI_S_IRUSR | VKI_S_IWUSR);
  if(sr_isError(file_result)){
    VG_(printf)("Couldn't open output file!\n");
    return;
  }
  Int file_d = sr_Res(file_result);

  if (marks == NULL){
    VG_(write)(file_d, "No outputs found.\n", 18);
    VG_(close)(file_d);
    VG_(printf)("Wrote report out to %s\n", filename);
    return;
  }

  XArray* influencesPrinted = VG_(newXA)(VG_(malloc), "already_printed_influences",
                                         VG_(free), sizeof(Op_Info*));

  for(int i = 0; i < VG_(sizeXA)(marks); ++i){
    OutputMark* mark = *(OutputMark**)VG_(indexXA)(marks, i);

    HChar buf[ENTRY_BUFFER_SIZE];
    UInt entry_len;

    if (!report_all){
      if (human_readable){
        entry_len = VG_(snprintf)(buf, ENTRY_BUFFER_SIZE,
                                  "Result in %s at %s:%u (address %lX)\n",
                                  mark->debuginfo.fnname,
                                  mark->debuginfo.src_filename,
                                  mark->debuginfo.src_line,
                                  mark->debuginfo.addr);
        if (mark->op != NULL){
          entry_len += VG_(snprintf)(buf + entry_len,
                                     ENTRY_BUFFER_SIZE - entry_len,
                                     "%f bits average error\n"
                                     "%f bits max error\n"
                                     "Aggregated over %lu instances\n",
                                     mark->evalinfo.total_error /
                                     mark->evalinfo.num_calls,
                                     mark->evalinfo.max_error,
                                     mark->evalinfo.num_calls);
        }
        entry_len += VG_(snprintf)(buf + entry_len,
                                   ENTRY_BUFFER_SIZE - entry_len,
                                   "Influenced by erroneous expressions:\n\n");
      } else {
        entry_len = VG_(snprintf)(buf, ENTRY_BUFFER_SIZE,
                                  "(output\n"
                                  "  (function \"%s\")\n"
                                  "  (filename \"%s\")\n"
                                  "  (line-num %u)\n"
                                  "  (instr-addr %lX)\n",
                                  mark->debuginfo.fnname,
                                  mark->debuginfo.src_filename,
                                  mark->debuginfo.src_line,
                                  mark->debuginfo.addr);
        if (mark->op != NULL){
          entry_len += VG_(snprintf)(buf + entry_len,
                                     ENTRY_BUFFER_SIZE - entry_len,
                                     "  (avg-error %f)\n"
                                     "  (max-error %f)\n"
                                     "  (num-calls %lu)\n",
                                     mark->evalinfo.total_error /
                                     mark->evalinfo.num_calls,
                                     mark->evalinfo.max_error,
                                     mark->evalinfo.num_calls);
        }
        entry_len += VG_(snprintf)(buf + entry_len,
                                   ENTRY_BUFFER_SIZE - entry_len,
                                   "  (influences\n");

      }
      VG_(write)(file_d, buf, entry_len);
    }

    entry_len =
      VG_(snprintf)(buf, ENTRY_BUFFER_SIZE,
                    "   According to lightweight complete influences system:\n");
    VG_(write)(file_d, buf, entry_len);
    for(int j = 0; j < sizeof(InfluenceBits) * 8; ++j){
      if (checkBitOn(mark->lciBits, j)){
        writeEntry(influencesTable[j], file_d);
      }
    }
    entry_len =
      VG_(snprintf)(buf, ENTRY_BUFFER_SIZE,
                    "   END\n\n");
    VG_(write)(file_d, buf, entry_len);

    if (mark->op != NULL){
      // Clear the subexpressions of each expression so that we don't
      // print both an expression and one of it's subexpressions if
      // there are multiple sources of error.
      XArray* influences = mark->influences;
      if (report_exprs){
        for (int j = VG_(sizeXA)(influences) - 1; j >= 0; --j){
          Op_Info* influence = *(Op_Info**)VG_(indexXA)(influences, j);
          if (influence == NULL) continue;
          recursivelyClearChildren(influence->tea, influences);
        }
      }
      VG_(setCmpFnXA)(influences, (XACmpFn_t)cmp_debuginfo);
      // Sort the entries by maximum error.
      VG_(sortXA)(influences);

      for (int j = 0; j < VG_(sizeXA)(influences); ++j){
        Op_Info* influence = *(Op_Info**)VG_(indexXA)(influences, j);
        if (influence == NULL){
          continue;
        }

        if (report_all){
          // Remove duplicates
          Bool alreadyPrinted = False;
          for(int k = 0; k < VG_(sizeXA)(influencesPrinted); ++k){
            if (influence == *(Op_Info**)VG_(indexXA)(influencesPrinted, k)){
              alreadyPrinted = True;
              VG_(printf)("Influence already printed!\n");
              break;
            }
          }
          if (alreadyPrinted){
            VG_(printf)("Influence already printed!\n");
            continue;
          }
        }

        writeEntry(influence, file_d);

        if (report_all){
          VG_(addToXA)(influencesPrinted, &influence);
        }
      }
    }
    if (!human_readable){
      VG_(write)(file_d, "  ))\n", 5);
    }
  }
  VG_(deleteXA)(influencesPrinted);
  VG_(close)(file_d);
  VG_(printf)("Wrote report out to %s\n", filename);
}

void dedupAdd(XArray* array, void* item){
  Bool already_have = False;
  for (SizeT k = 0; k < VG_(sizeXA)(array); ++k){
    if (*(void**)VG_(indexXA)(array, k) == item){
      already_have = True;
      break;
    }
  }
  if (!already_have){
    VG_(addToXA)(array, &item);
  }
}
int addInfluenceToTableDedup(Op_Info* influence){
  int i;
  for (i = 0; i < 64; ++i){
    if (influencesTable[i] == influence){
      return i;
    }
    if (influencesTable[i] == NULL){
      break;
    }
  }
  tl_assert2(i < 64 * 4, "Too many influences added to table!!!\n");
  influencesTable[i] = influence;
  return i;
}

void writeEntry(Op_Info* opinfo, Int file_d){
  UInt entry_len;
  HChar buf[ENTRY_BUFFER_SIZE];
  if (report_exprs){
    char* benchString = teaToBenchString(opinfo->tea, True);
    if (human_readable){
      entry_len =
        VG_(snprintf)(buf, ENTRY_BUFFER_SIZE,
                      "    %s\n"
                      "    in %s at %s:%u (address %lX)\n"
                      "    %f bits average error\n"
                      "    %f bits max error\n"
                      "    %f bits max local error\n"
                      "    Aggregated over %lu instances\n\n",
                      benchString,
                      opinfo->debuginfo.fnname,
                      opinfo->debuginfo.src_filename,
                      opinfo->debuginfo.src_line,
                      opinfo->debuginfo.addr,
                      opinfo->evalinfo.total_error /
                      opinfo->evalinfo.num_calls,
                      opinfo->evalinfo.max_error,
                      opinfo->evalinfo.max_local,
                      opinfo->evalinfo.num_calls);
    } else {
      entry_len =
        VG_(snprintf)(buf, ENTRY_BUFFER_SIZE,
                      "    (%s\n"
                      "     (function \"%s\")\n"
                      "     (filename \"%s\")\n"
                      "     (line-num %u)\n"
                      "     (instr-addr %lX)\n"
                      "     (avg-error %f)\n"
                      "     (max-error %f)\n"
                      "     (max-local %f)\n"
                      "     (num-calls %lu))\n",
                      benchString,
                      opinfo->debuginfo.fnname,
                      opinfo->debuginfo.src_filename,
                      opinfo->debuginfo.src_line,
                      opinfo->debuginfo.addr,
                      opinfo->evalinfo.total_error /
                      opinfo->evalinfo.num_calls,
                      opinfo->evalinfo.max_error,
                      opinfo->evalinfo.max_local,
                      opinfo->evalinfo.num_calls);
    }
  } else {
    if (human_readable){
      entry_len =
        VG_(snprintf)(buf, ENTRY_BUFFER_SIZE,
                      "    %s in %s at %s:%u (address %lX)\n"
                      "    %f bits average error\n"
                      "    %f bits max error\n"
                      "    Aggregated over %lu instances\n\n",
                      opinfo->debuginfo.plain_opname,
                      opinfo->debuginfo.fnname,
                      opinfo->debuginfo.src_filename,
                      opinfo->debuginfo.src_line,
                      opinfo->debuginfo.addr,
                      opinfo->evalinfo.total_error /
                      opinfo->evalinfo.num_calls,
                      opinfo->evalinfo.max_error,
                      opinfo->evalinfo.num_calls);
    } else {
      entry_len =
        VG_(snprintf)(buf, ENTRY_BUFFER_SIZE,
                      "    ((plain-name \"%s\")\n"
                      "     (function \"%s\")\n"
                      "     (filename \"%s\")\n"
                      "     (line-num %u)\n"
                      "     (instr-addr %lX)\n"
                      "     (avg-error %f)\n"
                      "     (max-error %f)\n"
                      "     (num-calls %lu))\n",
                      opinfo->debuginfo.plain_opname,
                      opinfo->debuginfo.fnname,
                      opinfo->debuginfo.src_filename,
                      opinfo->debuginfo.src_line,
                      opinfo->debuginfo.addr,
                      opinfo->evalinfo.total_error /
                      opinfo->evalinfo.num_calls,
                      opinfo->evalinfo.max_error,
                      opinfo->evalinfo.num_calls);
    }
  }
  VG_(write)(file_d, buf, entry_len);
}
