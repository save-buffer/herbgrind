/*--------------------------------------------------------------------*/
/*--- HerbGrind: a valgrind tool for Herbie               hg_lci.h ---*/
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

#ifndef _HG_LCI_H
#define _HG_LCI_H

#include "pub_tool_basics.h"
#include "hg_storage_runtime.h"
#include "pub_tool_hashtable.h"

#define MAX_LIBM_ARGS 3

typedef struct _InfluenceBits {
  UWord data[4];
} InfluenceBits;

typedef struct _CopyInfluenceInfo {
  UWord src;
  UWord dest;
  UWord size;
} CopyInfluenceInfo;

extern InfluenceBits tempInfluences[MAX_TEMPS];
extern UWord maxTempInfluencesUsed;
extern VgHashTable* memoryInfluences;
extern InfluenceBits tsInfluences[MAX_THREADS][MAX_REGISTERS];
extern InfluenceBits savedInfluences[MAX_LIBM_ARGS];

InfluenceBits getMaskTemp(UWord temp);
InfluenceBits getMaskMem(Addr addr);

void lciGlobalInit(void);
void lciGlobalTeardown(void);
void lciBlockTeardown(void);
VG_REGPARM(3) void copyInfluenceToMem(UWord src_temp, Addr dest_mem,
                                      UWord size);
VG_REGPARM(2) void copyInfluenceToMemIf(CopyInfluenceInfo* info,
                                        UWord cond);
VG_REGPARM(3) void copyInfluenceFromMem(Addr src_mem, UWord dest_temp,
                                        UWord size);
VG_REGPARM(2) void copyInfluenceFromMemIf(CopyInfluenceInfo* info,
                                          UWord cond);
VG_REGPARM(2) void printIfBitsNonZero(Addr bitsLoc, char* label);

void setMaskMem(Addr addr, InfluenceBits influence);

void setBitOn(InfluenceBits* bits, int bits_index);
Bool checkBitOn(InfluenceBits bits, int bits_index);
void compoundAssignOr(InfluenceBits* dest, InfluenceBits other);
void clearInfluenceBits(InfluenceBits* bits);
Bool isNonZero(InfluenceBits bits);

#define IB_ZERO ((InfluenceBits){0})

#endif
