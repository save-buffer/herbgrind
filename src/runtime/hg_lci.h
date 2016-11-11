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
#include "pub_tool_basics.h"
#include "hg_storage_runtime.h"
#include "pub_tool_hashtable.h"

extern UWord tempInfluences[MAX_TEMPS];
extern UWord maxTempInfluencesUsed;
extern VgHashTable* memoryInfluences;
extern UWord tsInfluences[MAX_THREADS][MAX_REGISTERS];

UWord getMaskTemp(UWord temp);
UWord getMaskMem(Addr addr);

void lciGlobalInit(void);
void lciGlobalTeardown(void);
void lciBlockTeardown(void);
VG_REGPARM(2) void copyInfluenceToMem(UWord src_temp, Addr dest_mem);
VG_REGPARM(3) void copyInfluenceToMemIf(UWord src_temp, Addr dest_mem,
                                        UWord cond);
VG_REGPARM(2) void copyInfluenceFromMem(Addr src_mem, UWord dest_temp);
VG_REGPARM(3) void copyInfluenceFromMemIf(Addr src_mem, UWord dest_temp,
                                          UWord cond);
VG_REGPARM(2) void printIfBitsNonZero(Addr bitsLoc, char* label);

void setMaskMem(Addr addr, UWord influence);
