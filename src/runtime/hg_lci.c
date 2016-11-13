/*--------------------------------------------------------------------*/
/*--- HerbGrind: a valgrind tool for Herbie               hg_lci.c ---*/
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

#include "hg_lci.h"
#include "hg_mathreplace.h"

#include "../include/hg_macros.h"

#include "pub_tool_libcbase.h"

InfluenceBits tempInfluences[MAX_TEMPS];
UWord maxTempInfluencesUsed = 0;
VgHashTable* memoryInfluences = NULL;
InfluenceBits tsInfluences[MAX_THREADS][MAX_REGISTERS];

typedef struct _MemEntry {
  struct _MemEntry* next;
  UWord addr;
  InfluenceBits influence;
} MemEntry;

void lciGlobalInit(){
  memoryInfluences = VG_(HT_construct)("mem influences");
}
void lciGlobalTeardown(){
  VG_(HT_destruct)(memoryInfluences, VG_(free));
}
void lciBlockTeardown(){
  VG_(memset)(tempInfluences, 0, sizeof(InfluenceBits) * maxTempInfluencesUsed);
}

VG_REGPARM(2) void copyInfluenceToMem(UWord src_temp, Addr dest_mem){
  InfluenceBits influence = tempInfluences[src_temp];
  setMaskMem(dest_mem, influence);
}
VG_REGPARM(3) void copyInfluenceToMemIf(UWord src_temp, Addr dest_mem,
                                        UWord cond){
  if (cond){
    copyInfluenceToMem(src_temp, dest_mem); 
  }
}
VG_REGPARM(2) void copyInfluenceFromMem(Addr src_mem, UWord dest_temp){
  MemEntry* entry = VG_(HT_lookup)(memoryInfluences, src_mem);
  if (entry){
    /* VG_(printf)("{%p}Copied non-zero influence from %p to temp %lu\n", */
    /*             (void*)getCallAddr(), */
    /*             (void*)src_mem, dest_temp); */
    tempInfluences[dest_temp] = entry->influence;
  } else {
    clearInfluenceBits(&(tempInfluences[dest_temp]));
  }
}
VG_REGPARM(3) void copyInfluenceFromMemIf(Addr src_mem, UWord dest_temp,
                                          UWord cond){
  if (cond){
    copyInfluenceFromMem(src_mem, dest_temp);
  }
}

InfluenceBits getMaskTemp(UWord temp){
  return tempInfluences[temp];
}
InfluenceBits getMaskMem(Addr addr){
  MemEntry* entry = VG_(HT_lookup)(memoryInfluences, addr);
  if (entry){
    return entry->influence;
  } else {
    return IB_ZERO;
  }
}
void setMaskMem(Addr dest_mem, InfluenceBits influence){
  MemEntry* entry = VG_(HT_lookup)(memoryInfluences, dest_mem);
  if (isNonZero(influence) && entry){
    entry->influence = influence;
    /* VG_(printf)("{%p}Copied non-zero influence to %p\n", */
    /*             (void*)getCallAddr(), */
    /*             (void*)dest_mem); */
  } else if (entry){
    clearInfluenceBits(&(entry->influence));
    /* VG_(printf)("{%p}Erased non-zero influence at %p\n", */
    /*             (void*)getCallAddr(), */
    /*             (void*)dest_mem); */
    // Use this if we end up memory constrained.
    /* VG_(free)(VG_(HT_remove)(memoryInfluences, dest_mem)); */
  } else if (isNonZero(influence)){
    ALLOC(entry, "memory influence entry", 1, sizeof(MemEntry));
    entry->addr = dest_mem;
    entry->influence = influence;
    VG_(HT_add_node)(memoryInfluences, entry);
    /* VG_(printf)("{%p}Copied non-zero influence to %p\n", */
    /*             (void*)getCallAddr(), */
    /*             (void*)dest_mem); */
  }
}
VG_REGPARM(2) void printIfBitsNonZero(Addr bitsLoc, char* label){
  if (isNonZero(*(InfluenceBits*)bitsLoc)){
    VG_(printf)("[%s at %p] Found non-zero influence bits at %p\n",
                label,
                (void*)getCallAddr(),
                (void*)bitsLoc);
  }
}

void setBitOn(InfluenceBits* bits, int bits_index){
  bits->data[bits_index / (sizeof(UWord) * 8)] |= 1 << (bits_index % (sizeof(UWord) * 8));
}
Bool checkBitOn(InfluenceBits bits, int bits_index){
  return ((bits.data[bits_index / (sizeof(UWord) * 8)] & (1 << (bits_index % (sizeof(UWord) * 8)))) != 0);
}
void compoundAssignOr(InfluenceBits* dest, InfluenceBits other){
  for (int i = 0; i < 4; ++i){
    dest->data[i] |= other.data[i];
  }
}
void clearInfluenceBits(InfluenceBits* bits){
  for (int i = 0; i < 4; ++i){
    bits->data[i] = 0;
  }
}
Bool isNonZero(InfluenceBits bits){
  for (int i = 0; i < 4; ++i){
    if (bits.data[i] != 0){
      return True;
    }
  }
  return False;
}
