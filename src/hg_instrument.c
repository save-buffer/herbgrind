
/*--------------------------------------------------------------------*/
/*--- HerbGrind: a valgrind tool for Herbie        hg_instrument.c ---*/
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

#include "hg_instrument.h"
#include "include/hg_helper.h"
#include "include/hg_macros.h"
#include "runtime/hg_mathreplace.h"
#include "runtime/hg_lci.h"
#include "pub_tool_hashtable.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_libcassert.h"

VgHashTable* opinfo_store;

void instrumentStatement(IRStmt* st, IRSB* sbOut, Addr stAddr, int opNum){
  IRExpr* expr;
  IRDirty* copyShadowLocation;
  LoadG_Info* loadGInfo;
  CpShadow_Info* cpinfo;

  addStmtToIRSB(sbOut, st);

  switch (st->tag) {
    // If it's a no op, or just metadata, we'll just pass it into
    // the result IR.
  case Ist_NoOp:
  case Ist_IMark:
    // If it's a memory bus event, an exit, or a hint, we shouldn't have to
    // do much with it either.
  case Ist_MBE:
  case Ist_Exit:
  case Ist_AbiHint:
    break;
  case Ist_Put:
    // Here we'll want to instrument moving Shadow values into
    // thread state. In flattened IR, these shadow values should
    // always come from temporaries.

    expr = st->Ist.Put.data;
    switch (expr->tag) {
    case Iex_RdTmp:
      if (isFloat(sbOut->tyenv, expr->Iex.RdTmp.tmp)){
        ALLOC(cpinfo, "hg.copyShadowTmptoTSInfo.1", 1, sizeof(CpShadow_Info));
        cpinfo->instr_addr = stAddr;
        cpinfo->type = typeOfIRTemp(sbOut->tyenv, expr->Iex.RdTmp.tmp);
        // The number of the temporary
        cpinfo->src_idx = expr->Iex.RdTmp.tmp;
        // The thread state offset
        cpinfo->dest_idx = st->Ist.Put.offset;

        copyShadowLocation =
          unsafeIRDirty_0_N(1,
                            "copyShadowTmptoTS",
                            VG_(fnptr_to_fnentry)(&copyShadowTmptoTS),
                            mkIRExprVec_1(mkU64((uintptr_t)cpinfo)));
        addStmtToIRSB(sbOut, IRStmt_Dirty(copyShadowLocation));
      } else {
        copyShadowLocation =
          unsafeIRDirty_0_N(2,
                            "clearTS",
                            VG_(fnptr_to_fnentry)(&clearTS),
                            mkIRExprVec_2(mkU64(st->Ist.Put.offset),
                                          mkU64(sizeOfIRType(typeOfIRTemp(sbOut->tyenv, expr->Iex.RdTmp.tmp)))));
      }
      IRTemp influence = newIRTemp(sbOut->tyenv, Ity_I64);
      addLoad64(sbOut, &(tempInfluences[expr->Iex.RdTmp.tmp]), influence);
      for (int i = 0; i < sizeOfIRType(typeOfIRTemp(sbOut->tyenv,
                                                    influence));
           ++i){
        addStore(sbOut,
                 IRExpr_RdTmp(influence),
                 &(tsInfluences
                   [VG_(get_running_tid)()]
                   [st->Ist.Put.offset + i]));
      }
      break;
    case Iex_Const:
      copyShadowLocation =
        unsafeIRDirty_0_N(2,
                          "clearTS",
                          VG_(fnptr_to_fnentry)(&clearTS),
                          mkIRExprVec_2(mkU64(st->Ist.Put.offset),
                                        mkU64(sizeOfIRType(typeOfIRConst(expr->Iex.Const.con)))));
      /* addStmtToIRSB(sbOut, IRStmt_Dirty(copyShadowLocation)); */
      /* for(int i = 0; i < sizeOfIRType(typeOfIRConst(expr->Iex.Const.con)); */
      /*     ++i){ */
      /*   addStore(sbOut, */
      /*            mkU64(0), */
      /*            &(threadRegisters */
      /*              [VG_(get_running_tid)()] */
      /*              [st->Ist.Put.offset + i])); */
      /* } */
      /* addStore(sbOut, */
      /*          mkU64(0), */
      /*          &(threadRegisters */
      /*            [VG_(get_running_tid)()] */
      /*            [st->Ist.Put.offset])); */
      break;
    default:
      // This shouldn't happen in flattened IR.
      VG_(dmsg)("\
A non-constant or temp is being placed into thread state in a single IR statement! \
That doesn't seem flattened...\n");
      break;
    }
    break;
  case Ist_PutI:
    /* tl_assert(0); */
    // This will look a lot like above, but we have to deal with not
    // knowing at compile time which piece of thread state we're
    // putting into. This will probably involve putting more burden
    // on the runtime c function which we'll insert after the put to
    // process it.

    expr = st->Ist.PutI.details->data;
    switch (expr->tag) {
    case Iex_RdTmp:
      {
        IRExpr* indexExpr =
          // Calculate array_base + (ix + bias) %
          // array_len at run time. This will give us
          // the offset into the thread state at which
          // the actual put is happening, so we can
          // use that same offset for the shadow get.
          mkArrayLookupExpr(st->Ist.PutI.details->descr->base,
                            st->Ist.PutI.details->ix,
                            st->Ist.PutI.details->bias,
                            st->Ist.PutI.details->descr->nElems,
                            sbOut);
        IRTemp influence = newIRTemp(sbOut->tyenv, Ity_I64);
        addLoad64(sbOut, &(tempInfluences[expr->Iex.RdTmp.tmp]),
                  influence);
        IRTemp destAddr = newIRTemp(sbOut->tyenv, Ity_I64);
        IRStmt* computeDestAddr =
          IRStmt_WrTmp(destAddr,
                       IRExpr_Binop(Iop_Add64,
                                    mkU64((uintptr_t)
                                          (tsInfluences
                                           [VG_(get_running_tid)()])),
                                    indexExpr));
        addStmtToIRSB(sbOut, computeDestAddr);
        addStoreE(sbOut,
                  IRExpr_RdTmp(influence),
                  IRExpr_RdTmp(destAddr));
        if (isFloat(sbOut->tyenv, expr->Iex.RdTmp.tmp)){
          ALLOC(cpinfo, "hg.copyShadowTmptoTSInfo.1", 1, sizeof(CpShadow_Info));
          cpinfo->instr_addr = stAddr;
          cpinfo->type = typeOfIRTemp(sbOut->tyenv, expr->Iex.RdTmp.tmp);
          cpinfo->src_idx = expr->Iex.RdTmp.tmp;

          addStore(sbOut,
                   indexExpr,
                   &(cpinfo->dest_idx));
          copyShadowLocation =
            unsafeIRDirty_0_N(1, "copyShadowTmptoTS",
                              VG_(fnptr_to_fnentry)(&copyShadowTmptoTS),
                              mkIRExprVec_1(mkU64((uintptr_t)cpinfo)));
          addStmtToIRSB(sbOut, IRStmt_Dirty(copyShadowLocation));
        } else {
          IRTemp shadowDestAddr = newIRTemp(sbOut->tyenv, Ity_I64);
          IRStmt* computeSDestAddr =
            IRStmt_WrTmp(shadowDestAddr,
                         IRExpr_Binop(Iop_Add64,
                                      mkU64((uintptr_t)threadRegisters
                                            [VG_(get_running_tid)()]),
                                      indexExpr));
          addStmtToIRSB(sbOut, computeSDestAddr);
          addStoreE(sbOut,
                    mkU64(0),
                    IRExpr_RdTmp(shadowDestAddr));
        }
      }
      break;
    case Iex_Const:
      {
        IRExpr* indexExpr =
          // Calculate array_base + (ix + bias) %
          // array_len at run time. This will give us
          // the offset into the thread state at which
          // the actual put is happening, so we can
          // use that same offset for the shadow get.
          mkArrayLookupExpr(st->Ist.PutI.details->descr->base,
                            st->Ist.PutI.details->ix,
                            st->Ist.PutI.details->bias,
                            st->Ist.PutI.details->descr->nElems,
                            sbOut);
        IRTemp shadowDestAddr = newIRTemp(sbOut->tyenv, Ity_I64);
        IRStmt* computeSDestAddr =
          IRStmt_WrTmp(shadowDestAddr,
                       IRExpr_Binop(Iop_Add64,
                                    mkU64((uintptr_t)
                                          (threadRegisters
                                           [VG_(get_running_tid)()])),
                                    indexExpr));
        addStmtToIRSB(sbOut, computeSDestAddr);
        addStoreE(sbOut,
                  mkU64(0),
                  IRExpr_RdTmp(shadowDestAddr));
      }
      break;
    default:
      // This shouldn't happen in flattened IR.
      VG_(dmsg)("\
A non-constant or temp is being placed into thread state in a single IR statement! \
That doesn't seem flattened...\n");
      break;
    }
    break;
  case Ist_WrTmp:
    // Here we'll instrument moving Shadow values into temps. See
    // above.
    expr = st->Ist.WrTmp.data;
    IRTemp oldMax = newIRTemp(sbOut->tyenv, Ity_I64);
    addLoad64(sbOut, &maxTempInfluencesUsed, oldMax);
    IRTemp greaterThanMaxTemp = newIRTemp(sbOut->tyenv, Ity_I1);
    IRStmt* checkGreater =
      IRStmt_WrTmp(greaterThanMaxTemp,
                   IRExpr_Binop(Iop_CmpLT64U,
                                IRExpr_RdTmp(oldMax),
                                mkU64(st->Ist.WrTmp.tmp)));
    addStmtToIRSB(sbOut, checkGreater);
    IRTemp newMaxTemp = newIRTemp(sbOut->tyenv, Ity_I64);
    IRStmt* getNewMax =
      IRStmt_WrTmp(newMaxTemp,
                   IRExpr_ITE(IRExpr_RdTmp(greaterThanMaxTemp),
                              mkU64(st->Ist.WrTmp.tmp),
                              IRExpr_RdTmp(oldMax)));
    addStmtToIRSB(sbOut, getNewMax);

    addStore(sbOut,
             IRExpr_RdTmp(newMaxTemp),
             &maxTempInfluencesUsed);
    switch(expr->tag) {
    case Iex_Get:
      {
        IRTemp influence = newIRTemp(sbOut->tyenv, Ity_I64);
        IRStmt* clearInfluence =
          IRStmt_WrTmp(influence, mkU64(0));
        addStmtToIRSB(sbOut, clearInfluence);
        for (int i = 0; i < sizeOfIRType(expr->Iex.Get.ty); ++i){
          IRTemp influencePart = newIRTemp(sbOut->tyenv, Ity_I64);
          addLoad64(sbOut,
                    &(tsInfluences
                      [VG_(get_running_tid)()]
                      [expr->Iex.Get.offset + i]),
                    influencePart);
          IRTemp newInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
          IRStmt* unionInfluence =
            IRStmt_WrTmp(newInfluence,
                         IRExpr_Binop(Iop_Or64,
                                      IRExpr_RdTmp(influence),
                                      IRExpr_RdTmp(influencePart)));
          addStmtToIRSB(sbOut, unionInfluence);
          influence = newInfluence;
        }

        addStore(sbOut,
                 IRExpr_RdTmp(influence),
                 &(tempInfluences[st->Ist.WrTmp.tmp]));
        if (!isFloat(sbOut->tyenv, st->Ist.WrTmp.tmp)) break;
        ALLOC(cpinfo, "hg.copyShadowTStoTmpInfo.1", 1,
              sizeof(CpShadow_Info));
        cpinfo->instr_addr = stAddr;
        cpinfo->type = expr->Iex.Get.ty;
        cpinfo->src_idx = expr->Iex.Get.offset;
        cpinfo->dest_idx = st->Ist.WrTmp.tmp;
        copyShadowLocation =
          unsafeIRDirty_0_N(1,
                            "copyShadowTStoTmp",
                            VG_(fnptr_to_fnentry)(&copyShadowTStoTmp),
                            mkIRExprVec_1(mkU64((uintptr_t)cpinfo)));
        addStmtToIRSB(sbOut, IRStmt_Dirty(copyShadowLocation));
      }
      break;
    case Iex_GetI:
      {
        /* tl_assert(0); */
        IRExpr* indexExpr =
          // Calculate array_base + (ix + bias) %
          // array_len at run time. This will give us
          // the offset into the thread state at which
          // the actual get is happening, so we can
          // use that same offset for the shadow get.
          mkArrayLookupExpr(expr->Iex.GetI.descr->base,
                            expr->Iex.GetI.ix,
                            expr->Iex.GetI.bias,
                            expr->Iex.GetI.descr->nElems,
                            sbOut);
        IRTemp srcAddr = newIRTemp(sbOut->tyenv, Ity_I64);
        IRStmt* computeSrcAddr =
          IRStmt_WrTmp(srcAddr,
                       IRExpr_Binop(Iop_Add64,
                                    mkU64((uintptr_t)tsInfluences
                                          [VG_(get_running_tid)()]),
                                    indexExpr));
        addStmtToIRSB(sbOut, computeSrcAddr);
        IRTemp influence = newIRTemp(sbOut->tyenv, Ity_I64);
        addLoad64E(sbOut, IRExpr_RdTmp(srcAddr),
                   influence);
        addStore(sbOut,
                 IRExpr_RdTmp(influence),
                 &(tempInfluences[st->Ist.WrTmp.tmp]));
        if (!isFloat(sbOut->tyenv, st->Ist.WrTmp.tmp)) break;
        // See comments above on PutI to make sense of this thing.
        ALLOC(cpinfo, "hg.copyShadowTStoTmpInfo.1", 1,
              sizeof(CpShadow_Info));
        cpinfo->instr_addr = stAddr;
        cpinfo->type = expr->Iex.Get.ty;
        cpinfo->dest_idx = st->Ist.WrTmp.tmp;

        addStore(sbOut,
                 // Calculate array_base + (ix + bias) %
                 // array_len at run time. This will give us
                 // the offset into the thread state at which
                 // the actual get is happening, so we can
                 // use that same offset for the shadow get.
                 mkArrayLookupExpr(expr->Iex.GetI.descr->base,
                                   expr->Iex.GetI.ix,
                                   expr->Iex.GetI.bias,
                                   expr->Iex.GetI.descr->nElems,
                                   sbOut),
                 &(cpinfo->src_idx));
        copyShadowLocation =
          unsafeIRDirty_0_N(1,
                            "copyShadowTStoTmp",
                            VG_(fnptr_to_fnentry)(&copyShadowTStoTmp),
                            mkIRExprVec_1(mkU64((uintptr_t)cpinfo)));
        addStmtToIRSB(sbOut, IRStmt_Dirty(copyShadowLocation));
      }
      break;
    case Iex_RdTmp:
      {
        IRTemp influence = newIRTemp(sbOut->tyenv, Ity_I64);
        addLoad64(sbOut, &(tempInfluences[expr->Iex.RdTmp.tmp]),
                  influence);
        addStore(sbOut,
                 IRExpr_RdTmp(influence),
                 &(tempInfluences[st->Ist.WrTmp.tmp]));
        /* addRuntimeMaskCheck(sbOut, &(tempInfluences[expr->Iex.RdTmp.tmp]), */
        /*                     "TMP"); */
        if (!isFloat(sbOut->tyenv, st->Ist.WrTmp.tmp)) break;
        ALLOC(cpinfo, "hg.copyShadowTmptoTmpInfo.1", 1,
              sizeof(CpShadow_Info));
        cpinfo->instr_addr = stAddr;
        /* tl_assert(typeOfIRTemp(sbOut->tyenv, expr->Iex.RdTmp.tmp) == */
        /*           typeOfIRTemp(sbOut->tyenv, st->Ist.WrTmp.tmp)); */
        cpinfo->type = typeOfIRTemp(sbOut->tyenv, expr->Iex.RdTmp.tmp);
        cpinfo->src_idx = expr->Iex.RdTmp.tmp;
        cpinfo->dest_idx = st->Ist.WrTmp.tmp;
        copyShadowLocation =
          unsafeIRDirty_0_N(1,
                            "copyShadowTmptoTmp",
                            VG_(fnptr_to_fnentry)(&copyShadowTmptoTmp),
                            mkIRExprVec_1(mkU64((uintptr_t)cpinfo)));
        addStmtToIRSB(sbOut, IRStmt_Dirty(copyShadowLocation));
      }
      break;
    case Iex_ITE:
      {
        // When we have an ITE, we want to transfer across the shadow
        // value for one temp if the cond is true, and the other if
        // the cond is false. We do that by branching on the cond, and
        // assigning the temp number of the temp we want to transfer
        // from to condTmp. This means that condTmp is a temp that
        // stores a temp. Or, at least, a reference to one.
        IRTemp trueTemp, falseTemp;
        if (expr->Iex.ITE.iftrue->tag == Iex_Const){
          // We don't actually need to populate this temporary with
          // anything for now, because since it's coming from a const
          // it's not going to have a shadow value anyway, and ITE's
          // don't give their arguments shadow values.
          trueTemp = newIRTemp(sbOut->tyenv, Ity_I64);
        } else {
          trueTemp = expr->Iex.ITE.iftrue->Iex.RdTmp.tmp;
        }
        if (expr->Iex.ITE.iffalse->tag == Iex_Const){
          // We don't actually need to populate this temporary with
          // anything for now, because since it's coming from a const
          // it's not going to have a shadow value anyway, and ITE's
          // don't give their arguments shadow values.
          falseTemp = newIRTemp(sbOut->tyenv, Ity_I64);
        } else {
          falseTemp = expr->Iex.ITE.iffalse->Iex.RdTmp.tmp;
        }

        IRTemp condTmp = newIRTemp(sbOut->tyenv, Ity_I64);
        IRStmt* pickTmp = IRStmt_WrTmp(condTmp,
                                       IRExpr_ITE(expr->Iex.ITE.cond,
                                                  // The branches of
                                                  // the "if" should
                                                  // be temps, since
                                                  // the IR is
                                                  // flattened at
                                                  // instrumentation
                                                  // time. If they
                                                  // aren't, we're in
                                                  // trouble.
                                                  mkU64(trueTemp),
                                                  mkU64(falseTemp)));
        addStmtToIRSB(sbOut, pickTmp);

        IRTemp influenceAddr = newIRTemp(sbOut->tyenv, Ity_I64);
        IRStmt* getAddr =
          IRStmt_WrTmp(influenceAddr,
                       IRExpr_Binop(Iop_Add64,
                                    mkU64((uintptr_t)tempInfluences),
                                    IRExpr_RdTmp(condTmp)));
        addStmtToIRSB(sbOut, getAddr);
        IRTemp influence = newIRTemp(sbOut->tyenv, Ity_I64);
        addStmtToIRSB(sbOut,
                      IRStmt_WrTmp(influence,
                                   IRExpr_Load(ENDIAN,
                                               Ity_I64,
                                               IRExpr_RdTmp(influenceAddr))));
        addStore(sbOut,
                 IRExpr_RdTmp(influence),
                 &(tempInfluences[st->Ist.WrTmp.tmp]));
        if (!isFloat(sbOut->tyenv, st->Ist.WrTmp.tmp)) break;

        ALLOC(cpinfo, "hg.copyShadowTmptoTmpInfo.1", 1, sizeof(CpShadow_Info));
        cpinfo->instr_addr = stAddr;
        cpinfo->type = typeOfIRTemp(sbOut->tyenv, st->Ist.WrTmp.tmp);
        cpinfo->dest_idx = st->Ist.WrTmp.tmp;
        cpinfo->src_idx = 999999999999999;
        addStore(sbOut,
                 IRExpr_RdTmp(condTmp),
                 &(cpinfo->src_idx));
        // Once we have the temp we want to transfer from in condTmp,
        // we can call our shadow value transfering function for temps
        // like normal.
        copyShadowLocation =
          unsafeIRDirty_0_N(1,
                            "copyShadowTmptoTmp",
                            VG_(fnptr_to_fnentry)(&copyShadowTmptoTmp),
                            mkIRExprVec_1(mkU64((uintptr_t)cpinfo)));
        addStmtToIRSB(sbOut, IRStmt_Dirty(copyShadowLocation));
      }
      break;
    case Iex_Load:
      {
        IRDirty* cpInfluence =
          unsafeIRDirty_0_N(3,
                            "copyInfluenceFromMem",
                            VG_(fnptr_to_fnentry)(&copyInfluenceFromMem),
                            mkIRExprVec_3(expr->Iex.Load.addr,
                                          mkU64((uintptr_t)
                                                st->Ist.WrTmp.tmp),
                                          mkU64(sizeOfIRType(expr->Iex.Load.ty))));

        addStmtToIRSB(sbOut, IRStmt_Dirty(cpInfluence));
        if (isFloatType(expr->Iex.Load.ty)){
          ALLOC(cpinfo, "hg.copyShadowMemtoTmpInfo.1", 1, sizeof(CpShadow_Info));
          cpinfo->instr_addr = stAddr;
          cpinfo->type = expr->Iex.Load.ty;
          cpinfo->dest_idx = st->Ist.WrTmp.tmp;
          addStore(sbOut,
                   expr->Iex.Load.addr,
                   &(cpinfo->src_idx));
          copyShadowLocation =
            unsafeIRDirty_0_N(1,
                              "copyShadowMemtoTmp",
                              VG_(fnptr_to_fnentry)(&copyShadowMemtoTmp),
                              mkIRExprVec_1(mkU64((uintptr_t)cpinfo)));
          addStmtToIRSB(sbOut, IRStmt_Dirty(copyShadowLocation));
        }
      }
      break;
    case Iex_Qop:
    case Iex_Triop:
    case Iex_Binop:
    case Iex_Unop:
      switch(expr->tag){
      case Iex_Unop:
        {
          IRExpr* arg = expr->Iex.Unop.arg;
          if(arg->tag == Iex_RdTmp){
            IRTemp influence = newIRTemp(sbOut->tyenv, Ity_I64);
            addLoad64(sbOut,
                      &(tempInfluences[arg->Iex.RdTmp.tmp]),
                      influence);
            addStore(sbOut,
                     IRExpr_RdTmp(influence),
                     &(tempInfluences[st->Ist.WrTmp.tmp]));
          } else {
            addStore(sbOut,
                     mkU64(0),
                     &(tempInfluences[st->Ist.WrTmp.tmp]));
          }
        }
        break;
      case Iex_Binop:
        {
          IRExpr* arg1 = expr->Iex.Binop.arg1;
          IRExpr* arg2 = expr->Iex.Binop.arg2;

          IRTemp newInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
          addStmtToIRSB(sbOut,
                        IRStmt_WrTmp(newInfluence, mkU64(0)));

          if (arg1->tag == Iex_RdTmp){
            IRTemp arg1Influence = newIRTemp(sbOut->tyenv, Ity_I64);
            addLoad64(sbOut, &(tempInfluences[arg1->Iex.RdTmp.tmp]),
                      arg1Influence);
            IRTemp nextInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
            IRStmt* andArg1 =
              IRStmt_WrTmp(nextInfluence,
                           IRExpr_Binop(Iop_Or64,
                                        IRExpr_RdTmp(arg1Influence),
                                        IRExpr_RdTmp(newInfluence)));
            addStmtToIRSB(sbOut, andArg1);
            newInfluence = nextInfluence;
          }
          if (arg2->tag == Iex_RdTmp){
            IRTemp arg2Influence = newIRTemp(sbOut->tyenv, Ity_I64);
            addLoad64(sbOut, &(tempInfluences[arg2->Iex.RdTmp.tmp]),
                      arg2Influence);
            IRTemp nextInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
            IRStmt* andArg2 =
              IRStmt_WrTmp(nextInfluence,
                           IRExpr_Binop(Iop_Or64,
                                        IRExpr_RdTmp(arg2Influence),
                                        IRExpr_RdTmp(newInfluence)));
            addStmtToIRSB(sbOut, andArg2);
            newInfluence = nextInfluence;
          }
          addStore(sbOut,
                   IRExpr_RdTmp(newInfluence),
                   &(tempInfluences[st->Ist.WrTmp.tmp]));
        }
        break;
      case Iex_Triop:
        {
          IRExpr* arg1 = expr->Iex.Triop.details->arg1;
          IRExpr* arg2 = expr->Iex.Triop.details->arg2;
          IRExpr* arg3 = expr->Iex.Triop.details->arg3;

          IRTemp newInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
          addStmtToIRSB(sbOut,
                        IRStmt_WrTmp(newInfluence, mkU64(0)));

          if (arg1->tag == Iex_RdTmp){
            IRTemp arg1Influence = newIRTemp(sbOut->tyenv, Ity_I64);
            addLoad64(sbOut, &(tempInfluences[arg1->Iex.RdTmp.tmp]),
                      arg1Influence);
            IRTemp nextInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
            IRStmt* andArg1 =
              IRStmt_WrTmp(nextInfluence,
                           IRExpr_Binop(Iop_Or64,
                                        IRExpr_RdTmp(arg1Influence),
                                        IRExpr_RdTmp(newInfluence)));
            addStmtToIRSB(sbOut, andArg1);
            newInfluence = nextInfluence;
          }
          if (arg2->tag == Iex_RdTmp){
            IRTemp arg2Influence = newIRTemp(sbOut->tyenv, Ity_I64);
            addLoad64(sbOut, &(tempInfluences[arg2->Iex.RdTmp.tmp]),
                      arg2Influence);
            IRTemp nextInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
            IRStmt* andArg2 =
              IRStmt_WrTmp(nextInfluence,
                           IRExpr_Binop(Iop_Or64,
                                        IRExpr_RdTmp(arg2Influence),
                                        IRExpr_RdTmp(newInfluence)));
            addStmtToIRSB(sbOut, andArg2);
            newInfluence = nextInfluence;
          }
          if (arg3->tag == Iex_RdTmp){
            IRTemp arg3Influence = newIRTemp(sbOut->tyenv, Ity_I64);
            addLoad64(sbOut, &(tempInfluences[arg3->Iex.RdTmp.tmp]),
                      arg3Influence);
            IRTemp nextInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
            IRStmt* andArg3 =
              IRStmt_WrTmp(nextInfluence,
                           IRExpr_Binop(Iop_Or64,
                                        IRExpr_RdTmp(arg3Influence),
                                        IRExpr_RdTmp(newInfluence)));
            addStmtToIRSB(sbOut, andArg3);
            newInfluence = nextInfluence;
          }
          addStore(sbOut,
                   IRExpr_RdTmp(newInfluence),
                   &(tempInfluences[st->Ist.WrTmp.tmp]));
        }
        break;
      case Iex_Qop:
        {
          IRExpr* arg1 = expr->Iex.Qop.details->arg1;
          IRExpr* arg2 = expr->Iex.Qop.details->arg2;
          IRExpr* arg3 = expr->Iex.Qop.details->arg3;
          IRExpr* arg4 = expr->Iex.Qop.details->arg4;

          IRTemp newInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
          addStmtToIRSB(sbOut,
                        IRStmt_WrTmp(newInfluence, mkU64(0)));

          if (arg1->tag == Iex_RdTmp){
            IRTemp arg1Influence = newIRTemp(sbOut->tyenv, Ity_I64);
            addLoad64(sbOut, &(tempInfluences[arg1->Iex.RdTmp.tmp]),
                      arg1Influence);
            IRTemp nextInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
            IRStmt* andArg1 =
              IRStmt_WrTmp(nextInfluence,
                           IRExpr_Binop(Iop_Or64,
                                        IRExpr_RdTmp(arg1Influence),
                                        IRExpr_RdTmp(newInfluence)));
            addStmtToIRSB(sbOut, andArg1);
            newInfluence = nextInfluence;
          }
          if (arg2->tag == Iex_RdTmp){
            IRTemp arg2Influence = newIRTemp(sbOut->tyenv, Ity_I64);
            addLoad64(sbOut, &(tempInfluences[arg2->Iex.RdTmp.tmp]),
                      arg2Influence);
            IRTemp nextInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
            IRStmt* andArg2 =
              IRStmt_WrTmp(nextInfluence,
                           IRExpr_Binop(Iop_Or64,
                                        IRExpr_RdTmp(arg2Influence),
                                        IRExpr_RdTmp(newInfluence)));
            addStmtToIRSB(sbOut, andArg2);
            newInfluence = nextInfluence;
          }
          if (arg3->tag == Iex_RdTmp){
            IRTemp arg3Influence = newIRTemp(sbOut->tyenv, Ity_I64);
            addLoad64(sbOut, &(tempInfluences[arg3->Iex.RdTmp.tmp]),
                      arg3Influence);
            IRTemp nextInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
            IRStmt* andArg3 =
              IRStmt_WrTmp(nextInfluence,
                           IRExpr_Binop(Iop_Or64,
                                        IRExpr_RdTmp(arg3Influence),
                                        IRExpr_RdTmp(newInfluence)));
            addStmtToIRSB(sbOut, andArg3);
            newInfluence = nextInfluence;
          }
          if (arg4->tag == Iex_RdTmp){
            IRTemp arg4Influence = newIRTemp(sbOut->tyenv, Ity_I64);
            addLoad64(sbOut, &(tempInfluences[arg4->Iex.RdTmp.tmp]),
                      arg4Influence);
            IRTemp nextInfluence = newIRTemp(sbOut->tyenv, Ity_I64);
            IRStmt* andArg4 =
              IRStmt_WrTmp(nextInfluence,
                           IRExpr_Binop(Iop_Or64,
                                        IRExpr_RdTmp(arg4Influence),
                                        IRExpr_RdTmp(newInfluence)));
            addStmtToIRSB(sbOut, andArg4);
            newInfluence = nextInfluence;
          }
          addStore(sbOut,
                   IRExpr_RdTmp(newInfluence),
                   &(tempInfluences[st->Ist.WrTmp.tmp]));
        }
        break;
      default:
        tl_assert(0);
        return;
      }
      instrumentOp(sbOut, st->Ist.WrTmp.tmp, expr, stAddr, opNum);
      break;
      // We don't have to do anything for constants, since a
      // constant isn't considered a float yet.
    case Iex_Const:
      // There's really nothing we can do about opaque pure C calls,
      // so we'll skip them.
    case Iex_CCall:
      break;
    default:
      // This shouldn't happen in flattened IR.
      VG_(dmsg)("We don't recognize this expression! It's type is %s.\n", IRExprTagString(expr->tag));
      break;
    }
    break;
  case Ist_Store:
    // Here we'll instrument moving Shadow values into memory,
    // unconditionally.
    expr = st->Ist.Store.data;
    switch (expr->tag) {
    case Iex_RdTmp:
      {
        IRDirty* cpInfluence =
          unsafeIRDirty_0_N(3,
                            "copyInfluenceToMem",
                            VG_(fnptr_to_fnentry)(&copyInfluenceToMem),
                            mkIRExprVec_3(mkU64(expr->Iex.RdTmp.tmp),
                                          st->Ist.Store.addr,
                                          mkU64(sizeOfIRType(typeOfIRTemp(sbOut->tyenv,
                                                                          expr->Iex.RdTmp.tmp)))));
        addStmtToIRSB(sbOut, IRStmt_Dirty(cpInfluence));
        if (isFloat(sbOut->tyenv, expr->Iex.RdTmp.tmp)){
          ALLOC(cpinfo, "hg.copyShadowTmptoMemInfo.1", 1, sizeof(CpShadow_Info));
          cpinfo->src_idx = expr->Iex.RdTmp.tmp;
          cpinfo->instr_addr = stAddr;
          cpinfo->type = typeOfIRTemp(sbOut->tyenv, expr->Iex.RdTmp.tmp);

          addStore(sbOut,
                   st->Ist.Store.addr,
                   &(cpinfo->dest_idx));

          copyShadowLocation =
            unsafeIRDirty_0_N(1,
                              "copyShadowTmptoMem",
                              VG_(fnptr_to_fnentry)(&copyShadowTmptoMem),
                              mkIRExprVec_1(mkU64((uintptr_t)cpinfo)));
          addStmtToIRSB(sbOut, IRStmt_Dirty(copyShadowLocation));
        }
      }
      break;
    case Iex_Const:
      break;
    default:
      // This shouldn't happen in flattened IR.
      VG_(dmsg)("\
A non-constant or temp is being placed into memory in a single IR statement! \
That doesn't seem flattened...\n");
      break;
    }
    break;
  case Ist_StoreG:
    // Same as above, but only assigns the value to memory if a
    // guard returns true.
    expr = st->Ist.StoreG.details->data;
    switch(expr->tag) {
    case Iex_RdTmp:
      {
        CopyInfluenceInfo* info;
        ALLOC(info, "copy influence info", 1, sizeof(CopyInfluenceInfo));
        info->src = expr->Iex.RdTmp.tmp;
        info->size = sizeOfIRType(typeOfIRTemp(sbOut->tyenv,
                                               expr->Iex.RdTmp.tmp));
        addStore(sbOut, st->Ist.StoreG.details->addr, &(info->dest));
        IRDirty* cpInfluence =
          unsafeIRDirty_0_N(2,
                            "copyInfluenceToMemIf",
                            VG_(fnptr_to_fnentry)(&copyInfluenceToMemIf),
                            mkIRExprVec_2(mkU64((uintptr_t)info),
                                          st->Ist.StoreG.details->guard));
        addStmtToIRSB(sbOut, IRStmt_Dirty(cpInfluence));
        if (isFloat(sbOut->tyenv, expr->Iex.RdTmp.tmp)){
          ALLOC(cpinfo, "hg.copyShadowTmptoMemGInfo.1", 1, sizeof(CpShadow_Info));
          cpinfo->src_idx = expr->Iex.RdTmp.tmp;
          cpinfo->instr_addr = stAddr;
          cpinfo->type = typeOfIRTemp(sbOut->tyenv, expr->Iex.RdTmp.tmp);

          addStore(sbOut,
                   st->Ist.StoreG.details->addr,
                   &(cpinfo->dest_idx));

          copyShadowLocation =
            unsafeIRDirty_0_N(2,
                              "copyShadowTmptoMemG",
                              VG_(fnptr_to_fnentry)(&copyShadowTmptoMemG),
                              mkIRExprVec_2(st->Ist.StoreG.details->guard,
                                            mkU64((uintptr_t)cpinfo)));
          addStmtToIRSB(sbOut, IRStmt_Dirty(copyShadowLocation));
        }
      }
      break;
    case Iex_Const:
      break;
    default:
      // This shouldn't happen in flattened IR.
      VG_(dmsg)("\
A non-constant or temp is being placed into memory in a single IR statement! \
That doesn't seem flattened...\n");
      break;
    }
    break;
  case Ist_LoadG:
    // Guarded load. This will load a value from memory, and write
    // it to a temp, but only if a condition returns true.
    {
      CopyInfluenceInfo* info;
      ALLOC(info, "copy influence info", 1, sizeof(CopyInfluenceInfo));
      addStore(sbOut, st->Ist.LoadG.details->addr, &(info->src));
      info->size = sizeOfIRType(typeOfIRTemp(sbOut->tyenv,
                                             st->Ist.LoadG.details->dst));
      info->dest = st->Ist.LoadG.details->dst;
      IRDirty* cpInfluence =
        unsafeIRDirty_0_N(2,
                          "copyInfluenceFromMemIf",
                          VG_(fnptr_to_fnentry)(&copyInfluenceFromMemIf),
                          mkIRExprVec_2(mkU64((uintptr_t)info),
                                        st->Ist.LoadG.details->guard));
      addStmtToIRSB(sbOut, IRStmt_Dirty(cpInfluence));
    }
    if (isFloat(sbOut->tyenv, st->Ist.LoadG.details->dst)){
      ALLOC(loadGInfo, "hg.loadGmalloc.1", 1, sizeof(LoadG_Info));
      // These are the lines we'd like to write. Unfortunately, we
      // can't, because these values in theory are not known until the
      // block is run. So, we're going to do the same thing, but at
      // runtime, by inserting store instructions.

      /* loadGInfo->cond = st->Ist.LoadG.details->guard; */
      /* loadGInfo->src_mem = st->Ist.LoadG.details->addr; */
      /* loadGInfo->alt_tmp = st->Ist.LoadG.details->alt; */

      addStore(sbOut,
               st->Ist.LoadG.details->guard,
               &(loadGInfo->cond));
      addStore(sbOut,
               st->Ist.LoadG.details->addr,
               &(loadGInfo->src_mem));
      addStore(sbOut,
               st->Ist.LoadG.details->alt,
               &(loadGInfo->alt_tmp));

      loadGInfo->dest_tmp = st->Ist.LoadG.details->dst;
      loadGInfo->dest_type = typeOfIRTemp(sbOut->tyenv, st->Ist.LoadG.details->dst);

      copyShadowLocation =
        unsafeIRDirty_0_N(1,
                          "copyShadowMemtoTmpIf",
                          VG_(fnptr_to_fnentry)(&copyShadowMemtoTmpIf),
                          mkIRExprVec_1(mkU64((uintptr_t)loadGInfo)));
      addStmtToIRSB(sbOut, IRStmt_Dirty(copyShadowLocation));
    }
    break;
  case Ist_CAS:
    {
      /* tl_assert(st->Ist.CAS.details->expdHi == NULL); */
      IRDirty* copyOldInfluence =
        unsafeIRDirty_0_N(3,
                          "copyInfluenceFromMem",
                          VG_(fnptr_to_fnentry)(&copyInfluenceFromMem),
                          mkIRExprVec_3(st->Ist.CAS.details->addr,
                                        mkU64(st->Ist.CAS.details->oldLo),
                                        mkU64(sizeOfIRType(typeOfIRTemp(sbOut->tyenv,
                                                                        st->Ist.CAS.details->oldLo)))));
      addStmtToIRSB(sbOut, IRStmt_Dirty(copyOldInfluence));
      if (st->Ist.CAS.details->dataLo->tag == Iex_RdTmp){
        IROp compare;
        switch(typeOfIRTemp(sbOut->tyenv,
                            st->Ist.CAS.details->oldLo)){
        case Ity_I8:
          compare = Iop_CasCmpEQ8;
          break;
        case Ity_I16:
          compare = Iop_CasCmpEQ16;
          break;
        case Ity_I32:
          compare = Iop_CasCmpEQ32;
          break;
        case Ity_I64:
          compare = Iop_CasCmpEQ64;
          break;
        default:
          compare = Iop_INVALID;
          tl_assert(0);
          return;
        }
        IRTemp succeeded = newIRTemp(sbOut->tyenv, Ity_I1);
        IRStmt* checkSucceeded =
          IRStmt_WrTmp(succeeded,
                       IRExpr_Binop(compare,
                                    st->Ist.CAS.details->expdLo,
                                    IRExpr_RdTmp(st->Ist.CAS.details->oldLo)));
        addStmtToIRSB(sbOut, checkSucceeded);
        IRTemp succeededWord = newIRTemp(sbOut->tyenv, Ity_I64);
        IRStmt* convertSucceeded =
          IRStmt_WrTmp(succeededWord,
                       IRExpr_Unop(Iop_1Uto64, IRExpr_RdTmp(succeeded)));
        addStmtToIRSB(sbOut, convertSucceeded);
        CopyInfluenceInfo* info;
        ALLOC(info, "copy influence info", 1, sizeof(CopyInfluenceInfo));
        info->src = st->Ist.CAS.details->dataLo->Iex.RdTmp.tmp;
        info->size = sizeOfIRType(typeOfIRTemp(sbOut->tyenv,
                                               st->Ist.CAS.details->dataLo->Iex.RdTmp.tmp));
        addStore(sbOut, st->Ist.CAS.details->addr, &(info->dest));
        IRDirty* copyInfluenceIfSucceeded =
          unsafeIRDirty_0_N(2,
                            "copyInfluenceToMemIf",
                            VG_(fnptr_to_fnentry)(&copyInfluenceToMemIf),
                            mkIRExprVec_2(mkU64((uintptr_t)info),
                                          IRExpr_RdTmp(succeededWord)));
        addStmtToIRSB(sbOut, IRStmt_Dirty(copyInfluenceIfSucceeded));
      }
    }
    // This is an atomic compare and swap operation. Basically, has
    // three parts: a destination, a value address, an expected
    // value, and a result value. If the value at the value address
    // is equal to the expected value, then the result value is
    // stored in the destination temp.
    break;
  case Ist_LLSC:
    // I honestly have no goddamn idea what this does. See: libvex_ir.h:2816

    // TODO: Add something here if we ever want to support multithreading.

    VG_(dmsg)("\
Warning! Herbgrind does not currently support the Load Linked / Store Conditional \
set of instructions, because we don't support multithreaded programs.\n");
    break;
  case Ist_Dirty:
    // Call a C function, possibly with side affects. The possible
    // side effects should be denoted in the attributes of this
    // instruction.
    break;
  }
}

// Produce an expression to calculate (base + ((idx + bias) % len)),
// where base, bias, and len are fixed, and idx can vary at runtime.
// The type of the resulting expression is Ity_I32.
IRExpr* mkArrayLookupExpr(Int base, IRExpr* idx, Int bias, Int len, IRSB* sbOut){
  // Set op the temps to hold all the different intermediary values.
  IRTemp idxPLUSbias = newIRTemp(sbOut->tyenv, Ity_I32);
  IRTemp idxPLUSbias64 = newIRTemp(sbOut->tyenv, Ity_I64);
  IRTemp idxPLUSbiasDIVMODlen = newIRTemp(sbOut->tyenv, Ity_I64);
  IRTemp idxPLUSbiasMODlen = newIRTemp(sbOut->tyenv, Ity_I32);
  IRTemp idxPLUSbiasMODlenPLUSbase = newIRTemp(sbOut->tyenv, Ity_I32);
  IRTemp resultWidened = newIRTemp(sbOut->tyenv, Ity_I64);

  // idx + bias
  addStmtToIRSB(sbOut,
                IRStmt_WrTmp(idxPLUSbias,
                             IRExpr_Binop(Iop_Add32,
                                          idx,
                                          mkU32(bias))));
  // We need to convert to 64 bits so we can do the mod.
  addStmtToIRSB(sbOut,
                IRStmt_WrTmp(idxPLUSbias64,
                             IRExpr_Unop(Iop_32Uto64,
                                         IRExpr_RdTmp(idxPLUSbias))));
  // These two operations together are mod.
  // (idx + bias) % len
  addStmtToIRSB(sbOut,
                IRStmt_WrTmp(idxPLUSbiasDIVMODlen,
                             IRExpr_Binop(Iop_DivModU64to32,
                                          IRExpr_RdTmp(idxPLUSbias64),
                                          mkU32(len))));
  addStmtToIRSB(sbOut,
                IRStmt_WrTmp(idxPLUSbiasMODlen,
                             IRExpr_Unop(Iop_64HIto32,
                                         IRExpr_RdTmp(idxPLUSbiasDIVMODlen))));
  // base + ((idx + bias) % len)
  addStmtToIRSB(sbOut,
                IRStmt_WrTmp(idxPLUSbiasMODlenPLUSbase,
                             IRExpr_Binop(Iop_Add32,
                                          IRExpr_RdTmp(idxPLUSbiasMODlen),
                                          mkU32(base))));
  // Finally, widen the result.
  addStmtToIRSB(sbOut,
                IRStmt_WrTmp(resultWidened,
                             IRExpr_Unop(Iop_32Uto64,
                                          IRExpr_RdTmp(idxPLUSbiasMODlenPLUSbase))));

  return IRExpr_RdTmp(resultWidened);
}

void startBlock(IRSB* sbOut){
  IRDirty* initBlockCall =
    unsafeIRDirty_0_N(0, "initBlock", VG_(fnptr_to_fnentry)(&initBlock), mkIRExprVec_0());
  addStmtToIRSB(sbOut, IRStmt_Dirty(initBlockCall));
}

void finalizeBlock(IRSB* sbOut){

  // Finalize the block
  IRDirty* cleanupTemps =
    unsafeIRDirty_0_N(0, "cleanupBlock", VG_(fnptr_to_fnentry)(&cleanupBlock), mkIRExprVec_0());
  addStmtToIRSB(sbOut, IRStmt_Dirty(cleanupTemps));  
}

// A bit misleading of a name, but returns whether the temp COULD
// contain a float that we care about. It might also contain a
// vectorized integer thing.
int isFloat(IRTypeEnv* env, IRTemp temp){
  IRType type = typeOfIRTemp(env, temp);
  return isFloatType(type);
}
int isFloatType(IRType type){
  return type == Ity_F32 || type == Ity_F64
    || type == Ity_V128 || type == Ity_I32
    || type == Ity_I64;
}
Bool isOp(IRStmt* st){
  switch(st->tag){
  case Ist_WrTmp:
    switch(st->Ist.WrTmp.data->tag){
    case Iex_Qop:
    case Iex_Triop:
    case Iex_Binop:
    case Iex_Unop:
      return True;
    default:
      return False;
    }
  default:
    return False;
  }
}

int sizeOfIRType(IRType type){
  switch(type){
  case Ity_INVALID:
  case Ity_I1:
  case Ity_I8:
    return 1;
  case Ity_I16:
  case Ity_F16:   /* 16 bit float */
    return 2;
  case Ity_I32:
  case Ity_F32:   /* IEEE 754 float */
  case Ity_D32:   /* 32-bit Decimal floating point */
    return 3;
  case Ity_I64:
  case Ity_F64:   /* IEEE 754 double */
  case Ity_D64:   /* 64-bit Decimal floating point */
    return 4;
  case Ity_I128:  /* 128-bit scalar */
  case Ity_D128:  /* 128-bit Decimal floating point */
  case Ity_F128:  /* 128-bit floating point; implementation defined */
  case Ity_V128:  /* 128-bit SIMD */
    return 8;
  case Ity_V256:   /* 256-bit SIMD */
    return 16;
  default:
    tl_assert(0);
    return 0;
  }
}
void init_instrumentation(){
  opinfo_store = VG_(HT_construct)("opinfo store");
}
