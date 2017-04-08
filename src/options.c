/*--------------------------------------------------------------------*/
/*--- Herbgrind: a valgrind tool for Herbie              options.c ---*/
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

#include "options.h"

#include "pub_tool_options.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcprint.h"

#include "mpfr.h"

Bool print_in_blocks = False;
Bool print_out_blocks = False;
Bool print_block_boundries = False;
Bool print_run_blocks = False;
Bool print_temp_moves = False;
Bool print_value_moves = False;
Bool print_semantic_ops = False;
Bool print_conversions = False;
Bool print_types = False;
Bool print_allocs = False;
Bool print_errors = False;
Bool print_errors_long = False;
Bool print_expr_updates = False;
Bool print_object_files = False;
Bool running = True;
Bool always_on = False;
Bool output_sexp = False;
Bool print_flagged = False;
Int longprint_len = 15;
Int precision = 1000;
double error_threshold = 5.0;
const char* output_filename = NULL;

// Called to process each command line option.
Bool hg_process_cmd_line_option(const HChar* arg){
  if VG_XACT_CLO(arg, "--print-in-blocks", print_in_blocks, True) {}
  else if VG_XACT_CLO(arg, "--print-out-blocks", print_out_blocks, True) {}
  else if VG_XACT_CLO(arg, "--print-block-boundries", print_block_boundries, True) {}
  else if VG_XACT_CLO(arg, "--print-run-blocks", print_run_blocks, True) {}
  else if VG_XACT_CLO(arg, "--print-temp-moves", print_temp_moves, True) {}
  else if VG_XACT_CLO(arg, "--print-value-moves", print_value_moves, True) {}
  else if VG_XACT_CLO(arg, "--print-semantic-ops", print_semantic_ops, True) {}
  else if VG_XACT_CLO(arg, "--print-conversions", print_conversions, True) {}
  else if VG_XACT_CLO(arg, "--print-types", print_types, True) {}
  else if VG_XACT_CLO(arg, "--print-allocs", print_allocs, True) {}
  else if VG_XACT_CLO(arg, "--print-errors", print_errors, True) {}
  else if VG_XACT_CLO(arg, "--print-errors-long", print_errors_long, True) {}
  else if VG_XACT_CLO(arg, "--print-expr-updates", print_expr_updates, True) {}
  else if VG_XACT_CLO(arg, "--print-object-files", print_object_files, True) {}
  else if VG_XACT_CLO(arg, "--start-off", running, False) {}
  else if VG_XACT_CLO(arg, "--always-on", always_on, True) {}
  else if VG_XACT_CLO(arg, "--output-sexp", output_sexp, True) {}
  else if VG_XACT_CLO(arg, "--print-flagged", print_flagged, True) {}
  else if VG_BINT_CLO(arg, "--longprint-len", longprint_len, 1, 1000) {}
  else if VG_BINT_CLO(arg, "--precision", precision, MPFR_PREC_MIN, MPFR_PREC_MAX){}
  else if VG_DBL_CLO(arg, "--error-threshold", error_threshold) {}
  else if VG_STR_CLO(arg, "--outfile", output_filename) {}
  else return False;
  return True;
}

void hg_print_usage(void){
  VG_(printf)("    --precision=value    "
              "Sets the mantissa size of the shadow \"real\" values. [1000]\n"
              "    --error-threshold=bits    "
              "The number of bits of error at which to start "
              "tracking a computation. [5.0]\n"
              "    --outfile=name    "
              "The name of the file to write out. If no name is "
              "specified, will use <executable-name>.gh.\n"
              "    --output-sexp    "
              "Output in an easy-to-parse s-expression based format.\n"
              );
}
void hg_print_debug_usage(void){
  VG_(printf)(" --print-in-blocks "
              "Prints the VEX superblocks that Herbgrind receives "
              "from Valgrind.\n"
              " --print-out-blocks "
              "Prints the instrumented VEX superblocks that Herbgrind "
              "returns to Valgrind.\n"
              " --print-block-boundries "
              "Prints +++++ between each executed block.\n"
              " --print-run-blocks"
              "Prints the addresses of each run block.\n"
              " --print-temp-moves "
              "Prints each shadow temp movement.\n"
              " --print-value-moves "
              "Prints each shadow value movement.\n"
              " --print-semantic-ops "
              "Prints each semantic op executed\n"
              " --print-conversions "
              "Prints each conversion op executed\n"
              " --print-types "
              "Prints some type inferences\n"
              " --print-allocs "
              "Prints for each major allocation.\n"
              " --print-errors "
              "Prints the error of the result of each operation.\n"
              " --print-errors-long "
              "Prints the error of the result of each operation, "
              "with long mpfr values.\n"
              " --print-expr-updates "
              "Prints the expressions that are derived for each "
              "operation.\n"
              " --print-object-files "
              "Prints the object name everywhere binary addresses are printed.\n"
              " --start-off "
              "Start's the analysis with the running flag set to off\n"
              " --always-on "
              "Ignore calls to HERBGRIND_END()\n"
              " --longprint-len=length "
              "How many digits of long real values to print.\n"
              " --print-flagged"
              "Print every operation that is flagged.\n");
}
