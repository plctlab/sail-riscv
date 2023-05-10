/*=======================================================================================*/
/*  RISCV Sail Model                                                                     */
/*                                                                                       */
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except for the snapshots of the Lem and Sail libraries                   */
/*  in the prover_snapshots directory (which include copies of their                     */
/*  licences), is subject to the BSD two-clause licence below.                           */
/*                                                                                       */
/*  Copyright (c) 2017-2021                                                              */
/*    Prashanth Mundkur                                                                  */
/*    Rishiyur S. Nikhil and Bluespec, Inc.                                              */
/*    Jon French                                                                         */
/*    Brian Campbell                                                                     */
/*    Robert Norton-Wright                                                               */
/*    Alasdair Armstrong                                                                 */
/*    Thomas Bauereiss                                                                   */
/*    Shaked Flur                                                                        */
/*    Christopher Pulte                                                                  */
/*    Peter Sewell                                                                       */
/*    Alexander Richardson                                                               */
/*    Hesham Almatary                                                                    */
/*    Jessica Clarke                                                                     */
/*    Microsoft, for contributions by Robert Norton-Wright and Nathaniel Wesley Filardo  */
/*    Peter Rugg                                                                         */
/*    Aril Computer Corp., for contributions by Scott Johnson                            */
/*                                                                                       */
/*  All rights reserved.                                                                 */
/*                                                                                       */
/*  This software was developed by the above within the Rigorous                         */
/*  Engineering of Mainstream Systems (REMS) project, partly funded by                   */
/*  EPSRC grant EP/K008528/1, at the Universities of Cambridge and                       */
/*  Edinburgh.                                                                           */
/*                                                                                       */
/*  This software was developed by SRI International and the University of               */
/*  Cambridge Computer Laboratory (Department of Computer Science and                    */
/*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and                 */
/*  under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA                 */
/*  SSITH research programme.                                                            */
/*                                                                                       */
/*  This project has received funding from the European Research Council                 */
/*  (ERC) under the European Union’s Horizon 2020 research and innovation                */
/*  programme (grant agreement 789108, ELVER).                                           */
/*                                                                                       */
/*                                                                                       */
/*  Redistribution and use in source and binary forms, with or without                   */
/*  modification, are permitted provided that the following conditions                   */
/*  are met:                                                                             */
/*  1. Redistributions of source code must retain the above copyright                    */
/*     notice, this list of conditions and the following disclaimer.                     */
/*  2. Redistributions in binary form must reproduce the above copyright                 */
/*     notice, this list of conditions and the following disclaimer in                   */
/*     the documentation and/or other materials provided with the                        */
/*     distribution.                                                                     */
/*                                                                                       */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''                   */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED                    */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A                      */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR                  */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,                         */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT                     */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF                     */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND                  */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,                   */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT                   */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF                   */
/*  SUCH DAMAGE.                                                                         */
/*=======================================================================================*/

/* **************************************************************** */
/* This file specifies the instructions in the Zfbfmin extension    */

/* RISC-V follows IEEE 754-2008 floating point arithmetic standard. */

/* **************************************************************** */

/* **************************************************************** */
/* Helper functions for 'encdec()'                                  */

function haveBF16FPU() -> bool = haveZfbfmin() | haveZfbfinxmin()

/* AST */

union clause ast = F_UN_RM_TYPE_BF16 : (regidx, rounding_mode, regidx, f_un_rm_op_BF16)

/* AST <-> Binary encoding ================================ */

mapping clause encdec =
    F_UN_RM_TYPE_BF16(rs1, rm, rd, FCVT_BF16_S)                               if haveBF16FPU()
<-> 0b010_0010 @ 0b01000 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveBF16FPU()

mapping clause encdec =
    F_UN_RM_TYPE_BF16(rs1, rm, rd, FCVT_S_BF16)                               if haveBF16FPU()
<-> 0b010_0000 @ 0b00110 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveBF16FPU()

/* Execution semantics ================================ */

function clause execute (F_UN_RM_TYPE_BF16(rs1, rm, rd, FCVT_BF16_S)) = {
  let rs1_val_S = F_or_X_S(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_H) = riscv_f32ToBF16 (rm_3b, rs1_val_S);

      write_fflags(fflags);
      F_or_X_BF16(rd) = rd_val_H;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_BF16(rs1, rm, rd, FCVT_S_BF16)) = {
  let rs1_val_H = F_or_X_BF16(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_S) = riscv_bf16ToF32 (rm_3b, rs1_val_H);

      write_fflags(fflags);
      F_or_X_S(rd) = rd_val_S;
      RETIRE_SUCCESS
    }
  }
}

/* AST -> Assembly notation ================================ */

mapping f_un_rm_type_mnemonic_BF16 : f_un_rm_op_BF16 <-> string = {
    FCVT_BF16_S  <-> "fcvt.bf16.s",
    FCVT_S_BF16  <-> "fcvt.s.bf16",
}

mapping clause assembly = F_UN_RM_TYPE_BF16(rs1, rm, rd, FCVT_BF16_S)
                      <-> f_un_rm_type_mnemonic_BF16(FCVT_BF16_S)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_BF16(rs1, rm, rd, FCVT_S_BF16)
                      <-> f_un_rm_type_mnemonic_BF16(FCVT_S_BF16)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)
                          