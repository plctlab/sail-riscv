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

/* Definitions for floating point registers (F and D extensions) */

/* default register type */
type fregtype = flenbits

/* default zero register */
let zero_freg : fregtype = EXTZ(0x0)

/* default register printer */
val FRegStr : fregtype -> string
function FRegStr(r) = BitStr(r)

/* conversions */

val fregval_from_freg : fregtype -> flenbits
function fregval_from_freg(r) = r

val fregval_into_freg : flenbits -> fregtype
function fregval_into_freg(v) = v


/* Rounding Mode
    Rounding modes occur as a 3-bit field in F,D instructions,
    and also as a 3-bit 'frm' field in the 'fcsr' CSR.
    RISC-V uses the following IEEE-defined rounding modes.
*/

enum rounding_mode = {RM_RNE, RM_RTZ, RM_RDN, RM_RUP, RM_RMM, RM_DYN}

enum f_madd_op_S = {FMADD_S, FMSUB_S, FNMSUB_S, FNMADD_S}

enum f_bin_rm_op_S = {FADD_S, FSUB_S, FMUL_S, FDIV_S}

enum f_un_rm_op_S = {FSQRT_S, FCVT_W_S, FCVT_WU_S, FCVT_S_W, FCVT_S_WU,    // RV32 and RV64
                     FCVT_L_S, FCVT_LU_S, FCVT_S_L, FCVT_S_LU}             // RV64 only

enum f_un_op_S = {FCLASS_S, FMV_X_W, FMV_W_X}    /* RV32 and RV64 */

enum f_bin_op_S = {FSGNJ_S, FSGNJN_S, FSGNJX_S, FMIN_S, FMAX_S, FEQ_S, FLT_S, FLE_S}

enum f_madd_op_D = {FMADD_D, FMSUB_D, FNMSUB_D, FNMADD_D}

enum f_bin_rm_op_D = {FADD_D, FSUB_D, FMUL_D, FDIV_D}

enum f_un_rm_op_D = {FSQRT_D, FCVT_W_D, FCVT_WU_D, FCVT_D_W, FCVT_D_WU,    // RV32 and RV64
                     FCVT_S_D, FCVT_D_S,
                     FCVT_L_D, FCVT_LU_D, FCVT_D_L, FCVT_D_LU}             // RV64 only

enum f_bin_op_D = {FSGNJ_D, FSGNJN_D, FSGNJX_D, FMIN_D, FMAX_D, FEQ_D, FLT_D, FLE_D}

enum f_un_op_D = {FCLASS_D,            /* RV32 and RV64 */
                  FMV_X_D, FMV_D_X}    /* RV64 only */
