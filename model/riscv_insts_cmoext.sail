/* ****************************************************************** */
/* This file specifies the instructions in the cmo extension */


/* ****************************************************************** */
union clause ast = RISCV_CBO : (cbop, regidx)

mapping encdec_cbop : cbop <-> bits(12) = {
  CBO_CLEAN <-> 0b000000000001,
  CBO_FLUSH <-> 0b000000000010,
  CBO_INVAL <-> 0b000000000000,
  CBO_ZERO  <-> 0b000000000100
}

mapping clause encdec = RISCV_CBO(cbop, rs1)
  <-> encdec_cbop(cbop) @ rs1 @ 0b010 @ 0b00000 @ 0b0001111

mapping cbo_mnemonic : cbop <-> string = {
  CBO_CLEAN <-> "cbo.clean",
  CBO_FLUSH <-> "cbo.flush",
  CBO_INVAL <-> "cbo.inval",
  CBO_ZERO  <-> "cbo.zero"
}

mapping clause assembly = RISCV_CBO(cbop, rs1)
  <-> cbo_mnemonic(cbop) ^ spc() ^ reg_name(rs1)

val write_zero: (xlenbits, xlenbits) -> MemoryOpResult(bool) effect {wmv, wmvt, rreg, wreg, escape}
function write_zero(paddr, width) = {
  let res : MemoryOpResult(bool) = mem_write_value(paddr, 8, to_bits(64, 0), false, false, false);
  match (res) {
    MemValue(true)  => {
      if(unsigned(width) > 8) then
        write_zero(paddr + 8, width - 8)
      else
        MemValue(true)
    },
    MemValue(false) => MemValue(false),
    MemException(e) => MemException(e)
  }
}

val process_cbo_zero : (xlenbits, xlenbits) -> Retired effect {eamem, escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function process_cbo_zero(vaddr, width)  = {
  match ext_data_get_addr(to_bits(5, 0), vaddr, Write(Data), BYTE) {
    Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); RETIRE_FAIL },
    Ext_DataAddr_OK(vaddr) =>
      match translateAddr(vaddr, Write(Data)) {
        TR_Failure(e, _)    => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
        TR_Address(paddr, _) => {
          let eares : MemoryOpResult(unit) = mem_write_ea(paddr, 1, false, false, false);
          match (eares) {
            MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
            MemValue(_) => {
              let res : MemoryOpResult(bool) = write_zero(paddr, width);
              match (res) {
                MemValue(true)  => RETIRE_SUCCESS,
                MemValue(false) => internal_error("store got false from mem_write_value"),
                MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL }
              }
            }
          }
        }
      }
  }
}

union translation_check = {
  TransTrap : ExceptionType,
  TransSuccess : unit
}

val process_clean_inval : (xlenbits, xlenbits, bool, bool) -> Retired effect {escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function process_clean_inval(vaddr, width, clean, inval) = {
  let load: translation_check = match ext_data_get_addr(to_bits(5, 0), vaddr, Read(Data), BYTE) {
    Ext_DataAddr_Error(e)  => TransTrap(E_Reserved_14()),
    Ext_DataAddr_OK(vaddr) =>
      match translateAddr(vaddr, Read(Data)) {
        TR_Failure(e, _)    => TransTrap(e),
        TR_Address(paddr, _) => TransSuccess()
      }
  };
  match load {
    TransSuccess() => RETIRE_SUCCESS,
    TransTrap(le) => {
      let store: translation_check = match ext_data_get_addr(to_bits(5, 0), vaddr, Write(Data), BYTE) {
        Ext_DataAddr_Error(e)  => TransTrap(E_Reserved_14()),
        Ext_DataAddr_OK(vaddr) =>
          match translateAddr(vaddr, Write(Data)) {
            TR_Failure(e, _)    => TransTrap(e),
            TR_Address(paddr, _) => TransSuccess()
          }
      };
      match store {
        TransSuccess() => RETIRE_SUCCESS,
        TransTrap(se) => {
          let fetch: translation_check = match ext_control_check_addr(vaddr) {
            Ext_ControlAddr_Error(e)  => TransTrap(E_Reserved_14()),
            Ext_ControlAddr_OK(vaddr) =>
              match translateAddr(vaddr, Execute()) {
                TR_Failure(e, _)    => TransTrap(e),
                TR_Address(paddr, _) => TransSuccess()
              }
          };
          match fetch {
            TransSuccess() => RETIRE_SUCCESS,
            TransTrap(fe) =>
              match (le, se, fe) {
                (E_Load_Access_Fault(), _, _) => { handle_mem_exception(vaddr, E_SAMO_Access_Fault()); RETIRE_FAIL },
                (_, E_SAMO_Access_Fault(), _) => { handle_mem_exception(vaddr, E_SAMO_Access_Fault()); RETIRE_FAIL },
                (_, _, E_Fetch_Access_Fault()) => { handle_mem_exception(vaddr, E_SAMO_Access_Fault()); RETIRE_FAIL },
                (E_Load_Page_Fault(), _, _) => { handle_mem_exception(vaddr, E_SAMO_Page_Fault()); RETIRE_FAIL },
                (_, E_SAMO_Page_Fault(), _) => { handle_mem_exception(vaddr, E_SAMO_Page_Fault()); RETIRE_FAIL },
                (_, _, E_Fetch_Page_Fault()) => { handle_mem_exception(vaddr, E_SAMO_Page_Fault()); RETIRE_FAIL },
                (E_Extension(e), _ , _ ) => { ext_handle_data_check_error(e); RETIRE_FAIL }
              }
          }
        }
      }
    }
  }
}

function check_clean_flush(p : Privilege) -> bool = {
  let ret : bool = ~(((p != Machine) & (menvcfg.CBCFE() == 0b0)) |
                    ((p == User) & (senvcfg.CBCFE() == 0b0)));
  ret
}

function check_inval(p : Privilege) -> bits(2) = {
  let bit0 : bool = ((p != Machine) & (menvcfg.CBIE() == 0b00)) |
                    ((p == User) & (senvcfg.CBIE() == 0b00));
  let bit1 : bool = ((p != Machine) & (menvcfg.CBIE() == 0b01)) |
                    ((p == User) & (senvcfg.CBIE() == 0b01));
  if bit0 then EXTZ(0b0)
  else if bit1 then EXTZ(0b1)
  else EXTZ(0b11)
}

function check_zero(p : Privilege) -> bool = {
  let ret : bool = ~(((p != Machine) & (menvcfg.CBZE() == 0b0)) |
                    ((p == User) & (senvcfg.CBZE() == 0b0)));
  ret
}

function clause execute(RISCV_CBO(cbop, rs1)) = {
  let rs1_val = X(rs1);
  let cache_block_size : xlenbits = plat_cache_block_size() ;
  let vaddr: xlenbits = rs1_val & ~(cache_block_size - EXTZ(0b1));
  match cbop {
    CBO_CLEAN => {
      if (check_clean_flush(cur_privilege)) then
        /* perform clean*/
        process_clean_inval(vaddr, cache_block_size, true, false)
      else {
        handle_illegal();
        RETIRE_FAIL
      }
    },
    CBO_FLUSH => {
      if (check_clean_flush(cur_privilege)) then
        /* perform flush*/
        process_clean_inval(vaddr, cache_block_size, true, true)
      else {
        handle_illegal();
        RETIRE_FAIL
      }
    },
    CBO_INVAL => {
      match (check_inval(cur_privilege)) {
        0b00 => {
          handle_illegal();
          RETIRE_FAIL
          },
        0b01 => process_clean_inval(vaddr, cache_block_size, true, true),  /*perform flush*/
        0b10 => process_clean_inval(vaddr, cache_block_size, false, true) /*perform inval*/
      }
    },
    CBO_ZERO  => {
      if (check_zero(cur_privilege)) then
        process_cbo_zero(vaddr, cache_block_size)
      else {
        handle_illegal();
        RETIRE_FAIL
      }
    }
  }
}

union clause ast = RISCV_PREFETCH : (preop, regidx, bits(7))

mapping encdec_prefetch : preop <-> bits(5) = {
  PREFETCH_I <-> 0b00000,
  PREFETCH_R <-> 0b00001,
  PREFETCH_W <-> 0b00011
}

mapping clause encdec = RISCV_PREFETCH(op, rs1, offset)
  <-> offset @ encdec_prefetch(op) @ rs1 @ 0b110 @ 0b00000 @ 0b0010011

mapping pre_mnemonic : preop <-> string = {
  PREFETCH_I <-> "prefetch.i",
  PREFETCH_R <-> "prefetch.r",
  PREFETCH_W <-> "prefetch.w"
}

mapping clause assembly = RISCV_PREFETCH(op, rs1, offset)
  <-> pre_mnemonic(op) ^ spc() ^ hex_bits_12(offset @ 0b00000) ^ "(" ^ reg_name(rs1) ^ ")"

function clause execute(RISCV_PREFETCH(preop, rs1, offset)) = {
  /* do nothing other than translate_address for prefetch.i/r/w */
  match preop {
    PREFETCH_I => {
      let vaddr = X(rs1) + EXTS(offset @ 0b00000);
      match ext_control_check_addr(vaddr) {
        Ext_ControlAddr_Error(e)  => RETIRE_SUCCESS,
          Ext_ControlAddr_OK(vaddr) =>
            match translateAddr(vaddr, Execute()) {
              TR_Failure(e, _)    => RETIRE_SUCCESS,
              TR_Address(paddr, _) => RETIRE_SUCCESS
            }
      }
    },
    PREFETCH_W => {
      match ext_data_get_addr(rs1, EXTS(offset @ 0b00000), Write(Data), BYTE) {
        Ext_DataAddr_Error(e)  => RETIRE_SUCCESS,
        Ext_DataAddr_OK(vaddr) =>
          match translateAddr(vaddr, Write(Data)) {
            TR_Failure(e, _)     => RETIRE_SUCCESS,
            TR_Address(paddr, _) => RETIRE_SUCCESS
          }
      }
    },
    PREFETCH_R => {
      match ext_data_get_addr(rs1, EXTS(offset @ 0b00000), Read(Data), BYTE) {
        Ext_DataAddr_Error(e)  => RETIRE_SUCCESS,
        Ext_DataAddr_OK(vaddr) =>
          match translateAddr(vaddr, Read(Data)) {
            TR_Failure(e, _)     => RETIRE_SUCCESS,
            TR_Address(paddr, _) => RETIRE_SUCCESS
          }
      }
    }
  }
}