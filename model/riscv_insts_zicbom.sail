/* ****************************************************************** */
/* This file specifies the instructions in the Zicbom extension */


/* ****************************************************************** */
union clause ast = RISCV_ZICBOM : (cbop_zicbom, regidx)

mapping encdec_cbop : cbop_zicbom <-> bits(12) = {
  CBO_CLEAN <-> 0b000000000001,
  CBO_FLUSH <-> 0b000000000010,
  CBO_INVAL <-> 0b000000000000
}

mapping clause encdec = RISCV_ZICBOM(cbop, rs1) if haveZicbom()
  <-> encdec_cbop(cbop) @ rs1 @ 0b010 @ 0b00000 @ 0b0001111 if haveZicbom()

mapping cbop_mnemonic : cbop_zicbom <-> string = {
  CBO_CLEAN <-> "cbo.clean",
  CBO_FLUSH <-> "cbo.flush",
  CBO_INVAL <-> "cbo.inval"
}

mapping clause assembly = RISCV_ZICBOM(cbop, rs1)
  <-> cbop_mnemonic(cbop) ^ spc() ^ reg_name(rs1)

val process_clean_inval : (xlenbits, xlenbits, bool, bool) -> Retired effect {escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function process_clean_inval(vaddr, width, clean, inval) = {
  match ext_data_get_addr(zeros(), vaddr, Read(Data), BYTE) {
    Ext_DataAddr_Error(e) => { ext_handle_data_check_error(e); RETIRE_FAIL },
    Ext_DataAddr_OK(vaddr) => {
      let data: option(ExceptionType) = match translateAddr(vaddr, Read(Data)) {
        TR_Address(paddr, _) =>  pmpCheck_xlen(paddr, width, Read(Data), cur_privilege),
        TR_Failure(e, _) => Some(e)
      };
      match data {
        None() => RETIRE_SUCCESS,
        Some(e) => {
          match (e) {
            E_Load_Access_Fault() => { handle_mem_exception(vaddr, E_SAMO_Access_Fault()); RETIRE_FAIL },
            E_Load_Page_Fault() => { handle_mem_exception(vaddr, E_SAMO_Page_Fault()); RETIRE_FAIL }
          }
        }
      }
    }
  }
}

function cbo_clean_flush_enable(p : Privilege) -> bool = {
   ~(((p != Machine) & (menvcfg.CBCFE() == 0b0)) | ((p == User) & (senvcfg.CBCFE() == 0b0)))
}

function cbop_for_cbo_inval(p : Privilege) -> option(cbop_zicbom) = {
  let illegal = ((p != Machine) & (menvcfg.CBIE() == 0b00)) |
                ((p == User) & (senvcfg.CBIE() == 0b00));
  let flush = ((p != Machine) & (menvcfg.CBIE() == 0b01)) |
              ((p == User) & (senvcfg.CBIE() == 0b01));
  if illegal then None()
  else if flush then Some(CBO_FLUSH)
  else Some(CBO_INVAL)
}

function clause execute(RISCV_ZICBOM(cbop, rs1)) = {
  let rs1_val = X(rs1);
  let cache_block_size = plat_cache_block_size();
  let vaddr = rs1_val & ~(cache_block_size - EXTZ(0b1));
  let cbcfe = cbo_clean_flush_enable(cur_privilege);
  let final_op : option(cbop_zicbom) = match (cbop, cbcfe) {
    (CBO_CLEAN, true) => Some(CBO_CLEAN),
    (CBO_CLEAN, false) => None(),
    (CBO_FLUSH, true) => Some(CBO_FLUSH),
    (CBO_FLUSH, false) => None(),
    (CBO_INVAL, _) => cbop_for_cbo_inval(cur_privilege)
  };
  match final_op {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(CBO_CLEAN) => process_clean_inval(vaddr, cache_block_size, true, false),
    Some(CBO_FLUSH) => process_clean_inval(vaddr, cache_block_size, true, true),
    Some(CBO_INVAL) => process_clean_inval(vaddr, cache_block_size, false, true)
  }
}

