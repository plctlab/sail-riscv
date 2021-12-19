/* ****************************************************************** */
/* This file specifies the instructions in the Zicboz extension */
union clause ast = RISCV_ZICBOZ : (regidx)
mapping clause encdec = RISCV_ZICBOZ(rs1) if haveZicboz()
  <-> 0b000000000100 @ rs1 @ 0b010 @ 0b00000 @ 0b0001111 if haveZicboz()

mapping clause assembly = RISCV_ZICBOZ(rs1)
  <-> "cbo.zero" ^ spc() ^ reg_name(rs1)

function get_envcfg_cbze(p : Privilege) -> bool = {
  ~(((p != Machine) & (menvcfg.CBZE() == 0b0)) | ((p == User) & (senvcfg.CBZE() == 0b0)))
}

val process_cbo_zero : (xlenbits, xlenbits) -> Retired effect {eamem, escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function process_cbo_zero(vaddr, width) = {
  offset : xlenbits = zeros();
  failed : bool = false;
  while (offset <_u width) & (failed == false) do {
    let addr = vaddr + offset;
    match ext_data_get_addr(zeros(), addr, Write(Data), BYTE) {
      Ext_DataAddr_Error(e) => { ext_handle_data_check_error(e); failed = true },
      Ext_DataAddr_OK(vaddr) =>
        match translateAddr(vaddr, Write(Data)) {
          TR_Failure(e, _) => { handle_mem_exception(vaddr, e); failed = true },
          TR_Address(paddr, _) => {
            let eares : MemoryOpResult(unit) = mem_write_ea(paddr, 1, false, false, false);
            match (eares) {
              MemException(e) => { handle_mem_exception(vaddr, e); failed = true },
              MemValue(_) => {
                let res : MemoryOpResult(bool) = mem_write_value(paddr, 1, zeros(), false, false, false);
                match (res) {
                  MemValue(true) => offset = offset + EXTZ(0b1),
                  MemValue(false) => internal_error("store got false from mem_write_value"),
                  MemException(e) => { handle_mem_exception(vaddr, e); failed = true }
                }
              }
            }
          }
        }
    };
  };
  if failed then RETIRE_FAIL
  else RETIRE_SUCCESS
}

function clause execute(RISCV_ZICBOZ(rs1)) = {
  let rs1_val = X(rs1);
  let cache_block_size = plat_cache_block_size();
  let vaddr = rs1_val & ~(cache_block_size - EXTZ(0b1));
  if get_envcfg_cbze(cur_privilege) then
    process_cbo_zero(vaddr, cache_block_size)
  else {
    handle_illegal();
    RETIRE_FAIL
  }
}

