/* ****************************************************************** */
/* This file specifies the instructions in the Zicbop extension */


/* ****************************************************************** */
union clause ast = RISCV_ZICBOP : (prop_zicbop, regidx, bits(7))

mapping encdec_prop : prop_zicbop <-> bits(5) = {
  PREFETCH_I <-> 0b00000,
  PREFETCH_R <-> 0b00001,
  PREFETCH_W <-> 0b00011
}

mapping clause encdec = RISCV_ZICBOP(prop, rs1, offset) if haveZicbop()
  <-> offset @ encdec_prop(prop) @ rs1 @ 0b110 @ 0b00000 @ 0b0010011 if haveZicbop()

mapping prop_mnemonic : prop_zicbop <-> string = {
  PREFETCH_I <-> "prefetch.i",
  PREFETCH_R <-> "prefetch.r",
  PREFETCH_W <-> "prefetch.w"
}

mapping clause assembly = RISCV_ZICBOP(prop, rs1, offset)
  <-> prop_mnemonic(prop) ^ spc() ^ hex_bits_12(offset @ 0b00000) ^ "(" ^ reg_name(rs1) ^ ")"

function clause execute(RISCV_ZICBOP(prop, rs1, offset)) = {
  /* do nothing other than translate_address for prefetch.i/r/w */
  match prop {
    PREFETCH_I => {
      let vaddr = X(rs1) + EXTS(offset @ 0b00000);
      match ext_control_check_addr(vaddr) {
        Ext_ControlAddr_Error(e) => RETIRE_SUCCESS,
          Ext_ControlAddr_OK(vaddr) =>
            match translateAddr(vaddr, Execute()) {
              TR_Failure(e, _) => RETIRE_SUCCESS,
              TR_Address(paddr, _) => RETIRE_SUCCESS
            }
      }
    },
    PREFETCH_W => {
      match ext_data_get_addr(rs1, EXTS(offset @ 0b00000), Write(Data), BYTE) {
        Ext_DataAddr_Error(e) => RETIRE_SUCCESS,
        Ext_DataAddr_OK(vaddr) =>
          match translateAddr(vaddr, Write(Data)) {
            TR_Failure(e, _) => RETIRE_SUCCESS,
            TR_Address(paddr, _) => RETIRE_SUCCESS
          }
      }
    },
    PREFETCH_R => {
      match ext_data_get_addr(rs1, EXTS(offset @ 0b00000), Read(Data), BYTE) {
        Ext_DataAddr_Error(e) => RETIRE_SUCCESS,
        Ext_DataAddr_OK(vaddr) =>
          match translateAddr(vaddr, Read(Data)) {
            TR_Failure(e, _) => RETIRE_SUCCESS,
            TR_Address(paddr, _) => RETIRE_SUCCESS
          }
      }
    }
  }
}
