`define MK_DECL(SFX) \
  class foo``SFX #(type REQ=int) \
    extends uvm_port_base; \
    `MS_IMP_COMMON(SFX) \
    \
    `PUT_IMP(SFX, m_req_imp, REQ, t) // req \
    \
    `GET_IMP(SFX, m_rsp_imp, RSP, t) // rsp \
    `PEEK_IMP(SFX, m_rsp_imp, RSP, t) // rsp \
    \
  endclass
// MACRO: `MK_DECL2
//
// Define the class bar.
//
`define MK_DECL2(SFX) \
  class bar``SFX #(type REQ=int) \
    extends uvm_port_base; \
    `MS_IMP_COMMON(SFX) \
    \
    `PUT_IMP(SFX, m_req_imp, REQ, t) // req \
    \
  endclass
x = 1;
