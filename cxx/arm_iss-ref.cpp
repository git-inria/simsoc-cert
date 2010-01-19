#include "arm_iss_base.hpp"

struct ARM_ISS: ARM_ISS_Base {

  // A4.1.2 ADC
  void ADC(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t n,
           const uint32_t shifter_operand);

  // A4.1.3 ADD
  void ADD(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t n,
           const uint32_t shifter_operand);

  // A4.1.4 AND
  void AND(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t n,
           const bool shifter_carry_out,
           const uint32_t shifter_operand);

  // A4.1.5 B, BL
  void B_BL(const bool L,
            const ARM_Processor::Condition cond,
            const uint32_t signed_immed_24);

  // A4.1.6 BIC
  void BIC(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t n,
           const bool shifter_carry_out,
           const uint32_t shifter_operand);

  // A4.1.7 BKPT
  void BKPT();

  // A4.1.8 BLX (1)
  void BLX_1(const uint32_t H,
             const uint32_t signed_immed_24);

  // A4.1.9 BLX (2)
  void BLX_2(const ARM_Processor::Condition cond,
             const uint8_t m);

  // A4.1.10 BX
  void BX(const ARM_Processor::Condition cond,
          const uint8_t m);

  // A4.1.11 BXJ
  void BXJ(const ARM_Processor::Condition cond,
           const uint8_t m);

  // A4.1.12 CDP
  void CDP(const ARM_Processor::Condition cond,
           const uint8_t cp_num);

  // A4.1.13 CLZ
  void CLZ(const uint8_t d,
           const uint8_t m);

  // A4.1.14 CMN
  void CMN(const ARM_Processor::Condition cond,
           const uint8_t n,
           const uint32_t shifter_operand);

  // A4.1.15 CMP
  void CMP(const ARM_Processor::Condition cond,
           const uint8_t n,
           const uint32_t shifter_operand);

  // A4.1.16 CPS
  void CPS(const bool A,
           const bool F,
           const bool I,
           const uint8_t imod,
           const bool mmod,
           const ARM_Processor::Mode mode);

  // A4.1.17 CPY
  void CPY(const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t m);

  // A4.1.18 EOR
  void EOR(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t n,
           const bool shifter_carry_out,
           const uint32_t shifter_operand);

  // A4.1.19 LDC
  void LDC(const ARM_Processor::Condition cond,
           const uint8_t cp_num,
           const uint32_t start_address);

  // A4.1.20 LDM (1)
  void LDM_1(const ARM_Processor::Condition cond,
             const uint16_t register_list,
             const uint32_t start_address);

  // A4.1.21 LDM (2)
  void LDM_2(const ARM_Processor::Condition cond,
             const uint16_t register_list,
             const uint32_t start_address);

  // A4.1.22 LDM (3)
  void LDM_3(const ARM_Processor::Condition cond,
             const uint16_t register_list,
             const uint32_t start_address);

  // A4.1.23 LDR
  void LDR(const uint32_t address,
           const ARM_Processor::Condition cond,
           const uint8_t d);

  // A4.1.24 LDRB
  void LDRB(const uint32_t address,
            const ARM_Processor::Condition cond,
            const uint8_t d);

  // A4.1.25 LDRBT
  void LDRBT(const uint32_t address,
             const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t n);

  // A4.1.26 LDRD
  void LDRD(const uint32_t address,
            const ARM_Processor::Condition cond,
            const uint8_t d);

  // A4.1.27 LDREX
  void LDREX(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t n);

  // A4.1.28 LDRH
  void LDRH(const uint32_t address,
            const ARM_Processor::Condition cond,
            const uint8_t d);

  // A4.1.29 LDRSB
  void LDRSB(const uint32_t address,
             const ARM_Processor::Condition cond,
             const uint8_t d);

  // A4.1.30 LDRSH
  void LDRSH(const uint32_t address,
             const ARM_Processor::Condition cond,
             const uint8_t d);

  // A4.1.31 LDRT
  void LDRT(const uint32_t address,
            const ARM_Processor::Condition cond,
            const uint8_t d);

  // A4.1.32 MCR
  void MCR(const ARM_Processor::Condition cond,
           const uint8_t cp_num,
           const uint8_t d);

  // A4.1.33 MCRR
  void MCRR(const ARM_Processor::Condition cond,
            const uint8_t cp_num,
            const uint8_t d,
            const uint8_t n);

  // A4.1.34 MLA
  void MLA(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t m,
           const uint8_t n,
           const uint8_t s);

  // A4.1.35 MOV
  void MOV(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const bool shifter_carry_out,
           const uint32_t shifter_operand);

  // A4.1.36 MRC
  void MRC(const ARM_Processor::Condition cond,
           const uint8_t cp_num,
           const uint8_t d);

  // A4.1.37 MRRC
  void MRRC(const ARM_Processor::Condition cond,
            const uint8_t cp_num,
            const uint8_t d,
            const uint8_t n);

  // A4.1.38 MRS
  void MRS(const bool R,
           const ARM_Processor::Condition cond,
           const uint8_t d);

  // A4.1.39 MSR
  void MSR(const bool R,
           const ARM_Processor::Condition cond,
           const uint8_t field_mask,
           const uint8_t immed_8,
           const uint8_t m,
           const uint32_t opcode,
           const uint8_t rotate_imm);

  // A4.1.40 MUL
  void MUL(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t m,
           const uint8_t s);

  // A4.1.41 MVN
  void MVN(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const bool shifter_carry_out,
           const uint32_t shifter_operand);

  // A4.1.42 ORR
  void ORR(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t n,
           const bool shifter_carry_out,
           const uint32_t shifter_operand);

  // A4.1.43 PKHBT
  void PKHBT(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n,
             const uint8_t shift_imm);

  // A4.1.44 PKHTB
  void PKHTB(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n,
             const uint8_t shift_imm);

  // A4.1.45 PLD
  void PLD();

  // A4.1.46 QADD
  void QADD(const ARM_Processor::Condition cond,
            const uint8_t d,
            const uint8_t m,
            const uint8_t n);

  // A4.1.47 QADD16
  void QADD16(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n);

  // A4.1.48 QADD8
  void QADD8(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n);

  // A4.1.49 QADDSUBX
  void QADDSUBX(const ARM_Processor::Condition cond,
                const uint8_t d,
                const uint8_t m,
                const uint8_t n);

  // A4.1.50 QDADD
  void QDADD(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n);

  // A4.1.51 QDSUB
  void QDSUB(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n);

  // A4.1.52 QSUB
  void QSUB(const ARM_Processor::Condition cond,
            const uint8_t d,
            const uint8_t m,
            const uint8_t n);

  // A4.1.53 QSUB16
  void QSUB16(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n);

  // A4.1.54 QSUB8
  void QSUB8(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n);

  // A4.1.55 QSUBADDX
  void QSUBADDX(const ARM_Processor::Condition cond,
                const uint8_t d,
                const uint8_t m,
                const uint8_t n);

  // A4.1.56 REV
  void REV(const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t m);

  // A4.1.57 REV16
  void REV16(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m);

  // A4.1.58 REVSH
  void REVSH(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m);

  // A4.1.59 RFE
  void RFE(const uint32_t start_address);

  // A4.1.60 RSB
  void RSB(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t n,
           const uint32_t shifter_operand);

  // A4.1.61 RSC
  void RSC(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t n,
           const uint32_t shifter_operand);

  // A4.1.62 SADD16
  void SADD16(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n);

  // A4.1.63 SADD8
  void SADD8(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n);

  // A4.1.64 SADDSUBX
  void SADDSUBX(const ARM_Processor::Condition cond,
                const uint8_t d,
                const uint8_t m,
                const uint8_t n);

  // A4.1.65 SBC
  void SBC(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t n,
           const uint32_t shifter_operand);

  // A4.1.66 SEL
  void SEL(const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t m,
           const uint8_t n);

  // A4.1.67 SETEND
  void SETEND();

  // A4.1.68 SHADD16
  void SHADD16(const ARM_Processor::Condition cond,
               const uint8_t d,
               const uint8_t m,
               const uint8_t n);

  // A4.1.69 SHADD8
  void SHADD8(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n);

  // A4.1.70 SHADDSUBX
  void SHADDSUBX(const ARM_Processor::Condition cond,
                 const uint8_t d,
                 const uint8_t m,
                 const uint8_t n);

  // A4.1.71 SHSUB16
  void SHSUB16(const ARM_Processor::Condition cond,
               const uint8_t d,
               const uint8_t m,
               const uint8_t n);

  // A4.1.72 SHSUB8
  void SHSUB8(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n);

  // A4.1.73 SHSUBADDX
  void SHSUBADDX(const ARM_Processor::Condition cond,
                 const uint8_t d,
                 const uint8_t m,
                 const uint8_t n);

  // A4.1.74 SMLA<x><y>
  void SMLA(const ARM_Processor::Condition cond,
            const uint8_t d,
            const uint8_t m,
            const uint8_t n,
            const uint8_t s,
            const bool x,
            const bool y);

  // A4.1.75 SMLAD
  void SMLAD(const bool X,
             const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n,
             const uint8_t s);

  // A4.1.76 SMLAL
  void SMLAL(const bool S,
             const ARM_Processor::Condition cond,
             const uint8_t dHi,
             const uint8_t dLo,
             const uint8_t m,
             const uint8_t s);

  // A4.1.77 SMLAL<x><y>
  void SMLAL(const ARM_Processor::Condition cond,
             const uint8_t dHi,
             const uint8_t dLo,
             const uint8_t m,
             const uint8_t s,
             const bool x,
             const bool y);

  // A4.1.78 SMLALD
  void SMLALD(const bool X,
              const ARM_Processor::Condition cond,
              const uint8_t dHi,
              const uint8_t dLo,
              const uint8_t m,
              const uint8_t s);

  // A4.1.79 SMLAW<y>
  void SMLAW(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n,
             const uint8_t s,
             const bool y);

  // A4.1.80 SMLSD
  void SMLSD(const bool X,
             const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n,
             const uint8_t s);

  // A4.1.81 SMLSLD
  void SMLSLD(const bool X,
              const ARM_Processor::Condition cond,
              const uint8_t dHi,
              const uint8_t dLo,
              const uint8_t m,
              const uint8_t s);

  // A4.1.82 SMMLA
  void SMMLA(const bool R,
             const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n,
             const uint8_t s);

  // A4.1.83 SMMLS
  void SMMLS(const bool R,
             const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n,
             const uint8_t s);

  // A4.1.84 SMMUL
  void SMMUL(const bool R,
             const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t s);

  // A4.1.85 SMUAD
  void SMUAD(const bool X,
             const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t s);

  // A4.1.86 SMUL<x><y>
  void SMUL(const ARM_Processor::Condition cond,
            const uint8_t d,
            const uint8_t m,
            const uint8_t s,
            const bool x,
            const bool y);

  // A4.1.87 SMULL
  void SMULL(const bool S,
             const ARM_Processor::Condition cond,
             const uint8_t dHi,
             const uint8_t dLo,
             const uint8_t m,
             const uint8_t s);

  // A4.1.88 SMULW<y>
  void SMULW(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t s,
             const bool y);

  // A4.1.89 SMUSD
  void SMUSD(const bool X,
             const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t s);

  // A4.1.90 SRS
  void SRS(const uint32_t start_address);

  // A4.1.91 SSAT
  void SSAT(const ARM_Processor::Condition cond,
            const uint8_t d,
            const uint8_t m,
            const uint8_t sat_imm,
            const bool shift,
            const uint8_t shift_imm);

  // A4.1.92 SSAT16
  void SSAT16(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t sat_imm);

  // A4.1.93 SSUB16
  void SSUB16(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n);

  // A4.1.94 SSUB8
  void SSUB8(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n);

  // A4.1.95 SSUBADDX
  void SSUBADDX(const ARM_Processor::Condition cond,
                const uint8_t d,
                const uint8_t m,
                const uint8_t n);

  // A4.1.96 STC
  void STC(const ARM_Processor::Condition cond,
           const uint8_t cp_num,
           const uint32_t start_address);

  // A4.1.97 STM (1)
  void STM_1(const ARM_Processor::Condition cond,
             const uint16_t register_list,
             const uint32_t start_address);

  // A4.1.98 STM (2)
  void STM_2(const ARM_Processor::Condition cond,
             const uint16_t register_list,
             const uint32_t start_address);

  // A4.1.99 STR
  void STR(const uint32_t address,
           const ARM_Processor::Condition cond,
           const uint8_t d);

  // A4.1.100 STRB
  void STRB(const uint32_t address,
            const ARM_Processor::Condition cond,
            const uint8_t d);

  // A4.1.101 STRBT
  void STRBT(const uint32_t address,
             const ARM_Processor::Condition cond,
             const uint8_t d);

  // A4.1.102 STRD
  void STRD(const uint32_t address,
            const ARM_Processor::Condition cond,
            const uint8_t d);

  // A4.1.103 STREX
  void STREX(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n);

  // A4.1.104 STRH
  void STRH(const uint32_t address,
            const ARM_Processor::Condition cond,
            const uint8_t d);

  // A4.1.105 STRT
  void STRT(const uint32_t address,
            const ARM_Processor::Condition cond,
            const uint8_t d);

  // A4.1.106 SUB
  void SUB(const bool S,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t n,
           const uint32_t shifter_operand);

  // A4.1.107 SWI
  void SWI(const ARM_Processor::Condition cond);

  // A4.1.108 SWP
  void SWP(const uint32_t address,
           const ARM_Processor::Condition cond,
           const uint8_t d,
           const uint8_t m);

  // A4.1.109 SWPB
  void SWPB(const uint32_t address,
            const ARM_Processor::Condition cond,
            const uint8_t d,
            const uint8_t m);

  // A4.1.110 SXTAB
  void SXTAB(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n,
             const uint8_t rotate);

  // A4.1.111 SXTAB16
  void SXTAB16(const ARM_Processor::Condition cond,
               const uint8_t d,
               const uint8_t m,
               const uint8_t n,
               const uint8_t rotate);

  // A4.1.112 SXTAH
  void SXTAH(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n,
             const uint8_t rotate);

  // A4.1.113 SXTB
  void SXTB(const ARM_Processor::Condition cond,
            const uint8_t d,
            const uint8_t m,
            const uint8_t rotate);

  // A4.1.114 SXTB16
  void SXTB16(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t rotate);

  // A4.1.115 SXTH
  void SXTH(const ARM_Processor::Condition cond,
            const uint8_t d,
            const uint8_t m,
            const uint8_t rotate);

  // A4.1.116 TEQ
  void TEQ(const ARM_Processor::Condition cond,
           const uint8_t n,
           const bool shifter_carry_out,
           const uint32_t shifter_operand);

  // A4.1.117 TST
  void TST(const ARM_Processor::Condition cond,
           const uint8_t n,
           const bool shifter_carry_out,
           const uint32_t shifter_operand);

  // A4.1.118 UADD16
  void UADD16(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n);

  // A4.1.119 UADD8
  void UADD8(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n);

  // A4.1.120 UADDSUBX
  void UADDSUBX(const ARM_Processor::Condition cond,
                const uint8_t d,
                const uint8_t m,
                const uint8_t n);

  // A4.1.121 UHADD16
  void UHADD16(const ARM_Processor::Condition cond,
               const uint8_t d,
               const uint8_t m,
               const uint8_t n);

  // A4.1.122 UHADD8
  void UHADD8(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n);

  // A4.1.123 UHADDSUBX
  void UHADDSUBX(const ARM_Processor::Condition cond,
                 const uint8_t d,
                 const uint8_t m,
                 const uint8_t n);

  // A4.1.124 UHSUB16
  void UHSUB16(const ARM_Processor::Condition cond,
               const uint8_t d,
               const uint8_t m,
               const uint8_t n);

  // A4.1.125 UHSUB8
  void UHSUB8(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n);

  // A4.1.126 UHSUBADDX
  void UHSUBADDX(const ARM_Processor::Condition cond,
                 const uint8_t d,
                 const uint8_t m,
                 const uint8_t n);

  // A4.1.127 UMAAL
  void UMAAL(const ARM_Processor::Condition cond,
             const uint8_t dHi,
             const uint8_t dLo,
             const uint8_t m,
             const uint8_t s);

  // A4.1.128 UMLAL
  void UMLAL(const bool S,
             const ARM_Processor::Condition cond,
             const uint8_t dHi,
             const uint8_t dLo,
             const uint8_t m,
             const uint8_t s);

  // A4.1.129 UMULL
  void UMULL(const bool S,
             const ARM_Processor::Condition cond,
             const uint8_t dHi,
             const uint8_t dLo,
             const uint8_t m,
             const uint8_t s);

  // A4.1.130 UQADD16
  void UQADD16(const ARM_Processor::Condition cond,
               const uint8_t d,
               const uint8_t m,
               const uint8_t n);

  // A4.1.131 UQADD8
  void UQADD8(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n);

  // A4.1.132 UQADDSUBX
  void UQADDSUBX(const ARM_Processor::Condition cond,
                 const uint8_t d,
                 const uint8_t m,
                 const uint8_t n);

  // A4.1.133 UQSUB16
  void UQSUB16(const ARM_Processor::Condition cond,
               const uint8_t d,
               const uint8_t m,
               const uint8_t n);

  // A4.1.134 UQSUB8
  void UQSUB8(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n);

  // A4.1.135 UQSUBADDX
  void UQSUBADDX(const ARM_Processor::Condition cond,
                 const uint8_t d,
                 const uint8_t m,
                 const uint8_t n);

  // A4.1.136 USAD8
  void USAD8(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t s);

  // A4.1.137 USADA8
  void USADA8(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n,
              const uint8_t s);

  // A4.1.138 USAT
  void USAT(const ARM_Processor::Condition cond,
            const uint8_t d,
            const uint8_t m,
            const uint8_t sat_imm,
            const bool shift,
            const uint8_t shift_imm);

  // A4.1.139 USAT16
  void USAT16(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t sat_imm);

  // A4.1.140 USUB16
  void USUB16(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t n);

  // A4.1.141 USUB8
  void USUB8(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n);

  // A4.1.142 USUBADDX
  void USUBADDX(const ARM_Processor::Condition cond,
                const uint8_t d,
                const uint8_t m,
                const uint8_t n);

  // A4.1.143 UXTAB
  void UXTAB(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n,
             const uint8_t rotate);

  // A4.1.144 UXTAB16
  void UXTAB16(const ARM_Processor::Condition cond,
               const uint8_t d,
               const uint8_t m,
               const uint8_t n,
               const uint8_t rotate);

  // A4.1.145 UXTAH
  void UXTAH(const ARM_Processor::Condition cond,
             const uint8_t d,
             const uint8_t m,
             const uint8_t n,
             const uint8_t rotate);

  // A4.1.146 UXTB
  void UXTB(const ARM_Processor::Condition cond,
            const uint8_t d,
            const uint8_t m,
            const uint8_t rotate);

  // A4.1.147 UXTB16
  void UXTB16(const ARM_Processor::Condition cond,
              const uint8_t d,
              const uint8_t m,
              const uint8_t rotate);

  // A4.1.148 UXTH
  void UXTH(const ARM_Processor::Condition cond,
            const uint8_t d,
            const uint8_t m,
            const uint8_t rotate);

};

// A4.1.2 ADC
void ARM_ISS::ADC(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t n,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(((old_Rn + shifter_operand) + proc.cpsr.C_flag));
    else
      proc.reg(d) = ((old_Rn + shifter_operand) + proc.cpsr.C_flag);
    if (((S == 1) && d==15)) {
      if (CurrentModeHasSPSR()) {
        proc.cpsr = proc.spsr();
      } else {
        unpredictable();
      }
    } else {
      if ((S == 1)) {
        proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
        proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
        proc.cpsr.C_flag = CarryFrom_add3(old_Rn, shifter_operand, proc.cpsr.C_flag);
        proc.cpsr.V_flag = OverflowFrom_add3(old_Rn, shifter_operand, proc.cpsr.C_flag);
      }
    }
  }
}

// A4.1.3 ADD
void ARM_ISS::ADD(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t n,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((old_Rn + shifter_operand));
    else
      proc.reg(d) = (old_Rn + shifter_operand);
    if (((S == 1) && d==15)) {
      if (CurrentModeHasSPSR()) {
        proc.cpsr = proc.spsr();
      } else {
        unpredictable();
      }
    } else {
      if ((S == 1)) {
        proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
        proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
        proc.cpsr.C_flag = CarryFrom_add2(old_Rn, shifter_operand);
        proc.cpsr.V_flag = OverflowFrom_add2(old_Rn, shifter_operand);
      }
    }
  }
}

// A4.1.4 AND
void ARM_ISS::AND(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t n,
                  const bool shifter_carry_out,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((old_Rn & shifter_operand));
    else
      proc.reg(d) = (old_Rn & shifter_operand);
    if (((S == 1) && d==15)) {
      if (CurrentModeHasSPSR()) {
        proc.cpsr = proc.spsr();
      } else {
        unpredictable();
      }
    } else {
      if ((S == 1)) {
        proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
        proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
        proc.cpsr.C_flag = shifter_carry_out;
      }
    }
  }
}

// A4.1.5 B, BL
void ARM_ISS::B_BL(const bool L,
                   const ARM_Processor::Condition cond,
                   const uint32_t signed_immed_24) {
  if (ConditionPassed(cond)) {
    if ((L == 1)) {
      proc.reg(14) = next_instr();
    }
    proc.set_pc_raw((proc.reg(15) + (SignExtend_24to30(signed_immed_24) << 2)));
  }
}

// A4.1.6 BIC
void ARM_ISS::BIC(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t n,
                  const bool shifter_carry_out,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((old_Rn & NOT(shifter_operand)));
    else
      proc.reg(d) = (old_Rn & NOT(shifter_operand));
    if (((S == 1) && d==15)) {
      if (CurrentModeHasSPSR()) {
        proc.cpsr = proc.spsr();
      } else {
        unpredictable();
      }
    } else {
      if ((S == 1)) {
        proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
        proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
        proc.cpsr.C_flag = shifter_carry_out;
      }
    }
  }
}

// A4.1.7 BKPT
void ARM_ISS::BKPT() {
  if (not_overridden_by_debug_hardware()) {
    proc.reg(14,ARM_Processor::abt) = (this_instr() + 4);
    proc.spsr(ARM_Processor::abt) = proc.cpsr;
    proc.cpsr.mode = ARM_Processor::abt;
    proc.cpsr.T_flag = 0;
    proc.cpsr.I_flag = 1;
    proc.cpsr.A_flag = 1;
    proc.cpsr.E_flag = proc.cp15.get_reg1_EEbit();
    if (high_vectors_configured()) {
      proc.set_pc_raw(0xFFFF000C);
    } else {
      proc.set_pc_raw(0x0000000C);
    }
  }
}

// A4.1.8 BLX (1)
void ARM_ISS::BLX_1(const uint32_t H,
                    const uint32_t signed_immed_24) {
  proc.reg(14) = next_instr();
  proc.cpsr.T_flag = 1;
  proc.set_pc_raw(((proc.reg(15) + (SignExtend_24to30(signed_immed_24) << 2)) + (H << 1)));
}

// A4.1.9 BLX (2)
void ARM_ISS::BLX_2(const ARM_Processor::Condition cond,
                    const uint8_t m) {
  const uint32_t old_Rm = proc.reg(m);
  uint32_t target;
  if (ConditionPassed(cond)) {
    target = old_Rm;
    proc.reg(14) = next_instr();
    proc.cpsr.T_flag = ((target>>0)&1);
    proc.set_pc_raw((target & 0xFFFFFFFE));
  }
}

// A4.1.10 BX
void ARM_ISS::BX(const ARM_Processor::Condition cond,
                 const uint8_t m) {
  const uint32_t old_Rm = proc.reg(m);
  if (ConditionPassed(cond)) {
    proc.cpsr.T_flag = ((old_Rm>>0)&1);
    proc.set_pc_raw((old_Rm & 0xFFFFFFFE));
  }
}

// A4.1.11 BXJ
void ARM_ISS::BXJ(const ARM_Processor::Condition cond,
                  const uint8_t m) {
  const uint32_t old_Rm = proc.reg(m);
  uint32_t jpc;
  uint32_t invalidhandler;
  if (ConditionPassed(cond)) {
    if ((JE_bit_of_Main_Configuration_register() == 0)) {
      proc.cpsr.T_flag = ((old_Rm>>0)&1);
      proc.set_pc_raw((old_Rm & 0xFFFFFFFE));
    } else {
      jpc = SUBARCHITECTURE_DEFINED_value();
      invalidhandler = SUBARCHITECTURE_DEFINED_value();
      if (Jazelle_Extension_accepts_opcode_at_jpc()) {
        if ((CV_bit_of_Jazelle_OS_Control_register() == 0)) {
          proc.set_pc_raw(invalidhandler);
        } else {
          proc.cpsr.J_flag = 1;
          Start_opcode_execution_at(jpc);
        }
      } else {
        if (((CV_bit_of_Jazelle_OS_Control_register() == 0) & IMPLEMENTATION_DEFINED_CONDITION())) {
          proc.set_pc_raw(invalidhandler);
        } else {
          proc.cpsr.T_flag = ((old_Rm>>0)&1);
          proc.set_pc_raw((old_Rm & 0xFFFFFFFE));
        }
      }
    }
  }
}

// A4.1.12 CDP
void ARM_ISS::CDP(const ARM_Processor::Condition cond,
                  const uint8_t cp_num) {
  if (ConditionPassed(cond)) {
    proc.coproc(cp_num)->dependent_operation();
  }
}

// A4.1.13 CLZ
void ARM_ISS::CLZ(const uint8_t d,
                  const uint8_t m) {
  const uint32_t old_Rm = proc.reg(m);
  if ((old_Rm == 0)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(32);
    else
      proc.reg(d) = 32;
  } else {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((31 - bit_position_of_most_significant_1(old_Rm)));
    else
      proc.reg(d) = (31 - bit_position_of_most_significant_1(old_Rm));
  }
}

// A4.1.14 CMN
void ARM_ISS::CMN(const ARM_Processor::Condition cond,
                  const uint8_t n,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  uint32_t alu_out;
  if (ConditionPassed(cond)) {
    alu_out = (old_Rn + shifter_operand);
    proc.cpsr.N_flag = ((alu_out>>31)&1);
    proc.cpsr.Z_flag = ((alu_out == 0)? 1: 0);
    proc.cpsr.C_flag = CarryFrom_add2(old_Rn, shifter_operand);
    proc.cpsr.V_flag = OverflowFrom_add2(old_Rn, shifter_operand);
  }
}

// A4.1.15 CMP
void ARM_ISS::CMP(const ARM_Processor::Condition cond,
                  const uint8_t n,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  uint32_t alu_out;
  if (ConditionPassed(cond)) {
    alu_out = (old_Rn - shifter_operand);
    proc.cpsr.N_flag = ((alu_out>>31)&1);
    proc.cpsr.Z_flag = ((alu_out == 0)? 1: 0);
    proc.cpsr.C_flag = NOT(BorrowFrom_sub2(old_Rn, shifter_operand));
    proc.cpsr.V_flag = OverflowFrom_sub2(old_Rn, shifter_operand);
  }
}

// A4.1.16 CPS
void ARM_ISS::CPS(const bool A,
                  const bool F,
                  const bool I,
                  const uint8_t imod,
                  const bool mmod,
                  const ARM_Processor::Mode mode) {
  if (InAPrivilegedMode()) {
    if ((((imod>>1)&1) == 1)) {
      if ((A == 1)) {
        proc.cpsr.A_flag = ((imod>>0)&1);
      }
      if ((I == 1)) {
        proc.cpsr.I_flag = ((imod>>0)&1);
      }
      if ((F == 1)) {
        proc.cpsr.F_flag = ((imod>>0)&1);
      }
    }
    if ((mmod == 1)) {
      proc.cpsr.mode = mode;
    }
  }
}

// A4.1.17 CPY
void ARM_ISS::CPY(const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t m) {
  const uint32_t old_Rm = proc.reg(m);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(old_Rm);
    else
      proc.reg(d) = old_Rm;
  }
}

// A4.1.18 EOR
void ARM_ISS::EOR(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t n,
                  const bool shifter_carry_out,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((old_Rn ^ shifter_operand));
    else
      proc.reg(d) = (old_Rn ^ shifter_operand);
    if (((S == 1) && d==15)) {
      if (CurrentModeHasSPSR()) {
        proc.cpsr = proc.spsr();
      } else {
        unpredictable();
      }
    } else {
      if ((S == 1)) {
        proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
        proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
        proc.cpsr.C_flag = shifter_carry_out;
      }
    }
  }
}

// A4.1.19 LDC
void ARM_ISS::LDC(const ARM_Processor::Condition cond,
                  const uint8_t cp_num,
                  const uint32_t start_address) {
  uint32_t address;
  if (ConditionPassed(cond)) {
    address = start_address;
    proc.coproc(cp_num)->load(proc.mmu.read_word(address));
    while (proc.coproc(cp_num)->NotFinished())
      address = (address + 4);
    proc.coproc(cp_num)->load(proc.mmu.read_word(address));
  }
}

// A4.1.20 LDM (1)
void ARM_ISS::LDM_1(const ARM_Processor::Condition cond,
                    const uint16_t register_list,
                    const uint32_t start_address) {
  uint32_t value;
  uint32_t address;
  if (ConditionPassed(cond)) {
    address = start_address;
    for (size_t i = 0; i<14; ++i) {
      if ((((register_list>>i)&1) == 1)) {
        proc.reg(i) = proc.mmu.read_word(address);
        address = (address + 4);
      }
    }
    if ((((register_list>>15)&1) == 1)) {
      value = proc.mmu.read_word(address);
      if (proc.v5_and_above) {
        proc.set_pc_raw((value & 0xFFFFFFFE));
        proc.cpsr.T_flag = ((value>>0)&1);
      } else {
        proc.set_pc_raw((value & 0xFFFFFFFC));
      }
      address = (address + 4);
    }
  }
}

// A4.1.21 LDM (2)
void ARM_ISS::LDM_2(const ARM_Processor::Condition cond,
                    const uint16_t register_list,
                    const uint32_t start_address) {
  uint32_t address;
  if (ConditionPassed(cond)) {
    address = start_address;
    for (size_t i = 0; i<14; ++i) {
      if ((((register_list>>i)&1) == 1)) {
        proc.reg(i,ARM_Processor::usr) = proc.mmu.read_word(address);
        address = (address + 4);
      }
    }
  }
}

// A4.1.22 LDM (3)
void ARM_ISS::LDM_3(const ARM_Processor::Condition cond,
                    const uint16_t register_list,
                    const uint32_t start_address) {
  uint32_t value;
  uint32_t address;
  if (ConditionPassed(cond)) {
    address = start_address;
    for (size_t i = 0; i<14; ++i) {
      if ((((register_list>>i)&1) == 1)) {
        proc.reg(i) = proc.mmu.read_word(address);
        address = (address + 4);
      }
    }
    if (CurrentModeHasSPSR()) {
      proc.cpsr = proc.spsr();
    } else {
      unpredictable();
    }
    value = proc.mmu.read_word(address);
    proc.set_pc_raw(value);
    address = (address + 4);
  }
}

// A4.1.23 LDR
void ARM_ISS::LDR(const uint32_t address,
                  const ARM_Processor::Condition cond,
                  const uint8_t d) {
  uint32_t data;
  if (ConditionPassed(cond)) {
    if ((proc.cp15.get_reg1_Ubit() == 0)) {
      data = rotate_right(proc.mmu.read_word(address), (8 * get_bits(address,1,0)));
    } else {
      data = proc.mmu.read_word(address);
    }
    if (d==15) {
      if (proc.v5_and_above) {
        proc.set_pc_raw((data & 0xFFFFFFFE));
        proc.cpsr.T_flag = ((data>>0)&1);
      } else {
        proc.set_pc_raw((data & 0xFFFFFFFC));
      }
    } else {
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(data);
      else
        proc.reg(d) = data;
    }
  }
}

// A4.1.24 LDRB
void ARM_ISS::LDRB(const uint32_t address,
                   const ARM_Processor::Condition cond,
                   const uint8_t d) {
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(proc.mmu.read_byte(address));
    else
      proc.reg(d) = proc.mmu.read_byte(address);
  }
}

// A4.1.25 LDRBT
void ARM_ISS::LDRBT(const uint32_t address,
                    const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t n) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(proc.mmu.read_byte(address));
    else
      proc.reg(d) = proc.mmu.read_byte(address);
    proc.reg(n) = address;
  }
}

// A4.1.26 LDRD
void ARM_ISS::LDRD(const uint32_t address,
                   const ARM_Processor::Condition cond,
                   const uint8_t d) {
  if (ConditionPassed(cond)) {
    if ((((is_even(d) && d!=14) && (get_bits(address,1,0) == 0)) && ((proc.cp15.get_reg1_Ubit() == 1) || (((address>>2)&1) == 0)))) {
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(proc.mmu.read_word(address));
      else
        proc.reg(d) = proc.mmu.read_word(address);
      proc.reg((d + 1)) = proc.mmu.read_word((address + 4));
    } else {
      unpredictable();
    }
  }
}

// A4.1.27 LDREX
void ARM_ISS::LDREX(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t n) {
  const uint32_t old_Rn = proc.reg(n);
  size_t processor_id;
  uint32_t physical_address;
  if (ConditionPassed(cond)) {
    processor_id = ExecutingProcessor();
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(proc.mmu.read_word(old_Rn));
    else
      proc.reg(d) = proc.mmu.read_word(old_Rn);
    physical_address = TLB(old_Rn);
    if ((Shared(old_Rn) == 1)) {
      MarkExclusiveGlobal(physical_address, processor_id, 4);
    }
    MarkExclusiveLocal(physical_address, processor_id, 4);
  }
}

// A4.1.28 LDRH
void ARM_ISS::LDRH(const uint32_t address,
                   const ARM_Processor::Condition cond,
                   const uint8_t d) {
  uint16_t data;
  if (ConditionPassed(cond)) {
    if ((proc.cp15.get_reg1_Ubit() == 0)) {
      if ((((address>>0)&1) == 0)) {
        data = proc.mmu.read_half(address);
      } else {
        unpredictable();
      }
    } else {
      data = proc.mmu.read_half(address);
    }
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(ZeroExtend(get_half_0(data)));
    else
      proc.reg(d) = ZeroExtend(get_half_0(data));
  }
}

// A4.1.29 LDRSB
void ARM_ISS::LDRSB(const uint32_t address,
                    const ARM_Processor::Condition cond,
                    const uint8_t d) {
  uint8_t data;
  if (ConditionPassed(cond)) {
    data = proc.mmu.read_byte(address);
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(SignExtend(data));
    else
      proc.reg(d) = SignExtend(data);
  }
}

// A4.1.30 LDRSH
void ARM_ISS::LDRSH(const uint32_t address,
                    const ARM_Processor::Condition cond,
                    const uint8_t d) {
  uint16_t data;
  if (ConditionPassed(cond)) {
    if ((proc.cp15.get_reg1_Ubit() == 0)) {
      if ((((address>>0)&1) == 0)) {
        data = proc.mmu.read_half(address);
      } else {
        unpredictable();
      }
    } else {
      data = proc.mmu.read_half(address);
    }
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(SignExtend(get_half_0(data)));
    else
      proc.reg(d) = SignExtend(get_half_0(data));
  }
}

// A4.1.31 LDRT
void ARM_ISS::LDRT(const uint32_t address,
                   const ARM_Processor::Condition cond,
                   const uint8_t d) {
  if (ConditionPassed(cond)) {
    if ((proc.cp15.get_reg1_Ubit() == 0)) {
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(rotate_right(proc.mmu.read_word(address), (8 * get_bits(address,1,0))));
      else
        proc.reg(d) = rotate_right(proc.mmu.read_word(address), (8 * get_bits(address,1,0)));
    } else {
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(proc.mmu.read_word(address));
      else
        proc.reg(d) = proc.mmu.read_word(address);
    }
  }
}

// A4.1.32 MCR
void ARM_ISS::MCR(const ARM_Processor::Condition cond,
                  const uint8_t cp_num,
                  const uint8_t d) {
  if (ConditionPassed(cond)) {
    proc.coproc(cp_num)->send(proc.reg(d));
  }
}

// A4.1.33 MCRR
void ARM_ISS::MCRR(const ARM_Processor::Condition cond,
                   const uint8_t cp_num,
                   const uint8_t d,
                   const uint8_t n) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    proc.coproc(cp_num)->send(proc.reg(d));
    proc.coproc(cp_num)->send(old_Rn);
  }
}

// A4.1.34 MLA
void ARM_ISS::MLA(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t m,
                  const uint8_t n,
                  const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  const uint32_t old_Rs = proc.reg(s);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(get_bits(((old_Rm * old_Rs) + old_Rn),31,0));
    else
      proc.reg(d) = get_bits(((old_Rm * old_Rs) + old_Rn),31,0);
    if ((S == 1)) {
      proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
      proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
    }
  }
}

// A4.1.35 MOV
void ARM_ISS::MOV(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const bool shifter_carry_out,
                  const uint32_t shifter_operand) {
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(shifter_operand);
    else
      proc.reg(d) = shifter_operand;
    if (((S == 1) && d==15)) {
      if (CurrentModeHasSPSR()) {
        proc.cpsr = proc.spsr();
      } else {
        unpredictable();
      }
    } else {
      if ((S == 1)) {
        proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
        proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
        proc.cpsr.C_flag = shifter_carry_out;
      }
    }
  }
}

// A4.1.36 MRC
void ARM_ISS::MRC(const ARM_Processor::Condition cond,
                  const uint8_t cp_num,
                  const uint8_t d) {
  uint32_t data;
  if (ConditionPassed(cond)) {
    data = proc.coproc(cp_num)->value();
    if (d==15) {
      proc.cpsr.N_flag = ((data>>31)&1);
      proc.cpsr.Z_flag = ((data>>30)&1);
      proc.cpsr.C_flag = ((data>>29)&1);
      proc.cpsr.V_flag = ((data>>28)&1);
    } else {
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(data);
      else
        proc.reg(d) = data;
    }
  }
}

// A4.1.37 MRRC
void ARM_ISS::MRRC(const ARM_Processor::Condition cond,
                   const uint8_t cp_num,
                   const uint8_t d,
                   const uint8_t n) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(proc.coproc(cp_num)->first_value());
    else
      proc.reg(d) = proc.coproc(cp_num)->first_value();
    proc.reg(n) = proc.coproc(cp_num)->second_value();
  }
}

// A4.1.38 MRS
void ARM_ISS::MRS(const bool R,
                  const ARM_Processor::Condition cond,
                  const uint8_t d) {
  if (ConditionPassed(cond)) {
    if ((R == 1)) {
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(proc.spsr());
      else
        proc.reg(d) = proc.spsr();
    } else {
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(proc.cpsr);
      else
        proc.reg(d) = proc.cpsr;
    }
  }
}

// A4.1.39 MSR
void ARM_ISS::MSR(const bool R,
                  const ARM_Processor::Condition cond,
                  const uint8_t field_mask,
                  const uint8_t immed_8,
                  const uint8_t m,
                  const uint32_t opcode,
                  const uint8_t rotate_imm) {
  const uint32_t old_Rm = proc.reg(m);
  uint32_t operand;
  uint32_t mask;
  uint32_t byte_mask;
  if (ConditionPassed(cond)) {
    if ((((opcode>>25)&1) == 1)) {
      operand = rotate_right(immed_8, (rotate_imm * 2));
    } else {
      operand = old_Rm;
    }
    if (((operand & proc.msr_UnallocMask()) != 0)) {
      unpredictable();
    }
    byte_mask = (((((((field_mask>>0)&1) == 1)? 0x000000FF: 0x00000000) | ((((field_mask>>1)&1) == 1)? 0x0000FF00: 0x00000000)) | ((((field_mask>>2)&1) == 1)? 0x00FF0000: 0x00000000)) | ((((field_mask>>3)&1) == 1)? 0xFF000000: 0x00000000));
    if ((R == 0)) {
      if (InAPrivilegedMode()) {
        if (((operand & proc.msr_StateMask()) != 0)) {
          unpredictable();
        } else {
          mask = (byte_mask & (proc.msr_UserMask() | proc.msr_PrivMask()));
        }
      } else {
        mask = (byte_mask & proc.msr_UserMask());
      }
      proc.cpsr = ((proc.cpsr & NOT(mask)) | (operand & mask));
    } else {
      if (CurrentModeHasSPSR()) {
        mask = (byte_mask & ((proc.msr_UserMask() | proc.msr_PrivMask()) | proc.msr_StateMask()));
        proc.spsr() = ((proc.spsr() & NOT(mask)) | (operand & mask));
      } else {
        unpredictable();
      }
    }
  }
}

// A4.1.40 MUL
void ARM_ISS::MUL(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t m,
                  const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(get_bits((old_Rm * old_Rs),31,0));
    else
      proc.reg(d) = get_bits((old_Rm * old_Rs),31,0);
    if ((S == 1)) {
      proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
      proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
    }
  }
}

// A4.1.41 MVN
void ARM_ISS::MVN(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const bool shifter_carry_out,
                  const uint32_t shifter_operand) {
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(NOT(shifter_operand));
    else
      proc.reg(d) = NOT(shifter_operand);
    if (((S == 1) && d==15)) {
      if (CurrentModeHasSPSR()) {
        proc.cpsr = proc.spsr();
      } else {
        unpredictable();
      }
    } else {
      if ((S == 1)) {
        proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
        proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
        proc.cpsr.C_flag = shifter_carry_out;
      }
    }
  }
}

// A4.1.42 ORR
void ARM_ISS::ORR(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t n,
                  const bool shifter_carry_out,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((old_Rn | shifter_operand));
    else
      proc.reg(d) = (old_Rn | shifter_operand);
    if (((S == 1) && d==15)) {
      if (CurrentModeHasSPSR()) {
        proc.cpsr = proc.spsr();
      } else {
        unpredictable();
      }
    } else {
      if ((S == 1)) {
        proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
        proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
        proc.cpsr.C_flag = shifter_carry_out;
      }
    }
  }
}

// A4.1.43 PKHBT
void ARM_ISS::PKHBT(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n,
                    const uint8_t shift_imm) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 15, 0, get_half_0(old_Rn));
    set_field(proc.reg(d), 31, 16, get_half_1((old_Rm << shift_imm)));
  }
}

// A4.1.44 PKHTB
void ARM_ISS::PKHTB(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n,
                    const uint8_t shift_imm) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if ((shift_imm == 0)) {
      if ((((old_Rm>>31)&1) == 0)) {
        set_field(proc.reg(d), 15, 0, 0x0000);
      } else {
        set_field(proc.reg(d), 15, 0, 0xFFFF);
      }
    } else {
      set_field(proc.reg(d), 15, 0, get_half_0(asr(old_Rm, shift_imm)));
    }
    set_field(proc.reg(d), 31, 16, get_half_1(old_Rn));
  }
}

// A4.1.45 PLD
void ARM_ISS::PLD() {
}

// A4.1.46 QADD
void ARM_ISS::QADD(const ARM_Processor::Condition cond,
                   const uint8_t d,
                   const uint8_t m,
                   const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(SignedSat_add32(old_Rm, old_Rn));
    else
      proc.reg(d) = SignedSat_add32(old_Rm, old_Rn);
    if (SignedDoesSat_add32(old_Rm, old_Rn)) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.47 QADD16
void ARM_ISS::QADD16(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 15, 0, SignedSat_add16(get_half_0(old_Rn), get_half_0(old_Rm)));
    set_field(proc.reg(d), 31, 16, SignedSat_add16(get_half_1(old_Rn), get_half_1(old_Rm)));
  }
}

// A4.1.48 QADD8
void ARM_ISS::QADD8(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 7, 0, SignedSat_add8(get_byte_0(old_Rn), get_byte_0(old_Rm)));
    set_field(proc.reg(d), 15, 8, SignedSat_add8(get_byte_1(old_Rn), get_byte_1(old_Rm)));
    set_field(proc.reg(d), 23, 16, SignedSat_add8(get_byte_2(old_Rn), get_byte_2(old_Rm)));
    set_field(proc.reg(d), 31, 24, SignedSat_add8(get_byte_3(old_Rn), get_byte_3(old_Rm)));
  }
}

// A4.1.49 QADDSUBX
void ARM_ISS::QADDSUBX(const ARM_Processor::Condition cond,
                       const uint8_t d,
                       const uint8_t m,
                       const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 31, 16, SignedSat_add16(get_half_1(old_Rn), get_half_0(old_Rm)));
    set_field(proc.reg(d), 15, 0, SignedSat_sub16(get_half_0(old_Rn), get_half_1(old_Rm)));
  }
}

// A4.1.50 QDADD
void ARM_ISS::QDADD(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(SignedSat_add32(old_Rm, SignedSat_double32(old_Rn)));
    else
      proc.reg(d) = SignedSat_add32(old_Rm, SignedSat_double32(old_Rn));
    if ((SignedDoesSat_add32(old_Rm, SignedSat_double32(old_Rn)) || SignedDoesSat_double32(old_Rn))) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.51 QDSUB
void ARM_ISS::QDSUB(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(SignedSat_sub32(old_Rm, SignedSat_double32(old_Rn)));
    else
      proc.reg(d) = SignedSat_sub32(old_Rm, SignedSat_double32(old_Rn));
    if ((SignedDoesSat_sub32(old_Rm, SignedSat_double32(old_Rn)) || SignedDoesSat_double32(old_Rn))) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.52 QSUB
void ARM_ISS::QSUB(const ARM_Processor::Condition cond,
                   const uint8_t d,
                   const uint8_t m,
                   const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(SignedSat_sub32(old_Rm, old_Rn));
    else
      proc.reg(d) = SignedSat_sub32(old_Rm, old_Rn);
    if (SignedDoesSat_sub32(old_Rm, old_Rn)) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.53 QSUB16
void ARM_ISS::QSUB16(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 15, 0, SignedSat_sub16(get_half_0(old_Rn), get_half_0(old_Rm)));
    set_field(proc.reg(d), 31, 16, SignedSat_sub16(get_half_1(old_Rn), get_half_1(old_Rm)));
  }
}

// A4.1.54 QSUB8
void ARM_ISS::QSUB8(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 7, 0, SignedSat_sub8(get_byte_0(old_Rn), get_byte_0(old_Rm)));
    set_field(proc.reg(d), 15, 8, SignedSat_sub8(get_byte_1(old_Rn), get_byte_1(old_Rm)));
    set_field(proc.reg(d), 23, 16, SignedSat_sub8(get_byte_2(old_Rn), get_byte_2(old_Rm)));
    set_field(proc.reg(d), 31, 24, SignedSat_sub8(get_byte_3(old_Rn), get_byte_3(old_Rm)));
  }
}

// A4.1.55 QSUBADDX
void ARM_ISS::QSUBADDX(const ARM_Processor::Condition cond,
                       const uint8_t d,
                       const uint8_t m,
                       const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 31, 16, SignedSat_sub16(get_half_1(old_Rn), get_half_0(old_Rm)));
    set_field(proc.reg(d), 15, 0, SignedSat_add16(get_half_0(old_Rn), get_half_1(old_Rm)));
  }
}

// A4.1.56 REV
void ARM_ISS::REV(const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t m) {
  const uint32_t old_Rm = proc.reg(m);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 31, 24, get_byte_0(old_Rm));
    set_field(proc.reg(d), 23, 16, get_byte_1(old_Rm));
    set_field(proc.reg(d), 15, 8, get_byte_2(old_Rm));
    set_field(proc.reg(d), 7, 0, get_byte_3(old_Rm));
  }
}

// A4.1.57 REV16
void ARM_ISS::REV16(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m) {
  const uint32_t old_Rm = proc.reg(m);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 15, 8, get_byte_0(old_Rm));
    set_field(proc.reg(d), 7, 0, get_byte_1(old_Rm));
    set_field(proc.reg(d), 31, 24, get_byte_2(old_Rm));
    set_field(proc.reg(d), 23, 16, get_byte_3(old_Rm));
  }
}

// A4.1.58 REVSH
void ARM_ISS::REVSH(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m) {
  const uint32_t old_Rm = proc.reg(m);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 15, 8, get_byte_0(old_Rm));
    set_field(proc.reg(d), 7, 0, get_byte_1(old_Rm));
    if ((((old_Rm>>7)&1) == 1)) {
      set_field(proc.reg(d), 31, 16, 0xFFFF);
    } else {
      set_field(proc.reg(d), 31, 16, 0x0000);
    }
  }
}

// A4.1.59 RFE
void ARM_ISS::RFE(const uint32_t start_address) {
  uint32_t value;
  uint32_t address;
  address = start_address;
  value = proc.mmu.read_word(address);
  if (InAPrivilegedMode()) {
    proc.cpsr = proc.mmu.read_word((address + 4));
  } else {
    unpredictable();
  }
  proc.set_pc_raw(value);
}

// A4.1.60 RSB
void ARM_ISS::RSB(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t n,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((shifter_operand - old_Rn));
    else
      proc.reg(d) = (shifter_operand - old_Rn);
    if (((S == 1) && d==15)) {
      if (CurrentModeHasSPSR()) {
        proc.cpsr = proc.spsr();
      } else {
        unpredictable();
      }
    } else {
      if ((S == 1)) {
        proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
        proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
        proc.cpsr.C_flag = NOT(BorrowFrom_sub2(shifter_operand, old_Rn));
        proc.cpsr.V_flag = OverflowFrom_sub2(shifter_operand, old_Rn);
      }
    }
  }
}

// A4.1.61 RSC
void ARM_ISS::RSC(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t n,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(((shifter_operand - old_Rn) - NOT(proc.cpsr.C_flag)));
    else
      proc.reg(d) = ((shifter_operand - old_Rn) - NOT(proc.cpsr.C_flag));
    if (((S == 1) && d==15)) {
      if (CurrentModeHasSPSR()) {
        proc.cpsr = proc.spsr();
      } else {
        unpredictable();
      }
    } else {
      if ((S == 1)) {
        proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
        proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
        proc.cpsr.C_flag = NOT(BorrowFrom_sub3(shifter_operand, old_Rn, NOT(proc.cpsr.C_flag)));
        proc.cpsr.V_flag = OverflowFrom_sub3(shifter_operand, old_Rn, NOT(proc.cpsr.C_flag));
      }
    }
  }
}

// A4.1.62 SADD16
void ARM_ISS::SADD16(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  if (ConditionPassed(cond)) {
    sum = (get_half_0(old_Rn) + get_half_0(old_Rm));
    set_field(proc.reg(d), 15, 0, get_half_0(sum));
    set_field(proc.cpsr.GE, 1, 0, ((sum >= 0)? 3: 0));
    sum = (get_half_1(old_Rn) + get_half_1(old_Rm));
    set_field(proc.reg(d), 31, 16, get_half_0(sum));
    set_field(proc.cpsr.GE, 3, 2, ((sum >= 0)? 3: 0));
  }
}

// A4.1.63 SADD8
void ARM_ISS::SADD8(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  if (ConditionPassed(cond)) {
    sum = (get_byte_0(old_Rn) + get_byte_0(old_Rm));
    set_field(proc.reg(d), 7, 0, get_byte_0(sum));
    set_bit(proc.cpsr.GE, 0, ((sum >= 0)? 1: 0));
    sum = (get_byte_1(old_Rn) + get_byte_1(old_Rm));
    set_field(proc.reg(d), 15, 8, get_byte_0(sum));
    set_bit(proc.cpsr.GE, 1, ((sum >= 0)? 1: 0));
    sum = (get_byte_2(old_Rn) + get_byte_2(old_Rm));
    set_field(proc.reg(d), 23, 16, get_byte_0(sum));
    set_bit(proc.cpsr.GE, 2, ((sum >= 0)? 1: 0));
    sum = (get_byte_3(old_Rn) + get_byte_3(old_Rm));
    set_field(proc.reg(d), 31, 24, get_byte_0(sum));
    set_bit(proc.cpsr.GE, 3, ((sum >= 0)? 1: 0));
  }
}

// A4.1.64 SADDSUBX
void ARM_ISS::SADDSUBX(const ARM_Processor::Condition cond,
                       const uint8_t d,
                       const uint8_t m,
                       const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  uint32_t diff;
  if (ConditionPassed(cond)) {
    sum = (get_half_1(old_Rn) + get_half_0(old_Rm));
    set_field(proc.reg(d), 31, 16, get_half_0(sum));
    set_field(proc.cpsr.GE, 3, 2, ((sum >= 0)? 3: 0));
    diff = (get_half_0(old_Rn) - get_half_1(old_Rm));
    set_field(proc.reg(d), 15, 0, get_half_0(diff));
    set_field(proc.cpsr.GE, 1, 0, ((diff >= 0)? 3: 0));
  }
}

// A4.1.65 SBC
void ARM_ISS::SBC(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t n,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(((old_Rn - shifter_operand) - NOT(proc.cpsr.C_flag)));
    else
      proc.reg(d) = ((old_Rn - shifter_operand) - NOT(proc.cpsr.C_flag));
    if (((S == 1) && d==15)) {
      if (CurrentModeHasSPSR()) {
        proc.cpsr = proc.spsr();
      } else {
        unpredictable();
      }
    } else {
      if ((S == 1)) {
        proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
        proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
        proc.cpsr.C_flag = NOT(BorrowFrom_sub3(old_Rn, shifter_operand, NOT(proc.cpsr.C_flag)));
        proc.cpsr.V_flag = OverflowFrom_sub3(old_Rn, shifter_operand, NOT(proc.cpsr.C_flag));
      }
    }
  }
}

// A4.1.66 SEL
void ARM_ISS::SEL(const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t m,
                  const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 7, 0, ((((proc.cpsr.GE>>0)&1) == 1)? get_byte_0(old_Rn): get_byte_0(old_Rm)));
    set_field(proc.reg(d), 15, 8, ((((proc.cpsr.GE>>1)&1) == 1)? get_byte_1(old_Rn): get_byte_1(old_Rm)));
    set_field(proc.reg(d), 23, 16, ((((proc.cpsr.GE>>2)&1) == 1)? get_byte_2(old_Rn): get_byte_2(old_Rm)));
    set_field(proc.reg(d), 31, 24, ((((proc.cpsr.GE>>3)&1) == 1)? get_byte_3(old_Rn): get_byte_3(old_Rm)));
  }
}

// A4.1.67 SETEND
void ARM_ISS::SETEND() {
  proc.cpsr = CPSR_with_specified_E_bit_modification();
}

// A4.1.68 SHADD16
void ARM_ISS::SHADD16(const ARM_Processor::Condition cond,
                      const uint8_t d,
                      const uint8_t m,
                      const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  if (ConditionPassed(cond)) {
    sum = (get_half_0(old_Rn) + get_half_0(old_Rm));
    set_field(proc.reg(d), 15, 0, get_bits(sum,16,1));
    sum = (get_half_1(old_Rn) + get_half_1(old_Rm));
    set_field(proc.reg(d), 31, 16, get_bits(sum,16,1));
  }
}

// A4.1.69 SHADD8
void ARM_ISS::SHADD8(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  if (ConditionPassed(cond)) {
    sum = (get_byte_0(old_Rn) + get_byte_0(old_Rm));
    set_field(proc.reg(d), 7, 0, get_bits(sum,8,1));
    sum = (get_byte_1(old_Rn) + get_byte_1(old_Rm));
    set_field(proc.reg(d), 15, 8, get_bits(sum,8,1));
    sum = (get_byte_2(old_Rn) + get_byte_2(old_Rm));
    set_field(proc.reg(d), 23, 16, get_bits(sum,8,1));
    sum = (get_byte_3(old_Rn) + get_byte_3(old_Rm));
    set_field(proc.reg(d), 31, 24, get_bits(sum,8,1));
  }
}

// A4.1.70 SHADDSUBX
void ARM_ISS::SHADDSUBX(const ARM_Processor::Condition cond,
                        const uint8_t d,
                        const uint8_t m,
                        const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  uint32_t diff;
  if (ConditionPassed(cond)) {
    sum = (get_half_1(old_Rn) + get_half_0(old_Rm));
    set_field(proc.reg(d), 31, 16, get_bits(sum,16,1));
    diff = (get_half_0(old_Rn) - get_half_1(old_Rm));
    set_field(proc.reg(d), 15, 0, get_bits(diff,16,1));
  }
}

// A4.1.71 SHSUB16
void ARM_ISS::SHSUB16(const ARM_Processor::Condition cond,
                      const uint8_t d,
                      const uint8_t m,
                      const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t diff;
  if (ConditionPassed(cond)) {
    diff = (get_half_0(old_Rn) - get_half_0(old_Rm));
    set_field(proc.reg(d), 15, 0, get_bits(diff,16,1));
    diff = (get_half_1(old_Rn) - get_half_1(old_Rm));
    set_field(proc.reg(d), 31, 16, get_bits(diff,16,1));
  }
}

// A4.1.72 SHSUB8
void ARM_ISS::SHSUB8(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t diff;
  if (ConditionPassed(cond)) {
    diff = (get_byte_0(old_Rn) - get_byte_0(old_Rm));
    set_field(proc.reg(d), 7, 0, get_bits(diff,8,1));
    diff = (get_byte_1(old_Rn) - get_byte_1(old_Rm));
    set_field(proc.reg(d), 15, 8, get_bits(diff,8,1));
    diff = (get_byte_2(old_Rn) - get_byte_2(old_Rm));
    set_field(proc.reg(d), 23, 16, get_bits(diff,8,1));
    diff = (get_byte_3(old_Rn) - get_byte_3(old_Rm));
    set_field(proc.reg(d), 31, 24, get_bits(diff,8,1));
  }
}

// A4.1.73 SHSUBADDX
void ARM_ISS::SHSUBADDX(const ARM_Processor::Condition cond,
                        const uint8_t d,
                        const uint8_t m,
                        const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  uint32_t diff;
  if (ConditionPassed(cond)) {
    diff = (get_half_1(old_Rn) - get_half_0(old_Rm));
    set_field(proc.reg(d), 31, 16, get_bits(diff,16,1));
    sum = (get_half_0(old_Rn) + get_half_1(old_Rm));
    set_field(proc.reg(d), 15, 0, get_bits(sum,16,1));
  }
}

// A4.1.74 SMLA<x><y>
void ARM_ISS::SMLA(const ARM_Processor::Condition cond,
                   const uint8_t d,
                   const uint8_t m,
                   const uint8_t n,
                   const uint8_t s,
                   const bool x,
                   const bool y) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t operand2;
  uint32_t operand1;
  if (ConditionPassed(cond)) {
    if ((x == 0)) {
      operand1 = SignExtend(get_half_0(old_Rm));
    } else {
      operand1 = SignExtend(get_half_1(old_Rm));
    }
    if ((y == 0)) {
      operand2 = SignExtend(get_half_0(old_Rs));
    } else {
      operand2 = SignExtend(get_half_1(old_Rs));
    }
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(((operand1 * operand2) + old_Rn));
    else
      proc.reg(d) = ((operand1 * operand2) + old_Rn);
    if (OverflowFrom_add2((operand1 * operand2), old_Rn)) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.75 SMLAD
void ARM_ISS::SMLAD(const bool X,
                    const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t product2;
  uint32_t product1;
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    if ((X == 1)) {
      operand2 = rotate_right(old_Rs, 16);
    } else {
      operand2 = old_Rs;
    }
    product1 = (get_half_0(old_Rm) * get_half_0(operand2));
    product2 = (get_half_1(old_Rm) * get_half_1(operand2));
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(((old_Rn + product1) + product2));
    else
      proc.reg(d) = ((old_Rn + product1) + product2);
    if (OverflowFrom_add3(old_Rn, product1, product2)) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.76 SMLAL
void ARM_ISS::SMLAL(const bool S,
                    const ARM_Processor::Condition cond,
                    const uint8_t dHi,
                    const uint8_t dLo,
                    const uint8_t m,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  if (ConditionPassed(cond)) {
    proc.reg(dLo) = (get_bits((old_Rm * old_Rs),31,0) + proc.reg(dLo));
    proc.reg(dHi) = ((get_bits((old_Rm * old_Rs),63,32) + proc.reg(dHi)) + CarryFrom_add2(get_bits((old_Rm * old_Rs),31,0), proc.reg(dLo)));
    if ((S == 1)) {
      proc.cpsr.N_flag = ((proc.reg(dHi)>>31)&1);
      proc.cpsr.Z_flag = (((proc.reg(dHi) == 0) && (proc.reg(dLo) == 0))? 1: 0);
    }
  }
}

// A4.1.77 SMLAL<x><y>
void ARM_ISS::SMLAL(const ARM_Processor::Condition cond,
                    const uint8_t dHi,
                    const uint8_t dLo,
                    const uint8_t m,
                    const uint8_t s,
                    const bool x,
                    const bool y) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t operand2;
  uint32_t operand1;
  if (ConditionPassed(cond)) {
    if ((x == 0)) {
      operand1 = SignExtend(get_half_0(old_Rm));
    } else {
      operand1 = SignExtend(get_half_1(old_Rm));
    }
    if ((y == 0)) {
      operand2 = SignExtend(get_half_0(old_Rs));
    } else {
      operand2 = SignExtend(get_half_1(old_Rs));
    }
    proc.reg(dLo) = (proc.reg(dLo) + (operand1 * operand2));
    proc.reg(dHi) = ((proc.reg(dHi) + (((operand1 * operand2) < 0)? 0xFFFFFFFF: 0)) + CarryFrom_add2(proc.reg(dLo), (operand1 * operand2)));
  }
}

// A4.1.78 SMLALD
void ARM_ISS::SMLALD(const bool X,
                     const ARM_Processor::Condition cond,
                     const uint8_t dHi,
                     const uint8_t dLo,
                     const uint8_t m,
                     const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  uint64_t result;
  uint32_t product2;
  uint32_t product1;
  uint32_t operand2;
  uint64_t accvalue;
  if (ConditionPassed(cond)) {
    if ((X == 1)) {
      operand2 = rotate_right(old_Rs, 16);
    } else {
      operand2 = old_Rs;
    }
    set_field(accvalue, 31, 0, proc.reg(dLo));
    set_field(accvalue, 63, 32, proc.reg(dHi));
    product1 = (get_half_0(old_Rm) * get_half_0(operand2));
    product2 = (get_half_1(old_Rm) * get_half_1(operand2));
    result = ((accvalue + product1) + product2);
    proc.reg(dLo) = get_bits(result,31,0);
    proc.reg(dHi) = get_bits(result,63,32);
  }
}

// A4.1.79 SMLAW<y>
void ARM_ISS::SMLAW(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n,
                    const uint8_t s,
                    const bool y) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    if ((y == 0)) {
      operand2 = SignExtend(get_half_0(old_Rs));
    } else {
      operand2 = SignExtend(get_half_1(old_Rs));
    }
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((get_bits((old_Rm * operand2),47,16) + old_Rn));
    else
      proc.reg(d) = (get_bits((old_Rm * operand2),47,16) + old_Rn);
    if (OverflowFrom_add2(get_bits((old_Rm * operand2),47,16), old_Rn)) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.80 SMLSD
void ARM_ISS::SMLSD(const bool X,
                    const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t product2;
  uint32_t product1;
  uint32_t operand2;
  uint32_t diffofproducts;
  if (ConditionPassed(cond)) {
    if ((X == 1)) {
      operand2 = rotate_right(old_Rs, 16);
    } else {
      operand2 = old_Rs;
    }
    product1 = (get_half_0(old_Rm) * get_half_0(operand2));
    product2 = (get_half_1(old_Rm) * get_half_1(operand2));
    diffofproducts = (product1 - product2);
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((old_Rn + diffofproducts));
    else
      proc.reg(d) = (old_Rn + diffofproducts);
    if (OverflowFrom_add2(old_Rn, diffofproducts)) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.81 SMLSLD
void ARM_ISS::SMLSLD(const bool X,
                     const ARM_Processor::Condition cond,
                     const uint8_t dHi,
                     const uint8_t dLo,
                     const uint8_t m,
                     const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  uint64_t result;
  uint32_t product2;
  uint32_t product1;
  uint32_t operand2;
  uint64_t accvalue;
  if (ConditionPassed(cond)) {
    if ((X == 1)) {
      operand2 = rotate_right(old_Rs, 16);
    } else {
      operand2 = old_Rs;
    }
    set_field(accvalue, 31, 0, proc.reg(dLo));
    set_field(accvalue, 63, 32, proc.reg(dHi));
    product1 = (get_half_0(old_Rm) * get_half_0(operand2));
    product2 = (get_half_1(old_Rm) * get_half_1(operand2));
    result = ((accvalue + product1) - product2);
    proc.reg(dLo) = get_bits(result,31,0);
    proc.reg(dHi) = get_bits(result,63,32);
  }
}

// A4.1.82 SMMLA
void ARM_ISS::SMMLA(const bool R,
                    const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t value;
  if (ConditionPassed(cond)) {
    value = (old_Rm * old_Rs);
    if ((R == 1)) {
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(get_bits((((static_cast<uint64_t>(old_Rn) << 32) + value) + 0x80000000),63,32));
      else
        proc.reg(d) = get_bits((((static_cast<uint64_t>(old_Rn) << 32) + value) + 0x80000000),63,32);
    } else {
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(get_bits(((static_cast<uint64_t>(old_Rn) << 32) + value),63,32));
      else
        proc.reg(d) = get_bits(((static_cast<uint64_t>(old_Rn) << 32) + value),63,32);
    }
  }
}

// A4.1.83 SMMLS
void ARM_ISS::SMMLS(const bool R,
                    const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t value;
  if (ConditionPassed(cond)) {
    value = (old_Rm * old_Rs);
    if ((R == 1)) {
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(get_bits((((static_cast<uint64_t>(old_Rn) << 32) - value) + 0x80000000),63,32));
      else
        proc.reg(d) = get_bits((((static_cast<uint64_t>(old_Rn) << 32) - value) + 0x80000000),63,32);
    } else {
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(get_bits(((static_cast<uint64_t>(old_Rn) << 32) - value),63,32));
      else
        proc.reg(d) = get_bits(((static_cast<uint64_t>(old_Rn) << 32) - value),63,32);
    }
  }
}

// A4.1.84 SMMUL
void ARM_ISS::SMMUL(const bool R,
                    const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t value;
  if (ConditionPassed(cond)) {
    if ((R == 1)) {
      value = ((old_Rm * old_Rs) + 0x80000000);
    } else {
      value = (old_Rm * old_Rs);
    }
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(get_bits(value,63,32));
    else
      proc.reg(d) = get_bits(value,63,32);
  }
}

// A4.1.85 SMUAD
void ARM_ISS::SMUAD(const bool X,
                    const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t product2;
  uint32_t product1;
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    if ((X == 1)) {
      operand2 = rotate_right(old_Rs, 16);
    } else {
      operand2 = old_Rs;
    }
    product1 = (get_half_0(old_Rm) * get_half_0(operand2));
    product2 = (get_half_1(old_Rm) * get_half_1(operand2));
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((product1 + product2));
    else
      proc.reg(d) = (product1 + product2);
    if (OverflowFrom_add2(product1, product2)) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.86 SMUL<x><y>
void ARM_ISS::SMUL(const ARM_Processor::Condition cond,
                   const uint8_t d,
                   const uint8_t m,
                   const uint8_t s,
                   const bool x,
                   const bool y) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t operand2;
  uint32_t operand1;
  if (ConditionPassed(cond)) {
    if ((x == 0)) {
      operand1 = SignExtend(get_half_0(old_Rm));
    } else {
      operand1 = SignExtend(get_half_1(old_Rm));
    }
    if ((y == 0)) {
      operand2 = SignExtend(get_half_0(old_Rs));
    } else {
      operand2 = SignExtend(get_half_1(old_Rs));
    }
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((operand1 * operand2));
    else
      proc.reg(d) = (operand1 * operand2);
  }
}

// A4.1.87 SMULL
void ARM_ISS::SMULL(const bool S,
                    const ARM_Processor::Condition cond,
                    const uint8_t dHi,
                    const uint8_t dLo,
                    const uint8_t m,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  if (ConditionPassed(cond)) {
    proc.reg(dHi) = get_bits((old_Rm * old_Rs),63,32);
    proc.reg(dLo) = get_bits((old_Rm * old_Rs),31,0);
    if ((S == 1)) {
      proc.cpsr.N_flag = ((proc.reg(dHi)>>31)&1);
      proc.cpsr.Z_flag = (((proc.reg(dHi) == 0) && (proc.reg(dLo) == 0))? 1: 0);
    }
  }
}

// A4.1.88 SMULW<y>
void ARM_ISS::SMULW(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t s,
                    const bool y) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    if ((y == 0)) {
      operand2 = SignExtend(get_half_0(old_Rs));
    } else {
      operand2 = SignExtend(get_half_1(old_Rs));
    }
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(get_bits((old_Rm * operand2),47,16));
    else
      proc.reg(d) = get_bits((old_Rm * operand2),47,16);
  }
}

// A4.1.89 SMUSD
void ARM_ISS::SMUSD(const bool X,
                    const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t product2;
  uint32_t product1;
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    if ((X == 1)) {
      operand2 = rotate_right(old_Rs, 16);
    } else {
      operand2 = old_Rs;
    }
    product1 = (get_half_0(old_Rm) * get_half_0(operand2));
    product2 = (get_half_1(old_Rm) * get_half_1(operand2));
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((product1 - product2));
    else
      proc.reg(d) = (product1 - product2);
  }
}

// A4.1.90 SRS
void ARM_ISS::SRS(const uint32_t start_address) {
  size_t processor_id;
  uint32_t physical_address;
  uint32_t address;
  processor_id = ExecutingProcessor();
  address = start_address;
  proc.mmu.write_word(address, proc.reg(14));
  if (Shared(address)) {
    physical_address = TLB(address);
    ClearExclusiveByAddress(physical_address, processor_id, 4);
  }
  if (CurrentModeHasSPSR()) {
    proc.mmu.write_word((address + 4), proc.spsr());
    if (Shared((address + 4))) {
      physical_address = TLB((address + 4));
      ClearExclusiveByAddress(physical_address, processor_id, 4);
    }
  } else {
    unpredictable();
  }
}

// A4.1.91 SSAT
void ARM_ISS::SSAT(const ARM_Processor::Condition cond,
                   const uint8_t d,
                   const uint8_t m,
                   const uint8_t sat_imm,
                   const bool shift,
                   const uint8_t shift_imm) {
  const uint32_t old_Rm = proc.reg(m);
  uint32_t operand;
  if (ConditionPassed(cond)) {
    if ((shift == 1)) {
      if ((shift_imm == 0)) {
        operand = get_bits(asr(old_Rm, 32),31,0);
      } else {
        operand = get_bits(asr(old_Rm, shift_imm),31,0);
      }
    } else {
      operand = get_bits((old_Rm << shift_imm),31,0);
    }
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(SignedSat(operand, (sat_imm + 1)));
    else
      proc.reg(d) = SignedSat(operand, (sat_imm + 1));
    if (SignedDoesSat(operand, (sat_imm + 1))) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.92 SSAT16
void ARM_ISS::SSAT16(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t sat_imm) {
  const uint32_t old_Rm = proc.reg(m);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 15, 0, SignedSat(get_half_0(old_Rm), (sat_imm + 1)));
    set_field(proc.reg(d), 31, 16, SignedSat(get_half_1(old_Rm), (sat_imm + 1)));
    if ((SignedDoesSat(get_half_0(old_Rm), (sat_imm + 1)) | SignedDoesSat(get_half_1(old_Rm), (sat_imm + 1)))) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.93 SSUB16
void ARM_ISS::SSUB16(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t diff;
  if (ConditionPassed(cond)) {
    diff = (get_half_0(old_Rn) - get_half_0(old_Rm));
    set_field(proc.reg(d), 15, 0, get_half_0(diff));
    set_field(proc.cpsr.GE, 1, 0, ((diff >= 0)? 3: 0));
    diff = (get_half_1(old_Rn) - get_half_1(old_Rm));
    set_field(proc.reg(d), 31, 16, get_half_0(diff));
    set_field(proc.cpsr.GE, 3, 2, ((diff >= 0)? 3: 0));
  }
}

// A4.1.94 SSUB8
void ARM_ISS::SSUB8(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t diff;
  if (ConditionPassed(cond)) {
    diff = (get_byte_0(old_Rn) - get_byte_0(old_Rm));
    set_field(proc.reg(d), 7, 0, get_byte_0(diff));
    set_bit(proc.cpsr.GE, 0, ((diff >= 0)? 1: 0));
    diff = (get_byte_1(old_Rn) - get_byte_1(old_Rm));
    set_field(proc.reg(d), 15, 8, get_byte_0(diff));
    set_bit(proc.cpsr.GE, 1, ((diff >= 0)? 1: 0));
    diff = (get_byte_2(old_Rn) - get_byte_2(old_Rm));
    set_field(proc.reg(d), 23, 16, get_byte_0(diff));
    set_bit(proc.cpsr.GE, 2, ((diff >= 0)? 1: 0));
    diff = (get_byte_3(old_Rn) - get_byte_3(old_Rm));
    set_field(proc.reg(d), 31, 24, get_byte_0(diff));
    set_bit(proc.cpsr.GE, 3, ((diff >= 0)? 1: 0));
  }
}

// A4.1.95 SSUBADDX
void ARM_ISS::SSUBADDX(const ARM_Processor::Condition cond,
                       const uint8_t d,
                       const uint8_t m,
                       const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  uint32_t diff;
  if (ConditionPassed(cond)) {
    diff = (get_half_1(old_Rn) - get_half_0(old_Rm));
    set_field(proc.reg(d), 31, 16, get_half_0(diff));
    set_field(proc.cpsr.GE, 3, 2, ((diff >= 0)? 3: 0));
    sum = (get_half_0(old_Rn) + get_half_1(old_Rm));
    set_field(proc.reg(d), 15, 0, get_half_0(sum));
    set_field(proc.cpsr.GE, 1, 0, ((sum >= 0)? 3: 0));
  }
}

// A4.1.96 STC
void ARM_ISS::STC(const ARM_Processor::Condition cond,
                  const uint8_t cp_num,
                  const uint32_t start_address) {
  size_t processor_id;
  uint32_t physical_address;
  uint32_t address;
  processor_id = ExecutingProcessor();
  if (ConditionPassed(cond)) {
    address = start_address;
    proc.mmu.write_word(address, proc.coproc(cp_num)->value());
    if (Shared(address)) {
      physical_address = TLB(address);
      ClearExclusiveByAddress(physical_address, processor_id, 4);
    }
    while (proc.coproc(cp_num)->NotFinished())
      address = (address + 4);
    proc.mmu.write_word(address, proc.coproc(cp_num)->value());
    if (Shared(address)) {
      physical_address = TLB(address);
      ClearExclusiveByAddress(physical_address, processor_id, 4);
    }
  }
}

// A4.1.97 STM (1)
void ARM_ISS::STM_1(const ARM_Processor::Condition cond,
                    const uint16_t register_list,
                    const uint32_t start_address) {
  size_t processor_id;
  uint32_t physical_address;
  uint32_t address;
  processor_id = ExecutingProcessor();
  if (ConditionPassed(cond)) {
    address = start_address;
    for (size_t i = 0; i<15; ++i) {
      if ((((register_list>>i)&1) == 1)) {
        proc.mmu.write_word(address, proc.reg(i));
        address = (address + 4);
        if (Shared(address)) {
          physical_address = TLB(address);
          ClearExclusiveByAddress(physical_address, processor_id, 4);
        }
      }
    }
  }
}

// A4.1.98 STM (2)
void ARM_ISS::STM_2(const ARM_Processor::Condition cond,
                    const uint16_t register_list,
                    const uint32_t start_address) {
  size_t processor_id;
  uint32_t physical_address;
  uint32_t address;
  processor_id = ExecutingProcessor();
  if (ConditionPassed(cond)) {
    address = start_address;
    for (size_t i = 0; i<15; ++i) {
      if ((((register_list>>i)&1) == 1)) {
        proc.mmu.write_word(address, proc.reg(i,ARM_Processor::usr));
        address = (address + 4);
        if (Shared(address)) {
          physical_address = TLB(address);
          ClearExclusiveByAddress(physical_address, processor_id, 4);
        }
      }
    }
  }
}

// A4.1.99 STR
void ARM_ISS::STR(const uint32_t address,
                  const ARM_Processor::Condition cond,
                  const uint8_t d) {
  size_t processor_id;
  uint32_t physical_address;
  processor_id = ExecutingProcessor();
  if (ConditionPassed(cond)) {
    proc.mmu.write_word(address, proc.reg(d));
    if (Shared(address)) {
      physical_address = TLB(address);
      ClearExclusiveByAddress(physical_address, processor_id, 4);
    }
  }
}

// A4.1.100 STRB
void ARM_ISS::STRB(const uint32_t address,
                   const ARM_Processor::Condition cond,
                   const uint8_t d) {
  size_t processor_id;
  uint32_t physical_address;
  processor_id = ExecutingProcessor();
  if (ConditionPassed(cond)) {
    proc.mmu.write_byte(address, get_byte_0(proc.reg(d)));
    if (Shared(address)) {
      physical_address = TLB(address);
      ClearExclusiveByAddress(physical_address, processor_id, 1);
    }
  }
}

// A4.1.101 STRBT
void ARM_ISS::STRBT(const uint32_t address,
                    const ARM_Processor::Condition cond,
                    const uint8_t d) {
  size_t processor_id;
  uint32_t physical_address;
  processor_id = ExecutingProcessor();
  if (ConditionPassed(cond)) {
    proc.mmu.write_byte(address, get_byte_0(proc.reg(d)));
    if (Shared(address)) {
      physical_address = TLB(address);
      ClearExclusiveByAddress(physical_address, processor_id, 1);
    }
  }
}

// A4.1.102 STRD
void ARM_ISS::STRD(const uint32_t address,
                   const ARM_Processor::Condition cond,
                   const uint8_t d) {
  size_t processor_id;
  uint32_t physical_address;
  processor_id = ExecutingProcessor();
  if (ConditionPassed(cond)) {
    if ((((is_even(d) && d!=14) && (get_bits(address,1,0) == 0)) && ((proc.cp15.get_reg1_Ubit() == 1) || (((address>>2)&1) == 0)))) {
      proc.mmu.write_word(address, proc.reg(d));
      proc.mmu.write_word((address + 4), proc.reg((d + 1)));
    } else {
      unpredictable();
    }
    if (Shared(address)) {
      physical_address = TLB(address);
      ClearExclusiveByAddress(physical_address, processor_id, 4);
    }
    if (Shared((address + 4))) {
      physical_address = TLB((address + 4));
      ClearExclusiveByAddress(physical_address, processor_id, 4);
    }
  }
}

// A4.1.103 STREX
void ARM_ISS::STREX(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  size_t processor_id;
  uint32_t physical_address;
  if (ConditionPassed(cond)) {
    processor_id = ExecutingProcessor();
    physical_address = TLB(old_Rn);
    if (IsExclusiveLocal(physical_address, processor_id, 4)) {
      if ((Shared(old_Rn) == 1)) {
        if (IsExclusiveGlobal(physical_address, processor_id, 4)) {
          proc.mmu.write_word(old_Rn, old_Rm);
          if (d==ARM_Processor::PC)
            proc.set_pc_raw(0);
          else
            proc.reg(d) = 0;
          ClearExclusiveByAddress(physical_address, processor_id, 4);
        } else {
          if (d==ARM_Processor::PC)
            proc.set_pc_raw(1);
          else
            proc.reg(d) = 1;
        }
      } else {
        proc.mmu.write_word(old_Rn, old_Rm);
        if (d==ARM_Processor::PC)
          proc.set_pc_raw(0);
        else
          proc.reg(d) = 0;
      }
    } else {
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(1);
      else
        proc.reg(d) = 1;
    }
    ClearExclusiveLocal(processor_id);
  }
}

// A4.1.104 STRH
void ARM_ISS::STRH(const uint32_t address,
                   const ARM_Processor::Condition cond,
                   const uint8_t d) {
  size_t processor_id;
  uint32_t physical_address;
  processor_id = ExecutingProcessor();
  if (ConditionPassed(cond)) {
    if ((proc.cp15.get_reg1_Ubit() == 0)) {
      if ((((address>>0)&1) == 0)) {
        proc.mmu.write_half(address, get_half_0(proc.reg(d)));
      } else {
        unpredictable();
      }
    } else {
      proc.mmu.write_half(address, get_half_0(proc.reg(d)));
    }
    if (Shared(address)) {
      physical_address = TLB(address);
      ClearExclusiveByAddress(physical_address, processor_id, 2);
    }
  }
}

// A4.1.105 STRT
void ARM_ISS::STRT(const uint32_t address,
                   const ARM_Processor::Condition cond,
                   const uint8_t d) {
  size_t processor_id;
  uint32_t physical_address;
  processor_id = ExecutingProcessor();
  if (ConditionPassed(cond)) {
    proc.mmu.write_word(address, proc.reg(d));
    if (Shared(address)) {
      physical_address = TLB(address);
      ClearExclusiveByAddress(physical_address, processor_id, 4);
    }
  }
}

// A4.1.106 SUB
void ARM_ISS::SUB(const bool S,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t n,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((old_Rn - shifter_operand));
    else
      proc.reg(d) = (old_Rn - shifter_operand);
    if (((S == 1) && d==15)) {
      if (CurrentModeHasSPSR()) {
        proc.cpsr = proc.spsr();
      } else {
        unpredictable();
      }
    } else {
      if ((S == 1)) {
        proc.cpsr.N_flag = ((proc.reg(d)>>31)&1);
        proc.cpsr.Z_flag = ((proc.reg(d) == 0)? 1: 0);
        proc.cpsr.C_flag = NOT(BorrowFrom_sub2(old_Rn, shifter_operand));
        proc.cpsr.V_flag = OverflowFrom_sub2(old_Rn, shifter_operand);
      }
    }
  }
}

// A4.1.107 SWI
void ARM_ISS::SWI(const ARM_Processor::Condition cond) {
  if (ConditionPassed(cond)) {
    proc.reg(14,ARM_Processor::svc) = next_instr();
    proc.spsr(ARM_Processor::svc) = proc.cpsr;
    proc.cpsr.mode = ARM_Processor::svc;
    proc.cpsr.T_flag = 0;
    proc.cpsr.I_flag = 1;
    proc.cpsr.E_flag = proc.cp15.get_reg1_EEbit();
    if (high_vectors_configured()) {
      proc.set_pc_raw(0xFFFF0008);
    } else {
      proc.set_pc_raw(0x00000008);
    }
  }
}

// A4.1.108 SWP
void ARM_ISS::SWP(const uint32_t address,
                  const ARM_Processor::Condition cond,
                  const uint8_t d,
                  const uint8_t m) {
  const uint32_t old_Rm = proc.reg(m);
  uint32_t temp;
  size_t processor_id;
  uint32_t physical_address;
  processor_id = ExecutingProcessor();
  if (ConditionPassed(cond)) {
    if ((proc.cp15.get_reg1_Ubit() == 0)) {
      temp = rotate_right(proc.mmu.read_word(address), (8 * get_bits(address,1,0)));
      proc.mmu.write_word(address, old_Rm);
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(temp);
      else
        proc.reg(d) = temp;
    } else {
      temp = proc.mmu.read_word(address);
      proc.mmu.write_word(address, old_Rm);
      if (d==ARM_Processor::PC)
        proc.set_pc_raw(temp);
      else
        proc.reg(d) = temp;
    }
    if (Shared(address)) {
      physical_address = TLB(address);
      ClearExclusiveByAddress(physical_address, processor_id, 4);
    }
  }
}

// A4.1.109 SWPB
void ARM_ISS::SWPB(const uint32_t address,
                   const ARM_Processor::Condition cond,
                   const uint8_t d,
                   const uint8_t m) {
  const uint32_t old_Rm = proc.reg(m);
  uint8_t temp;
  size_t processor_id;
  uint32_t physical_address;
  processor_id = ExecutingProcessor();
  if (ConditionPassed(cond)) {
    temp = proc.mmu.read_byte(address);
    proc.mmu.write_byte(address, get_byte_0(old_Rm));
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(temp);
    else
      proc.reg(d) = temp;
    if (Shared(address)) {
      physical_address = TLB(address);
      ClearExclusiveByAddress(physical_address, processor_id, 1);
    }
  }
}

// A4.1.110 SXTAB
void ARM_ISS::SXTAB(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n,
                    const uint8_t rotate) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    operand2 = rotate_right(old_Rm, (8 * rotate));
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((old_Rn + SignExtend(get_byte_0(operand2))));
    else
      proc.reg(d) = (old_Rn + SignExtend(get_byte_0(operand2)));
  }
}

// A4.1.111 SXTAB16
void ARM_ISS::SXTAB16(const ARM_Processor::Condition cond,
                      const uint8_t d,
                      const uint8_t m,
                      const uint8_t n,
                      const uint8_t rotate) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    operand2 = rotate_right(old_Rm, (8 * rotate));
    set_field(proc.reg(d), 15, 0, (get_half_0(old_Rn) + SignExtend(get_byte_0(operand2))));
    set_field(proc.reg(d), 31, 16, (get_half_1(old_Rn) + SignExtend(get_byte_2(operand2))));
  }
}

// A4.1.112 SXTAH
void ARM_ISS::SXTAH(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n,
                    const uint8_t rotate) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    operand2 = rotate_right(old_Rm, (8 * rotate));
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((old_Rn + SignExtend(get_half_0(operand2))));
    else
      proc.reg(d) = (old_Rn + SignExtend(get_half_0(operand2)));
  }
}

// A4.1.113 SXTB
void ARM_ISS::SXTB(const ARM_Processor::Condition cond,
                   const uint8_t d,
                   const uint8_t m,
                   const uint8_t rotate) {
  const uint32_t old_Rm = proc.reg(m);
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    operand2 = rotate_right(old_Rm, (8 * rotate));
    set_field(proc.reg(d), 31, 0, SignExtend(get_byte_0(operand2)));
  }
}

// A4.1.114 SXTB16
void ARM_ISS::SXTB16(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t rotate) {
  const uint32_t old_Rm = proc.reg(m);
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    operand2 = rotate_right(old_Rm, (8 * rotate));
    set_field(proc.reg(d), 15, 0, SignExtend(get_byte_0(operand2)));
    set_field(proc.reg(d), 31, 16, SignExtend(get_byte_2(operand2)));
  }
}

// A4.1.115 SXTH
void ARM_ISS::SXTH(const ARM_Processor::Condition cond,
                   const uint8_t d,
                   const uint8_t m,
                   const uint8_t rotate) {
  const uint32_t old_Rm = proc.reg(m);
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    operand2 = rotate_right(old_Rm, (8 * rotate));
    set_field(proc.reg(d), 31, 0, SignExtend(get_half_0(operand2)));
  }
}

// A4.1.116 TEQ
void ARM_ISS::TEQ(const ARM_Processor::Condition cond,
                  const uint8_t n,
                  const bool shifter_carry_out,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  uint32_t alu_out;
  if (ConditionPassed(cond)) {
    alu_out = (old_Rn ^ shifter_operand);
    proc.cpsr.N_flag = ((alu_out>>31)&1);
    proc.cpsr.Z_flag = ((alu_out == 0)? 1: 0);
    proc.cpsr.C_flag = shifter_carry_out;
  }
}

// A4.1.117 TST
void ARM_ISS::TST(const ARM_Processor::Condition cond,
                  const uint8_t n,
                  const bool shifter_carry_out,
                  const uint32_t shifter_operand) {
  const uint32_t old_Rn = proc.reg(n);
  uint32_t alu_out;
  if (ConditionPassed(cond)) {
    alu_out = (old_Rn & shifter_operand);
    proc.cpsr.N_flag = ((alu_out>>31)&1);
    proc.cpsr.Z_flag = ((alu_out == 0)? 1: 0);
    proc.cpsr.C_flag = shifter_carry_out;
  }
}

// A4.1.118 UADD16
void ARM_ISS::UADD16(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 15, 0, (get_half_0(old_Rn) + get_half_0(old_Rm)));
    set_field(proc.cpsr.GE, 1, 0, ((CarryFrom16_add2(get_half_0(old_Rn), get_half_0(old_Rm)) == 1)? 3: 0));
    set_field(proc.reg(d), 31, 16, (get_half_1(old_Rn) + get_half_1(old_Rm)));
    set_field(proc.cpsr.GE, 3, 2, ((CarryFrom16_add2(get_half_1(old_Rn), get_half_1(old_Rm)) == 1)? 3: 0));
  }
}

// A4.1.119 UADD8
void ARM_ISS::UADD8(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 7, 0, (get_byte_0(old_Rn) + get_byte_0(old_Rm)));
    set_bit(proc.cpsr.GE, 0, CarryFrom8_add2(get_byte_0(old_Rn), get_byte_0(old_Rm)));
    set_field(proc.reg(d), 15, 8, (get_byte_1(old_Rn) + get_byte_1(old_Rm)));
    set_bit(proc.cpsr.GE, 1, CarryFrom8_add2(get_byte_1(old_Rn), get_byte_1(old_Rm)));
    set_field(proc.reg(d), 23, 16, (get_byte_2(old_Rn) + get_byte_2(old_Rm)));
    set_bit(proc.cpsr.GE, 2, CarryFrom8_add2(get_byte_2(old_Rn), get_byte_2(old_Rm)));
    set_field(proc.reg(d), 31, 24, (get_byte_3(old_Rn) + get_byte_3(old_Rm)));
    set_bit(proc.cpsr.GE, 3, CarryFrom8_add2(get_byte_3(old_Rn), get_byte_3(old_Rm)));
  }
}

// A4.1.120 UADDSUBX
void ARM_ISS::UADDSUBX(const ARM_Processor::Condition cond,
                       const uint8_t d,
                       const uint8_t m,
                       const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  uint32_t diff;
  if (ConditionPassed(cond)) {
    sum = (get_half_1(old_Rn) + get_half_0(old_Rm));
    set_field(proc.reg(d), 31, 16, get_half_0(sum));
    set_field(proc.cpsr.GE, 3, 2, (CarryFrom16_add2(get_half_1(old_Rn), get_half_0(old_Rm))? 3: 0));
    diff = (get_half_0(old_Rn) - get_half_1(old_Rm));
    set_field(proc.reg(d), 15, 0, get_half_0(diff));
    set_field(proc.cpsr.GE, 1, 0, (BorrowFrom_sub2(get_half_0(old_Rn), get_half_1(old_Rm))? 3: 0));
  }
}

// A4.1.121 UHADD16
void ARM_ISS::UHADD16(const ARM_Processor::Condition cond,
                      const uint8_t d,
                      const uint8_t m,
                      const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  if (ConditionPassed(cond)) {
    sum = (get_half_0(old_Rn) + get_half_0(old_Rm));
    set_field(proc.reg(d), 15, 0, get_bits(sum,16,1));
    sum = (get_half_1(old_Rn) + get_half_1(old_Rm));
    set_field(proc.reg(d), 31, 16, get_bits(sum,16,1));
  }
}

// A4.1.122 UHADD8
void ARM_ISS::UHADD8(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  if (ConditionPassed(cond)) {
    sum = (get_byte_0(old_Rn) + get_byte_0(old_Rm));
    set_field(proc.reg(d), 7, 0, get_bits(sum,8,1));
    sum = (get_byte_1(old_Rn) + get_byte_1(old_Rm));
    set_field(proc.reg(d), 15, 8, get_bits(sum,8,1));
    sum = (get_byte_2(old_Rn) + get_byte_2(old_Rm));
    set_field(proc.reg(d), 23, 16, get_bits(sum,8,1));
    sum = (get_byte_3(old_Rn) + get_byte_3(old_Rm));
    set_field(proc.reg(d), 31, 24, get_bits(sum,8,1));
  }
}

// A4.1.123 UHADDSUBX
void ARM_ISS::UHADDSUBX(const ARM_Processor::Condition cond,
                        const uint8_t d,
                        const uint8_t m,
                        const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  uint32_t diff;
  if (ConditionPassed(cond)) {
    sum = (get_half_1(old_Rn) + get_half_0(old_Rm));
    set_field(proc.reg(d), 31, 16, get_bits(sum,16,1));
    diff = (get_half_0(old_Rn) - get_half_1(old_Rm));
    set_field(proc.reg(d), 15, 0, get_bits(diff,16,1));
  }
}

// A4.1.124 UHSUB16
void ARM_ISS::UHSUB16(const ARM_Processor::Condition cond,
                      const uint8_t d,
                      const uint8_t m,
                      const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t diff;
  if (ConditionPassed(cond)) {
    diff = (get_half_0(old_Rn) - get_half_0(old_Rm));
    set_field(proc.reg(d), 15, 0, get_bits(diff,16,1));
    diff = (get_half_1(old_Rn) - get_half_1(old_Rm));
    set_field(proc.reg(d), 31, 16, get_bits(diff,16,1));
  }
}

// A4.1.125 UHSUB8
void ARM_ISS::UHSUB8(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t diff;
  if (ConditionPassed(cond)) {
    diff = (get_byte_0(old_Rn) - get_byte_0(old_Rm));
    set_field(proc.reg(d), 7, 0, get_bits(diff,8,1));
    diff = (get_byte_1(old_Rn) - get_byte_1(old_Rm));
    set_field(proc.reg(d), 15, 8, get_bits(diff,8,1));
    diff = (get_byte_2(old_Rn) - get_byte_2(old_Rm));
    set_field(proc.reg(d), 23, 16, get_bits(diff,8,1));
    diff = (get_byte_3(old_Rn) - get_byte_3(old_Rm));
    set_field(proc.reg(d), 31, 24, get_bits(diff,8,1));
  }
}

// A4.1.126 UHSUBADDX
void ARM_ISS::UHSUBADDX(const ARM_Processor::Condition cond,
                        const uint8_t d,
                        const uint8_t m,
                        const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  uint32_t diff;
  if (ConditionPassed(cond)) {
    diff = (get_half_1(old_Rn) - get_half_0(old_Rm));
    set_field(proc.reg(d), 31, 16, get_bits(diff,16,1));
    sum = (get_half_0(old_Rn) + get_half_1(old_Rm));
    set_field(proc.reg(d), 15, 0, get_bits(sum,16,1));
  }
}

// A4.1.127 UMAAL
void ARM_ISS::UMAAL(const ARM_Processor::Condition cond,
                    const uint8_t dHi,
                    const uint8_t dLo,
                    const uint8_t m,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  uint64_t result;
  if (ConditionPassed(cond)) {
    result = (((old_Rm * old_Rs) + proc.reg(dLo)) + proc.reg(dHi));
    proc.reg(dLo) = get_bits(result,31,0);
    proc.reg(dHi) = get_bits(result,63,32);
  }
}

// A4.1.128 UMLAL
void ARM_ISS::UMLAL(const bool S,
                    const ARM_Processor::Condition cond,
                    const uint8_t dHi,
                    const uint8_t dLo,
                    const uint8_t m,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  if (ConditionPassed(cond)) {
    proc.reg(dLo) = (get_bits((old_Rm * old_Rs),31,0) + proc.reg(dLo));
    proc.reg(dHi) = ((get_bits((old_Rm * old_Rs),63,32) + proc.reg(dHi)) + CarryFrom_add2(get_bits((old_Rm * old_Rs),31,0), proc.reg(dLo)));
    if ((S == 1)) {
      proc.cpsr.N_flag = ((proc.reg(dHi)>>31)&1);
      proc.cpsr.Z_flag = (((proc.reg(dHi) == 0) && (proc.reg(dLo) == 0))? 1: 0);
    }
  }
}

// A4.1.129 UMULL
void ARM_ISS::UMULL(const bool S,
                    const ARM_Processor::Condition cond,
                    const uint8_t dHi,
                    const uint8_t dLo,
                    const uint8_t m,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  if (ConditionPassed(cond)) {
    proc.reg(dHi) = get_bits((old_Rm * old_Rs),63,32);
    proc.reg(dLo) = get_bits((old_Rm * old_Rs),31,0);
    if ((S == 1)) {
      proc.cpsr.N_flag = ((proc.reg(dHi)>>31)&1);
      proc.cpsr.Z_flag = (((proc.reg(dHi) == 0) && (proc.reg(dLo) == 0))? 1: 0);
    }
  }
}

// A4.1.130 UQADD16
void ARM_ISS::UQADD16(const ARM_Processor::Condition cond,
                      const uint8_t d,
                      const uint8_t m,
                      const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 15, 0, UnsignedSat_add16(get_half_0(old_Rn), get_half_0(old_Rm)));
    set_field(proc.reg(d), 31, 16, UnsignedSat_add16(get_half_1(old_Rn), get_half_1(old_Rm)));
  }
}

// A4.1.131 UQADD8
void ARM_ISS::UQADD8(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 7, 0, UnsignedSat_add8(get_byte_0(old_Rn), get_byte_0(old_Rm)));
    set_field(proc.reg(d), 15, 8, UnsignedSat_add8(get_byte_1(old_Rn), get_byte_1(old_Rm)));
    set_field(proc.reg(d), 23, 16, UnsignedSat_add8(get_byte_2(old_Rn), get_byte_2(old_Rm)));
    set_field(proc.reg(d), 31, 24, UnsignedSat_add8(get_byte_3(old_Rn), get_byte_3(old_Rm)));
  }
}

// A4.1.132 UQADDSUBX
void ARM_ISS::UQADDSUBX(const ARM_Processor::Condition cond,
                        const uint8_t d,
                        const uint8_t m,
                        const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 15, 0, UnsignedSat_sub16(get_half_0(old_Rn), get_half_1(old_Rm)));
    set_field(proc.reg(d), 31, 16, UnsignedSat_add16(get_half_1(old_Rn), get_half_0(old_Rm)));
  }
}

// A4.1.133 UQSUB16
void ARM_ISS::UQSUB16(const ARM_Processor::Condition cond,
                      const uint8_t d,
                      const uint8_t m,
                      const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 15, 0, UnsignedSat_sub16(get_half_0(old_Rn), get_half_0(old_Rm)));
    set_field(proc.reg(d), 31, 16, UnsignedSat_sub16(get_half_1(old_Rn), get_half_1(old_Rm)));
  }
}

// A4.1.134 UQSUB8
void ARM_ISS::UQSUB8(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 7, 0, UnsignedSat_sub8(get_byte_0(old_Rn), get_byte_0(old_Rm)));
    set_field(proc.reg(d), 15, 8, UnsignedSat_sub8(get_byte_1(old_Rn), get_byte_1(old_Rm)));
    set_field(proc.reg(d), 23, 16, UnsignedSat_sub8(get_byte_2(old_Rn), get_byte_2(old_Rm)));
    set_field(proc.reg(d), 31, 24, UnsignedSat_sub8(get_byte_3(old_Rn), get_byte_3(old_Rm)));
  }
}

// A4.1.135 UQSUBADDX
void ARM_ISS::UQSUBADDX(const ARM_Processor::Condition cond,
                        const uint8_t d,
                        const uint8_t m,
                        const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 31, 16, UnsignedSat_sub16(get_half_1(old_Rn), get_half_0(old_Rm)));
    set_field(proc.reg(d), 15, 0, UnsignedSat_add16(get_half_0(old_Rn), get_half_1(old_Rm)));
  }
}

// A4.1.136 USAD8
void ARM_ISS::USAD8(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t diff4;
  uint32_t diff3;
  uint32_t diff2;
  uint32_t diff1;
  if (ConditionPassed(cond)) {
    if ((get_byte_0(old_Rm) < get_byte_0(old_Rs))) {
      diff1 = (get_byte_0(old_Rs) - get_byte_0(old_Rm));
    } else {
      diff1 = (get_byte_0(old_Rm) - get_byte_0(old_Rs));
    }
    if ((get_byte_1(old_Rm) < get_byte_1(old_Rs))) {
      diff2 = (get_byte_1(old_Rs) - get_byte_1(old_Rm));
    } else {
      diff2 = (get_byte_1(old_Rm) - get_byte_1(old_Rs));
    }
    if ((get_byte_2(old_Rm) < get_byte_2(old_Rs))) {
      diff3 = (get_byte_2(old_Rs) - get_byte_2(old_Rm));
    } else {
      diff3 = (get_byte_2(old_Rm) - get_byte_2(old_Rs));
    }
    if ((get_byte_3(old_Rm) < get_byte_3(old_Rs))) {
      diff4 = (get_byte_3(old_Rs) - get_byte_3(old_Rm));
    } else {
      diff4 = (get_byte_3(old_Rm) - get_byte_3(old_Rs));
    }
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((((ZeroExtend(diff1) + ZeroExtend(diff2)) + ZeroExtend(diff3)) + ZeroExtend(diff4)));
    else
      proc.reg(d) = (((ZeroExtend(diff1) + ZeroExtend(diff2)) + ZeroExtend(diff3)) + ZeroExtend(diff4));
  }
}

// A4.1.137 USADA8
void ARM_ISS::USADA8(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n,
                     const uint8_t s) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  const uint32_t old_Rs = proc.reg(s);
  uint32_t diff4;
  uint32_t diff3;
  uint32_t diff2;
  uint32_t diff1;
  if (ConditionPassed(cond)) {
    if ((get_byte_0(old_Rm) < get_byte_0(old_Rs))) {
      diff1 = (get_byte_0(old_Rs) - get_byte_0(old_Rm));
    } else {
      diff1 = (get_byte_0(old_Rm) - get_byte_0(old_Rs));
    }
    if ((get_byte_1(old_Rm) < get_byte_1(old_Rs))) {
      diff2 = (get_byte_1(old_Rs) - get_byte_1(old_Rm));
    } else {
      diff2 = (get_byte_1(old_Rm) - get_byte_1(old_Rs));
    }
    if ((get_byte_2(old_Rm) < get_byte_2(old_Rs))) {
      diff3 = (get_byte_2(old_Rs) - get_byte_2(old_Rm));
    } else {
      diff3 = (get_byte_2(old_Rm) - get_byte_2(old_Rs));
    }
    if ((get_byte_3(old_Rm) < get_byte_3(old_Rs))) {
      diff4 = (get_byte_3(old_Rs) - get_byte_3(old_Rm));
    } else {
      diff4 = (get_byte_3(old_Rm) - get_byte_3(old_Rs));
    }
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(((((old_Rn + ZeroExtend(diff1)) + ZeroExtend(diff2)) + ZeroExtend(diff3)) + ZeroExtend(diff4)));
    else
      proc.reg(d) = ((((old_Rn + ZeroExtend(diff1)) + ZeroExtend(diff2)) + ZeroExtend(diff3)) + ZeroExtend(diff4));
  }
}

// A4.1.138 USAT
void ARM_ISS::USAT(const ARM_Processor::Condition cond,
                   const uint8_t d,
                   const uint8_t m,
                   const uint8_t sat_imm,
                   const bool shift,
                   const uint8_t shift_imm) {
  const uint32_t old_Rm = proc.reg(m);
  uint32_t operand;
  if (ConditionPassed(cond)) {
    if ((shift == 1)) {
      if ((shift_imm == 0)) {
        operand = get_bits(asr(old_Rm, 32),31,0);
      } else {
        operand = get_bits(asr(old_Rm, shift_imm),31,0);
      }
    } else {
      operand = get_bits((old_Rm << shift_imm),31,0);
    }
    if (d==ARM_Processor::PC)
      proc.set_pc_raw(UnsignedSat(operand, sat_imm));
    else
      proc.reg(d) = UnsignedSat(operand, sat_imm);
    if (UnsignedDoesSat(operand, sat_imm)) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.139 USAT16
void ARM_ISS::USAT16(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t sat_imm) {
  const uint32_t old_Rm = proc.reg(m);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 15, 0, UnsignedSat(get_half_0(old_Rm), sat_imm));
    set_field(proc.reg(d), 31, 16, UnsignedSat(get_half_1(old_Rm), sat_imm));
    if ((UnsignedDoesSat(get_half_0(old_Rm), sat_imm) | UnsignedDoesSat(get_half_1(old_Rm), sat_imm))) {
      proc.cpsr.Q_flag = 1;
    }
  }
}

// A4.1.140 USUB16
void ARM_ISS::USUB16(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 15, 0, (get_half_0(old_Rn) - get_half_0(old_Rm)));
    set_field(proc.cpsr.GE, 1, 0, (BorrowFrom_sub2(get_half_0(old_Rn), get_half_0(old_Rm))? 0: 3));
    set_field(proc.reg(d), 31, 16, (get_half_1(old_Rn) - get_half_1(old_Rm)));
    set_field(proc.cpsr.GE, 3, 2, (BorrowFrom_sub2(get_half_1(old_Rn), get_half_1(old_Rm))? 0: 3));
  }
}

// A4.1.141 USUB8
void ARM_ISS::USUB8(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 7, 0, (get_byte_0(old_Rn) - get_byte_0(old_Rm)));
    set_bit(proc.cpsr.GE, 0, NOT(BorrowFrom_sub2(get_byte_0(old_Rn), get_byte_0(old_Rm))));
    set_field(proc.reg(d), 15, 8, (get_byte_1(old_Rn) - get_byte_1(old_Rm)));
    set_bit(proc.cpsr.GE, 1, NOT(BorrowFrom_sub2(get_byte_1(old_Rn), get_byte_1(old_Rm))));
    set_field(proc.reg(d), 23, 16, (get_byte_2(old_Rn) - get_byte_2(old_Rm)));
    set_bit(proc.cpsr.GE, 2, NOT(BorrowFrom_sub2(get_byte_2(old_Rn), get_byte_2(old_Rm))));
    set_field(proc.reg(d), 31, 24, (get_byte_3(old_Rn) - get_byte_3(old_Rm)));
    set_bit(proc.cpsr.GE, 3, NOT(BorrowFrom_sub2(get_byte_3(old_Rn), get_byte_3(old_Rm))));
  }
}

// A4.1.142 USUBADDX
void ARM_ISS::USUBADDX(const ARM_Processor::Condition cond,
                       const uint8_t d,
                       const uint8_t m,
                       const uint8_t n) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t sum;
  uint32_t diff;
  if (ConditionPassed(cond)) {
    diff = (get_half_1(old_Rn) - get_half_0(old_Rm));
    set_field(proc.reg(d), 31, 16, get_half_0(diff));
    set_field(proc.cpsr.GE, 3, 2, (BorrowFrom_sub2(get_half_1(old_Rn), get_half_0(old_Rm))? 3: 0));
    sum = (get_half_0(old_Rn) + get_half_1(old_Rm));
    set_field(proc.reg(d), 15, 0, get_half_0(sum));
    set_field(proc.cpsr.GE, 1, 0, (CarryFrom16_add2(get_half_0(old_Rn), get_half_1(old_Rm))? 3: 0));
  }
}

// A4.1.143 UXTAB
void ARM_ISS::UXTAB(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n,
                    const uint8_t rotate) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    operand2 = (rotate_right(old_Rm, (8 * rotate)) & 0x000000ff);
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((old_Rn + operand2));
    else
      proc.reg(d) = (old_Rn + operand2);
  }
}

// A4.1.144 UXTAB16
void ARM_ISS::UXTAB16(const ARM_Processor::Condition cond,
                      const uint8_t d,
                      const uint8_t m,
                      const uint8_t n,
                      const uint8_t rotate) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    operand2 = (rotate_right(old_Rm, (8 * rotate)) & 0x00ff00ff);
    set_field(proc.reg(d), 15, 0, (get_half_0(old_Rn) + get_half_0(operand2)));
    set_field(proc.reg(d), 31, 16, (get_half_1(old_Rn) + get_byte_2(operand2)));
  }
}

// A4.1.145 UXTAH
void ARM_ISS::UXTAH(const ARM_Processor::Condition cond,
                    const uint8_t d,
                    const uint8_t m,
                    const uint8_t n,
                    const uint8_t rotate) {
  const uint32_t old_Rm = proc.reg(m);
  const uint32_t old_Rn = proc.reg(n);
  uint32_t operand2;
  if (ConditionPassed(cond)) {
    operand2 = (rotate_right(old_Rm, (8 * rotate)) & 0x0000ffff);
    if (d==ARM_Processor::PC)
      proc.set_pc_raw((old_Rn + operand2));
    else
      proc.reg(d) = (old_Rn + operand2);
  }
}

// A4.1.146 UXTB
void ARM_ISS::UXTB(const ARM_Processor::Condition cond,
                   const uint8_t d,
                   const uint8_t m,
                   const uint8_t rotate) {
  const uint32_t old_Rm = proc.reg(m);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 31, 0, (rotate_right(old_Rm, (8 * rotate)) & 0x000000ff));
  }
}

// A4.1.147 UXTB16
void ARM_ISS::UXTB16(const ARM_Processor::Condition cond,
                     const uint8_t d,
                     const uint8_t m,
                     const uint8_t rotate) {
  const uint32_t old_Rm = proc.reg(m);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 31, 0, (rotate_right(old_Rm, (8 * rotate)) & 0x00ff00ff));
  }
}

// A4.1.148 UXTH
void ARM_ISS::UXTH(const ARM_Processor::Condition cond,
                   const uint8_t d,
                   const uint8_t m,
                   const uint8_t rotate) {
  const uint32_t old_Rm = proc.reg(m);
  if (ConditionPassed(cond)) {
    set_field(proc.reg(d), 31, 0, (rotate_right(old_Rm, (8 * rotate)) & 0x0000ffff));
  }
}
