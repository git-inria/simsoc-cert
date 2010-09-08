/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* Features that are not implemented yet. */

#ifndef ARM_NOT_IMPLEMENTED_H
#define ARM_NOT_IMPLEMENTED_H

#include "common.h"

/* no MMU */
inline uint32_t TLB(uint32_t virtual_address) {return virtual_address;}

/* Shared memory is not implemented */
inline size_t ExecutingProcessor() {return 0;}
inline bool Shared(uint32_t a) {return false;}
inline void MarkExclusiveGlobal(uint32_t a, size_t b, uint32_t c) {}
inline void MarkExclusiveLocal(uint32_t a, size_t b, uint32_t c) {}
inline void ClearExclusiveByAddress(uint32_t a, size_t b, uint32_t c) {}
inline void ClearExclusiveLocal(size_t a) {}
inline bool IsExclusiveLocal(uint32_t a, size_t b, uint32_t c) {return true;}
inline bool IsExclusiveGlobal(uint32_t a, size_t b, uint32_t c) {return true;}

/* Jazelle is not implemented */
inline bool JE_bit_of_Main_Configuration_register() {return false;}
inline uint32_t jpc_SUB_ARCHITECTURE_DEFINED_value() {return 0;}
inline uint32_t invalidhandler_SUB_ARCHITECTURE_DEFINED_value() {return 0;}
inline bool Jazelle_Extension_accepts_opcode_at(uint32_t a) {return false;}
inline bool CV_bit_of_Jazelle_OS_Control_register() {return false;}
inline void Start_opcode_execution_at(uint32_t a) {}
inline bool IMPLEMENTATION_DEFINED_CONDITION() {return false;}

/* for BKPT */
inline bool not_overridden_by_debug_hardware() {return true;}

#endif /* ARM_NOT_IMPLEMENTED_H */
