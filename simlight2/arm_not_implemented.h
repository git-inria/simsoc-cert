/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* Features that are not implemented yet. */

#ifndef ARM_NOT_IMPLEMENTED_H
#define ARM_NOT_IMPLEMENTED_H

#include "common.h"

struct SLv6_Processor;

/* no IRQ or FIQ */
static inline void update_pending_flags(struct SLv6_Processor *proc) {}

/* no MMU */
static inline uint32_t slv6_TLB(uint32_t virtual_address) {return virtual_address;}

/* Shared memory is not implemented */
static inline size_t ExecutingProcessor() {return 0;}
static inline bool Shared(uint32_t a) {return false;}
static inline void MarkExclusiveGlobal(uint32_t a, size_t b, uint32_t c) {}
static inline void MarkExclusiveLocal(uint32_t a, size_t b, uint32_t c) {}
static inline void ClearExclusiveByAddress3(uint32_t a, size_t b, uint32_t c) {}
static inline void ClearExclusiveByAddress2(uint32_t a, uint32_t c) {}
static inline void ClearExclusiveLocal(size_t a) {}
static inline bool IsExclusiveLocal(uint32_t a, size_t b, uint32_t c) {return true;}
static inline bool IsExclusiveGlobal(uint32_t a, size_t b, uint32_t c) {return true;}

/* Jazelle is not implemented */
static inline bool JE_bit_of_Main_Configuration_register() {return false;}
static inline uint32_t jpc_SUB_ARCHITECTURE_DEFINED_value() {return 0;}
static inline uint32_t invalidhandler_SUB_ARCHITECTURE_DEFINED_value() {return 0;}
static inline bool Jazelle_Extension_accepts_opcode_at(uint32_t a) {return false;}
static inline bool CV_bit_of_Jazelle_OS_Control_register() {return false;}
static inline void Start_opcode_execution_at(uint32_t a) {}
static inline bool IMPLEMENTATION_DEFINED_CONDITION() {return false;}

/* for BKPT */
static inline bool not_overridden_by_debug_hardware() {return true;}

/* for coprocessors */
extern void dependent_operation(struct SLv6_Processor *proc, uint8_t n);
extern void load(struct SLv6_Processor *proc, uint8_t n, uint32_t x);
extern void send(struct SLv6_Processor *proc, uint8_t n, uint32_t x);
extern bool NotFinished(struct SLv6_Processor *proc, uint8_t n);
extern uint32_t first_value(struct SLv6_Processor *proc, uint8_t n);
extern uint32_t second_value(struct SLv6_Processor *proc, uint8_t n);
extern uint32_t value(struct SLv6_Processor *proc, uint8_t n);

#endif /* ARM_NOT_IMPLEMENTED_H */
