(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Global state.
*)

Set Implicit Arguments.

Require Import Proc Arm SCC Bitvec List.

Record state : Type := mk_state {
  (* Processor *)
  proc : Proc.state;
  (* System control coprocessor *)
  scc : SCC.state
}.

Definition cpsr (s : state) : word := cpsr (proc s).

Definition set_cpsr (s : state) (w : word) : state :=
  mk_state (set_cpsr (proc s) w) (scc s).

Definition spsr (s : state) (o : option exn_mode) : word := spsr (proc s) o.

Definition set_spsr (s : state) (o : option exn_mode) (w : word) : state :=
  mk_state (set_spsr (proc s) o w) (scc s).

Definition reg_content_of_mode (s : state) (m : proc_mode) (k : regnum) : word
  := reg_content_of_mode (proc s) m k.

Definition reg_content (s : state) (k : regnum) : word :=
  reg_content (proc s) k.

Definition set_reg_of_mode (s : state) (m : proc_mode) (k : regnum) (w : word)
  : state := mk_state (set_reg_of_mode (proc s) m k w) (scc s).

Definition set_reg (s : state) (k : regnum) (w : word) : state :=
  mk_state (set_reg (proc s) k w) (scc s).

Definition exns (s : state) : list exception := exns (proc s).

Definition set_exns (s : state) (es : list exception) : state :=
  mk_state (set_exns (proc s) es) (scc s).

Definition mode (s : state) : proc_mode := mode (proc s).

Definition cur_inst_address (s : state) : word := cur_inst_address (proc s).

Definition next_inst_address (s : state) : word := next_inst_address (proc s).

Definition CurrentModeHasSPSR (s : state) : bool := CurrentModeHasSPSR (mode s).

Definition InAPrivilegedMode (s : state) : bool := InAPrivilegedMode (mode s).

Definition ConditionPassed (s : state) (op : opcode) : bool :=
  ConditionPassed (cspr s) op.
