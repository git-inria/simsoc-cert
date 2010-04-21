(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Global state.
*)

Set Implicit Arguments.

Require Import Proc SCC.

Record state : Type := mk_state {
  (* Processor *)
  proc : Proc.state;
  (* System control coprocessor *)
  scc : SCC.state
}.

Definition set_proc s x := mk_state x (scc s).
Definition set_scc s x := mk_state (proc s) x.

Definition update_proc x s := set_proc s x.
Definition update_scc x s := set_scc s x.

Definition update_cpsr w s := update_proc (update_cpsr w (proc s)) s.
Definition update_spsr m w s := update_proc (update_spsr m w (proc s)) s.
Definition update_reg k w s := update_proc (update_reg k w (proc s)) s.
