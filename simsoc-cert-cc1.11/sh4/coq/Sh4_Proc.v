(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.

Processor state.
*)

Set Implicit Arguments.

Require Import Sh4 Bitvec List Util.

(*WARNING: invariant to preserve:

proc_mode_of_word (cpsr s) = Some m -> mode s = m.

To preserve this invariant, always use the function set_cpsr defined
hereafter. *)

Record state : Type := mk_state {
  (* Current program status register *)
  cpsr : word;
  (* Registers *)
  reg : register -> word;
  (* Raised exceptions *)
  exns : list exception;
  (* Processor mode *)
  mode : proc_mode
}.


Definition set_cpsr (s : state) (w : word) : state :=
  match proc_mode_of_word w with
    | Some m => mk_state w (reg s) (exns s) m
    | None => mk_state w (reg s) (exns s) (mode s) (*FIXME?*)
  end.

Definition set_cpsr_bit (s : state) (n : nat) (w : word) : state :=
  set_cpsr s (set_bit n w (cpsr s)).

Definition reg_content_mode (s : state) (m : proc_mode) (k : regnum) : word :=
  reg s (reg_mode m k).

Definition reg_content (s : state) (k : regnum) : word :=
  reg_content_mode s (mode s) k.

Definition set_reg_mode (s : state) (m : proc_mode) (k : regnum) (w : word) :
  state :=
  mk_state (cpsr s)
  (update_map register_eqdec (reg s) (reg_mode m k) w)
  (exns s) (mode s).

Definition set_reg (s : state) (k : regnum) (w : word) : state :=
  set_reg_mode s (mode s) k w.

Definition set_exns (s : state) (es : list exception) : state :=
  mk_state (cpsr s) (reg s) es (mode s).

Definition add_exn (s : state) (e : exception) : state :=
  set_exns s (insert e (exns s)).

(****************************************************************************)
(** Current instruction address *)
(****************************************************************************)

Definition address_of_current_instruction (s : state) : word :=
  sub (reg_content s PC) (repr 8).