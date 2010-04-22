(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Processor state.
*)

Set Implicit Arguments.

Require Import Arm Bitvec List Util Integers.
Import Int.

(*WARNING: invariant to preserve:

proc_mode_of_word (cpsr s) = Some m -> mode s = m.

To preserve this invariant, always use the function set_cpsr defined
hereafter. *)

Record state : Type := mk_state {
  (* Current program status register *)
  cpsr : word;
  (* Saved program status registers *)
  spsr : option exn_mode -> word;
  (* Registers *)
  reg : register -> word;
  (* Raised exceptions *)
  exns : list exception;
  (* Processor mode *)
  mode : proc_mode
}.

Definition set_cpsr (s : state) (w : word) : state :=
  match proc_mode_of_word w with
    | Some m => mk_state w (spsr s) (reg s) (exns s) m
    | None => mk_state w (spsr s) (reg s) (exns s) (mode s) (*FIXME?*)
  end.

Definition set_cpsr_bit (s : state) (n : nat) (v : word) : state :=
  set_cpsr s (update_bit n v (cpsr s)).

Definition set_cpsr_bits (s : state) (p n : nat) (v : word) : state :=
  set_cpsr s (update_bits p n v (cpsr s)).

Definition set_spsr (s : state) (o : option exn_mode) (w : word) : state :=
  mk_state (cpsr s)
  (update_map opt_exn_mode_eqdec (spsr s) o w)
  (reg s) (exns s) (mode s).

Definition set_reg_mode (s : state) (m : proc_mode) (k : regnum) (w : word)
  : state :=
  mk_state (cpsr s) (spsr s)
  (update_map register_eqdec (reg s) (reg_mode m k) w)
  (exns s) (mode s).

Definition set_reg (s : state) (k : regnum) (w : word) : state :=
  set_reg_mode s (mode s) k w.

Definition reg_content_mode (s : state) (m : proc_mode) (k : regnum)
  : word := reg s (reg_mode m k).

Definition reg_content (s : state) (k : regnum) : word :=
  reg_content_mode s (mode s) k.

Definition set_exns (s : state) (es : list exception) : state :=
  mk_state (cpsr s) (spsr s) (reg s) es (mode s).

Definition add_exn (s : state) (e : exception) : state :=
  set_exns s (insert e (exns s)).

(****************************************************************************)
(** Current instruction address
cf. A2.4.3 Register 15 and the program counter,
Reading the program counter (p. 47) *)
(****************************************************************************)

(*IMPROVE: add cur_inst_address as new field in state?*)
Definition cur_inst_address (s : state) : word := sub (reg_content s PC) w8.

(****************************************************************************)
(** Next instruction address
cf. A2.7.1 Address space (p. 70) *)
(****************************************************************************)

Definition next_inst_address (s : state) : word :=
  (*REMARK: [add (cur_inst_address s m PC) w4] is replaced by: *)
  sub (reg_content s PC) w4.
