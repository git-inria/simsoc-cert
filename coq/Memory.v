(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Memory.
*)

Set Implicit Arguments.

Require Import Bitvec ZArith Coqlib Util Integers.
Import Int.

Open Scope Z_scope.

(****************************************************************************)
(** A2.8 Unaligned access support (p. 76) *)
(****************************************************************************)

(****************************************************************************)
(** Addressing modes (p. 411) *)
(****************************************************************************)

Inductive addressing_mode : Type :=
  | dataProcessing_oprand
  | LS_word_or_UnsignedByte
  | miscellaneous_LS
  | LS_multiple
  | LS_CP.

(****************************************************************************)
(** Memory *)
(****************************************************************************)

(*
Inductive endian_model : Type := LowE | BE_8 | BE_32.

Inductive mmu_read_result : Set :=
  | MRR_std : word -> mmu_read_result
  | MMR_exn : state (* to be updated later *) -> mmu_read_result.

Inductive mmu_write_result : Set :=
  | MWR_std : (address -> word) -> mmu_write_result
  | MWR_exn : state (* to be updated later *) -> mmu_write_result.

(* FIXME: this MMU does not check the last two bits;
          and the physical address is the same as the virtual address *)
Definition mmu_read_word (s: state) (a: address) : mmu_read_result :=
  MRR_std (mem s a).

(*FIXME: to finish
Definition mmu_read_halfword (s: state) (a: address) : mmu_read_result :=
  let all := mem s a[31#2] in
  if a[1] then 
  MRR_std ().
*)

Record block_contents : Type := mk_block {
  addr : address;
  length : Z;
  contents : word
}.

Record memory : Type := mk_mem {
  blocks : address -> Z -> block_contents
}.
*)