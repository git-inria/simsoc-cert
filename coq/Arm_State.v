(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Global state. We assume that there is only one processor and only one
coprocessor: the system control coprocessor (CP15). Hence, there is no
shared memory. We do not handle virtual memory either. *)

Set Implicit Arguments.

Require Import Arm_Proc Arm Arm_SCC Bitvec List.

Record state : Type := mk_state {
  (* Processor *)
  proc : Arm_Proc.state;
  (* System control coprocessor *)
  scc : Arm_SCC.state
}.

(****************************************************************************)
(** Processor access/update functions *)
(****************************************************************************)

Definition cpsr (s : state) : word := cpsr (proc s).

Definition set_cpsr (s : state) (w : word) : state :=
  mk_state (set_cpsr (proc s) w) (scc s).

Definition set_cpsr_bit (s : state) (n : nat) (w : word) : state :=
  mk_state (set_cpsr_bit (proc s) n w) (scc s).

Definition spsr (s : state) (o : exn_mode) : word := spsr (proc s) o.

Definition set_spsr (s : state) (o : exn_mode) (w : word) : state :=
  mk_state (set_spsr (proc s) o w) (scc s).

Definition reg_content_mode (s : state) (m : proc_mode) (k : regnum) : word
  := reg_content_mode (proc s) m k.

Definition reg_content (s : state) (k : regnum) : word :=
  reg_content (proc s) k.

Definition set_reg_mode (s : state) (m : proc_mode) (k : regnum) (w : word)
  : state := mk_state (set_reg_mode (proc s) m k w) (scc s).

Definition set_reg (s : state) (k : regnum) (w : word) : state :=
  mk_state (set_reg (proc s) k w) (scc s).

Definition exns (s : state) : list exception := exns (proc s).

Definition add_exn (s : state) (e : exception) : state :=
  mk_state (add_exn (proc s) e) (scc s).

Definition mode (s : state) : proc_mode := mode (proc s).

Definition address_of_current_instruction (s : state) : word
  := address_of_current_instruction (proc s).

Definition address_of_next_instruction (s : state) : word
  := address_of_next_instruction (proc s).

(****************************************************************************)
(** System control coprocessor and Memory access/update functions *)
(****************************************************************************)

Definition CP15_reg1 (s : state) : word := CP15_reg1 (scc s).

Definition high_vectors_configured (s : state) : bool :=
  high_vectors_configured (scc s).

Definition read (s : state) (a : word) (n : size) : word :=
  read (scc s) a n.

Definition write (s : state) (a : word) (n : size) (w : word) : state :=
  mk_state (proc s) (write (scc s) a n w).

(****************************************************************************)
(** TLB (p. 87)

If CP15 register 1 bit[0] (Mbit) is set, TLB(<Rm>) returns the
physical address corresponding to the virtual address in Rm for the
executing processor's current process ID and TLB entries. If Mbit is
not set, or the system does not implement a virtual to physical
translation, it returns the value in Rm. *)
(****************************************************************************)

(*IMPROVE: handle virtual memory*)
Definition TLB (s : state) (w : word) : word := w.

(****************************************************************************)
(** Shared (p. 87)

If CP15 register 1 bit[0] (Mbit) is set, Shared(<Rm>) returns the
value of the shared memory region attribute corresponding to the
virtual address in Rm for the executing processor's current process ID
and TLB entries for the VMSA, or the PMSA region descriptors. If Mbit
is not set, the value returned is a function of the memory system
behavior (see Chapter B4 Virtual Memory System Architecture and
Chapter B5 Protected Memory System Architecture). *)
(****************************************************************************)

(*REMARK: returns always false since there is only one processor *)
Definition Shared (s : state) (w : word) : bool := false. (*FIXME*)

(****************************************************************************)
(** ExecutingProcessor (p. 87)

returns a value distinct amongst all processors in a given system,
corresponding to the processor executing the operation. *)
(****************************************************************************)

(*REMARK: since there is only one processor, we can return any value *)
Definition ExecutingProcessor (s : state) : nat := 0%nat.

(****************************************************************************)
(** MarkExclusiveGlobal (p. 87)

MarkExclusiveGlobal(<physical_address>,<processor_id>,<size>) records
the fact that processor <processor_id> has requested exclusive access
covering at least <size> bytes from address <physical_address>. The
size of region marked as exclusive is IMPLEMENTATION DEFINED, up to a
limit of 128 bytes, and no smaller than <size>, and aligned in the
address space to the size of the region. It is UNPREDICTABLE whether
this causes any previous request for exclusive access to any other
address by the same processor to be cleared. *)
(****************************************************************************)

Definition MarkExclusiveGlobal (s : state) (addr : word) (pid : nat)
  (size : nat) : state := s. (*FIXME*)

(****************************************************************************)
(** MarkExclusiveLocal (p. 87)

MarkExclusiveLocal(<physical_address>,<processor_id>,<size>) records
in a local record the fact that processor <processor_id> has requested
exclusive access to an address covering at least <size> bytes from
address <physical_address>. The size of the region marked as exclusive
is IMPLEMENTATION DEFINED, and can at its largest cover the whole of
memory, but is no smaller than <size>, and is aligned in the address
space to the size of the region. It is IMPLEMENTATION DEFINED whether
this also performs a
MarkExclusiveGlobal(<physical_address>,<processor_id>,<size>). *)
(****************************************************************************)

Definition MarkExclusiveLocal (s : state) (addr : word) (pid : nat)
  (size : nat) : state := s. (*FIXME*)

(****************************************************************************)
(** IsExclusiveGlobal (p. 87)

IsExclusiveGlobal(<physical_address>,<processor_id>,<size>) returns
TRUE if the processor <processor_id> has marked in a global record an
address range as exclusive access requested which covers at least the
<size> bytes from address <physical_address>. It is IMPLEMENTATION
DEFINED whether it returns TRUE or FALSE if a global record has marked
a different address as exclusive access requested. If no address is
marked in a global record as exclusive access,
IsExclusiveGlobal(<physical_address>,<processor_id>,<size>) will
return FALSE. *)
(****************************************************************************)

Definition IsExclusiveGlobal (s : state) (addr : word) (pid : nat)
  (size : nat) : bool := false. (*FIXME*)

(****************************************************************************)
(** IsExclusiveLocal (p. 88)

IsExclusiveLocal(<physical_address>,<processor_id>,<size>) returns
TRUE if the processor <processor_id> has marked an address range as
exclusive access requested which covers at least the <size> bytes from
address <physical_address>. It is IMPLEMENTATION DEFINED whether this
function returns TRUE or FALSE if the address marked as exclusive
access requested does not cover all of the <size> bytes from address
<physical_address>. If no address is marked as exclusive access
requested, then this function returns FALSE. It is IMPLEMENTATION
DEFINED whether this result is ANDed with the result of an
IsExclusiveGlobal(<physical_address>,<processor_id>,<size>). *)
(****************************************************************************)

Definition IsExclusiveLocal (s : state) (addr : word) (pid : nat)
  (size : nat) : bool := false. (*FIXME*)

(****************************************************************************)
(** ClearExclusiveByAddress (p. 88)

ClearExclusiveByAddress(<physical_address>,<processor_id>,<size>)
clears the global records of all processors, other than
<processor_id>, that an address region including any of the bytes
between <physical_address> and (<physical_address>+<size>-1) has had a
request for an exclusive access.  It is IMPLEMENTATION DEFINED whether
the equivalent global record of the processor <processor_id> is also
cleared if any of the bytes between <physical_address> and
(<physical_address>+<size>-1) have had a request for an exclusive
access, or if any other address has had a request for an exclusive
access. *)
(****************************************************************************)

Definition ClearExclusiveByAddress (s : state) (addr: word) (pid : nat)
  (size : nat) : state := s. (*FIXME*)

(****************************************************************************)
(** ClearExclusiveLocal (p. 88)

ClearExclusiveLocal(<processor_id>) clears the local record of
processor <processor_id> that an address has had a request for an
exclusive access. It is IMPLEMENTATION DEFINED whether this operation
also clears the global record of processor <processor_id> that an
address has had a request for an exclusive access. *)
(****************************************************************************)

Definition ClearExclusiveLocal (s : state) (pid : nat) : state := s. (*FIXME*)
