(* This file describe the relation between COQ and C state for ARM *)

(*Require Import Globalenvs Memory.*)
Require Import Csyntax Csem AST Coqlib Integers Values Maps. 
Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec.
Require Import adc_compcert New_Memory New_Globalenvs.

(* load/store in loc env*)
Definition store_value_of_type' (ty_dest: type) (m: Mem.mem) (loc: block) (ofs: int) (v: val) : option Mem.mem :=
  match access_mode ty_dest with
  | By_value chunk => Mem.storev chunk m (Vptr loc ofs) v
  | By_reference => None
  | By_nothing => None
  end.

Definition load_value_of_type' (ty: type) (m: Mem.mem) (b: block) (ofs: int) : option val :=
  match access_mode ty with
  | By_value chunk => Mem.loadv chunk m (Vptr b ofs)
  | By_reference => Some (Vptr b ofs)
  | By_nothing => None
  end.

(* Initial local environment, an empty PTree contents var location & type*)
Definition env0 := (PTree.empty (block * type)).

(* Initialize the memory with program p defined in adc_compcert*)
Definition mem1 := Genv.init_mem p. 

(* Allocate a type in memory *)
Definition alloc_loc_var (t: type) (ofs:int) := 
  match mem1 with
    |Some m=>let (m',b):= Mem.alloc m ofs (sizeof t) in Some b
    |None=>None
  end.

(* put new local variable and return new environment *)
Definition build_env (id:ident) (t:type) (ofs :int) (e:env):= 
  match (alloc_loc_var t ofs) with
    |Some b => 
      PTree.set id (b,t) e
    |None => e
  end.

Require Import  Cnotations.

Definition build_env_sr (e : env) :=
  build_env background uint32 Int.zero
  (build_env mode uint32 Int.zero
  (build_env T_flag uint8 Int.zero
  (build_env F_flag uint8 Int.zero
  (build_env I_flag uint8 Int.zero
  (build_env A_flag uint8 Int.zero
  (build_env E_flag uint8 Int.zero
  (build_env GE3 uint8 Int.zero
  (build_env GE2 uint8 Int.zero
  (build_env GE1 uint8 Int.zero
  (build_env GE0 uint8 Int.zero
  (build_env J_flag uint8 Int.zero
  (build_env Q_flag uint8 Int.zero  
  (build_env V_flag uint8 Int.zero
  (build_env C_flag uint8 Int.zero
  (build_env Z_flag uint8 Int.zero
  (build_env N_flag uint8 Int.zero e)))))))))))))))).

Definition build_env_cpsr (e : env) :=
  build_env cpsr typ_SLv6_StatusRegister Int.zero e.

Definition build_env_spsrs (e : env) :=
  build_env spsrs (Tarray typ_SLv6_StatusRegister 5) Int.zero e.

Definition build_env_mmu (e : env) :=
  build_env adc_compcert.mem (`*` uint8) Int.zero
  (build_env _end uint32 Int.zero
  (build_env size uint32 Int.zero
  (build_env begin uint32 Int.zero e))).


(* Check the block which stores N_flag*)
Definition nflag_blk :=
  match (PTree.get N_flag env1) with
    |Some (b,t) => Some b
    |None => None
  end.

(* store value of cpsr to memory*)
Definition store_cpsr_bit (m:Mem.mem) (id:ident) (e:env) (ofs:offset) (v:val) :=
  match m with
    |Some m=>(match (PTree.get id e) with
      |Some (b,t)=>store_value_of_type' t m b ofs v
      |None=>None end)
    |None=>None
  end.

(* map the N flag of COQ ARM to CompcertC ARM*)
(*Definition cpsr_proj (coqcpsr: word) :=
  let nflag := coqcpsr[31] in
  let zflag := coqcpsr[30] in
  let cflag := coqcpsr[29] in
  let vflag := coqcpsr[28] in
  let qflag := coqcpsr[27] in
  let jflag := coqcpsr[24] in
  let ge0 := coqcpsr[16] in
  let ge1 := coqcpsr[17] in
  let ge2 := coqcpsr[18] in
  let ge3 := coqcpsr[19] in
  let eflag := coqcpsr[9] in
  let aflag := coqcpsr[8] in
  let iflag := coqcpsr[7] in
  let fflag := coqcpsr[6] in
  let tflag := coqcpsr[5] in
  let bg := add coqcpsr[23 # 20] coqcpsr[15 # 10] in
*)

(* Get the N_flag value from memory*)
(*Definition nflag_val :=
  match cpsr_map (repr 0) with
    |Some m => 
      (match (PTree.get N_flag env0) with
         |Some (b,t) => load_value_of_type' t m b Int.zero
         |None => None
       end)
    |None => None
  end.*)

(* Boolean function to check the equivalence of two cpsr*)
(*Definition equiv_cpsr (coqcpsr : word) : bool =
  let eq_nflag n := Int.eq coqcpsr[31] n in
  (*let eq_zflag z := Int.eq coqcpsr[30] z in
  let eq_cflag c := Int.eq coqcpsr[29] c in
  let eq_vflag v := Int.eq coqcpsr[28] v in*)
    match nflag_val with
      |Some n => eq_nflag n
      |None => false
    end.
*)

(*
Set Printing Depth 10.
Transparent Mem.alloc.
About Mem.alloc.
Transparent Mem.range_perm_dec.
About Mem.range_perm_dec.
Transparent Mem.store.
Opaque Mem.valid_access_dec.
Eval lazy in ccpsr_val.

Theorem tt : {true = true}+{True}.
right; exact I.
Qed.

About tt.
Opaque tt.
About tt.
Transparent tt.
About tt.

Transparent Mem.range_perm_dec.
About Mem.range_perm_dec.

Check ccpsr_val.
Print val.*)