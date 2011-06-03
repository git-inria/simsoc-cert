(* This file describe the relation between COQ and C state for ARM *)

Require Import Globalenvs Memory.
Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors. 
Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import adc_compcert.
(*Require Import New_Memory New_Globalenvs.*)

(*
(* load/store local variables of type t*)
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

Definition store_value_of_type':=store_value_of_type.
Definition load_value_of_type':=load_value_of_type.*)

(* Initial local environment, an empty PTree contents var location & type*)
Definition env0 := (PTree.empty (block * type)).

(* Initialize the memory with program p defined in adc_compcert*)
Definition mem0 := Genv.init_mem p. 

(* If an option val is Some integer then return the integer value else return zero*)
Definition load_val (v : option val):word:=
  match v with
    |Some (Vint v')=> v'                     
    |_ => Int.zero
  end.

(* Find the offset for elements in a struct*)
(* If there is no variable id in struct t then the returned offset will be zero
   (this location is then the same as for t);
   later, if you want to L/S a value from this location, it will return None
 *)

Definition ofs_of_fld (f_id:AST.ident) (fl:fieldlist) :word:=
  match field_offset f_id fl with
    | Error _ => Int.zero
    | OK r => repr r
  end.

(* offset of each element in Processor Tstruct *)
Definition cpsr_ofs:int:=ofs_of_fld cpsr fld_proc.

Definition spsr_ofs:int:=ofs_of_fld spsrs fld_proc.

Definition mode_ofs:int:=
  add (ofs_of_fld cpsr fld_proc) (ofs_of_fld mode fld_sr).

Definition reg_ofs (id:AST.ident):int:=ofs_of_fld id fld_proc.

Definition mmu_ofs:int:=ofs_of_fld mmu_ptr fld_proc.

Definition mem_ofs:int:=ofs_of_fld adc_compcert.mem fld_mmu.

Definition cp15_ofs:int:=ofs_of_fld cp15 fld_proc.

Definition pc_ofs:int:=ofs_of_fld pc fld_proc.

Definition id_ofs:int:=ofs_of_fld adc_compcert.id fld_proc.

Definition jump_ofs:int:=ofs_of_fld jump fld_proc.

Definition proc_loc (m:Mem.mem) (e:env):option val:=
  match e!proc with
    |Some(b,_)=>load_value_of_type (Tpointer typ_SLv6_Processor) m b Int.zero
    |None=>None
  end.

(* Projection from C parameters to COQ parameters*)
(* If in local env the parameter of ADC (S, cond, d or n) exists,
   then return the value of it else return zero*)

Definition param_val (id:AST.ident) (m:Mem.mem) (e:env):val:=
  match e!id with
    |Some(b,t)=>
      let ov:=load_value_of_type t m b Int.zero in
        match ov with
          |Some v=>v
          |None=>Vundef
        end
    |None=>Vundef
  end.

Definition varg_proj (v:val):int:=
  match v with
    |Vint v'=>v'
    |_=>Int.zero
  end.

Definition S_proj (m:Mem.mem) (e:env):bool:=
  bool_of_word (varg_proj (param_val S m e)).

Definition cond_proj (m:Mem.mem) (e:env):opcode:= 
  let c:=condition (varg_proj (param_val cond m e)) in
    match c with
      |Some c'=>c'
      |None=>AL
    end.

Definition d_proj (m:Mem.mem) (e:env):regnum:=
  mk_regnum (varg_proj (param_val d m e)).

Definition n_proj (m:Mem.mem) (e:env):regnum:=
  mk_regnum (varg_proj (param_val n m e)).

Definition so_proj (m:Mem.mem) (e:env):word:=
  varg_proj (param_val shifter_operand m e).

Definition find_field (id:AST.ident) (ofs:int) (m:Mem.mem) (e:env)
  :option val:=
  match proc_loc m e with
    |Some(Vptr b o) => Some (Vptr b (add o ofs))
    |_=>None
  end.

Definition find_cpsr (m:Mem.mem) (e:env):option val:=
  find_field cpsr cpsr_ofs m e.

Definition find_spsr (m:Mem.mem) (e:env):option val:=
  find_field spsr spsr_ofs m e.

Definition find_reg (rid:AST.ident) (m:Mem.mem) (e:env):option val:=
  find_field rid (ofs_of_fld rid fld_proc) m e.

Definition find_cp15 (m:Mem.mem) (e:env):option val:=
  find_field cp15 cp15_ofs m e.

Definition find_id (m:Mem.mem) (e:env):option val:=
  find_field adc_compcert.id id_ofs m e.

Definition find_jump (m:Mem.mem) (e:env):option val:=
  find_field jump jump_ofs m e.

(* If cpsr can be found, use the location of [cpsr] and the offset of 
   mode in StatusRegister struct to get location of [mode]*)
(* The mode field in cpsr and spsr should be the same. 
   And the element of spsrs array which is in use should correspond to the same mode.
   And the register array in use, should also corresponds to this mode.*)
Definition find_mode (m:Mem.mem) (e:env):option val:=
  match find_cpsr m e with
    |Some(Vptr b ofs)=>Some(Vptr b (add ofs mode_ofs))
    |_=>None
  end.

(* If in local environment the variable [porc] exists,
   then return the pointer of [proc] field [mmu_ptr].
   From this MMU struct, returns the pointer to the field [mem]*)
Definition find_mem (m:Mem.mem) (e:env):option val:=
  match proc_loc m e with
    |Some(Vptr bp op)=>
      let mmu_p:=
        load_value_of_type (Tpointer typ_SLv6_MMU) m bp (add op mmu_ofs) 
        in
        match mmu_p with
          |Some(Vptr bm om)=>
            load_value_of_type (Tpointer(Tint I8 Unsigned)) m bm (add om mem_ofs)
          |_=>None
        end
    |_=>None
  end.

(* If in local environment the variable [proc] exists
   then return the pointer of [proc] field [pc]*)
(* the pointer to [pc] should point to the exact location of
   the 16th element in array [user_regs]*)
Definition find_pc (m:Mem.mem) (e:env):option val:=
  match proc_loc m e with
    |Some(Vptr b ofs)=>
      load_value_of_type (Tpointer (Tint I32 Unsigned)) m b ofs
    |_=>None
  end.

Definition pc_usereg15 (m:Mem.mem) (e:env):Prop:=
  find_pc m e = find_reg user_regs m e.

(* From a StateRegister Tstruct to word*)
(* Every bit is transformed from uint8 to one bit *)
Definition sr_proj (m:Mem.mem) (b:block) (ofs:int) :word:=
  let load_val_of id tp :=
    load_val (load_value_of_type tp m b 
      (add ofs (ofs_of_fld id fld_sr))) in
  let nflag := load_val_of N_flag (Tint I8 Unsigned) in
  let zflag := load_val_of Z_flag (Tint I8 Unsigned) in
  let cflag := load_val_of C_flag (Tint I8 Unsigned) in
  let vflag := load_val_of V_flag (Tint I8 Unsigned) in
  let qflag := load_val_of Q_flag (Tint I8 Unsigned) in
  let jflag := load_val_of J_flag (Tint I8 Unsigned) in
  let ge0 := load_val_of GE0 (Tint I8 Unsigned) in
  let ge1 := load_val_of GE1 (Tint I8 Unsigned) in
  let ge2 := load_val_of GE2 (Tint I8 Unsigned) in
  let ge3 := load_val_of GE3 (Tint I8 Unsigned) in
  let eflag := load_val_of E_flag (Tint I8 Unsigned) in
  let aflag := load_val_of A_flag (Tint I8 Unsigned) in
  let iflag :=  load_val_of I_flag (Tint I8 Unsigned) in
  let fflag := load_val_of F_flag (Tint I8 Unsigned) in
  let tflag := load_val_of T_flag (Tint I8 Unsigned) in
  let md := load_val_of mode (Tint I32 Unsigned) in
(* according to P49,
   Implementations must read reversed bits as 0 and ignore writes to them.
   So no setting bits for the reversed bits*)
  let bg := Int.zero in
    (set_bit Nbit nflag
    (set_bit Zbit zflag
    (set_bit Cbit cflag
    (set_bit Vbit vflag
    (set_bit Qbit qflag
    (set_bit Jbit jflag
(* set bits 16 to 19 is set GEbits*)
    (set_bit 19 ge3
    (set_bit 18 ge2
    (set_bit 17 ge1
    (set_bit 16 ge0
    (set_bit Ebit eflag
    (set_bit Abit aflag
    (set_bit Ibit iflag 
    (set_bit Fbit fflag 
    (set_bit Tbit tflag 
(* set bits 0 to 4 is set Mbits*)
    (set_bits 4 0 md Int.zero)))))))))))))))).

(* Projection form C cpsr to COQ cpsr*)
(* If the location of cpsr is found, then project C cpsr to a word
   else return zero*)
Definition cpsr_proj (m:Mem.mem) (e:env) :word:=
  match find_cpsr m e with
    |Some (Vptr b ofs) => sr_proj m b ofs
    |_ => Int.zero
  end.

(* Projection from C spsr to COQ spsr*)
(* If the location of spsr of specified exception mode is found, 
   then project C cpsr to a word else return zero*)
Definition spsr_proj (m:Mem.mem) (e:env) (em:exn_mode):word:=
  let ofs o n:=add o (repr (n*sizeof typ_SLv6_StatusRegister)) in
  match find_spsr m e with
    |Some(Vptr b o)=>
      match em with
        |fiq=>sr_proj m b (ofs o 0)
        |irq=>sr_proj m b (ofs o 1)
        |svc=>sr_proj m b (ofs o 2)
        |abt=>sr_proj m b (ofs o 3)
        |und=>sr_proj m b (ofs o 4)
      end
    |_=>Int.zero
  end.

(* Projection from C mode in cpsr, to COQ mode*)
(* If the location of mode is found, 
   then project C mode to a proc_mode else return default user mode*)
(* The mode in cpsr should indecate which spsr mode is and which kind of register
   is used*)
Definition mode_proj (m:Mem.mem) (e:env) :proc_mode:=
  let om:=match find_mode m e with
    |Some(Vptr b ofs)=>
      proc_mode_of_word (load_val 
        (load_value_of_type (Tint I32 Unsigned) m b ofs))
    |_=>None
  end
  in 
  match om with
    |Some md=>md
    |None=>usr
  end.

(* Projection from C reg to COQ reg*)
(* If the location of reg is found, and by knowing which register mode
   and which register number it is, return the value of this register.
   else return zero*)
Definition regs_proj (m:Mem.mem) (e:env) (r:register):word:=
  let load_reg id n m e:=
    match find_reg id m e with 
    |Some(Vptr b ofs)=>
      load_val (load_value_of_type 
        (Tint I32 Unsigned) m b (add ofs (repr n))) 
    |_=>Int.zero
  end
    in
  match r with
    | R k => load_reg user_regs k m e
    | R_svc k _=> load_reg svc_regs k m e
    | R_abt k _=> load_reg abt_regs k m e
    | R_und k _=> load_reg und_regs k m e
    | R_irq k _=> load_reg irq_regs k m e
    | R_fiq k _=> load_reg fiq_regs k m e
  end.

(* Projection from C memory to COQ memory*)
(* If the location of memory is found, using the address to
   get the content of such memory block, else return zero*)
Definition mem_proj (m:Mem.mem) (e:env) (ad:address):word:=
  match find_mem m e with
    |Some(Vptr b ofs)=>
      load_val (load_value_of_type 
        (Tint I8 Unsigned) m b (add ofs (word_of_address ad)))
    |_=>Int.zero
  end.

(* Projection from C cp15 to COQ SCC register*)
(* If the location of cp15 is found, 
   get the value of ee_bit u_bit and v_bit to set the bits in
   COQ SCC reg*)
Definition screg_proj (m:Mem.mem) (e:env) (r:regnum):word:=
  match find_cp15 m e with
    |Some(Vptr b ofs)=>
      let regbit id:=
        load_val (load_value_of_type (Tint I8 Unsigned) m b
        (add ofs (ofs_of_fld id fld_sc))) in
        let ee := regbit ee_bit in
        let u := regbit u_bit in
        let v := regbit v_bit in
        set_bit Vbit v (set_bit Ubit u (set_bit EEbit ee Int.zero))
    |_=>Int.zero
  end.

(* Projection from C proc to COQ state. exn in COQ proc state is assigned by
   a nil exception list*)
Definition proc_proj (m:Mem.mem) (e:env):Arm6_State.state:=
  Arm6_State.mk_state 
  (Arm6_Proc.mk_state (cpsr_proj m e) (spsr_proj m e) (regs_proj m e) nil (mode_proj m e))
  (Arm6_SCC.mk_state (screg_proj m e) (mem_proj m e)).

(*Inductive proc_proj' (m:Mem.mem) (e:env):result:=
  |state_ok : 
    Ok tt (Arm6_State.mk_state 
    (Arm6_Proc.mk_state (cpsr_proj m e) (spsr_proj m e) (regs_proj m e) nil 
      (mode_proj m e))
    (Arm6_SCC.mk_state (screg_proj m e) (mem_proj m e)))
  |state_not_ok :
    forall mes, Ko mes
|*)

(* From given values to the C memory which stores the corresponding value*)

(* From address and a word to make a corresponding mem in C memory.
   if mem is not found then memory remain unchanged*)
Definition mk_mmu (ad:address) (mm:address->word) (e:env) (m:Mem.mem):Mem.mem:=
  match find_mem m e with
    |Some(Vptr b ofs)=>
      let om:=
      store_value_of_type 
      (Tint I8 Unsigned) m b (add ofs (word_of_address ad)) (Vint (mm ad)) in
      match om with
        |Some m'=>m'
        |None=> m
      end
    |_=> m
  end.

(* From a word to get all the value of fields in StatusRegister struct*)
Definition mk_sr (s:word) (b:block) (ofs:int) (m:Mem.mem):Mem.mem:=
  let stv t b id v m:=
    let om:=
      store_value_of_type t m b 
      (add ofs (ofs_of_fld id fld_sr)) v in
      match om with
        |Some m'=>m'
        |None=>m 
      end 
      in
(* No store for background, according to P49*)
(* Implementations must read reversed bits as 0 and ignore writes to them.*)
      (stv (Tint I32 Unsigned) b mode (Vint (repr (Mbits s)))
      (stv (Tint I8 Unsigned) b T_flag (Vint s[Tbit])
      (stv (Tint I8 Unsigned) b F_flag (Vint s[Fbit])
      (stv (Tint I8 Unsigned) b I_flag (Vint s[Ibit])
      (stv (Tint I8 Unsigned) b A_flag (Vint s[Abit])
      (stv (Tint I8 Unsigned) b E_flag (Vint s[Ebit])
(* From GEbits of word s to get value of GE0~3*)
      (stv (Tint I8 Unsigned) b GE3 (Vint s[19])
      (stv (Tint I8 Unsigned) b GE2 (Vint s[18])
      (stv (Tint I8 Unsigned) b GE1 (Vint s[17])
      (stv (Tint I8 Unsigned) b GE0 (Vint s[16])
      (stv (Tint I8 Unsigned) b J_flag (Vint s[Jbit])
      (stv (Tint I8 Unsigned) b Q_flag (Vint s[Qbit])
      (stv (Tint I8 Unsigned) b V_flag (Vint s[Vbit])
      (stv (Tint I8 Unsigned) b C_flag (Vint s[Cbit])
      (stv (Tint I8 Unsigned) b Z_flag (Vint s[Zbit])
      (stv (Tint I8 Unsigned) b N_flag (Vint s[Nbit]) m)))))))))))))))).

(* From word to make a corresponding cpsr in C memory.
   if cpsr is not found then memory remain unchanged*)
Definition mk_cpsr (c:word) (e:env) (m:Mem.mem):Mem.mem:=
  match find_cpsr m e with
    |Some(Vptr b ofs)=>mk_sr c b ofs m
    |_=> m
  end.

(* From exn_mode and a word to make a corresponding spsr in C memory.
   if spsr is not found then memory remain unchanged*)
Definition mk_spsr (em:exn_mode) (s:exn_mode->word) (e:env) (m:Mem.mem):Mem.mem:=
  let ofs o n:=add o (repr (n*sizeof typ_SLv6_StatusRegister)) in
  match find_spsr m e with
    |Some(Vptr b o)=>
      match em with
        |fiq=>mk_sr (s em) b (ofs o 0) m
        |irq=>mk_sr (s em) b (ofs o 1) m
        |svc=>mk_sr (s em) b (ofs o 2) m
        |abt=>mk_sr (s em) b (ofs o 3) m
        |und=>mk_sr (s em) b (ofs o 4) m
      end
    |_=> m
  end.

(* From regnum and a word to make a corresponding cp15 in C memory.
   if cp15 is not found then memory remain unchanged*)
Definition mk_cp15 (r:regnum) (s:regnum->word) (e:env) (m:Mem.mem):Mem.mem:=
  let stv b o id v m:=
    let om:=store_value_of_type 
      (Tint I8 Unsigned) m b (add o (ofs_of_fld id fld_sc)) v 
      in
      match om with
        |Some m'=>m'
        |None=>m
      end 
      in
      match find_cp15 m e with
        |Some(Vptr b ofs)=>
          stv b ofs v_bit (Vint (s r)[Vbit])
          (stv b ofs u_bit (Vint (s r)[Ubit])
          (stv b ofs ee_bit (Vint (s r)[EEbit]) m))
        |_=> m
      end.

(* From register type and a word to make a corresponding reg in C memory.
   if reg is not found then memory remain unchanged*)
Definition mk_reg (r:register) (v:register->word) 
  (e:env) (m:Mem.mem):Mem.mem:=
  let stv b o id k m:=
    let om:=
      store_value_of_type 
      (Tint I32 Unsigned) m b (add (reg_ofs id) (repr k)) (Vint (v r)) 
      in
      match om with
        |Some m'=>m'
        |None=>m
      end in
      let stv_r id k:=
      match find_reg id m e with
        |Some (Vptr b ofs)=> stv b ofs id k m
        |_=>m
      end
      in
      match r with
        | R k =>stv_r user_regs k
        | R_svc k _=>stv_r svc_regs k
        | R_abt k _=>stv_r abt_regs k
        | R_und k _=>stv_r und_regs k
        | R_irq k _=>stv_r irq_regs k
        | R_fiq k _=>stv_r fiq_regs k
      end.

(* From a word to make a corresponding id in C memory.
   if id is not found then memory remain unchanged*)
Definition mk_id (i: word) (e:env) (m:Mem.mem):Mem.mem:=
  let om:=
  match find_id m e with
    |Some(Vptr b ofs)=>store_value_of_type 
      (Tint I8 Signed) m b ofs (Vint i)
    |_=>None
  end
  in 
  match om with
    |Some m'=>m'
    |None=>m
  end.

(* From a word to make a corresponding pc in C memory.
   if pc is not found then memory remain unchanged*)
Definition mk_pc (p:word) (e:env) (m:Mem.mem):Mem.mem:=
  let om:=
  match find_pc m e with
    |Some(Vptr b ofs)=>store_value_of_type 
      (Tint I32 Signed) m b ofs (Vint p)
    |_=>None
  end
  in 
  match om with
    |Some m'=>m'
    |None=>m
  end.

(* From a word to make a corresponding jump in C memory.
   if jump is not found then memory remain unchanged*)
Definition mk_jump (j:word) (e:env) (m:Mem.mem):Mem.mem:=
  let om:=
  match find_jump m e with
    |Some(Vptr b ofs)=>store_value_of_type 
      (Tint I8 Signed) m b ofs (Vint j)
    |_=>None
  end
  in 
  match om with
    |Some m'=>m'
    |None=>m
  end.

(* From the given values to store the corresponding value in C memory*)
Definition mk_proc (j p i c:word) (em:exn_mode) (ad:address) (r:register)
  (mm:address->word) (s:exn_mode->word) (sc:regnum->word) 
  (rsc:regnum) (v:register->word) (m:Mem.mem) (e:env)
  :Mem.mem:=
  mk_jump j e 
  (mk_pc p e
  (mk_reg r v e
  (mk_id i e
  (mk_cp15 rsc sc e
  (mk_spsr em s e
  (mk_cpsr c e
  (mk_mmu ad mm e m))))))).


(* Stating theorems *)


(*Inductive proc_state_related : Mem.mem -> env -> Arm6_State.state -> Prop :=
  |proc_state_related_intro : 
    forall e m addr ad_mem cpsr_v em em_spsr screg reg_scc id_v 
      reg reg_v jump_v pc_v exns_coq mode_coq,
      proc_state_related
      (mk_proc jump_v pc_v id_v cpsr_v em addr reg ad_mem em_spsr reg_scc screg reg_v m e)
      e
      (Arm6_State.mk_state
        (Arm6_Proc.mk_state cpsr_v em_spsr reg_v exns_coq mode_coq)
        (Arm6_SCC.mk_state reg_scc ad_mem)).*)

Require Import Arm6_Simul.
Import I.
Import Arm6_Functions.Semantics.

Inductive proc_state_related_i : Mem.mem -> env -> @result unit -> Prop :=
  |proc_state_related_intro:
    forall m e l b, proc_state_related_i m e (Ok tt (mk_semstate l b (proc_proj m e))).

Inductive proc_state_related : Mem.mem -> env -> @result unit -> Prop :=
  |proc_state_related_ok : 
    forall m e l b, proc_state_related m e (Ok tt (mk_semstate l b (proc_proj m e)))
  |state_not_ok: forall e m mes, proc_state_related m e (Ko mes)
  |state_todo: forall e m mes, proc_state_related m e (Todo mes).

(* Functional relation between the C memory module which contains proc, 
   and the COQ specification of Arm6 state *)
Definition proc_state_func_related (m:Mem.mem) (e:env) (s:Arm6_State.state) :Prop:=
  proc_proj m e = s.

(* Functional relation between the C memory module which contains the other ADC parameters, 
   and the COQ specification of ADC parameters *)
Definition sbit_func_related (m:Mem.mem) (e:env) (sbit:bool):Prop:=
  S_proj m e = sbit.

Definition cond_func_related (m:Mem.mem) (e:env) (cond:opcode):Prop:=
  cond_proj m e = cond.

Definition d_func_related (m:Mem.mem) (e:env) (d:regnum):Prop:=
  d_proj m e = d.

Definition n_func_related (m:Mem.mem) (e:env) (n:regnum):Prop:=
  n_proj m e = n.

Definition so_func_related (m:Mem.mem) (e:env) (so:word):Prop:=
  so_proj m e = so.

(* Human readable renaming of [p], which is generated by the Coq printer *)
Definition prog_adc := p.

(* The assignment of old_Rn has a normal outcome *)
Lemma normal_outcome_for_assgnt: 
  forall a1 a2 ge t ev m e m' out,
  exec_stmt ge e m (Sdo (Eassign a1 a2 t)) ev m' out ->
  out = Out_normal.
Proof.
intros until out. intros exst. 
inv exst. reflexivity.
Qed.

Implicit Arguments normal_outcome_for_assgnt [a1 a2 ge t ev m e m' out].

Ltac noa :=
  match goal with
    [He: exec_stmt _ _ _ (Sdo (Eassign _ _ _)) _ _ ?out,
     Hd: ?out <> Out_normal |- _ ] =>
       case Hd; 
       apply (normal_outcome_for_assgnt He) end.

(* Any Sdo has a normal outcome*)
Lemma normal_outcome_for_do:
  forall exp ge t m e m' out,
    exec_stmt ge e m (Sdo exp) t m' out ->
    out = Out_normal.
Proof.
  intros until out. intros exst.
  inv exst. reflexivity.
Qed.

Implicit Arguments normal_outcome_for_do [exp ge t m e m' out].

Ltac nod :=
  match goal with
    [He: exec_stmt _ _ _ (Sdo _) _ _ ?out,
     Hd: ?out <> Out_normal |- _ ] =>
       case Hd; 
       apply (normal_outcome_for_do He) end.  

(* old_Rn = reg(proc,n) *)
Definition remember_assgnt := 
  Eassign (Evar old_Rn T1)
  (Ecall (Evalof (Evar reg T2) T2)
    (Econs (Evalof (Evar proc T3) T3)
      (Econs (Evalof (Evar adc_compcert.n T4) T4) Enil)) T1) T1.

(* The assignment of old_Rn has no effect on the part of memory where located proc*)
Lemma no_effect_for_old_Rn_assgnt:
 forall m e l b s m' v,
  proc_state_related m e (Ok tt (mk_semstate l b s)) ->
  eval_expression (Genv.globalenv prog_adc) e m
  remember_assgnt Events.E0 m' v ->
  forall l b, proc_state_related m' e (Ok tt (mk_semstate l b s)).
Proof.
  (*intros until v. intros psrel rn_assgnt.
  inv rn_assgnt. inv H. inv H5.
  inv H6. inv H3. inv H14.
  inv H5. inv H6. inv H5.
  inv H20. inv H5. inv H6.
  inv H19. simpl in *.*)
Admitted.

(* Lemmas on if ConditionPassed*)
Definition condpass :=
  Ecall (Evalof (Evar adc_compcert.ConditionPassed T5) T5)
  (Econs
    (Eaddrof
      (Efield (Ederef (Evalof (Evar proc T3) T3) T6) cpsr T6) T6)
    (Econs (Evalof (Evar adc_compcert.cond T7) T7) Enil)) T5.

Lemma no_effect_condpass :
  forall e m m' t v,
    eval_expression (Genv.globalenv prog_adc) e m condpass t m' v ->    
    m = m'.
Proof.
  (*intros until v. intros cdps.
  inv cdps. inv H. inv H4. inv H9.
  inv H5. inv H4. inv H5. inv H15. inv H4. inv H5.
  inv H14. inv H4. inv H5. inv H13.
  simpl in H8. inv H8.*)
Admitted.

Lemma condpass_false :
  forall e m t m' v cond s,
    eval_expression (Genv.globalenv prog_adc) e m condpass t m' v ->
    Csem.is_false v T5 ->
    Arm6_Functions.State.ConditionPassed s cond = false.
Proof.
  intros until s. intros cdps cdps_false.
  inv cdps_false.
Qed.

Lemma condpass_true :
  forall e m t m' v cond s,
    eval_expression (Genv.globalenv prog_adc) e m condpass t m' v ->
    Csem.is_true v T5 ->
    Arm6_Functions.State.ConditionPassed s cond = true.
Proof.
  intros until s. intros cdps cdps_true.
  inv cdps_true.
Qed.

(*Lemma on proc_state_relates holds after set_reg*)
Definition set_regpc :=
  Ecall (Evalof (Evar set_reg_or_pc T8) T8)
  (Econs (Evalof (Evar proc T3) T3)
    (Econs (Evalof (Evar adc_compcert.d T4) T4)
      (Econs
        (Ebinop Oadd
          (Ebinop Oadd (Evalof (Evar old_Rn T1) T1)
            (Evar shifter_operand T1) T1)
          (Efield (Efield (Evar proc T3) cpsr T6) C_flag T4) T1)
        Enil))) T9.
Check reg_content.
Lemma same_setregpc :
  forall e m l b s0 s t m' v d n so,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    n_func_related m e n ->
    so_func_related m e so ->
    eval_expression (Genv.globalenv prog_adc) e m set_regpc t m' v ->
    (forall l b, proc_state_related m' e 
      (Ok tt (mk_semstate l b
        (Arm6_State.set_reg s d (add (add (Arm6_State.reg_content s0 n) so)
          ((Arm6_State.cpsr s)[Cbit]) ))))).
Proof.
  intros until so. intros psrel nfrel sorel setreg.
  inv setreg. inv H. inv H4. inv H9.
  inv H5. inv H4. inv H5. inv H14. inv H4. inv H5.
  inv H13. inv H4. inv H17. inv H19. 
Qed.

(* Lemmas on if S==1 *)
Definition is_S_set :=
  Ebinop Oeq (Evar S T4) (Eval (Vint (repr 1)) T7) T1.

Lemma no_effect_is_S_set :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v ->
    m = m'.
Proof.
  intros until v. intros is_s. unfold is_S_set in is_s.
  inv is_s. inv H. clear H0 v. inversion H10. 
Qed.

Lemma S_not_set:
  forall e m t m' v sbit,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v ->
    Csem.is_false v T1 ->
    Util.zeq sbit 1 = false.
Proof.
  intros until sbit. intros s_set is_false.
  inv s_set. inv H. inv H10.
Qed.

Lemma S_is_set:
  forall e m t m' v sbit,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v ->
    Csem.is_true v T1 ->
    Util.zeq sbit 1 = true.
Proof.
  intros until sbit. intros s_set is_true.
  inv s_set. inv H. inv H10.
Qed.

(* Lemmas on if (((S == 1) && (d == 15)))*)
Definition is_S_set_and_is_pc :=
  Econdition (Ebinop Oeq (Evar S T4) (Eval (Vint (repr 1)) T7) T1)
  (Econdition
    (Ebinop Oeq (Evar adc_compcert.d T4)
      (Eval (Vint (repr 15)) T7) T1) (Eval (Vint (repr 1)) T7)
    (Eval (Vint (repr 0)) T7) T4) (Eval (Vint (repr 0)) T7) T4.

Lemma no_effect_is_S_set_and_is_pc :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set_and_is_pc t m' v ->
    m = m'.
Proof.
  intros until v. intros spc.
  inv spc. inv H. inv H5. inv H13. simpl in *. 
  inv H15.
Qed.

Lemma S_set_and_is_pc_true:
  forall e m t m' v sbit d,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set_and_is_pc t m' v ->
    Csem.is_true v T4 ->
    Util.zeq sbit 1 && Util.zeq d 15 = true.
Proof.
  intros until d. intros spc spc_true.
  inv spc. inv H; inv H5; inv H13.
Qed.  

Lemma S_set_and_is_pc_false:
  forall e m t m' v sbit d,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set_and_is_pc t m' v ->
    Csem.is_false v T4 ->
    Util.zeq sbit 1 && Util.zeq d 15 = false.
Proof.
  intros until d. intros spc spc_false.
  inv spc. inv H; inv H5; inv H13.
Qed.

(* Lemmas on if CurrentModeHasSPSR *)
Definition hasSPSR :=
  Ecall (Evalof (Evar CurrentModeHasSPSR T10) T10)
  (Econs (Evalof (Evar proc T3) T3) Enil) T10.

Lemma no_effect_hasSPSR :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m hasSPSR t m' v ->
    m = m'.
Proof.
  (*intros until v. intros hasspsr.
  inv hasspsr. inv H. inv H4. inv H9.
  inv H5. inv H4. inv H5. inv H14.
  simpl in H8.*)
Admitted.

Lemma hasSPSR_true :
  forall e m t m' v s em,
    eval_expression (Genv.globalenv prog_adc) e m hasSPSR t m' v ->
    Csem.is_true v T10 ->
    Arm6_State.mode s = exn  em.
Proof.
  intros until em. intros hasspsr has_true.
  inv has_true.
Qed.

Lemma hasSPSR_false :
  forall e m t m' v s,
    eval_expression (Genv.globalenv prog_adc) e m hasSPSR t m' v ->
    Csem.is_false v T10 ->
    Arm6_State.mode s = usr.
Proof.
  intros until s. intros hasspsr has_false.
  inv has_false.
Qed.

(*Lemma on proc_state_relates holds after copy_StatusRegister*)
Definition cp_SR :=
  Ecall (Evalof (Evar copy_StatusRegister T11) T11)
  (Econs
    (Eaddrof
      (Efield (Ederef (Evalof (Evar proc T3) T3) T6) cpsr T6) T6)
    (Econs
      (Ecall (Evalof (Evar spsr T6) T6)
        (Econs (Evalof (Evar proc T3) T3) Enil) T6) Enil)) T9.

Lemma same_cp_SR :
  forall e m l b s t m' v em,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    eval_expression (Genv.globalenv prog_adc) e m cp_SR t m' v ->
    (forall l b, proc_state_related m' e
      (Ok tt (mk_semstate l b
      (Arm6_State.set_cpsr s (Arm6_State.spsr s em))))).
Proof.
Admitted.

(*Lemma on proc_state_relates holds after unpredictable*)
Definition unpred :=
  Ecall (Evar adc_compcert.unpredictable T9) Enil T9.

Lemma same_unpred :
  forall e m s t m' v,
    proc_state_related m e s ->
    eval_expression (Genv.globalenv prog_adc) e m unpred t m' v ->
    proc_state_related m' e (Ko Arm6_Message.EmptyMessage).
Proof.
  intros until v. intros psrel unp.
  inv unp. inv H. inv H4.
Qed.
 (*    ([fun lbs0 : semstate =>
       set_reg d
         (add (add (Arm6_State.reg_content s n) so)
            (Arm6_State.cpsr (st lbs0)) [Cbit]) lbs0;
      [fun lbs0 : semstate =>
       set_cpsr_bit Nbit (Arm6_State.reg_content (st lbs0) d) [n31] lbs0;
      fun lbs0 : semstate =>
      set_cpsr_bit Zbit
        (if Util.zeq (Arm6_State.reg_content (st lbs0) d) 0
         then repr 1
         else repr 0) lbs0;
      fun lbs0 : semstate =>
      set_cpsr_bit Cbit
        (Arm6_Functions.CarryFrom_add3 (Arm6_State.reg_content s n) so
           (Arm6_State.cpsr (st lbs0)) [Cbit]) lbs0;
      fun lbs0 : semstate =>
      set_cpsr_bit Arm6_SCC.Vbit
        (Arm6_Functions.OverflowFrom_add3 (Arm6_State.reg_content s n) so
           (Arm6_State.cpsr (st lbs0)) [Cbit]) lbs0]]
        {| loc := nil; bo := true; st := s |})*)
(* Lemma on proc_state_relates holds after NZCV flag setting*)
Definition nflag_assgnt:=
  Eassign (Efield (Efield (Evar proc T3) cpsr T6) N_flag T4)
  (Ecall (Evalof (Evar get_bit T12) T12)
    (Econs
      (Ecall (Evalof (Evar reg T2) T2)
        (Econs (Evalof (Evar proc T3) T3)
          (Econs (Evalof (Evar adc_compcert.d T4) T4) Enil)) T1)
      (Econs (Eval (Vint (repr 31)) T7) Enil)) T1) T9.
Lemma same_nflag_assgnt :
  forall e m l b s d t m' v,
  proc_state_related m e (Ok tt (mk_semstate l b s)) ->
  d_func_related m e d ->
  eval_expression (Genv.globalenv prog_adc) e m nflag_assgnt t m' v->
  forall l b,
  proc_state_related m' e
    (Ok tt
        (mk_semstate l b
           (Arm6_State.set_cpsr_bit s Nbit
              (Arm6_State.reg_content s d) [n31] )
         )
    ).
Proof.
  intros until v. intros psrel dfrel nf.
  inv nf. inv H. simpl in *.
  inv H15.
Qed.
Definition zflag_assgnt :=
  Eassign (Efield (Efield (Evar proc T3) cpsr T6) Z_flag T4)
  (Econdition
    (Ebinop Oeq
      (Ecall (Evalof (Evar reg T2) T2)
        (Econs (Evalof (Evar proc T3) T3)
          (Econs (Evalof (Evar adc_compcert.d T4) T4) Enil)) T1)
      (Eval (Vint (repr 0)) T7) T1) (Eval (Vint (repr 1)) T7)
    (Eval (Vint (repr 0)) T7) T4) T9.
Lemma same_zflag_assgnt :
  forall e m l b s d t m' v,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    d_func_related m e d ->
    eval_expression (Genv.globalenv prog_adc) e m zflag_assgnt t m' v->
    forall l b, proc_state_related m' e 
      (Ok tt (mk_semstate l b (Arm6_State.set_cpsr_bit s Zbit
        (if Util.zeq (Arm6_State.reg_content s d) 0
         then repr 1
         else repr 0)))).
Proof.
  intros until v. intros psrel dfrel zf.
  inv zf. inv H. simpl in H15.
  inv H15.
Qed.
Definition cflag_assgnt:=
  Eassign (Efield (Efield (Evar proc T3) cpsr T6) C_flag T4)
  (Ecall (Evalof (Evar CarryFrom_add3 T9) T9)
    (Econs (Evalof (Evalof (Evar old_Rn T1) T1) T1)
      (Econs (Evalof (Evar shifter_operand T1) T1)
        (Econs
          (Evalof
            (Efield (Efield (Evar proc T3) cpsr T6) C_flag T4)
            T4) Enil))) T9) T9.
Lemma same_cflag_assgnt:
  forall m e l b s0 s n so t m' v,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    n_func_related m e n ->
    so_func_related m e so ->
    eval_expression (Genv.globalenv prog_adc) e m cflag_assgnt t m' v->
    forall l b, proc_state_related m' e
      (Ok tt (mk_semstate l b (Arm6_State.set_cpsr_bit s Cbit
        (Arm6_Functions.CarryFrom_add3 (Arm6_State.reg_content s0 n) so
          (Arm6_State.cpsr (st (mk_semstate l b s))) [Cbit])))).
Proof.
  intros until v. intros psrel nfrel sofrel cf.
  inv cf. inv H. simpl in H15.
  inv H15.
Qed.
Definition vflag_assgnt:=
  Eassign (Efield (Efield (Evar proc T3) cpsr T6) V_flag T4)
  (Ecall (Evalof (Evar OverflowFrom_add3 T9) T9)
    (Econs (Evalof (Evalof (Evar old_Rn T1) T1) T1)
      (Econs (Evalof (Evar shifter_operand T1) T1)
        (Econs
          (Evalof
            (Efield (Efield (Evar proc T3) cpsr T6) C_flag T4)
            T4) Enil))) T9) T9.
Lemma same_vflag_assgnt:
  forall m e l b s0 s n so t m' v,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    n_func_related m e n ->
    so_func_related m e so ->
    eval_expression (Genv.globalenv prog_adc) e m vflag_assgnt t m' v->
    proc_state_related m' e
      (Ok tt (mk_semstate l b (Arm6_State.set_cpsr_bit s Arm6_SCC.Vbit
        (Arm6_Functions.OverflowFrom_add3 (Arm6_State.reg_content s0 n) so
           (Arm6_State.cpsr (st (mk_semstate l b s))) [Cbit])))).
Proof.
  intros until v. intros psrel nfrel sofrel vf.
  inv vf. inv H. simpl in H15.
  inv H15.
Qed.


(* During function execution, none other parameters are changed*)
Lemma cp_SR_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m cp_SR Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
  intros until i. intros ex.
  inv ex. inv H. inv H5. inv H9.
  inv H6. inv H5. inv H6. inv H17. inv H5. inv H6.
  inv H15. inv H14.
  inv H5. inv H3. inv H15. inv H6. inv H21.
  inv H5. inv H6. simpl in *.
Admitted.

Lemma rn_ass_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m remember_assgnt Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma set_reg_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m set_regpc Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma unpred_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m unpred Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma nf_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m nflag_assgnt Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma zf_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m zflag_assgnt Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma vf_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m vflag_assgnt Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma cf_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m cflag_assgnt Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.


Theorem related_aft_ADC: forall e m0 m1 m2 mfin vargs s out sbit cond d n so,
  alloc_variables empty_env m0 (ADC_body.(fn_params) ++ ADC_body.(fn_vars)) e m1 ->
  bind_parameters e m1 ADC_body.(fn_params) vargs m2 ->
(* TODO: valid_access needs to be more precise *)
  (forall m ch b ofs, Mem.valid_access m ch b ofs Readable) ->
  proc_state_related m2 e (Ok tt (mk_semstate nil true s)) ->
  sbit_func_related m2 e sbit ->
  cond_func_related m2 e cond ->
  d_func_related m2 e d ->
  n_func_related m2 e n ->
  so_func_related m2 e so ->
(* Comparison between eval_funcall, exec_stmt:
   [eval_funcall] is big step semantic. It can be seen as 6 steps, 
   and we can observe 4 times of memory changes.
   1. Check there are no repetitive parameters in function parameter list;
   2. Allocate function parameters into memory and fill them in the empty local environment (m0->m1);
   3. Bind these parameters with there initial values (m1->m2);
   4. Execute all the statement of the function body (m2->m3);
   5. Clean up the memory which are used to store the local parameters when
   execution finishes (m3->m4).
   This final memory doesn't contain the final [proc] we expect. It is in [m3], but in [m4],
   their memory blocks are freed.
   [exec_stmt] is also big step semantic. It indicates the outcome of 
   statement execution [Out_break], [Out_continue], [Out_normal] and [Out_return].
   The final memory state is the memory which contains the final values of parameters.
   The final [proc] is in this memory state which we want to relate.*)
  exec_stmt (Genv.globalenv prog_adc) e m2 ADC_body.(fn_body) Events.E0 mfin out ->
  proc_state_related mfin e (S.ADC_step sbit cond d n so (mk_semstate nil true s)). 
Proof.
  
  intros until so.
  intros al bi valacc psrel sfrel cfrel dfrel nfrel sofrel exstmt.

  assert (Util.zne d 15 && Util.zne d 15 = Util.zne d 15) as d_15.
  destruct (Util.zne d 15); simpl; reflexivity.

  inv exstmt; [idtac | nod];
  apply Events.Eapp_E0_inv in H3; destruct H3; subst.
  rename H4 into rn_assgnt, H7 into main_p.
  inv rn_assgnt;
  rename H2 into rn_assgnt.
  apply (no_effect_for_old_Rn_assgnt m2 e nil true s m3 v) with nil true in psrel; 
    [idtac|exact rn_assgnt];
  unfold sbit_func_related in sfrel; unfold S_proj in sfrel;
  rewrite (rn_ass_params_not_changed m2 e v m3 S) in sfrel;
    [idtac | exact rn_assgnt];
  fold (S_proj m3 e) in sfrel; fold (sbit_func_related m3 e sbit) in sfrel.
  unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
  rewrite (rn_ass_params_not_changed m2 e v m3 adc_compcert.cond) in cfrel;
    [idtac | exact rn_assgnt];
  fold (cond_proj m3 e) in cfrel; fold (cond_func_related m3 e cond) in cfrel.
  unfold d_func_related in dfrel; unfold d_proj in dfrel;
  rewrite (rn_ass_params_not_changed m2 e v m3 adc_compcert.d) in dfrel;
    [idtac | exact rn_assgnt];
  fold (d_proj m3 e) in dfrel; fold (d_func_related m3 e d) in dfrel.
  unfold n_func_related in nfrel; unfold n_proj in nfrel;
  rewrite (rn_ass_params_not_changed m2 e v m3 adc_compcert.n) in nfrel;
    [idtac | exact rn_assgnt]; 
  fold (n_proj m3 e) in nfrel; fold (n_func_related m3 e n) in nfrel.
  unfold so_func_related in sofrel; unfold so_proj in sofrel;
  rewrite (rn_ass_params_not_changed m2 e v m3 shifter_operand) in sofrel;
    [clear rn_assgnt | exact rn_assgnt];
  fold (so_proj m3 e) in sofrel; fold (so_func_related m3 e so) in sofrel (* m2=m3 *).
  inv main_p;
  rename H5 into condpass, H8 into cp_b, H9 into main_p, H4 into evs;
      simpl in cp_b;
      apply Events.Eapp_E0_inv in evs; destruct evs; subst;
      apply no_effect_condpass in condpass0; rewrite condpass0 in * |- *;
        clear condpass0 (* m3=m4 *).
    (* ConditionPassed(&proc->cpsr, cond) evaluates to true *)
    inv main_p; [idtac | nod];
    rename H4 into setreg, H7 into main_p, H3 into evs;
    apply Events.Eapp_E0_inv in evs; destruct evs; subst.
    inv setreg;
    rename H2 into setreg;
    apply (same_setregpc e m4 nil true s s Events.E0 m5 v0 d n so) 
      with nil (Util.zne d 15) in psrel;
      [idtac | exact nfrel | exact sofrel | exact setreg].
    unfold sbit_func_related in sfrel; unfold S_proj in sfrel;   
    rewrite (set_reg_params_not_changed m4 e v0 m5 S) in sfrel;
      [idtac | exact setreg];
    fold (S_proj m5 e) in sfrel; fold (sbit_func_related m5 e sbit) in sfrel.
    unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
    rewrite (set_reg_params_not_changed m4 e v0 m5 adc_compcert.cond) in cfrel;
      [idtac | exact setreg];
    fold (cond_proj m5 e) in cfrel; fold (cond_func_related m5 e cond) in cfrel.
    unfold d_func_related in dfrel; unfold d_proj in dfrel;
    rewrite (set_reg_params_not_changed m4 e v0 m5 adc_compcert.d) in dfrel;
      [idtac | exact setreg];
    fold (d_proj m5 e) in dfrel; fold (d_func_related m5 e d) in dfrel.
    unfold n_func_related in nfrel; unfold n_proj in nfrel;
    rewrite (set_reg_params_not_changed m4 e v0 m5 adc_compcert.n) in nfrel;
      [idtac | exact setreg]; 
    fold (n_proj m5 e) in nfrel; fold (n_func_related m5 e n) in nfrel.
    unfold so_func_related in sofrel; unfold so_proj in sofrel;
    rewrite (set_reg_params_not_changed m4 e v0 m5 shifter_operand) in sofrel;
      [clear setreg | exact setreg];
    fold (so_proj m5 e) in sofrel; fold (so_func_related m5 e so) in sofrel (*m4 -> m5*).
    inv main_p;
    rename H5 into sd, H8 into sd_b, H9 into main_p, H4 into evs;
        simpl in sd_b;
        apply no_effect_is_S_set_and_is_pc in sd; rewrite sd in * |- *; clear sd; (* m5=m6 *)
        apply Events.Eapp_E0_inv in evs; destruct evs; subst.
      (* ((S == 1) && (d == 15)) evaluates to true *)
      apply (S_set_and_is_pc_true e mfin Events.E0 m6 v2 sbit d) in sd_b;
        [idtac | inv cp_b];
      apply (condpass_true e m4 Events.E0 m5 v1 cond s) in cp_b;
        [idtac |inv cp_b];
      inv main_p;
      rename H5 into hasspsr, H8 into spsr_b, H9 into main_p, H4 into evs;
          simpl in spsr_b;
          apply Events.Eapp_E0_inv in evs; destruct evs; subst;
          apply no_effect_hasSPSR in hasspsr; rewrite hasspsr in * |- *; 
            clear hasspsr (* m6=m7*).
        (* CurrentModeHasSPSR(proc) evaluates to true *)
        inv main_p;
        rename H2 into cp_sr.
        apply (same_cp_SR e m7 nil (Util.zne d 15)
          (Arm6_State.set_reg s d
                       (add (add (Arm6_State.reg_content s n) so)
                          (Arm6_State.cpsr s) [Cbit]))
          Events.E0 mfin v4 und) with nil (Util.zne d 15) in psrel;
          [idtac | exact cp_sr ].
        unfold sbit_func_related in sfrel; unfold S_proj in sfrel;   
        rewrite (cp_SR_params_not_changed m7 e v4 mfin S) in sfrel;
          [idtac | exact cp_sr];
        fold (S_proj mfin e) in sfrel; fold (sbit_func_related mfin e sbit) in sfrel.
        unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
        rewrite (cp_SR_params_not_changed m7 e v4 mfin adc_compcert.cond) in cfrel;
          [idtac | exact cp_sr];
        fold (cond_proj mfin e) in cfrel; fold (cond_func_related mfin e cond) in cfrel.
        unfold d_func_related in dfrel; unfold d_proj in dfrel;
        rewrite (cp_SR_params_not_changed m7 e v4 mfin adc_compcert.d) in dfrel;
          [idtac | exact cp_sr];
        fold (d_proj mfin e) in dfrel; fold (d_func_related mfin e d) in dfrel.
        unfold n_func_related in nfrel; unfold n_proj in nfrel;
        rewrite (cp_SR_params_not_changed m7 e v4 mfin adc_compcert.n) in nfrel;
          [idtac | exact cp_sr]; 
        fold (n_proj mfin e) in nfrel; fold (n_func_related mfin e n) in nfrel.
        unfold so_func_related in sofrel; unfold so_proj in sofrel;
        rewrite (cp_SR_params_not_changed m7 e v4 mfin shifter_operand) in sofrel;
          [clear cp_sr | exact cp_sr];
        fold (so_proj mfin e) in sofrel; fold (so_func_related mfin e so) in sofrel (*m7->mfin*).
        apply (hasSPSR_true e m6 Events.E0 m7 v3
          (Arm6_State.set_reg s d
            (add (add (Arm6_State.reg_content s n) so)
              (Arm6_State.cpsr s) [Cbit]))
          und) in spsr_b;
          [idtac |inv spsr_b].
        unfold S.ADC_step; unfold _get_st; unfold bind_s;
          unfold bind; simpl.
        rewrite cp_b; rewrite sd_b; simpl.
        unfold if_CurrentModeHasSPSR; unfold block; unfold fold_left;
        unfold _get_bo; unfold bind_s; unfold next; unfold bind; simpl;
        unfold _Arm_State.set_reg.
        rewrite spsr_b; simpl; unfold _Arm_State.set_reg; unfold _Arm_State.set_cpsr.
        unfold _set_bo; unfold ok_semstate. unfold loc. unfold st. rewrite d_15.
        apply psrel.
        (* CurrentModeHasSPSR(proc) evaluates to false *)
        inv main_p; rename H2 into unp.
        apply (same_unpred e m7 
                (Ok tt (mk_semstate nil (Util.zne d 15) (Arm6_State.set_reg s d
                  (add (add (Arm6_State.reg_content s n) so)
                    (Arm6_State.cpsr s) [Cbit]))))
                Events.E0 mfin v4) in psrel;
        [idtac | exact unp].
        unfold sbit_func_related in sfrel; unfold S_proj in sfrel;   
        rewrite (unpred_params_not_changed m7 e v4 mfin S) in sfrel;
          [idtac | exact unp];
        fold (S_proj mfin e) in sfrel; fold (sbit_func_related mfin e sbit) in sfrel.
        unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
        rewrite (unpred_params_not_changed m7 e v4 mfin adc_compcert.cond) in cfrel;
          [idtac | exact unp];
        fold (cond_proj mfin e) in cfrel; fold (cond_func_related mfin e cond) in cfrel.
        unfold d_func_related in dfrel; unfold d_proj in dfrel;
        rewrite (unpred_params_not_changed m7 e v4 mfin adc_compcert.d) in dfrel;
          [idtac | exact unp];
        fold (d_proj mfin e) in dfrel; fold (d_func_related mfin e d) in dfrel.
        unfold n_func_related in nfrel; unfold n_proj in nfrel;
        rewrite (unpred_params_not_changed m7 e v4 mfin adc_compcert.n) in nfrel;
          [idtac | exact unp]; 
        fold (n_proj mfin e) in nfrel; fold (n_func_related mfin e n) in nfrel.
        unfold so_func_related in sofrel; unfold so_proj in sofrel;
        rewrite (unpred_params_not_changed m7 e v4 mfin shifter_operand) in sofrel;
          [clear unp | exact unp];
        fold (so_proj mfin e) in sofrel; fold (so_func_related mfin e so) in sofrel.
        unfold S.ADC_step; unfold _get_st; unfold bind_s;
        unfold bind; simpl.
        rewrite cp_b; rewrite sd_b; simpl.
        apply (hasSPSR_false e m6 Events.E0 m7 v3
          (Arm6_State.set_reg s d
            (add (add (Arm6_State.reg_content s n) so)
              (Arm6_State.cpsr s) [Cbit]))
          ) in spsr_b;
          [idtac |inv spsr_b].
        unfold if_CurrentModeHasSPSR. unfold block. unfold fold_left.
        unfold _get_bo. unfold bind_s. unfold next. unfold bind.
        simpl; unfold _Arm_State.set_reg.
        rewrite spsr_b; simpl.
        exact psrel.
      (* ((S == 1) && (d == 15)) evaluates to false *)
      
      apply (S_set_and_is_pc_false e m5 Events.E0 m6 v2 sbit d) in sd_b;
        [idtac | inv cp_b].
      inv main_p;
      rename H5 into is_s, H8 into s_b, H9 into main_p, H4 into evs;
          simpl in s_b; 
          apply no_effect_is_S_set in is_s; rewrite is_s in * |- *; clear is_s; (* m6=m7*)
          apply Events.Eapp_E0_inv in evs; destruct evs; subst.      
        (* S == 1 evaluates to true *)
        inv main_p ;[idtac | nod];
        rename H4 into nf, H7 into main_p, H3 into evs;
        apply Events.Eapp_E0_inv in evs; destruct evs; subst.

        inv nf; rename H2 into nf;
        pose (s0 :=  Arm6_State.set_reg s d
                       (add (add (Arm6_State.reg_content s n) so)
                          (Arm6_State.cpsr s) [Cbit]));
        fold s0 in psrel;
        eapply (same_nflag_assgnt e m7 nil (Util.zne d 15)
          s0 d Events.E0 m8 v4)
          in psrel;
          [idtac | exact dfrel | exact nf].

        unfold sbit_func_related in sfrel; unfold S_proj in sfrel;   
        rewrite (nf_params_not_changed m7 e v4 m8 S) in sfrel;
          [idtac | exact nf];
        fold (S_proj m8 e) in sfrel; fold (sbit_func_related m8 e sbit) in sfrel.
        unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
        rewrite (nf_params_not_changed m7 e v4 m8 adc_compcert.cond) in cfrel;
          [idtac | exact nf];
        fold (cond_proj m8 e) in cfrel; fold (cond_func_related m8 e cond) in cfrel.
        unfold d_func_related in dfrel; unfold d_proj in dfrel;
        rewrite (nf_params_not_changed m7 e v4 m8 adc_compcert.d) in dfrel;
          [idtac | exact nf];
        fold (d_proj m8 e) in dfrel; fold (d_func_related m8 e d) in dfrel.
        unfold n_func_related in nfrel; unfold n_proj in nfrel;
        rewrite (nf_params_not_changed m7 e v4 m8 adc_compcert.n) in nfrel;
          [idtac | exact nf]; 
        fold (n_proj m8 e) in nfrel; fold (n_func_related m8 e n) in nfrel.
        unfold so_func_related in sofrel; unfold so_proj in sofrel;
        rewrite (nf_params_not_changed m7 e v4 m8 shifter_operand) in sofrel;
          [clear nf | exact nf];
        fold (so_proj m8 e) in sofrel; fold (so_func_related m8 e so) in sofrel.
        inv main_p ;[idtac | nod];
        rename H4 into zf, H7 into main_p, H3 into evs;
        apply Events.Eapp_E0_inv in evs; destruct evs; subst.

        inv zf; rename H2 into zf;
        pose (s1 := Arm6_State.set_cpsr_bit s0 Nbit
                       (Arm6_State.reg_content s0 d) [n31]);
        revert psrel; fold s1; intro psrel;
        eapply (same_zflag_assgnt e m8 nil (Util.zne d 15)
          s1
          d Events.E0 m9 v5) in psrel;
        [idtac| exact dfrel | exact zf].
        unfold sbit_func_related in sfrel; unfold S_proj in sfrel;   
        rewrite (zf_params_not_changed m8 e v5 m9 S) in sfrel;
          [idtac | exact zf];
        fold (S_proj m9 e) in sfrel; fold (sbit_func_related m9 e sbit) in sfrel.
        unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
        rewrite (zf_params_not_changed m8 e v5 m9 adc_compcert.cond) in cfrel;
          [idtac | exact zf];
        fold (cond_proj m9 e) in cfrel; fold (cond_func_related m9 e cond) in cfrel.
        unfold d_func_related in dfrel; unfold d_proj in dfrel;
        rewrite (zf_params_not_changed m8 e v5 m9 adc_compcert.d) in dfrel;
          [idtac | exact zf];
        fold (d_proj m9 e) in dfrel; fold (d_func_related m9 e d) in dfrel.
        unfold n_func_related in nfrel; unfold n_proj in nfrel;
        rewrite (zf_params_not_changed m8 e v5 m9 adc_compcert.n) in nfrel;
          [idtac | exact zf]; 
        fold (n_proj m9 e) in nfrel; fold (n_func_related m9 e n) in nfrel.
        unfold so_func_related in sofrel; unfold so_proj in sofrel;
        rewrite (zf_params_not_changed m8 e v5 m9 shifter_operand) in sofrel;
          [clear zf | exact zf];
        fold (so_proj m9 e) in sofrel; fold (so_func_related m9 e so) in sofrel.
        inv main_p ;[idtac | nod];
        rename H4 into cf, H7 into vf, H3 into evs;
        apply Events.Eapp_E0_inv in evs; destruct evs; subst.
        inv cf; rename H2 into cf;
        pose (s2 := Arm6_State.set_cpsr_bit s1 Zbit
                       (if Util.zeq (Arm6_State.reg_content s1 d) 0
                        then repr 1
                        else repr 0));
        revert psrel; fold s2; intro psrel;
        eapply (same_cflag_assgnt m9 e nil (Util.zne d 15)
          s s2
          n so Events.E0 m10 v6) in psrel;
        [idtac| exact nfrel | exact sofrel| exact cf]. 
        unfold sbit_func_related in sfrel; unfold S_proj in sfrel;   
        rewrite (cf_params_not_changed m9 e v6 m10 S) in sfrel;
          [idtac | exact cf];
        fold (S_proj m10 e) in sfrel; fold (sbit_func_related m10 e sbit) in sfrel.
        unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
        rewrite (cf_params_not_changed m9 e v6 m10 adc_compcert.cond) in cfrel;
          [idtac | exact cf];
        fold (cond_proj m10 e) in cfrel; fold (cond_func_related m10 e cond) in cfrel.
        unfold d_func_related in dfrel; unfold d_proj in dfrel;
        rewrite (cf_params_not_changed m9 e v6 m10 adc_compcert.d) in dfrel;
          [idtac | exact cf];
        fold (d_proj m10 e) in dfrel; fold (d_func_related m10 e d) in dfrel.
        unfold n_func_related in nfrel; unfold n_proj in nfrel;
        rewrite (cf_params_not_changed m9 e v6 m10 adc_compcert.n) in nfrel;
          [idtac | exact cf]; 
        fold (n_proj m10 e) in nfrel; fold (n_func_related m10 e n) in nfrel.
        unfold so_func_related in sofrel; unfold so_proj in sofrel;
        rewrite (cf_params_not_changed m9 e v6 m10 shifter_operand) in sofrel;
          [clear cf | exact cf];
        fold (so_proj m10 e) in sofrel; fold (so_func_related m10 e so) in sofrel.

        unfold st in psrel.
        inv vf; rename H2 into vf;
        pose (s3 := Arm6_State.set_cpsr_bit s2 Cbit
                       (Arm6_Functions.CarryFrom_add3
                         (Arm6_State.reg_content s n) so
                         (Arm6_State.cpsr s2) [Cbit]));
        revert psrel; fold s3; intro psrel;
        eapply (same_vflag_assgnt m10 e nil (Util.zne d 15)
          s s3
          n so Events.E0 mfin v7) in psrel;
        [clear vf| exact nfrel | exact sofrel| exact vf].
        apply (S_is_set e m10 Events.E0 mfin v3 sbit) in s_b;
          [idtac | inv cp_b];
        apply (condpass_true e m10 Events.E0 mfin v1 cond s) in cp_b;
          [idtac | inv cp_b].

        unfold S.ADC_step. unfold _get_st. unfold bind_s; unfold bind; simpl.
        rewrite cp_b. simpl. 
        unfold block. unfold fold_left at 1. unfold next. 
        unfold bind at 1 2. unfold _get_bo at 1. 
        unfold bind_s at 1. unfold bind at 1. unfold bind at 1. 
        unfold set_reg. simpl; unfold _Arm_State.set_reg. 
        fold s0. 
        rewrite sd_b; rewrite s_b; simpl.
        (* Nflag *)
        unfold bind at 5. unfold _get_bo at 2. unfold bind_s at 1. 
        unfold bind at 5. unfold bind at 5.
        simpl; unfold _Arm_State.set_cpsr_bit at 1. 
        unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
        unfold _set_bo at 1.  simpl. unfold ok_semstate.
        
        (* Zflag *)
        unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
        unfold bind at 5. simpl; unfold _Arm_State.set_cpsr_bit at 1.
        unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
        simpl. unfold _set_bo at 1. simpl. unfold ok_semstate.
        (* Cflag *)
        unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
        unfold bind at 5. simpl; unfold _Arm_State.set_cpsr_bit at 1.
        unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
        simpl. unfold _set_bo at 1. simpl. unfold ok_semstate.
        (* Vflag *)
        unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
        unfold bind at 5. simpl; unfold _Arm_State.set_cpsr_bit at 1.
        unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
        simpl. unfold _set_bo at 1. simpl. unfold ok_semstate.

(*        pose (fff x := st x). change (st lbs0) with (fff lbs0) at 1.
        
        pose (stl lbs0 := Arm6_State.set_cpsr_bit 
                               (st lbs0) Nbit
                               (Arm6_State.reg_content (st lbs0) d) [n31]).
        change *)
        unfold bind at 4. unfold loc at 1. unfold bo at 1. unfold bo at 3.
        unfold st at 1. unfold st at 3.
        unfold bind at 3. unfold loc at 1. unfold bo at 1. unfold bo at 5.
        unfold st at 1. unfold st at 5.
        unfold bind at 2. unfold loc at 1. unfold bo at 1. unfold bo at 9.
        unfold st at 1. unfold st at 9.
        
        unfold bind at 1. unfold _get_bo at 2. unfold bind_s at 1.
        unfold bind at 1. unfold bo at 1.
        unfold _set_bo at 1. unfold loc at 1. unfold st at 1.
        unfold ok_semstate.
        unfold _get_bo at 1. unfold bind_s at 1. unfold bind at 1.
        unfold loc at 1. unfold bo. unfold st at 1. unfold st.
        fold s1. fold s2. unfold s3 in psrel. unfold st in psrel.
        rewrite d_15. rewrite d_15. rewrite d_15. rewrite d_15. rewrite d_15.
        exact psrel.

        (* S == 1 evaluates to false *)
        inv main_p.
        apply (S_not_set e m6 Events.E0 mfin v3 sbit) in s_b;
          [idtac | inv cp_b];
        apply (condpass_true e m6 Events.E0 mfin v1 cond s) in cp_b;
          [idtac | inv cp_b].
        unfold S.ADC_step; unfold _get_st; unfold bind_s; unfold bind; simpl.
        rewrite cp_b; rewrite sd_b; rewrite s_b; simpl.
        unfold block. unfold fold_left. unfold next.
        unfold bind at 3. simpl; unfold _Arm_State.set_reg.
        unfold _get_bo at 2. unfold bind_s at 1. unfold _set_bo at 1.
        unfold ok_semstate.
        unfold bind at 3. unfold loc at 1. unfold bo at 1.
        unfold st at 1.
        unfold _get_bo at 1. unfold bind_s at 1. unfold bind at 3.
        unfold bind at 2.
        unfold bind at 2. unfold _get_bo at 1. unfold bind_s at 1.
        unfold bind at 2. unfold _get_bo at 1. unfold bind_s at 1.
        unfold _set_bo at 1. unfold ok_semstate.
        unfold bind at 2.
        unfold bind at 1. unfold loc. unfold bo. unfold st. simpl.
        simpl. rewrite d_15. exact psrel.

    (* ConditionPassed(&proc->cpsr, cond) evaluates to false *)
    inv main_p.
    unfold S.ADC_step; unfold _get_st; unfold bind_s; unfold bind; simpl.
    rewrite (condpass_false e mfin Events.E0 mfin v1); [simpl | inv cp_b|exact cp_b].
    exact psrel.
Qed.









  (*inv bi. unfold proc_state_func_related. unfold proc_proj.
  unfold cpsr_proj. unfold find_cpsr. unfold find_field. unfold proc_loc. 
  rewrite H4. unfold load_value_of_type. simpl.
  destruct (Mem.valid_access_load m3 AST.Mint32 b(signed w0)) as [v ev];
    [trivial | idtac].
        rewrite ev.
apply Mem.valid_access_load in H1.*)
 






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