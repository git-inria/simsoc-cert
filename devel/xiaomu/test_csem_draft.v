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

Definition param_val (id:AST.ident) (t:type) (m:Mem.mem) (e:env):val:=
  match e!id with
    |Some(b,_)=>
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
  bool_of_word (varg_proj (param_val S (Tint I8 Unsigned) m e)).

Definition cond_proj (m:Mem.mem) (e:env):opcode:= 
  let c:=condition (varg_proj (param_val cond (Tint I32 Unsigned) m e)) in
    match c with
      |Some c'=>c'
      |None=>AL
    end.

Definition d_proj (m:Mem.mem) (e:env):regnum:=
  mk_regnum (varg_proj (param_val d (Tint I32 Unsigned) m e)).

Definition n_proj (m:Mem.mem) (e:env):regnum:=
  mk_regnum (varg_proj (param_val n (Tint I32 Unsigned) m e)).

Definition so_proj (m:Mem.mem) (e:env):word:=
  varg_proj (param_val shifter_operand (Tint I32 Unsigned) m e).

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

Inductive proc_state_related : Mem.mem -> env -> Arm6_State.state -> Prop :=
  |proc_state_related_intro : 
    forall e m addr ad_mem cpsr_v em em_spsr screg reg_scc id_v 
      reg reg_v jump_v pc_v exns_coq mode_coq,
      proc_state_related
      (mk_proc jump_v pc_v id_v cpsr_v em addr reg ad_mem em_spsr reg_scc screg reg_v m e)
      e
      (Arm6_State.mk_state
        (Arm6_Proc.mk_state cpsr_v em_spsr reg_v exns_coq mode_coq)
        (Arm6_SCC.mk_state reg_scc ad_mem)).

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

(* Stating theorems *)

Require Import Arm6_Simul.
Import I.
Import Arm6_Functions.Semantics.

(* Human readable renaming of [p], which is generated by the Coq printer *)
Definition prog_adc := p.

Definition adc_return sbit cond d n so s :=
  let r:= S.ADC_step sbit cond d n so (mk_semstate nil true s) in
    match r with
      |Ok _ (mk_semstate l b s')=>s'
      |_=>s
    end.

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
 forall m e st m' v,
  proc_state_func_related m e st ->
  eval_expression (Genv.globalenv prog_adc) e m
  remember_assgnt Events.E0 m' v ->
  proc_state_func_related m' e st.
Proof.
Admitted.

(* Lemmas on if ConditionPassed*)
Definition condpass :=
  Ecall (Evalof (Evar adc_compcert.ConditionPassed T5) T5)
  (Econs
    (Eaddrof
      (Efield (Ederef (Evalof (Evar proc T3) T3) T6) cpsr T6) T6)
    (Econs (Evalof (Evar adc_compcert.cond T7) T7) Enil)) T5.

Lemma no_effect_condpass :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m condpass t m' v ->
    m = m'.
Proof.
Admitted.

Lemma condpass_false :
  forall (*e m t m'*) v cond s,
    (*eval_expression (Genv.globalenv prog_adc) e m condpass t m' v ->*)
    Csem.is_false v T5 ->
    Arm6_Functions.State.ConditionPassed s cond = false.
Proof.
Admitted.

Lemma condpass_true :
  forall (*e m t m'*) v cond s,
    (*eval_expression (Genv.globalenv prog_adc) e m condpass t m' v ->*)
    Csem.is_true v T5 ->
    Arm6_Functions.State.ConditionPassed s cond = true.
Proof.
Admitted.

(*Lemma on proc_state_func_relates holds after set_reg*)
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

Lemma same_setregpc :
  forall e m s t m' v d n so,
    proc_state_func_related m e s ->
    n_func_related m e n ->
    so_func_related m e so ->
    eval_expression (Genv.globalenv prog_adc) e m set_regpc t m' v ->
    proc_state_func_related m' e 
      (_Arm_State.set_reg s d (add (add (reg_content (Arm6_State.proc s) n) so)
                                   ((_Arm_State.cpsr s)[Cbit]) )).
Proof.
Admitted.

(* Lemmas on if S==1 *)
Definition is_S_set :=
  Ebinop Oeq (Evar S T4) (Eval (Vint (repr 1)) T7) T1.

Lemma no_effect_is_S_set :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v ->
    m = m'.
Proof.
Admitted.

Lemma S_not_set:
  forall e m t m' v sbit,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v ->
    Csem.is_false v T1 ->
    Util.zeq sbit 1 = false.
Proof.
Admitted.

Lemma S_is_set:
  forall e m t m' v sbit,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v ->
    Csem.is_true v T1 ->
    Util.zeq sbit 1 = true.
Proof.
Admitted.

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
Admitted.

Lemma S_set_and_is_pc_true:
  forall e m t m' v sbit d,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set_and_is_pc t m' v ->
    Csem.is_true v T4 ->
    Util.zeq sbit 1 && Util.zeq d 15 = true.
Proof.
Admitted.

Lemma S_set_and_is_pc_false:
  forall e m t m' v sbit d,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set_and_is_pc t m' v ->
    Csem.is_false v T4 ->
    Util.zeq sbit 1 && Util.zeq d 15 = false.
Proof.
Admitted.

(* Lemmas on if CurrentModeHasSPSR *)
Definition hasSPSR :=
  Ecall (Evalof (Evar CurrentModeHasSPSR T10) T10)
  (Econs (Evalof (Evar proc T3) T3) Enil) T10.

Lemma no_effect_hasSPSR :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m hasSPSR t m' v ->
    m = m'.
Proof.
Admitted.

Lemma hasSPSR_true :
  forall e m t m' v s em,
    eval_expression (Genv.globalenv prog_adc) e m hasSPSR t m' v ->
    Csem.is_true v T10 ->
    Arm6_State.mode s = exn  em.
Proof.
Admitted.

Lemma hasSPSR_false :
  forall e m t m' v s,
    eval_expression (Genv.globalenv prog_adc) e m hasSPSR t m' v ->
    Csem.is_false v T10 ->
    Arm6_State.mode s = usr.
Proof.
Admitted.

(*Lemma on proc_state_func_relates holds after copy_StatusRegister*)
Definition cp_SR :=
  Ecall (Evalof (Evar copy_StatusRegister T11) T11)
  (Econs
    (Eaddrof
      (Efield (Ederef (Evalof (Evar proc T3) T3) T6) cpsr T6) T6)
    (Econs
      (Ecall (Evalof (Evar spsr T6) T6)
        (Econs (Evalof (Evar proc T3) T3) Enil) T6) Enil)) T9.

Lemma same_cp_SR :
  forall e m s t m' v em,
    proc_state_func_related m e s ->
    eval_expression (Genv.globalenv prog_adc) e m cp_SR t m' v ->
    proc_state_func_related m' e 
    (_Arm_State.set_cpsr s (Arm6_State.spsr s em)).
Proof.
Admitted.

(*Lemma on proc_state_func_relates holds after unpredictable*)
Definition unpred :=
  Ecall (Evar adc_compcert.unpredictable T9) Enil T9 .

Lemma same_unpred :
  forall e m s t m' v,
    proc_state_func_related m e s ->
    eval_expression (Genv.globalenv prog_adc) e m unpred t m' v ->
    proc_state_func_related m' e s.
Proof.
Admitted.

(* Lemma on proc_state_func_relates holds after NZCV flag setting*)
(*[fun lbs0 : semstate =>
                 set_cpsr_bit Nbit (Arm6_State.reg_content (st lbs0) d) [n31]
                   lbs0;
                fun lbs0 : semstate =>
                set_cpsr_bit Zbit
                  (if Util.zeq (Arm6_State.reg_content (st lbs0) d) 0
                   then repr 1
                   else repr 0) lbs0;
                fun lbs0 : semstate =>
                set_cpsr_bit Cbit
                  (Arm6_Functions.CarryFrom_add3
                     (Arm6_State.reg_content
                        (st {| loc := nil; bo := true; st := s |}) n) so
                     (Arm6_State.cpsr (st lbs0)) [Cbit]) lbs0;
                fun lbs0 : semstate =>
                set_cpsr_bit Arm6_SCC.Vbit
                  (Arm6_Functions.OverflowFrom_add3
                     (Arm6_State.reg_content
                        (st {| loc := nil; bo := true; st := s |}) n) so
                     (Arm6_State.cpsr (st lbs0)) [Cbit]) lbs0]
*)
Definition nflag_assgnt:=
  Eassign (Efield (Efield (Evar proc T3) cpsr T6) N_flag T4)
  (Ecall (Evalof (Evar get_bit T12) T12)
    (Econs
      (Ecall (Evalof (Evar reg T2) T2)
        (Econs (Evalof (Evar proc T3) T3)
          (Econs (Evalof (Evar adc_compcert.d T4) T4) Enil)) T1)
      (Econs (Eval (Vint (repr 31)) T7) Enil)) T1) T9.
Lemma same_nflag_assgnt :
  forall e m s d t m' v,
    proc_state_func_related m e s ->
    d_func_related m e d ->
    eval_expression (Genv.globalenv prog_adc) e m nflag_assgnt t m' v->
    proc_state_func_related m' e 
      (_Arm_State.set_cpsr_bit s Nbit ((Arm6_State.reg_content s d)[n31])).
Proof.
Admitted. 
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
  forall e m s d t m' v,
    proc_state_func_related m e s ->
    d_func_related m e d ->
    eval_expression (Genv.globalenv prog_adc) e m zflag_assgnt t m' v->
    proc_state_func_related m' e 
    (_Arm_State.set_cpsr_bit s Zbit 
      (if Util.zeq (Arm6_State.reg_content s d) 0
        then repr 1
        else repr 0)).
Proof.
Admitted.
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
  forall m e s n so t m' v,
    proc_state_func_related m e s ->
    n_func_related m e n ->
    so_func_related m e so ->
    eval_expression (Genv.globalenv prog_adc) e m cflag_assgnt t m' v->
    proc_state_func_related m' e
    (_Arm_State.set_cpsr_bit s Cbit
      (Arm6_Functions.CarryFrom_add3
        (Arm6_State.reg_content s n) so
        (Arm6_State.cpsr s) [Cbit])).
Proof.
Admitted.
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
  forall m e s n so t m' v,
    proc_state_func_related m e s ->
    n_func_related m e n ->
    so_func_related m e so ->
    eval_expression (Genv.globalenv prog_adc) e m vflag_assgnt t m' v->
    proc_state_func_related m' e
    (_Arm_State.set_cpsr_bit s Arm6_SCC.Vbit
                  (Arm6_Functions.OverflowFrom_add3
                     (Arm6_State.reg_content s n) so
                     (Arm6_State.cpsr s) [Cbit])).
Proof.
Admitted.

(* During function execution, none other parameters are changed*)
Lemma sbit_not_changed:
  forall m e exp v m' sbit, 
    sbit_func_related m e sbit ->
    eval_expression (Genv.globalenv prog_adc) e m exp Events.E0 m' v ->
    sbit_func_related m' e sbit.
Proof.
Admitted.
Lemma cond_not_changed:
  forall m e exp v m' cond, 
    cond_func_related m e cond ->
    eval_expression (Genv.globalenv prog_adc) e m exp Events.E0 m' v ->
    cond_func_related m' e cond.
Proof.
Admitted.
Lemma d_not_changed:
  forall m e exp v m' d, 
    d_func_related m e d ->
    eval_expression (Genv.globalenv prog_adc) e m exp Events.E0 m' v ->
    d_func_related m' e d.
Proof.
Admitted.
Lemma n_not_changed:
  forall m e exp v m' n, 
    n_func_related m e n ->
    eval_expression (Genv.globalenv prog_adc) e m exp Events.E0 m' v ->
    n_func_related m' e n.
Proof.
Admitted.
Lemma so_not_changed:
  forall m e exp v m' so, 
    so_func_related m e so ->
    eval_expression (Genv.globalenv prog_adc) e m exp Events.E0 m' v ->
    so_func_related m' e so.
Proof.
Admitted.

Theorem related_aft_ADC: forall e m0 m1 m2 mfin vargs s out sbit cond d n so,
  alloc_variables empty_env m0 (ADC_body.(fn_params) ++ ADC_body.(fn_vars)) e m1 ->
  bind_parameters e m1 ADC_body.(fn_params) vargs m2 ->
(* TODO: valid_access needs to be more precise *)
  (forall m ch b ofs, Mem.valid_access m ch b ofs Readable) ->
  proc_state_func_related m2 e s ->
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
  proc_state_func_related mfin e
  (adc_return sbit cond d n so s). 
Proof.
  
  intros until so.
  intros al bi valacc psrel sfrel cfrel dfrel nfrel sofrel exstmt.

  inv exstmt; [idtac | nod];
  apply Events.Eapp_E0_inv in H3; destruct H3; subst.
  inv H4.
  apply (no_effect_for_old_Rn_assgnt m2 e s m3 v) in psrel; 
    [idtac|exact H2];
  apply (sbit_not_changed m2 e remember_assgnt v m3) in sfrel;
    [idtac | exact H2];
  apply (cond_not_changed m2 e remember_assgnt v m3) in cfrel;
    [idtac | exact H2];
  apply (d_not_changed m2 e remember_assgnt v m3) in dfrel;
    [idtac | exact H2];
  apply (n_not_changed m2 e remember_assgnt v m3) in nfrel;
    [idtac | exact H2]; 
  apply (so_not_changed m2 e remember_assgnt v m3) in sofrel;
    [clear H2 | exact H2]. (* m2=m3 *)
  inv H7 (*ugly name*);
      simpl in H9;
      apply Events.Eapp_E0_inv in H4; destruct H4; subst;
      apply no_effect_condpass in H5; rewrite H5 in * |- *; clear H5. (* m3=m4 *)
    (* ConditionPassed(&proc->cpsr, cond) evaluates to true *)
    inv H10; [idtac | nod];
    apply Events.Eapp_E0_inv in H3; destruct H3; subst.
    inv H4.
    apply (same_setregpc e m4 s Events.E0 m5 v0 d n so) in psrel;
        [idtac | exact nfrel | exact sofrel | exact H2];
    apply (sbit_not_changed m4 e set_regpc v0 m5) in sfrel;
      [idtac | exact H2];
    apply (cond_not_changed m4 e set_regpc v0 m5) in cfrel;
      [idtac | exact H2];
    apply (d_not_changed m4 e set_regpc v0 m5) in dfrel;
      [idtac | exact H2];
    apply (n_not_changed m4 e set_regpc v0 m5) in nfrel;
      [idtac | exact H2];
    apply (so_not_changed m4 e set_regpc v0 m5) in sofrel;
      [clear H2 | exact H2].
    inv H7;
        simpl in H10;
        apply no_effect_is_S_set_and_is_pc in H5; rewrite H5 in * |- *; clear H5; (* m5=m6 *)
        apply Events.Eapp_E0_inv in H4; destruct H4; subst.
      (* ((S == 1) && (d == 15)) evaluates to true *)
      inv H11;
          simpl in H8;
          apply Events.Eapp_E0_inv in H4; destruct H4; subst;
          apply no_effect_hasSPSR in H5; rewrite H5 in * |- *; clear H5 (* m6=m7*).
        (* CurrentModeHasSPSR(proc) evaluates to true *)
        inv H12.
        apply (same_cp_SR e m7 
          (_Arm_State.set_reg s d (add (add (reg_content (Arm6_State.proc s) n) so) 
            (_Arm_State.cpsr s) [Cbit])) 
          Events.E0 mfin v4 und) in psrel;
          [idtac | exact H2 ];
        apply (sbit_not_changed m7 e cp_SR v4 mfin) in sfrel;
          [idtac | exact H2];
        apply (cond_not_changed m7 e cp_SR v4 mfin) in cfrel;
          [idtac | exact H2];
        apply (d_not_changed m7 e cp_SR v4 mfin) in dfrel;
          [idtac | exact H2];
        apply (n_not_changed m7 e cp_SR v4 mfin) in nfrel;
          [idtac | exact H2];
        apply (so_not_changed m7 e cp_SR v4 mfin) in sofrel;
          [clear H2 | exact H2].      
        admit.
        (* CurrentModeHasSPSR(proc) evaluates to false *)
        inv H12.
        apply (same_unpred e m7 
                (_Arm_State.set_reg s d
                  (add (add (reg_content (Arm6_State.proc s) n) so)
                    (_Arm_State.cpsr s) [Cbit])) 
                Events.E0 mfin v4) in psrel;
        [idtac | exact H2];
        apply (sbit_not_changed m7 e unpred v4 mfin) in sfrel;
          [idtac | exact H2];
        apply (cond_not_changed m7 e unpred v4 mfin) in cfrel;
          [idtac | exact H2];
        apply (d_not_changed m7 e unpred v4 mfin) in dfrel;
          [idtac | exact H2];
        apply (n_not_changed m7 e unpred v4 mfin) in nfrel;
          [idtac | exact H2];
        apply (so_not_changed m7 e unpred v4 mfin) in sofrel;
          [clear H2 | exact H2]. 
        admit.
      (* ((S == 1) && (d == 15)) evaluates to false *)
      inv H11;
          simpl in H8; 
          apply no_effect_is_S_set in H5; rewrite H5 in * |- *; clear H5; (* m6=m7*)
          apply Events.Eapp_E0_inv in H4; destruct H4; subst.
        (* S == 1 evaluates to true *)
        inv H12 ;[idtac | nod].
        apply Events.Eapp_E0_inv in H3; destruct H3; subst.
        inv H4.
        apply (same_nflag_assgnt e m7 
            (_Arm_State.set_reg s d
               (add (add (reg_content (Arm6_State.proc s) n) so)
                  (_Arm_State.cpsr s) [Cbit])) d Events.E0 m8 v4) in psrel;
        [idtac| exact dfrel| exact H2];
        apply (d_not_changed m7 e nflag_assgnt v4 m8) in dfrel;
          [idtac | exact H2];
        apply (n_not_changed m7 e nflag_assgnt v4 m8) in nfrel;
          [idtac | exact H2];
        apply (so_not_changed m7 e nflag_assgnt v4 m8) in sofrel;
          [clear H2 | exact H2].
        inv H7 ;[idtac | nod].
        apply Events.Eapp_E0_inv in H3; destruct H3; subst.
        inv H4.
        apply (same_zflag_assgnt e m8 
          (Arm6_State.set_cpsr_bit
            (_Arm_State.set_reg s d
              (add (add (reg_content (Arm6_State.proc s) n) so)
                (_Arm_State.cpsr s) [Cbit])) Nbit
            (reg_content
              (Arm6_State.proc
                (_Arm_State.set_reg s d
                  (add (add (reg_content (Arm6_State.proc s) n) so)
                    (_Arm_State.cpsr s) [Cbit]))) d) [n31]) 
          d Events.E0 m9 v5) in psrel;
        [idtac| exact dfrel | exact H2];
        apply (d_not_changed m8 e zflag_assgnt v5 m9) in dfrel;
          [idtac | exact H2];
        apply (n_not_changed m8 e zflag_assgnt v5 m9) in nfrel;
          [idtac | exact H2];
        apply (so_not_changed m8 e zflag_assgnt v5 m9) in sofrel;
          [clear H2 | exact H2].
        inv H11 ;[idtac | nod];
        apply Events.Eapp_E0_inv in H3; destruct H3; subst.
        inv H4.
        apply (same_cflag_assgnt m9 e 
          (_Arm_State.set_cpsr_bit
            (Arm6_State.set_cpsr_bit
              (_Arm_State.set_reg s d
                (add (add (reg_content (Arm6_State.proc s) n) so)
                  (_Arm_State.cpsr s) [Cbit])) Nbit
              (reg_content
                (Arm6_State.proc
                  (_Arm_State.set_reg s d
                    (add (add (reg_content (Arm6_State.proc s) n) so)
                      (_Arm_State.cpsr s) [Cbit]))) d) [n31]) Zbit
            (if Util.zeq
              (Arm6_State.reg_content
                (Arm6_State.set_cpsr_bit
                  (_Arm_State.set_reg s d
                    (add
                      (add (reg_content (Arm6_State.proc s) n) so)
                      (_Arm_State.cpsr s) [Cbit])) Nbit
                  (reg_content
                    (Arm6_State.proc
                      (_Arm_State.set_reg s d
                        (add
                          (add
                            (reg_content (Arm6_State.proc s) n)
                            so) (_Arm_State.cpsr s) [Cbit]))) d)
                  [n31]) d) 0
              then repr 1
              else repr 0))
          n so Events.E0 m10 v6) in psrel;
        [idtac| exact nfrel | exact sofrel| exact H2];
        apply (n_not_changed m9 e cflag_assgnt v6 m10) in nfrel;
          [idtac | exact H2];
        apply (so_not_changed m9 e cflag_assgnt v6 m10) in sofrel;
          [clear H2 | exact H2].
        inv H7.
        apply (same_vflag_assgnt m10 e 
            (_Arm_State.set_cpsr_bit
               (_Arm_State.set_cpsr_bit
                  (Arm6_State.set_cpsr_bit
                     (_Arm_State.set_reg s d
                        (add (add (reg_content (Arm6_State.proc s) n) so)
                           (_Arm_State.cpsr s) [Cbit])) Nbit
                     (reg_content
                        (Arm6_State.proc
                           (_Arm_State.set_reg s d
                              (add
                                 (add (reg_content (Arm6_State.proc s) n) so)
                                 (_Arm_State.cpsr s) [Cbit]))) d) [n31]) Zbit
                  (if Util.zeq
                        (Arm6_State.reg_content
                           (Arm6_State.set_cpsr_bit
                              (_Arm_State.set_reg s d
                                 (add
                                    (add (reg_content (Arm6_State.proc s) n)
                                       so) (_Arm_State.cpsr s) [Cbit])) Nbit
                              (reg_content
                                 (Arm6_State.proc
                                    (_Arm_State.set_reg s d
                                       (add
                                          (add
                                             (reg_content 
                                                (Arm6_State.proc s) n) so)
                                          (_Arm_State.cpsr s) [Cbit]))) d)
                              [n31]) d) 0
                   then repr 1
                   else repr 0)) Cbit
               (Arm6_Functions.CarryFrom_add3
                  (Arm6_State.reg_content
                     (_Arm_State.set_cpsr_bit
                        (Arm6_State.set_cpsr_bit
                           (_Arm_State.set_reg s d
                              (add
                                 (add (reg_content (Arm6_State.proc s) n) so)
                                 (_Arm_State.cpsr s) [Cbit])) Nbit
                           (reg_content
                              (Arm6_State.proc
                                 (_Arm_State.set_reg s d
                                    (add
                                       (add
                                          (reg_content (Arm6_State.proc s) n)
                                          so) (_Arm_State.cpsr s) [Cbit]))) d)
                           [n31]) Zbit
                        (if Util.zeq
                              (Arm6_State.reg_content
                                 (Arm6_State.set_cpsr_bit
                                    (_Arm_State.set_reg s d
                                       (add
                                          (add
                                             (reg_content 
                                                (Arm6_State.proc s) n) so)
                                          (_Arm_State.cpsr s) [Cbit])) Nbit
                                    (reg_content
                                       (Arm6_State.proc
                                          (_Arm_State.set_reg s d
                                             (add
                                                (add
                                                  (reg_content
                                                  (Arm6_State.proc s) n) so)
                                                (_Arm_State.cpsr s) [Cbit])))
                                       d) [n31]) d) 0
                         then repr 1
                         else repr 0)) n) so
                  (Arm6_State.cpsr
                     (_Arm_State.set_cpsr_bit
                        (Arm6_State.set_cpsr_bit
                           (_Arm_State.set_reg s d
                              (add
                                 (add (reg_content (Arm6_State.proc s) n) so)
                                 (_Arm_State.cpsr s) [Cbit])) Nbit
                           (reg_content
                              (Arm6_State.proc
                                 (_Arm_State.set_reg s d
                                    (add
                                       (add
                                          (reg_content (Arm6_State.proc s) n)
                                          so) (_Arm_State.cpsr s) [Cbit]))) d)
                           [n31]) Zbit
                        (if Util.zeq
                              (Arm6_State.reg_content
                                 (Arm6_State.set_cpsr_bit
                                    (_Arm_State.set_reg s d
                                       (add
                                          (add
                                             (reg_content 
                                                (Arm6_State.proc s) n) so)
                                          (_Arm_State.cpsr s) [Cbit])) Nbit
                                    (reg_content
                                       (Arm6_State.proc
                                          (_Arm_State.set_reg s d
                                             (add
                                                (add
                                                  (reg_content
                                                  (Arm6_State.proc s) n) so)
                                                (_Arm_State.cpsr s) [Cbit])))
                                       d) [n31]) d) 0
                         then repr 1
                         else repr 0))) [Cbit])) n so Events.E0 mfin v7) in psrel;
        [clear H2| exact nfrel | exact sofrel| exact H2].
        admit.

        (* S == 1 evaluates to false *)
        inv H12.
        (*unfold adc_return. unfold S.ADC_step. unfold _get_st. unfold bind_s. unfold bind.
        erewrite condpass_true. simpl. erewrite S_set_and_is_pc_false. simpl.
        erewrite S_not_set. simpl.
        apply (same_setregpc (Genv.globalenv prog_adc) e m5 s Events.E0 mfin v1 d 
          (add (add (Arm6_State.reg_content s n) so) (Arm6_State.cpsr s) [Cbit])).*)
        admit.
      
    (* ConditionPassed(&proc->cpsr, cond) evaluates to false *)
    unfold adc_return; unfold S.ADC_step; unfold _get_st; unfold bind_s; unfold bind.
    rewrite (condpass_false v1); [simpl|exact H9]. 
    inv H10.
    apply psrel.
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