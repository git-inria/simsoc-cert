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

(*Definition pc_usereg15 (m:Mem.mem) (e:env):Prop:=
  find_pc m e = find_reg user_regs *)

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
Import Arm6_Functions.Semantics.S.
Import I.

(* Human readable renaming of [p], which is generated by the Coq printer *)
Definition prog_adc := p.

Definition adc_return sbit cond d n so s :=
  let r:= S.ADC_step sbit cond d n so (mk_semstate nil true s) in
    match r with
      |Ok _ (mk_semstate l b s')=>s'
      |_=>s
    end.


(*Section related.

Variable proc_blk: Values.block.
Variable S_blk: Values.block.
Variable e:env.
Variable m2:Mem.mem.
Hypothesis Proc_ex: e!proc = Some (proc_blk, typ_SLv6_Processor).
Hypothesis S_ex: e!S = Some (S_blk,Tint I8 Unsigned).
Hypothesis Load_S: exists v, load_value_of_type (Tint I8 Unsigned) m2 S_blk Int.zero = Some v.
*)

Theorem related_aft_ADC: forall e m0 m1 m2 m3 vargs s out sbit cond d n so,
  alloc_variables empty_env m0 (ADC_body.(fn_params) ++ ADC_body.(fn_vars)) e m1 ->
  bind_parameters e m1 ADC_body.(fn_params) vargs m2 ->
(*Write a lemma to say alloc_var -> exist proc*)
  (exists p_blk, e!proc=Some(p_blk,typ_SLv6_Processor))->
  (exists sbit_blk, e!S=Some(sbit_blk,Tint I8 Unsigned))->
  (forall ch b ofs, Mem.valid_access m2 ch b ofs Readable) ->
  proc_state_func_related m2 e s ->
  sbit_func_related m2 e sbit ->
  cond_func_related m2 e cond ->
  d_func_related m2 e d ->
  n_func_related m2 e n ->
  so_func_related m2 e so ->
(*Write comment on choice between exec_stmt eval_funcall sstep, etc*)
  exec_stmt (Genv.globalenv prog_adc) e m2 ADC_body.(fn_body) Events.E0 m3 out ->
  (*eval_funcall (Genv.globalenv prog_adc) m0 (snd fun_ADC) vargs Events.E0 m' vres ->*)
  proc_state_func_related m3 e
  (adc_return sbit cond d n so s).
  








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