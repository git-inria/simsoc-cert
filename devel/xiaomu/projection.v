(* This file describe the relation between COQ and C state for ARM *)

Require Import Globalenvs Memory.
Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors. 
Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import adc_compcert_fixed.

(* Some constants for ADC *)

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
Definition cpsr_ofs:int:=ofs_of_fld cpsr typ_struct_SLv6_Processor.

Definition spsr_ofs:int:=ofs_of_fld spsrs typ_struct_SLv6_Processor.

Definition mode_ofs:int:=
  add (ofs_of_fld cpsr typ_struct_SLv6_Processor) 
  (ofs_of_fld mode typ_struct_SLv6_StatusRegister).

Definition reg_ofs (id:AST.ident):int:=
  ofs_of_fld id typ_struct_SLv6_Processor.

Definition mmu_ofs:int:=ofs_of_fld mmu_ptr typ_struct_SLv6_Processor.

Definition mem_ofs:int:=ofs_of_fld mem typ_struct_SLv6_MMU.

Definition cp15_ofs:int:=ofs_of_fld cp15 typ_struct_SLv6_Processor.

Definition pc_ofs:int:=ofs_of_fld pc typ_struct_SLv6_Processor.

Definition id_ofs:int:=ofs_of_fld id typ_struct_SLv6_Processor.

Definition jump_ofs:int:=ofs_of_fld jump typ_struct_SLv6_Processor.

Definition proc_loc (m:Mem.mem) (e:env):option val:=
  match e!proc with
    |Some(b,_)=>
      match 
        (load_value_of_type (Tpointer typ_SLv6_Processor) m b Int.zero) with
        |Some(Vptr b o) as v=>v
        |_=>None
      end
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

(* singal bit parameter projection *)
Definition bit_proj (m:Mem.mem) (e:env) (id:AST.ident):bool:=
  eq (varg_proj (param_val id m e)) w1.

(* condition parameter projection *)
Definition cond_proj (m:Mem.mem) (e:env):opcode:= 
  let c:=condition (varg_proj (param_val cond m e)) in
    match c with
      |Some c'=>c'
      |None=>AL
    end.

(* register parameter projection *)
Definition reg_proj (m:Mem.mem) (e:env) (id:AST.ident):regnum:=
  mk_regnum (varg_proj (param_val id m e)).

(* bits parameter projection*)
Definition bits_proj (m:Mem.mem) (e:env) (id:AST.ident):word:=
  varg_proj (param_val shifter_operand m e).


Definition find_field (ofs:int) (m:Mem.mem) (e:env)
  :option val:=
  match proc_loc m e with
    |Some(Vptr b o) => Some (Vptr b (add o ofs))
    |_=>None
  end.

Definition find_cpsr (m:Mem.mem) (e:env):option val:=
  find_field cpsr_ofs m e.

Definition find_spsr (m:Mem.mem) (e:env):option val:=
  find_field spsr_ofs m e.

Definition find_reg (m:Mem.mem) (e:env) (rid:AST.ident):option val:=
  find_field (ofs_of_fld rid typ_struct_SLv6_Processor) m e.

Definition find_cp15 (m:Mem.mem) (e:env):option val:=
  find_field cp15_ofs m e.

Definition find_id (m:Mem.mem) (e:env):option val:=
  find_field id_ofs m e.

Definition find_jump (m:Mem.mem) (e:env):option val:=
  find_field jump_ofs m e.

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
Definition find_mmu (m:Mem.mem) (e:env):option val:=
  match proc_loc m e with
    |Some(Vptr bp op)=>
      match 
        (load_value_of_type (Tpointer typ_SLv6_MMU) m bp (add op mmu_ofs)) with
        |Some(Vptr bm om) as v=>v
        |_=>None
      end
    |_=>None
  end.

Definition find_mem (m:Mem.mem) (e:env):option val:=
  match find_mmu m e with
    |Some(Vptr bm om)=>
      match 
        (load_value_of_type (Tpointer(Tint I8 Unsigned)) m bm (add om mem_ofs)) with
        |Some(Vptr b o) as v=>v
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
      match 
        (load_value_of_type (Tpointer (Tint I32 Unsigned)) m b ofs) with
        |Some(Vptr b o) as v=>v
        |_=>None
      end
    |_=>None
  end.

Definition pc_usereg15 (m:Mem.mem) (e:env):Prop:=
  find_pc m e = find_reg m e user_regs.

Definition find_fld (f: Mem.mem->env->option val) (fld:fieldlist)
  (id:AST.ident) (m:Mem.mem) (e:env):
  option val:=
  match f m e with
    |Some(Vptr bp op)=> 
      Some(Vptr bp (add op (ofs_of_fld id fld)))
    |_=>None
  end.

(*
(*memory blocks of SystemCoproc*)
(*Record sc_mem := mk_scm
  {eeb: option val;
    ub: option val;
    vb: option val}.
*)
Record sc_mem := mk_scm
  {eeb: val;
    ub: val;
    vb: val}.

Definition slv6_sc (m:Mem.mem) (e:env):option sc_mem:=
  let fld_v b o id:= Vptr b (add o (ofs_of_fld id typ_struct_SLv6_SystemCoproc))
    in
    match find_cp15 m e with
      |Some(Vptr b o)=> 
        Some(mk_scm (fld_v b o ee_bit) (fld_v b o u_bit) (fld_v b o v_bit))
      |_=>None
  end.

(*memory blocks of StatusRegister*)
(*Record sr_mem := mk_srm
  {nf: option val;
    zf: option val;
    cf: option val;
    vf: option val;
    qf: option val;
    jf: option val;
    ge0: option val;
    ge1: option val;
    ge2: option val;
    ge3: option val;
    ef: option val;
    af: option val;
    i_f: option val;
    ff: option val;
    tf: option val;
    md: option val;
    bg: option val}.
*)
Record sr_mem := mk_srm
  {nf: val;
    zf: val;
    cf: val;
    vf: val;
    qf: val;
    jf: val;
    ge0: val;
    ge1: val;
    ge2: val;
    ge3: val;
    ef: val;
    af: val;
    i_f: val;
    ff: val;
    tf: val;
    md: val;
    bg: val}.

Definition slv6_cpsr (m:Mem.mem) (e:env):option sr_mem:=
  let fld_v b o id:=Vptr b (add o (ofs_of_fld id typ_struct_SLv6_StatusRegister))
    in
    match find_cpsr m e with
      |Some(Vptr b o)=>
        Some(mk_srm (fld_v b o N_flag) (fld_v b o Z_flag) (fld_v b o C_flag) 
          (fld_v b o V_flag) (fld_v b o Q_flag) (fld_v b o J_flag) 
          (fld_v b o GE0) (fld_v b o GE1) (fld_v b o GE2) (fld_v b o GE3)
          (fld_v b o E_flag) (fld_v b o A_flag) (fld_v b o I_flag) 
          (fld_v b o F_flag) (fld_v b o T_flag) (fld_v b o mode) 
          (fld_v b o background))
    |_=>None
    end.

Definition mode2mode (pm:proc_mode) :=
  match pm with
    |usr|sys=>(user_regs,5)
    |exn e=>match e with
              |fiq=>(fiq_regs,0)
              |irq=>(irq_regs,1)
              |svc=>(svc_regs,2)
              |abt=>(abt_regs,3)
              |und=>(und_regs,4)
            end
  end.

(*Definition find_spsr_m (m:Mem.mem) (e:env) (em:exn_mode):option val:=
  let ofs o :=
    add o (repr ((snd (mode2mode (exn em)))*sizeof typ_SLv6_StatusRegister)) in
  match find_spsr m e with
    |Some(Vptr b o)=>
      Some (Vptr b (ofs o))
    |_=>None
  end.
*)
Definition find_spsr_m (m:Mem.mem) (e:env):option(exn_mode->val):=
  let ofs o em:=
    add o (repr ((snd (mode2mode (exn em)))*sizeof typ_SLv6_StatusRegister)) in
  match find_spsr m e with
    |Some(Vptr b o)=>
      Some(fun em=>(Vptr b (ofs o em)))
    |_=>None
  end.

Definition blk_spsr (m:Mem.mem) (e:env):=
  let ofs o em:=
    add o (repr ((snd (mode2mode (exn em)))*sizeof typ_SLv6_StatusRegister)) in
  match find_spsr m e with
    |Some(Vptr b o)=>
      Some(fun em=>(b, (ofs o em)))
    |_=>None
  end.

Definition slv6_spsr (m:Mem.mem) (e:env):option(exn_mode->sr_mem):=
  let fld_v b o id:=Vptr b (add o (ofs_of_fld id typ_struct_SLv6_StatusRegister))
    in
    match blk_spsr m e with
      |Some v=>
        Some(fun em=>let (b,o):=v em in 
          mk_srm (fld_v b o N_flag) (fld_v b o Z_flag) (fld_v b o C_flag) 
          (fld_v b o V_flag) (fld_v b o Q_flag) (fld_v b o J_flag) 
          (fld_v b o GE0) (fld_v b o GE1) (fld_v b o GE2) (fld_v b o GE3)
          (fld_v b o E_flag) (fld_v b o A_flag) (fld_v b o I_flag) 
          (fld_v b o F_flag) (fld_v b o T_flag) (fld_v b o mode) 
          (fld_v b o background))
      |_=>None
    end.

(*memory blocks of MMU*)
Record mmu_mem := mk_mmum
  {bgn: val;
    sz: val;
    ed: val;
    mm: val}.

(*Record mmu_mem := mk_mmum
  {bgn: option val;
    sz: option val;
    ed: option val;
    mm: option val}.
*)

Definition slv6_mmu (m:Mem.mem) (e:env):option mmu_mem:=
  let fld_v b o id:=Vptr b (add o (ofs_of_fld id typ_struct_SLv6_MMU)) in
  match find_mmu m e with
    |Some(Vptr b o)=>
      Some(mk_mmum (fld_v b o begin) (fld_v b o size) 
                   (fld_v b o _end) (fld_v b o mem))
    |_=>None
  end.

(*memory blocks of proc*)
Record proc_mem := mk_pcm
  {mmup: mmu_mem;
    cpsr_m: sr_mem;
    spsr_m: exn_mode->sr_mem;
    sc: sc_mem;
    id: val;
    rg: register->val;
    p: val;
    jp: val}.

Definition reg2reg (r:register):=
  match r with
    |R k=>(user_regs,k)
    |R_svc k _=>(svc_regs,mk_regnum k)
    |R_abt k _=>(abt_regs,mk_regnum k)
    |R_und k _=>(und_regs,mk_regnum k)
    |R_irq k _=>(irq_regs,mk_regnum k)
    |R_fiq k _=>(fiq_regs,mk_regnum k)
  end.

Definition slv6_proc (m:Mem.mem) (e:env):option proc_mem:=
  let fld_v b o i:=Vptr b (add o (ofs_of_fld i typ_struct_SLv6_Processor)) in
  let fld_reg b o r:=
    Vptr b (add o (ofs_of_fld (fst(reg2reg r)) 
      typ_struct_SLv6_Processor)) in
  let mm:=slv6_mmu m e in
  let c:=slv6_cpsr m e in
  let s:=slv6_spsr m e in
  let sc:=slv6_sc m e in
    match proc_loc m e with
      |Some(Vptr b o)=>
        match mm,c,(*fs,is,ss,abs,us,*)s,sc with
          |Some vm,Some vc,(*Some vfs,Some vis,Some vss,Some vabs,Some vus,*)
            Some vs,Some vsc =>
            Some(mk_pcm vm vc (*vfs vis vss vabs vus*) vs vsc 
              (fld_v b o adc_compcert_fixed.id) 
              (fld_reg b o)
              (fld_v b o pc)
              (fld_v b o jump))
          |_,_,_,_(*,_,_,_,_*)=>None
        end
      |_=>None
    end.

(* From a StateRegister Tstruct to word*)
Definition sr_proj (m:Mem.mem) (sr:sr_mem) :option word:=
  let valof ptr typ :=
    match ptr with
      |Vptr b o=>load_value_of_type typ m b o
      |_=>None
    end in
    let setcpsr n ov ow :=
      match ov, ow with
        |Some(Vint v), Some w=>Some (set_bit n v w)
        |_,_=>None
      end in 
    let setcpsrs n1 n2 ov ow :=
      match ov, ow with
        |Some(Vint v), Some w=>Some (set_bits n1 n2 v w)
        |_,_=>None
      end in 
    (setcpsr Nbit (valof sr.(nf) (Tint I8 Unsigned))
    (setcpsr Zbit (valof sr.(zf) (Tint I8 Unsigned))
    (setcpsr Cbit (valof sr.(cf) (Tint I8 Unsigned))
    (setcpsr Vbit (valof sr.(vf) (Tint I8 Unsigned))
    (setcpsr Qbit (valof sr.(qf) (Tint I8 Unsigned))
    (setcpsr Jbit (valof sr.(jf) (Tint I8 Unsigned))
(* set bits 16 to 19 is set GEbits*)
    (setcpsr 19%nat (valof sr.(ge3) (Tint I8 Unsigned))
    (setcpsr 18%nat (valof sr.(ge2) (Tint I8 Unsigned))
    (setcpsr 17%nat (valof sr.(ge1) (Tint I8 Unsigned))
    (setcpsr 16%nat (valof sr.(ge0) (Tint I8 Unsigned))
    (setcpsr Ebit (valof sr.(ef) (Tint I8 Unsigned))
    (setcpsr Abit (valof sr.(af) (Tint I8 Unsigned))
    (setcpsr Ibit (valof sr.(i_f) (Tint I8 Unsigned))
    (setcpsr Fbit (valof sr.(ff) (Tint I8 Unsigned)) 
    (setcpsr Tbit (valof sr.(tf) (Tint I8 Unsigned)) 
(* set bits 0 to 4 is set Mbits*)
    (setcpsrs 0%nat 4%nat (valof sr.(md) (Tint I32 Unsigned)) 
      (Some Int.zero))))))))))))))))).

(* Projection form C cpsr to COQ cpsr*)
Definition cpsr_proj (m:Mem.mem) (c:sr_mem):option word:=
  sr_proj m c.

Definition spsr_proj (m:Mem.mem) (s:exn_mode->sr_mem) (em:exn_mode):word:=
  let sr:=s em in
    match sr_proj m sr with
      |Some w=>w
      |None=>repr 16
    end.

(* Projection from C mode in cpsr, to COQ mode*)
Definition mode_proj (m:Mem.mem) (c:sr_mem) :option proc_mode:=
  match c.(md) with
    |Vptr b o=>
      match load_value_of_type (Tint I32 Unsigned) m b o with
        |Some(Vint v)=>proc_mode_of_word v
        |_=>None
      end
    |_=>None
  end.


(* Projection from C reg to COQ reg*)
Definition regs_proj (m:Mem.mem) (p:proc_mem) (r:register):word:=
  let valof k:=
    match p.(rg) r with
      |Vptr b o=>load_value_of_type (Tint I32 Unsigned) m b (add o (repr k))
      |_=>None
    end in
    let reg_val v :=
    match v with
      |Some(Vint v')=> v'
      |_=>w0
    end in
    reg_val (valof (snd(reg2reg r))).


(* Projection from C memory to COQ memory*)
Definition mem_proj (m:Mem.mem) (mu:mmu_mem) (ad:address): word:=
  match mu.(mm) with
    |Vptr b o=>
      match
        load_value_of_type (Tint I8 Unsigned) m b (add o (word_of_address ad)) with
        |Some(Vint v)=>v
        |_=>w0
      end
    |_=>w0
  end.

(*Definition mem_proj (m:Mem.mem) (e:env) (ad:address):option word:=
  match (find_mem m e) with
    |Some(Vptr b o)=>
      match load_value_of_type (Tint I8 Unsigned) m b 
        (add o (word_of_address ad)) with
        |Some(Vint v)=>Some v
        |_=>None
      end
    |_=>None
  end.*)

(* Projection from C cp15 to COQ SCC register*)
Definition screg_proj (m:Mem.mem) (sc:sc_mem) (r:regnum): word:=
  let bit_val_e :=
  match sc.(eeb) with
    |Vptr b o=> load_value_of_type (Tint I8 Unsigned) m b o
    |_=>None
  end in
  let bit_val_u :=
  match sc.(ub) with
    |Vptr b o=> load_value_of_type (Tint I8 Unsigned) m b o
    |_=>None
  end in
  let bit_val_v :=
  match sc.(vb) with
    |Vptr b o=> load_value_of_type (Tint I8 Unsigned) m b o
    |_=>None
  end in  
  let setscreg n ov ow :=
    match ov, ow with
      |Some(Vint v),w=>set_bit n v w
      |_,_=>w0
    end in
    setscreg Vbit (bit_val_v) 
    (setscreg Ubit (bit_val_u) 
    (setscreg EEbit (bit_val_e) Int.zero)).  


(* Projection from C proc to COQ state. exn in COQ proc state is assigned by
   a nil exception list*)

Definition proc_proj (m:Mem.mem) (e:env):option (Arm6_State.state):=
  let mkpst ocpsr vspsr vreg omode:=
    match ocpsr, omode with
      |Some vcpsr, Some vmode=>
        Some (Arm6_Proc.mk_state vcpsr vspsr vreg nil vmode)
      |_,_ => None
    end in
    let mksst vscreg vmem := Arm6_SCC.mk_state vscreg vmem in
      let mkst oproc vscc :=
        match oproc with
          |Some vproc=>Some (Arm6_State.mk_state vproc vscc)
          |_=>None
        end in
        let opc := slv6_proc m e in
        match opc with
          |Some pc =>
            mkst (mkpst (cpsr_proj m pc.(cpsr_m)) (spsr_proj m pc.(spsr_m)) 
            (regs_proj m pc) 
            (mode_proj m pc.(cpsr_m)))
          (mksst (screg_proj m pc.(sc)) (mem_proj m pc.(mmup)))
          |None=>None
        end.
*)


(* From a StateRegister Tstruct to word*)
(* Every bit is transformed from uint8 to one bit *)

Definition fld_sr:= typ_struct_SLv6_StatusRegister.


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
    match find_reg m e id with 
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

Definition fld_sc :=typ_struct_SLv6_SystemCoproc.

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


(* Stating theorems *)

Require Import Arm6_Simul.
Import I.
Import Arm6_Functions.Semantics.

(*Inductive proc_state_related : Mem.mem -> env -> @result unit -> Prop :=
  |proc_state_related_ok : 
    forall m e l b v, 
      proc_proj m e = Some v ->
      proc_state_related m e (Ok tt (mk_semstate l b v))
  |state_not_ok: 
    forall e m mes,
      proc_proj m e = None ->
      proc_state_related m e (Ko mes)
  |state_todo: 
    forall e m mes,
      proc_proj m e = None ->
      proc_state_related m e (Todo mes).*)

Inductive proc_state_related : Mem.mem -> env -> @result unit -> Prop :=
  |proc_state_related_ok : 
    forall m e l b, proc_state_related m e (Ok tt (mk_semstate l b (proc_proj m e)))
  |state_not_ok: forall e m mes, proc_state_related m e (Ko mes)
  |state_todo: forall e m mes, proc_state_related m e (Todo mes).

(* Functional relation between the C memory module which contains proc, 
   and the COQ specification of Arm6 state *)
(*Definition proc_state_func_related (m:Mem.mem) (e:env) (s:Arm6_State.state) :Prop:=
  proc_proj m e = s.*)
