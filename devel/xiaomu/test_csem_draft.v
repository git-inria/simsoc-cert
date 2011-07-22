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

Definition S_proj (m:Mem.mem) (e:env):bool:=
  eq (varg_proj (param_val S m e)) w1.

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

Check proc_proj.

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
(*Definition prog_adc := adc_compcert_fixed.p.*)

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

(* Return the memory model which only relates to this ident *)
Parameter of_mem : AST.ident -> Mem.mem -> Mem.mem.

(*exp get_bit*)


Definition reg_id id :=
  Ecall (Evalof (Evar reg T2) T2)
  (Econs (Evalof (Evar proc T3) T3)
    (Econs 
      (Evalof (Evar id T4) T4) Enil)) T1.

Definition get_bit_reg :=
  Ecall (Evalof (Evar get_bit T16) T16)
  (Econs (reg_id d)
    (Econs (Eval (Vint (repr 31)) T9)
      Enil)) T4.

Axiom get_rg_ok :
  forall e m t m' a' st d,
    eval_expr (Genv.globalenv prog_adc) e m RV 
              (reg_id adc_compcert_fixed.d) t m' a' ->
    a'= (Eval (Vint (Arm6_State.reg_content st d)) T1).

Lemma same_nflag_assgnt :
  forall e m0 m0' vargs m l b s d t m' v,
    alloc_variables empty_env m0 
      (fun_internal_ADC.(fn_params) ++ fun_internal_ADC.(fn_vars)) e m0' ->
    bind_parameters e m0' fun_internal_ADC.(fn_params) vargs m ->
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    d_func_related m e d ->
    eval_expression (Genv.globalenv prog_adc) e m get_bit_reg t m' v->
    v = Vint ((Arm6_State.reg_content s d) [n31]).
Proof.
  intros until v. intros av bp psrel dfrel get_bit.
  inv get_bit. 
  (*rename H into get_bit_reg_exp, H0 into get_bit_reg_v.
  inv get_bit_reg_exp.*) 
  inv H.
  inv H4. inv H8. inv H9. inv H5.
  apply get_rg_ok with e m2 t1 m1 a1' s d in H4.
  rewrite H4 in *. 
  inv H13. inv H5. inv H14.
  inv H0. inv H6. inv H2. inv H4.
  inv H1.
    assert (e!get_bit=None).
    inv av. inv H9. inv H13. inv H14. inv H15. inv H17. inv H18. inv H19.
    simpl. reflexivity. rewrite H in H4. inv H4.
    inv H6.
    inv H7. inv H6. inv H10. inv H6. inv H13. simpl in H8.
    inv H8.
      (*cast int to int*) simpl in H16. simpl in H9. 
      inv H9;
        (*cast int to int*) simpl in H16;
        inv H3; inv H11;
        induction (eq_dec w0 w0); [idtac|inv H1|inv H3|inv H3].
        inv H1.
        inv H12. inv H0.
        inv H16. inv H4. simpl in H5.
        inv H5.
        inv H9. inv H5. inv H17. inv H16. inv H11. inv H19. inv H11. inv H18.
        inv H4; inv H6; simpl in H13; unfold sem_and in  H13; simpl in H13;
          [simpl|inv H8|inv H8].
          (*cast int to int*)
          destruct v1,v2; inv H13. inv H12. inv H11. simpl in H13.
          inv H1. simpl in H15. inv H16. simpl in H14. inv H17.
          inv H3. inv H19. inv H21.
          inv H10; inv H5.
          inv H4; [idtac|rewrite H17 in H5; inv H5].
          rewrite H17 in H9; inv H9.
          inv H12; inv H5.
          inv H4; [idtac|rewrite H16 in H5; inv H5].
          rewrite H16 in H10; inv H10.          
          simpl in H17. inv H17. simpl in H16. inv H16.
          unfold load_value_of_type in *; simpl in H8, H9.
          unfold store_value_of_type in *; simpl in H18, H20.
          assert (Mem.store AST.Mint32 m6 b2 (signed w0) (Vint (repr 31)) =
            Some m5).
          exact H20.
          apply Mem.load_store_other with
            AST.Mint32 _ _ _ _ _ AST.Mint32 b4 (signed w0) in H1; 
            [idtac|admit(*b<>b'*)].
          rewrite H1 in H8.
          eapply Mem.load_store_same in H18; [idtac|simpl; auto]. 
          rewrite H18 in H8.
          inv H8.
          eapply Mem.load_store_same in H20; [idtac|simpl; auto].
          rewrite H20 in H9.
          inv H9.
          inv H13.
          unfold bit. unfold bits. unfold bits_val. unfold masks.
          simpl masks_aux.
          rewrite and_commut.
          (*assert (forall c, and (repr 1) c = (repr c)).
             intro. unfold and. unfold bitwise_binop.
             apply eqm_samerepr. eapply eqm_trans. 2: apply Z_of_bits_of_Z.
             apply eqm_refl2. apply Z_of_bits_exten.
             intros. 
             fold one. rewrite unsigned_one.
             unfold wordsize. unfold Wordsize_32.wordsize.
             *)
          admit
(*Vint(zero_ext 8 (and (shru (Arm6_State.reg_content s d) (repr 31)) (repr 1)))
   = Vint (Arm6_State.reg_content s d) [n31]*).
        (*cast has no change*)
        inv H1; inv H4.
        inv H12. inv H0.
        inv H16. 
        inv H4. simpl in H5.
        inv H5.
        inv H9. inv H5. inv H17. inv H16. inv H11. inv H19. inv H11. inv H18.
        inv H4; inv H6; simpl in H13; unfold sem_and in  H13; simpl in H13;
          [simpl|inv H8|inv H8].
          destruct v1,v2; inv H13. inv H12. inv H11. simpl in H13.
          inv H1. simpl in H15. inv H16. simpl in H14. inv H17.
          inv H3. inv H19. inv H21.
          inv H10; inv H5.
          inv H4; [rewrite H17 in H9; inv H9|rewrite H17 in H5; inv H5].
          inv H12; inv H5.
          inv H4; [rewrite H16 in H10; inv H10|rewrite H16 in H5; inv H5].
          simpl in H17. inv H17. simpl in H16. inv H16.
          unfold load_value_of_type in *; simpl in H8, H9.
          unfold store_value_of_type in *; simpl in H18, H20.
          assert (Mem.store AST.Mint32 m6 b2 (signed w0) (Vint (repr 31)) =
            Some m5).
          exact H20.
          apply Mem.load_store_other with
            AST.Mint32 _ _ _ _ _ AST.Mint32 b4 (signed w0) in H1; 
            [idtac|admit(*b<>b'*)].
          rewrite H1 in H8.
          eapply Mem.load_store_same in H18; [idtac|simpl; auto]. 
          rewrite H18 in H8.
          inv H8.
          eapply Mem.load_store_same in H20; [idtac|simpl; auto].
          rewrite H20 in H9.
          inv H9.
          inv H13.
          admit
(*Vint(zero_ext 8 (and (shru (Arm6_State.reg_content s d) (repr 31)) (repr 1)))
   = Vint (Arm6_State.reg_content s d) [n31]*).
        (*cast has no change*)
        inv H1; inv H4.
        inv H3. inv H11; inv H0.
        induction (eq_dec w0 w0); [idtac|inv H1].
        inv H1. inv H12. simpl in H9.
        inv H16. 
        inv H4. simpl in H5. inv H5.
        inv H4; [idtac|inv H6|inv H6].
        inv H10; inv H4; inv H18; inv H17; inv H16; inv H11; inv H18; inv H11.
        inv H3; inv H17; inv H19.
        inv H5. inv H11. inv H12. simpl in H13. simpl in H19.
        inv H10. inv H17.
        inv H6; inv H10.
        inv H5; [rewrite H12 in H15; inv H15|rewrite H6 in H15; inv H15].        
        inv H8; [rewrite H10 in H14; inv H14|rewrite H5 in H14; inv H14].
        unfold load_value_of_type in *; simpl in H11, H20.
        unfold store_value_of_type in *; simpl in H16, H18.
        inv H9; simpl in H16.
        assert (Mem.store AST.Mint32 m4 b1 (signed w0) (Vint (repr 31)) =
          Some m5).
        exact H18.
        apply Mem.load_store_other with
          AST.Mint32 _ _ _ _ _ AST.Mint32 b0 (signed w0) in H3; 
          [idtac|admit(*b<>b'*)].
        rewrite H3 in H11.
        eapply Mem.load_store_same in H16; [idtac|simpl; auto].
        simpl in H16.
        rewrite H16 in H11; inv H11.
        eapply Mem.load_store_same in H18; [idtac|simpl; auto].
        simpl in H18.
        rewrite H18 in H20; inv H20.
        unfold sem_shr in H19. simpl in H19. inv H19.
        inv H13. simpl.
        admit
(*Vint(zero_ext 8 (and (shru (Arm6_State.reg_content s d) (repr 31)) (repr 1)))
   = Vint (Arm6_State.reg_content s d) [n31]*).
        assert (Mem.store AST.Mint32 m4 b1 (signed w0) (Vint (repr 31)) =
          Some m5).
        exact H18.
        apply Mem.load_store_other with
          AST.Mint32 _ _ _ _ _ AST.Mint32 b0 (signed w0) in H3; 
          [idtac|admit(*b<>b'*)].
        rewrite H3 in H11.
        eapply Mem.load_store_same in H16; [idtac|simpl; auto].
        simpl in H16.
        rewrite H16 in H11; inv H11.
        eapply Mem.load_store_same in H18; [idtac|simpl; auto].
        simpl in H18.
        rewrite H18 in H20; inv H20.
        unfold sem_shr in H19. simpl in H19. inv H19.
        inv H13. simpl.
        admit
(*Vint(zero_ext 8 (and (shru (Arm6_State.reg_content s d) (repr 31)) (repr 1)))
   = Vint (Arm6_State.reg_content s d) [n31]*).
Qed.
          


(* Assume that every function that ADC calls, executes correctly
   and the C proc and ARM state related after these function execution *)
Axiom functions_behavior_ok:
  forall e l b s vf fd m vargs t m' vres l' b' s',
    proc_state_related (of_mem proc m) e (Ok tt (mk_semstate l b s)) ->
    Genv.find_funct (Genv.globalenv prog_adc) vf = Some fd ->
    eval_funcall (Genv.globalenv prog_adc) m fd vargs t m' vres ->
    proc_state_related (of_mem proc m') e (Ok tt (mk_semstate l' b' s')).

(* Assume that call to unpredictable leads to an Ko result*)
Axiom funct_unpredictable:
  forall e semstt vf fd m vargs t m' vres,
    proc_state_related (of_mem proc m) e (Ok tt semstt) ->
    Genv.find_funct (Genv.globalenv prog_adc) vf = Some fd ->
    eval_funcall (Genv.globalenv prog_adc) m fd vargs t m' vres ->
    proc_state_related (of_mem proc m') e 
    (unpredictable Arm6_Message.EmptyMessage semstt).

(* Assume function reg_n only load from memory, not change it*)

Axiom get_reg_ok :
  forall e id m t m' r,
    eval_expr (Genv.globalenv prog_adc) e m RV (reg_id id) t m' r ->
    eval_expr (Genv.globalenv prog_adc) e m RV (reg_id id) t m r/\m=m'. 

Definition oldrn_assgnt := 
  Eassign (Evar old_Rn T1) (reg_id n) T1.

(* Assum the assignment of old_Rn has no effect on the part of memory
   where located proc*)
Axiom set_oldrn_ok:
  forall m m' v oldrn_blk ofs,
    store_value_of_type T1 m oldrn_blk ofs v = Some m'->
    of_mem proc m = of_mem proc m'.

Lemma oldrn_assgnt_ok:
 forall e m l b s t m' v,
  proc_state_related (of_mem proc m) e (Ok tt (mk_semstate l b s)) ->
  eval_expression (Genv.globalenv prog_adc) e m
    oldrn_assgnt t m' v ->
  proc_state_related (of_mem proc m') e (Ok tt (mk_semstate l b s)).
Proof.
  intros until v. intros psrel rn_as.
  inv rn_as. inv H. inv H4.
  eapply get_reg_ok in H5. inv H5.
  simpl in *.
  eapply set_oldrn_ok in H11.
  rewrite <- H11. exact psrel.
Qed.

(* Lemmas on if ConditionPassed*)
Definition condpass :=
  Ecall (Evalof (Evar ConditionPassed T5) T5)
  (Econs
    (Eaddrof
      (Efield (Ederef (Evalof (Evar proc T3) T3) T6) cpsr
        T6) T6) (Econs (Evalof (Evar cond T7) T7) Enil)) T5.

Axiom no_effect_condpass :
  forall e m m' t v,
    eval_expression (Genv.globalenv prog_adc) e m condpass t m' v ->    
    m = m'/\eval_expression (Genv.globalenv prog_adc) e m condpass t m' v.

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
    (Econs (Evalof (Evar d T4) T4)
      (Econs
        (Ebinop Oadd
          (Ebinop Oadd
            (Evalof (Evar old_Rn T1) T1)
            (Evalof (Evar shifter_operand T1) T1)
            T1)
          (Evalof
            (Efield
              (Efield
                (Ederef
                  (Evalof (Evar proc T3) T3)
                  (Tpointer T3)) cpsr T6)
              C_flag T4) T4) T1) Enil))) T9.

(*Axiom set_regpc_store :
  forall m m' t v p_blk,
    eval_expression (Genv.globalenv prog_adc) e m set_regpc t m' v ->
    store_value_of_type T1 m p_blk (add (reg_ofs user_regs) (repr 15)) v = Some m'.

Axiom set_regpc_ok:
  forall m s0 s m' t v n so ,
    eval_expression (Genv.globalenv prog_adc) e m set_regpc t m' v ->
    mk_reg (R (mk_regnum 15)) 
    (fun rn => (add (add (Arm6_State.reg_content s0 n) so)
      (Arm6_State.cpsr s) [Cbit])) e (of_mem proc m) = (of_mem proc m').*)

Lemma same_setregpc :
  forall e m l b s0 s t m' v d n so ,
    proc_state_related (of_mem proc m) e (Ok tt (mk_semstate l b s)) ->
    eval_expression (Genv.globalenv prog_adc) e m set_regpc t m' v ->
    (forall l b, proc_state_related (of_mem proc m') e 
      (Ok tt (mk_semstate l b
        (Arm6_State.set_reg s d (add (add (Arm6_State.reg_content s0 n) so)
          ((Arm6_State.cpsr s)[Cbit]) ))))).
Proof.
  intros until so. intros psrel setreg. intros.
  inv setreg. inv H. inv H4. inv H9. inv H5. inv H4. inv H5.
  inv H14. inv H4. inv H5. inv H13. inv H4. inv H17. inv H15.
  inv H4. inv H14. inv H19. inv H4. inv H18. inv H4. inv H14.
  inv H13. inv H4. inv H5.
  apply (functions_behavior_ok e l b s vf fd m2 vargs t3 m' vres l0 b0
    (Arm6_State.set_reg s d
      (add (add (Arm6_State.reg_content s0 n) so)
        (Arm6_State.cpsr s) [Cbit])))
    in psrel;
    [apply psrel|exact H11|exact H16].
Qed.

(* Lemmas on if S==1 *)
Definition is_S_set :=
  Ebinop Oeq (Evalof (Evar S T4) T4)
  (Eval (Vint (repr 1)) T9) T9.

Lemma no_effect_is_S_set :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v ->
    m = m'/\eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v.
Proof.
  intros until v. intros is_s.
  split. inv is_s. inv H. inv H10. inv H4. inv H11. reflexivity. exact is_s.
Qed.

Lemma S_not_set:
  forall e m t m' v sbit,
    sbit_func_related m e sbit ->
    eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v ->
    Csem.is_false v T9 ->
    Util.zeq sbit 1 = false.
Proof.
  intros until sbit. intros sfrel s_set is_false. inv is_false.
  inv s_set. inv H. inv H10. inv H4. inv H11.
  inv H0. inv H7.
  inv sfrel.
  unfold S_proj.
  unfold param_val. inv H5. inv H6. inv H2. rewrite H6.
  rewrite H7. unfold varg_proj.
  destruct v1; try auto.
    unfold sem_cmp in H0. unfold T4, T7, classify_cmp in H0. unfold typeconv in H0. 
    simpl in H0. unfold Val.of_bool in H0.
    unfold w1. 
    inv H0. destruct (eq i (repr 1)). inv H1. auto.
  rewrite H4. unfold varg_proj. simpl. reflexivity. 
Qed.

Lemma S_is_set:
  forall e m t m' v sbit,
    sbit_func_related m e sbit ->
    eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v ->
    Csem.is_true v T9 ->
    Util.zeq sbit 1 = true.
Proof.
  intros until sbit. intros sfrel s_set is_true.
  inv s_set. inv H. inv H10. inv H4. inv H11.
  inv H0. inv H6. inv H5. inv sfrel.
  simpl in H7.
  unfold S_proj. unfold param_val. 
  inv H1.
    rewrite H6. rewrite H4. unfold varg_proj.
    destruct v1; 
      unfold sem_cmp in H7; unfold classify_cmp, T4, T7 in H7; simpl in H7; inv H7.
      inv is_true0. 
      assert (w1 = repr 1). auto. rewrite H0.
      unfold Val.of_bool in H. unfold Vtrue in H. unfold Vfalse in H.
      destruct (eq i (repr 1)). 
        inv H. simpl. reflexivity.
        inv H. induction H1. reflexivity.
      unfold Val.of_bool in H0.
      destruct (eq i (repr 1)). inv H0. inv H0.
    inv H5.
Qed.

(* Lemmas on if (((S == 1) && (d == 15)))*)
Definition is_S_set_and_is_pc :=
  Econdition
  (Ebinop Oeq (Evalof (Evar S T4) T4)
    (Eval (Vint (repr 1)) T9) T9)
  (Econdition
    (Ebinop Oeq (Evalof (Evar d T4) T4)
      (Eval (Vint (repr 15)) T9) T9)
    (Eval (Vint (repr 1)) T9)
    (Eval (Vint (repr 0)) T9) T9)
  (Eval (Vint (repr 0)) T9) T9.

Lemma no_effect_is_S_set_and_is_pc :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set_and_is_pc t m' v ->
    m = m'/\eval_expression (Genv.globalenv prog_adc) e m is_S_set_and_is_pc t m' v.
Proof.
  intros until v. intros spc. split.
  inv spc. inv H. inv H5. inv H13. inv H4. inv H16. inv H10.
  inv H4. inv H17. inv H4. inv H20. inv H12. reflexivity.
  inv H12. inv H4. inv H16. inv H4. inv H17. reflexivity.
  inv H10. inv H5. inv H12. inv H4. inv H13. reflexivity.
  exact spc.
Qed.

Lemma same_reg_val :
forall i0,
(eq i0 (repr 15) = Util.zeq (mk_regnum i0) 15).
Proof.
Admitted.

Lemma S_set_and_is_pc_true:
  forall e m t m' v sbit d,
    sbit_func_related m e sbit ->
    d_func_related m e d ->
    eval_expression (Genv.globalenv prog_adc) e m is_S_set_and_is_pc t m' v ->
    Csem.is_true v T9 ->
    Util.zeq sbit 1 && Util.zeq d 15 = true.
Proof.
  intros until d. intros sfrel dfrel spc spc_true.
  inv spc; inv H; simpl in *;
    (*true*)
    inv H5; inv H13; inv H4; inv H16; inv H6; inv H8.
    inv H7; inv H5; inv H3; simpl in H4.
      (*S exists*)
      inv sfrel; unfold S_proj; unfold param_val. rewrite H8; rewrite H7.
      unfold varg_proj.
      destruct v2; simpl; try auto;
      unfold sem_cmp in H1; simpl in H1; inv H1.
      (*S is int*)
      unfold Val.of_bool in H9; unfold w1.
      destruct (eq i (repr 1)); simpl;
        [idtac|inv H9;destruct H2;reflexivity].
      (*S is set*)
      inv H10;
        (*d is 15*)
        simpl in H13; inv H16; inv H5; inv H18; inv H5;
        inv H19; inv H14; inv H20; inv H0; inv H6; inv H10; inv H5. 
        inv H1.
          (*d exists*)
          inv dfrel; unfold d_proj; unfold param_val.
          rewrite H10. rewrite H6.
          unfold varg_proj.
          destruct v0;
          unfold sem_binary_operation in H11; simpl in H11;
          unfold sem_cmp in H11; simpl in H11; inv H11.
          (*d is int*)
          unfold Val.of_bool in H13.
          rewrite <- (same_reg_val i0).
          destruct (eq i0 (repr 15)). 
          reflexivity. inv H13; destruct H1; reflexivity.
          (*d not exist*)
          inv H5.
      (*S not set*)
      inv H1;
        (*d exists*)
        unfold sem_binary_operation in H11; unfold sem_cmp in H11; simpl in H11.
        inv dfrel; unfold d_proj; unfold param_val.
        rewrite H10; rewrite H6.
        unfold varg_proj.
        destruct v0; inv H11. 
        (*d is int*)
          inv spc_true; destruct H1; auto.
        (*d not exist*)
        inv H5.
      (*S not exist*)
      inv H6.
    (*false*)
    inv H10; inv H0. inv H5. inv H7. inv H2.
      (*S exist*)
      inv sfrel; unfold S_proj; unfold param_val. 
      rewrite H7; rewrite H6.
      unfold varg_proj.
      destruct v2; simpl; try auto;
      unfold sem_cmp in H1; simpl in H1; inv H1.
      (*i is int*)
      unfold Val.of_bool in H9; unfold w1.
      destruct (eq i (repr 1)); simpl.
        inv H9.
        inv H14. inv spc_true; destruct H1; auto.
      (*S not exist*)
      inv H5.  
Qed.        

Lemma S_set_and_is_pc_false:
  forall e m t m' v sbit d,
    sbit_func_related m e sbit ->
    d_func_related m e d ->
    eval_expression (Genv.globalenv prog_adc) e m is_S_set_and_is_pc t m' v ->
    Csem.is_false v T9 ->
    Util.zeq sbit 1 && Util.zeq d 15 = false.
Proof.
  intros until d. intros sfrel dfrel spc spc_false.
  inv spc.
  inv H; simpl in *;
    (*true*)
    inv H5; inv H13; inv H4; inv H16; inv H6; inv H8.
    inv H7; inv H5; inv H3; simpl in H4.
      (*S exists*)
      inv sfrel; unfold S_proj; unfold param_val; 
      rewrite H8; rewrite H7;
      unfold varg_proj.
      destruct v2; simpl; try auto;
      unfold sem_cmp in H1; simpl in H1; inv H1.
      (*v2 is int*)
      unfold Val.of_bool in H9; unfold w1.
      destruct (eq i (repr 1)); simpl;
        [idtac|inv H9;destruct H2;reflexivity].
        (*i is false*)
        inv H10;
        simpl in H13; inv H16; inv H5; inv H18; inv H5;
        inv H19; inv H14; inv H20; inv H0; inv H6; inv H10; inv H5. 
        (*d is 15*)
        inv spc_false.
        (*d is not 15*)
        inv H1.
          (*d exists*)
          unfold sem_binary_operation in H11; simpl in H11;
          unfold sem_cmp in H11; simpl in H11; inv H11.
          inv dfrel; unfold d_proj; unfold param_val; unfold varg_proj.
          rewrite H10; rewrite H6.
          destruct v0; inv H0.
            (*d is int*)
            unfold Val.of_bool in H13.
            rewrite <- (same_reg_val i0).
            destruct (eq i0 (repr 15)). inv H13. reflexivity.
          (*d not exist*)
          inv H5.
      (*S not exist*)
      inv H6.
    (*false*)
    inv H10. inv H0. inv H14. inv H7. inv H5.
    inv H2.
      (*S exists*)
      inv sfrel; unfold S_proj; unfold param_val; unfold varg_proj.
      rewrite H7; rewrite H6.
      destruct v2; inv H1.
      (*S is int*)
      unfold Val.of_bool in H9. unfold w1.
      destruct (eq i (repr 1)). inv H9. auto.
      (*S not exist*)
      inv H5.
Qed.

(* Lemmas on if CurrentModeHasSPSR *)
Definition hasSPSR :=
  Ecall (Evalof (Evar CurrentModeHasSPSR T10) T10)
  (Econs (Evalof (Evar proc T3) T3) Enil) T10.

Axiom if_hasSPSR_ok :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m hasSPSR t m' v ->
    m = m'/\eval_expression (Genv.globalenv prog_adc) e m hasSPSR t m' v.

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
Definition get_spsr :=
  Ecall (Evalof (Evar spsr T6) T6)
  (Econs (Evalof (Evar proc T3) T3)
    Enil) T6.

Axiom get_spsr_ok:
  forall e m t m' r,
    eval_expr (Genv.globalenv prog_adc) e m RV get_spsr t m' r ->
    m = m'.

Definition cp_SR :=
  Ecall
  (Evalof (Evar copy_StatusRegister T11) T11)
  (Econs
    (Eaddrof
      (Efield
        (Ederef (Evalof (Evar proc T3) T3) T6)
        cpsr T6) T6)
    (Econs get_spsr Enil)) T9.

Lemma same_cp_SR :
  forall e m l b s t m' v em,
    proc_state_related (of_mem proc m) e (Ok tt (mk_semstate l b s)) ->
    eval_expression (Genv.globalenv prog_adc) e m cp_SR t m' v ->
    (forall l b, proc_state_related (of_mem proc m') e
      (Ok tt (mk_semstate l b
      (Arm6_State.set_cpsr s (Arm6_State.spsr s em))))).
Proof.
  intros until em. intros psrel cpsr l' b'.
  inv cpsr. inv H. inv H4. inv H9. simpl in *.
  inv H5. inv H4. inv H5. inv H15. inv H4. inv H5.
  inv H14. inv H4. inv H3. inv H15. inv H5. inv H4. inv H5. inv H21.
  inv H13. simpl in *.
  (* Function spsr, get spsr from the current state *)
  apply (functions_behavior_ok e l b s vf0 fd0 m4 vargs0 t5 m2 vres0 l b s) 
    in psrel; [idtac|exact H18|exact H23].
  (* Function copy_StatusRegister, copy the current spsr to cpsr*)
  apply (functions_behavior_ok e l b s vf fd m2 vargs t3 m' vres l' b'
    (Arm6_State.set_cpsr s (Arm6_State.spsr s em)))
    in psrel; [idtac|exact H11|exact H16].
  exact psrel.
Qed.

(* Lemma on proc_state_relates holds after unpredictable*)
(* In fact, unpredictable in simlight is a annotation, which will print
   a error message. 
   For the moment, we consider it as a function call with an 
   empty body *)
Definition unpred :=
  Ecall (Evalof (Evar adc_compcert_fixed.unpredicatable T9) T9) Enil T9.

Lemma same_unpred :
  forall e m s t m' v,
    proc_state_related (of_mem proc m) e (Ok tt s) ->
    eval_expression (Genv.globalenv prog_adc) e m unpred t m' v ->
    proc_state_related (of_mem proc m') e (Ko Arm6_Message.EmptyMessage).
Proof.
  intros until v. intros psrel unp.
  inv unp. inv H. inv H4. inv H9. inv H5.
  apply (funct_unpredictable e s vf fd m2 vargs t3 m' vres) in psrel;
  unfold unpredictable in psrel; unfold raise in psrel; 
  [exact psrel|exact H11|exact H16].
Qed.

(* Lemma on proc_state_relates holds after NZCV flag setting*)
Definition nflag_assgnt:=
  Eassign
  (Efield
    (Efield
      (Ederef (Evalof (Evar proc T3) T3)
        (Tpointer T3)) cpsr T6) N_flag T4)
  (Ecall (Evalof (Evar get_bit T12) T12)
    (Econs (reg_id d)
      (Econs (Eval (Vint (repr 31)) T7)
        Enil)) T4) T4.
Lemma same_nflag_assgnt :
  forall e m l b s d t m' v,
  proc_state_related (of_mem proc m) e (Ok tt (mk_semstate l b s)) ->
  d_func_related m e d ->
  eval_expression (Genv.globalenv prog_adc) e m nflag_assgnt t m' v->
  forall l b,
  proc_state_related (of_mem proc m') e
    (Ok tt
        (mk_semstate l b
           (Arm6_State.set_cpsr_bit s Nbit
              (Arm6_State.reg_content s d) [n31] )
         )
    ).
Proof.
  intros until v. intros psrel dfrel nf. intros.
  inv nf. inv H. simpl in *. inv H4. inv H14. inv H13. inv H4.
  inv H8. inv H5. inv H3. inv H13. inv H4. 
  eapply get_reg_ok in H5. subst.
  inv H19. inv H4. 
Admitted.

Definition zflag_assgnt :=
  Eassign
  (Efield
    (Efield
      (Ederef 
        (Evalof (Evar proc T3) T3)
        (Tpointer T3)) cpsr T6) Z_flag
    T4)
  (Econdition
    (Ebinop Oeq
      (Ecall (Evalof (Evar reg T2) T2)
        (Econs
          (Evalof (Evar proc T3) T3)
          (Econs
            (Evalof (Evar d T4) T4)
            Enil)) T1)
      (Eval (Vint (repr 0)) T7) T7)
    (Eval (Vint (repr 1)) T7)
    (Eval (Vint (repr 0)) T7) T7) T4.
Lemma same_zflag_assgnt :
  forall e m l b s d t m' v,
    proc_state_related (of_mem proc m) e (Ok tt (mk_semstate l b s)) ->
    d_func_related m e d ->
    eval_expression (Genv.globalenv prog_adc) e m zflag_assgnt t m' v->
    forall l b, proc_state_related (of_mem proc m') e 
      (Ok tt (mk_semstate l b (Arm6_State.set_cpsr_bit s Zbit
        (if Util.zeq (Arm6_State.reg_content s d) 0
         then repr 1
         else repr 0)))).
Proof.
  intros until v. intros psrel dfrel zf.
  inv zf. inv H. simpl in H15.
  inv H15.
Admitted.
Definition cflag_assgnt:=
  Eassign
  (Efield
    (Efield
      (Ederef
        (Evalof (Evar proc T3) T3)
        (Tpointer T3)) cpsr T6)
    C_flag T4)
  (Ecall
    (Evalof 
      (Evar CarryFrom_add3 T9) T9)
    (Econs
      (Evalof (Evar old_Rn T1) T1)
      (Econs
        (Evalof
          (Evar shifter_operand T1)
          T1)
        (Econs
          (Evalof
            (Efield
              (Efield
                (Ederef
                  (Evalof (Evar proc T3) T3)
                  (Tpointer T3)) cpsr T6)
              C_flag T4) T4) Enil))) T4)
  T4.
Lemma same_cflag_assgnt:
  forall m e l b s0 s n so t m' v,
    proc_state_related (of_mem proc m) e (Ok tt (mk_semstate l b s)) ->
    n_func_related m e n ->
    so_func_related m e so ->
    eval_expression (Genv.globalenv prog_adc) e m cflag_assgnt t m' v->
    forall l b, proc_state_related (of_mem proc m') e
      (Ok tt (mk_semstate l b (Arm6_State.set_cpsr_bit s Cbit
        (Arm6_Functions.CarryFrom_add3 (Arm6_State.reg_content s0 n) so
          (Arm6_State.cpsr (st (mk_semstate l b s))) [Cbit])))).
Proof.
  intros until v. intros psrel nfrel sofrel cf.
  inv cf. inv H. simpl in H15.
  inv H15.
Admitted.
Definition vflag_assgnt:=
  Eassign
  (Efield
    (Efield
      (Ederef
        (Evalof (Evar proc T3) T3)
        (Tpointer T3)) cpsr T6)
    V_flag T4)
  (Ecall
    (Evalof
      (Evar OverflowFrom_add3 T9) T9)
    (Econs
      (Evalof
        (Evalof (Evar old_Rn T1) T1)
        T1)
      (Econs
        (Evalof
          (Evar shifter_operand T1)
          T1)
        (Econs
          (Evalof
            (Efield
              (Efield
                (Ederef
                  (Evalof (Evar proc T3) T3)
                  (Tpointer T3)) cpsr T6)
              C_flag T4) T4) Enil))) T4)
  T4.
Lemma same_vflag_assgnt:
  forall m e l b s0 s n so t m' v,
    proc_state_related (of_mem proc m) e (Ok tt (mk_semstate l b s)) ->
    n_func_related m e n ->
    so_func_related m e so ->
    eval_expression (Genv.globalenv prog_adc) e m vflag_assgnt t m' v->
    proc_state_related (of_mem proc m') e
      (Ok tt (mk_semstate l b (Arm6_State.set_cpsr_bit s Arm6_SCC.Vbit
        (Arm6_Functions.OverflowFrom_add3 (Arm6_State.reg_content s0 n) so
           (Arm6_State.cpsr (st (mk_semstate l b s))) [Cbit])))).
Proof.
  intros until v. intros psrel nfrel sofrel vf.
  inv vf. inv H. simpl in H15.
  inv H15.
Admitted.


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
    eval_expression (Genv.globalenv prog_adc) e m oldrn_assgnt Events.E0 m' v ->
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

Lemma same_bool : forall b, b&&b = b.
Proof.
  destruct b;simpl;reflexivity.
Qed.

Theorem related_aft_ADC: forall e m0 m1 m2 mfin vargs s out sbit cond d n so,
  alloc_variables empty_env m0 (ADC_body.(fn_params) ++ ADC_body.(fn_vars)) e m1 ->
  bind_parameters e m1 ADC_body.(fn_params) vargs m2 ->
(* TODO: valid_access needs to be more precise *)
  (forall m ch b ofs, Mem.valid_access m ch b ofs Readable) ->
  proc_state_related (of_mem proc m2) e (Ok tt (mk_semstate nil true s)) ->
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
  proc_state_related (of_mem proc mfin) e (S.ADC_step sbit cond d n so (mk_semstate nil true s)). 
Proof.
  
  intros until so.
  intros al bi valacc psrel sfrel cfrel dfrel nfrel sofrel exstmt.

  inv exstmt; [idtac | nod];
  apply Events.Eapp_E0_inv in H3; destruct H3; subst.
  rename H4 into rn_assgnt, H7 into main_p.
  inv rn_assgnt;
  rename H2 into rn_assgnt.
  apply (oldrn_assgnt_ok e m2 nil true s Events.E0 m3 v) in psrel; 
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
      apply no_effect_condpass in condpass0; 
      inversion condpass0 (* m3=m4 *);
      rewrite H in * |- *; clear H condpass0;
      rename H0 into condpass.
    (* ConditionPassed(&proc->cpsr, cond) evaluates to true *)
    apply (condpass_true e m4 Events.E0 m4 v1 cond s) in cp_b;
      [idtac | inv cp_b].

    inv main_p; [idtac | nod];
    rename H4 into setreg, H7 into main_p, H3 into evs;
    apply Events.Eapp_E0_inv in evs; destruct evs; subst.
    inv setreg;
    rename H2 into setreg;
    apply (same_setregpc e m4 nil true s s Events.E0 m5 v0 d n so) 
      with nil (Util.zne d 15) in psrel;
      [idtac | apply setreg].
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
        apply no_effect_is_S_set_and_is_pc in sd; 
        inversion sd; 
        rewrite H in * |- *; clear H sd; (* m5=m6 *)
        rename H0 into sd;
        apply Events.Eapp_E0_inv in evs; destruct evs; subst.
      (* ((S == 1) && (d == 15)) evaluates to true *)
      apply (S_set_and_is_pc_true e m6 Events.E0 m6 v2 sbit d) in sd;
        [idtac|exact sfrel|exact dfrel|exact sd_b].
      inv main_p;
      rename H5 into hasspsr, H8 into spsr_b, H9 into main_p, H4 into evs;
          simpl in spsr_b;
          apply Events.Eapp_E0_inv in evs; destruct evs; subst;
          apply if_hasSPSR_ok in hasspsr;
          inversion hasspsr;
          rewrite H in * |- *; 
          clear H hasspsr; rename H0 into hasspsr (* m6=m7*).
        (* CurrentModeHasSPSR(proc) evaluates to true *)
        inv main_p;
        rename H2 into cp_sr.
        apply (same_cp_SR e m7 nil (Util.zne d 15) 
          (Arm6_State.set_reg s d
          (add (add (Arm6_State.reg_content s n) so)
            (Arm6_State.cpsr s) [Cbit])) Events.E0 mfin v4 und) 
        with nil (Util.zne d 15) in psrel;
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
        rewrite cp_b; rewrite sd; simpl.
        unfold if_CurrentModeHasSPSR; unfold block; unfold fold_left;
        unfold _get_bo; unfold bind_s; unfold next; unfold bind; simpl;
        unfold _Arm_State.set_reg.
        rewrite spsr_b; simpl; unfold _Arm_State.set_reg; unfold _Arm_State.set_cpsr.
        unfold _set_bo; unfold ok_semstate. unfold loc. unfold st. rewrite same_bool.
        apply psrel.
        (* CurrentModeHasSPSR(proc) evaluates to false *)
        inv main_p; rename H2 into unp.
        apply (same_unpred e m7 
                (mk_semstate nil (Util.zne d 15) (Arm6_State.set_reg s d
                  (add (add (Arm6_State.reg_content s n) so)
                    (Arm6_State.cpsr s) [Cbit])))
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
        rewrite cp_b; rewrite sd; simpl.
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
      apply (S_set_and_is_pc_false e m6 Events.E0 m6 v2 sbit d) in sd_b;
        [idtac|exact sfrel|exact dfrel|exact sd].
      inv main_p;
      rename H5 into is_s, H8 into s_b, H9 into main_p, H4 into evs;
          simpl in s_b; 
          apply no_effect_is_S_set in is_s;
          inversion is_s;
          rewrite H in * |- *;
          clear H is_s; rename H0 into is_s(* m6=m7*);
          apply Events.Eapp_E0_inv in evs; destruct evs; subst.      
        (* S == 1 evaluates to true *)
        inv main_p ;[idtac | nod];
        rename H4 into nf, H7 into main_p, H3 into evs;
        apply Events.Eapp_E0_inv in evs; destruct evs; subst.

        apply (S_is_set e m7 Events.E0 m7 v3 sbit) in s_b;
          [idtac|exact sfrel|exact is_s].

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
        fold s1. fold s2. fold s3. unfold st in psrel.
        rewrite same_bool; rewrite same_bool; rewrite same_bool;
        rewrite same_bool; rewrite same_bool.
        exact psrel.

        (* S == 1 evaluates to false *)
        inv main_p.
        apply (S_not_set e mfin Events.E0 mfin v3 sbit) in s_b;
          [idtac|exact sfrel|exact is_s].
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
        simpl. rewrite same_bool. exact psrel.

    (* ConditionPassed(&proc->cpsr, cond) evaluates to false *)
    inv main_p.
    unfold S.ADC_step; unfold _get_st; unfold bind_s; unfold bind; simpl.
    rewrite (condpass_false e mfin Events.E0 mfin v1); [simpl | inv cp_b|exact cp_b].
    exact psrel.
Qed.

