(* This file describe the relation between COQ and C state for ARM *)

(*Require Import Globalenvs Memory.*)
Require Import Csyntax Csem Coqlib Integers Values Maps. 
Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import adc_compcert New_Memory New_Globalenvs.

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

(* Initial local environment, an empty PTree contents var location & type*)
Definition env0 := (PTree.empty (block * type)).

(* Initialize the memory with program p defined in adc_compcert*)
Definition mem1 := Genv.init_mem p. 

(* Allocate a type in memory *)
Definition alloc_loc_var (t: type) (ofs:int) (m:Mem.mem) : (Mem.mem*option block) := 
  let (m',b):= Mem.alloc m ofs (sizeof t) in (m', Some b).

(* put new local variable and return new environment *)
Definition build_env (id:AST.ident) (t:type) (ofs :int) (m:Mem.mem) (e:env):(Mem.mem*env):= 
  match (alloc_loc_var t ofs m) with
    |(m',Some b) => 
      (m',PTree.set id (b,t) e)
    |(m',None) => (m',e)
  end.

(* store value of local variable by its id*)
Definition store_val (id:AST.ident) (e:env) (ofs:int) (v:val) (m:Mem.mem):Mem.mem:=
  match (match (PTree.get id e) with
           |Some (b,t)=> store_value_of_type' t m b ofs v
           |None=> Some m 
         end) with
    |Some m' => m'
    |None => m
  end.

(* load value of local variable by its id*)
Definition load_val (id:AST.ident) (e:env) (ofs:int) (m:Mem.mem):option val:=
  match (PTree.get id e) with
    |Some (b,t) => load_value_of_type' t m b ofs
    |None => None
  end.

(*Require Import  Cnotations.*)
(* build local environment for Processor state *)

(*Definition build_env_sr (me : Mem.mem) (e:env) :=
  build_env background (Tint I32 Unsigned) Int.zero
  (build_env mode (Tint I32 Unsigned) Int.zero
  (build_env T_flag (Tint I8 Unsigned) Int.zero
  (build_env F_flag (Tint I8 Unsigned) Int.zero
  (build_env I_flag (Tint I8 Unsigned) Int.zero
  (build_env A_flag (Tint I8 Unsigned) Int.zero
  (build_env E_flag (Tint I8 Unsigned) Int.zero
  (build_env GE3 (Tint I8 Unsigned) Int.zero
  (build_env GE2 (Tint I8 Unsigned) Int.zero
  (build_env GE1 (Tint I8 Unsigned) Int.zero
  (build_env GE0 (Tint I8 Unsigned) Int.zero
  (build_env J_flag (Tint I8 Unsigned) Int.zero
  (build_env Q_flag (Tint I8 Unsigned) Int.zero  
  (build_env V_flag (Tint I8 Unsigned) Int.zero
  (build_env C_flag (Tint I8 Unsigned) Int.zero
  (build_env Z_flag (Tint I8 Unsigned) Int.zero
  (build_env N_flag (Tint I8 Unsigned) Int.zero (m,e))))))))))))))))).

Definition build_env_cpsr (me:Mem.mem) (e:env) :=
  build_env_sr (build_env cpsr typ_SLv6_StatusRegister Int.zero (m,e)).

Definition build_env_spsrs (m:Mem.mem) (e:env) :=
  build_env spsrs (Tarray typ_SLv6_StatusRegister 5) Int.zero (m,e).

Definition build_env_mmu (m:Mem.mem) (e:env) :=
  build_env adc_compcert.mem (Tpointer (Tint I8 Unsigned)) Int.zero
  (build_env _end (Tint I32 Unsigned) Int.zero
  (build_env size (Tint I32 Unsigned) Int.zero
  (build_env begin (Tint I32 Unsigned) Int.zero 
  (build_env mmu_ptr typ_SLv6_MMU Int.zero (m,e))))).

Definition build_env_cp15 (m:Mem.mem) (e:env) :=
  build_env u_bit (Tint I8 Unsigned) Int.zero
  (build_env ee_bit (Tint I8 Unsigned) Int.zero
  (build_env cp15 typ_SLv6_SystemCoproc Int.zero (m,e))).

Definition build_env_proc (m:Mem.mem) (e:env) :=
  build_env jump (Tint I8 Unsigned) Int.zero
  (build_env pc (Tpointer (Tint I32 Unsigned)) Int.zero
  (build_env und_regs (Tarray (Tint I32 Unsigned) 2) Int.zero
  (build_env abt_regs (Tarray (Tint I32 Unsigned) 2) Int.zero
  (build_env svc_regs (Tarray (Tint I32 Unsigned) 2) Int.zero
  (build_env irq_regs (Tarray (Tint I32 Unsigned) 2) Int.zero
  (build_env fiq_regs (Tarray (Tint I32 Unsigned) 7) Int.zero
  (build_env user_regs (Tarray (Tint I32 Unsigned) 16) Int.zero
  (build_env id (Tint I32 Unsigned) Int.zero
  (build_env_cp15
  (build_env_spsrs
  (build_env_cpsr 
  (build_env_mmu 
  (build_env proc typ_SLv6_Processor Int.zero (m,e)))))))))))))).
*)

(* if an option val is Some integer then return the integer value else return zero*)
Definition load_val_bit (v : option val):word:=
  match v with
    |Some (Vint v')=> v'                     
    |_ => Int.zero
  end.

Require Import Errors.

(* find the offset for every element of a struct*)
Definition fld_of_struct (tp:type) :=
  match tp with
    |Tstruct id fl => fl
    |_ => Fnil
  end.

Definition ofs_of_fld (tp:type) (id:AST.ident):word:=
  match field_offset id (fld_of_struct tp) with
    | Error _ => Int.zero
    | OK r => repr r
  end.

(* Projection from C to COQ ARM processor state *)

(* from StateRegister to word*)
Definition sr_proj (m:Mem.mem) (e:env) (b:block) (ofs:int) :word:=
  let load_val_of id tp :=
    load_val_bit (load_value_of_type' tp m b (add ofs (ofs_of_fld typ_SLv6_StatusRegister id))) in
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
  let bg := load_val_of background (Tint I32 Unsigned) in
    (set_bit 31 nflag
    (set_bit 30 zflag
    (set_bit 29 cflag
    (set_bit 28 vflag
    (set_bit 27 qflag
    (set_bit 24 jflag
    (set_bit 19 ge3
    (set_bit 18 ge2
    (set_bit 17 ge1
    (set_bit 16 ge0
    (set_bit 9 eflag
    (set_bit 8 aflag
    (set_bit 7 iflag 
    (set_bit 6 fflag 
    (set_bit 5 tflag 
    (set_bits 4 0 md Int.zero)))))))))))))))).

(* projection form C cpsr to COQ cpsr*)
Definition cpsr_proj (m:Mem.mem) (e:env) :word:=
  match e!proc with
    |Some (b, t) => sr_proj m e b (ofs_of_fld t cpsr)
    |None => Int.zero
  end.
 
(* projection from C spsr to COQ spsr*)
Definition spsr_proj (m:Mem.mem) (e:env) (em:exn_mode):word:=
    match e!proc with 
      |Some(b,t)=> 
        let ob:=load_value_of_type' (Tarray typ_SLv6_StatusRegister 5) m b 
          (ofs_of_fld t spsrs) in
          match ob with
            |Some(Vptr b' ofs)=>
              match em with
                |fiq=>sr_proj m e b' (add ofs (repr 0))
                |irq=>sr_proj m e b' (add ofs (repr 1))
                |svc=>sr_proj m e b' (add ofs (repr 2))
                |abt=>sr_proj m e b' (add ofs (repr 3))
                |und=>sr_proj m e b' (add ofs (repr 4))
              end
            |_=>Int.zero
          end
      |None=>Int.zero
    end.

(* Projection form COQ cpsr to C memory model which contain such cpsr*)
(*Definition cpsr_proj' (s : Arm6_State.state) (m:Mem.mem) (e:env) :=
  let coqcpsr := Arm6_Proc.cpsr (Arm6_State.proc s) in
  let nflag := Vint coqcpsr[31] in
  let zflag := Vint coqcpsr[30] in
  let cflag := Vint coqcpsr[29] in
  let vflag := Vint coqcpsr[28] in
  let qflag := Vint coqcpsr[27] in
  let jflag := Vint coqcpsr[24] in
  let ge0 := Vint coqcpsr[16] in
  let ge1 := Vint coqcpsr[17] in
  let ge2 := Vint coqcpsr[18] in
  let ge3 := Vint coqcpsr[19] in
  let eflag := Vint coqcpsr[9] in
  let aflag := Vint coqcpsr[8] in
  let iflag := Vint coqcpsr[7] in
  let fflag := Vint coqcpsr[6] in
  let tflag := Vint coqcpsr[5] in
  let bg := Vint (add coqcpsr[23 # 20] coqcpsr[15 # 10]) in
  let md := Vint (Arm6.word_of_proc_mode (Arm6_Proc.mode (Arm6_State.proc s))) in
  (*let (m', e') := build_env_proc (m, e) in*)
    (store_val mode e Int.zero md
    (store_val background e Int.zero bg
    (store_val T_flag e Int.zero tflag
    (store_val F_flag e Int.zero fflag
    (store_val I_flag e Int.zero iflag
    (store_val A_flag e Int.zero aflag
    (store_val E_flag e Int.zero eflag
    (store_val GE3 e Int.zero ge3
    (store_val GE2 e Int.zero ge2
    (store_val GE1 e Int.zero ge1
    (store_val GE0 e Int.zero ge0
    (store_val J_flag e Int.zero jflag
    (store_val Q_flag e Int.zero qflag
    (store_val V_flag e Int.zero vflag
    (store_val C_flag e Int.zero cflag
    (store_val Z_flag e Int.zero zflag
    (store_val N_flag e Int.zero nflag m))))))))))))))))).
*)

Definition mode_proj (m:Mem.mem) (e:env) :proc_mode:=
  let md :=
    match e!proc with
      |Some(bp,t)=>
        proc_mode_of_word (load_val_bit (load_value_of_type' (Tint I32 Unsigned) m bp 
          (add (ofs_of_fld t cpsr) (ofs_of_fld typ_SLv6_StatusRegister mode)))) 
      |None=>None
    end in
    match md with
      |Some md'=>md'
      |None =>sys
    end.

Definition load_reg (id:AST.ident) (a n:Z) (m:Mem.mem) (e:env):word:=
  match e!proc with
    |Some(bp,t)=> 
      let ptr:=load_value_of_type' 
        (Tarray (Tint I32 Unsigned) a) m bp (ofs_of_fld t id) in
        match ptr with 
          |Some(Vptr ba ofs)=>
            match (load_value_of_type' (Tint I32 Unsigned) m ba (add ofs (repr n))) with
              |Some(Vint v)=>v
              |_=>Int.zero
            end
          |_=>Int.zero
        end
    |None=>Int.zero
  end.

Definition regs_proj (m:Mem.mem) (e:env) (r:register):word:=
  match r with
    | R k => load_reg user_regs 16 k m e
    | R_svc k _=> load_reg svc_regs 7 k m e
    | R_abt k _=> load_reg abt_regs 2 k m e
    | R_und k _=> load_reg und_regs 2 k m e
    | R_irq k _=> load_reg irq_regs 2 k m e
    | R_fiq k _=> load_reg fiq_regs 2 k m e
  end.

(*Definition op_case {A} (op:option A)*)

Definition mem_proj (m:Mem.mem) (e:env) (ad:address):word:=
  match e!proc with
    |Some(bp,t)=>
      let mptr:=load_value_of_type'
        (Tpointer typ_SLv6_MMU) m bp (ofs_of_fld t mmu_ptr)
        in match mptr with
          |Some(Vptr bm ofs)=>
            let mm:=load_value_of_type' 
            (Tpointer (Tint I8 Unsigned)) m bm (add ofs (ofs_of_fld typ_SLv6_MMU adc_compcert.mem))
            in match mm with
              |Some(Vptr b ofs)=>
                let ov:=load_value_of_type' (Tint I8 Unsigned) m b (add ofs (word_of_address ad))
                  in match ov with |Some(Vint v)=>v|_=>Int.zero end
              |_=>Int.zero end
          |_=>Int.zero
        end
    |None=>Int.zero
  end.

Definition scc_reg_proj (m:Mem.mem) (e:env) (r:regnum):word:=
  match e!proc with
    |Some(bp,t)=>
      let regbit id:=
        match (load_value_of_type' (Tint I8 Unsigned) m bp 
        (add (ofs_of_fld t cp15) (ofs_of_fld typ_SLv6_SystemCoproc id))) with
          |Some(Vint v)=>v
          |_=>Int.zero
        end in
  let ee := regbit ee_bit in
  let u := regbit u_bit in
  let v := regbit v_bit in
    set_bit 13 v (set_bit 22 u (set_bit 25 ee Int.zero))
    |None=>Int.zero
  end.

Definition proc_proj (m:Mem.mem) (e:env):Arm6_State.state:=
  Arm6_State.mk_state 
  (Arm6_Proc.mk_state (cpsr_proj m e) (spsr_proj m e) (regs_proj m e) nil (mode_proj m e))
  (Arm6_SCC.mk_state (scc_reg_proj m e) (mem_proj m e)).

(*Definition map_proc_mode (id:AST.ident) :proc_mode:=
  if Peqb id fiq_regs then exn fiq else if Peqb id irq_regs then exn irq
    else if Peqb id svc_regs then exn svc else if Peqb id abt_regs then exn abt
      else if Peqb id und_regs then exn und else if Peqb id user_regs then usr
        else sys.
*)

(*Definition mk_cpsr (c: val) (m:Mem.mem) (e:env) :=
  store_val cpsr e Int.zero c m.

Definition mk_spsr (s:val) (m:Mem.mem) (e:env) :=
  store_val spsrs e Int.zero s m.

Definition mk_mmu (mm:val) (m:Mem.mem) (e:env) :=
  store_val mmu_ptr e Int.zero mm m. *)

Definition mk_c_proc (mm c s cp i ur fr ir sr ar ur p jmp:val) (e:env) (m:Mem.mem):Mem.mem:=
  store_val jump e Int.zero jmp
  (store_val pc e Int.zero p
  (store_val und_regs e Int.zero ur
  (store_val abt_regs e Int.zero ar
  (store_val svc_regs e Int.zero sr
  (store_val irq_regs e Int.zero ir
  (store_val fiq_regs e Int.zero fr
  (store_val user_regs e Int.zero ur
  (store_val id e Int.zero i
  (store_val cp15 e Int.zero cp
  (store_val spsrs e Int.zero s
  (store_val cpsr e Int.zero c 
  (store_val mmu_ptr e Int.zero mm m)))))))))))).

Inductive proc_state_related : Mem.mem -> env -> Arm6_State.state -> Prop :=
  |proc_state_related_intro : 
    forall mmu_ptr_c cpsr_c spsrs_c cp15_c id_c user_regs_c fiq_regs_c irq_regs_c svc_regs_c abt_regs_c und_regs_c pc_c jump_c e m cpsr_coq spsr_coq reg_coq exns_coq mode_coq ssc_reg_coq mem_coq,
      proc_state_related
      (mk_c_proc mmu_ptr_c cpsr_c spsrs_c cp15_c id_c user_regs_c
        fiq_regs_c irq_regs_c svc_regs_c abt_regs_c und_regs_c pc_c jump_c e m) e
      (Arm6_State.mk_state 
        (Arm6_Proc.mk_state cpsr_coq spsr_coq reg_coq exns_coq mode_coq) 
        (Arm6_SCC.mk_state ssc_reg_coq mem_coq)).

Definition proc_state_func_related (m:Mem.mem) (e:env) (s:Arm6_State.state) :Prop:=
  proc_proj m e = s.

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