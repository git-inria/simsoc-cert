(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Coq code generator based on the Coq library written in ../coq
*)

open Ast;;
open Printf;;
open Util;;

let comment f b x = bprintf b "(*%a*)" f x;;

(*****************************************************************************)
(** variable types *)
(*****************************************************************************)

module G = struct

  type typ = string;;

  (* heuristic giving a type to a variable from its name *)
  let type_of_var = function
    | "cond" -> "opcode"
    | "mmod" | "opcode25" | "shift" -> "bool"
    | "n" | "d" | "m" | "s" | "dHi" | "dLo" -> "regnum"
    | "data" -> "word"
    | "accvalue" | "result" | "value" -> "long"
    | s -> if String.length s = 1 then "bool" else "word";;

  (* the type of global variables is given by their names *)
  let global_type = type_of_var;;

  (* type for memory values *)
  let type_of_size = function
    | Byte -> "byte"
    | Half -> "half"
    | Word -> "word";;

  (* the type of a local variable is given by its name, except when it
     is affected to some memory value *)
  let local_type s e =
    match e with
      | Memory (_, n) -> type_of_size n
      | _ -> type_of_var s;;

  let explicit_annot_type _ = function
    | "i" | "d" -> "word" 
    | _ -> "regnum" 

  (* type of variables used in case instructions *)
  let case_type = "word";;

end;;

module V = Ast.Make(G);;

(*****************************************************************************)
(** numbers *)
(*****************************************************************************)

(* convert a number string into a Coq integer *)
let num = string;;

(* convert a string of the form 0b[01]* into a Coq integer *)
let bin b s =
  let n = String.length s in
    if n <= 2 || String.sub s 0 2 <> "0b" then invalid_arg "Gencoq.bin";
    let i = ref 2 in
      while !i < n && s.[!i] = '0' do incr i done;
      if !i >= n then string b "Z0"
      else begin
        string b "Zpos 1";
        for i = !i+1 to n-1 do bprintf b "~%c" s.[i] done
      end;;

let bin b s = par bin b s;;

(* convert a string of the form 0x[0-9a-f]* into a Coq integer *)
(*IMPROVE: use a Coq function to convert an hexa string into a word*)
let hex b s =
  let n = Scanf.sscanf s "%li" (fun x -> x) in
    if Int32.compare n Int32.zero = 0 then bprintf b "Z0"
    else bprintf b "Zpos %lu" n;;

let hex b s = par hex b s;;

(* convert a number string into a Coq word by first converting the
   string into a Coq integer using f and then applying the Coq repr
   function *)
let word f b s = bprintf b "repr %a" f s;;

(*****************************************************************************)
(** registers *)
(*****************************************************************************)

(* convert a number string into a register number using the Coq
   mk_regnum function (use some pre-defined constant for some special
   registers) *)
let string_of_regnum = function
  | "15" -> "PC"
  | "14" -> "LR"
  | "13" -> "SP"
  | s -> Printf.sprintf "(mk_regnum %s)" s;;

let regnum b s = string b (string_of_regnum s);;

let input_registers = ["n"; "m"; "s"; "dLo"];;

(*****************************************************************************)
(** memory size *)
(*****************************************************************************)

let string_of_size = function
  | Byte -> "Byte"
  | Half -> "Half"
  | Word -> "Word";;

let size b s = string b (string_of_size s);;

(*****************************************************************************)
(** processor and addressing modes *)
(*****************************************************************************)

let exn_mode = Genpc.mode;;

let string_of_mode = function
  | Usr -> "usr"
  | Sys -> "sys"
  | m -> "(exn " ^ Genpc.string_of_mode m ^ ")";;

let mode b m = string b (string_of_mode m);;

let addr_mode b m = bprintf b "M%d" m;;

(*****************************************************************************)
(** functions and binary operators *)
(*****************************************************************************)

let depend_on_state = function
  | "address_of_next_instruction" | "address_of_current_instruction"
  | "CurrentModeHasSPSR" 
  | "ExecutingProcessor" | "IsExclusiveGlobal" | "IsExclusiveLocal"
  | "TLB" | "Shared" | "high_vectors_configured" -> true
  | _ -> false;;

let depend_on_init_state = function
  | "ConditionPassed" |"InAPrivilegedMode"  -> true
  | _ -> false;;

let depend_on_config = function
  | "JE_bit_of_Main_Configuration_register" | "SUB_ARCHITECTURE_DEFINED_value"
  | "CV_bit_of_Jazelle_OS_Control_register"
  | "Jazelle_Extension_accepts_opcode_at" -> true
  | _ -> false;;

let string_of_fun_name = function
  | "NOT" -> "not"
  | "not" -> "negb"
  | s when depend_on_config s -> "C." ^ s
  | s when depend_on_init_state s -> s ^ " s0"
  | s when depend_on_state s -> s ^ " st"
  | s -> s;;

let fun_name b s = string b (string_of_fun_name s);;

let string_of_binop = function
  | "AND" -> "and"
  | "OR" -> "or"
  | "EOR" -> "xor"
  | "and" -> "andb"
  | "or" -> "orb"
  | "+" -> "add"
  | "-" -> "sub"
  | "*" -> "mul"
  | "==" -> "zeq"
  | "!=" -> "zne"
  | ">=" -> "zge"
  | "<" -> "zlt"
  | "<<" -> "Logical_Shift_Left"
  | s -> s;;

let binop b s = string b (string_of_binop s);;

let binop64 b s = bprintf b "%s64" (string_of_binop s);;

let is_cp15_reg1 s =
  String.length s > 10 && String.sub s 0 10 = "CP15_reg1_";;

(*****************************************************************************)
(** expressions *)
(*****************************************************************************)

let rec update_lst s lst =
  match lst with
    | [] -> [s]
    | h :: t -> 
        if s = h then lst else update_lst s t
;;

let rec string_to_nb s lst =
  match lst with
    | [] -> List.length lst
    | h :: t -> 
        if s = h then List.length lst - List.length t
        else string_to_nb s t
;;

(*FIXME: raise an exception instead of use a todo for the instruction
  containing this expression*)

(*REMOVE when finished*)
let todo_exp s b e = bprintf b "(*todo: %a*) %s" Genpc.exp e s;;
let todo_word = todo_exp "(repr 0)";;

let is_not_num = function
  | Num _ -> false
  | _ -> true;;

(* add parentheses around complex expressions *)

let rec pexp' (loc: (string*string*int) list) nm sz b = function
  | Var s as e -> 
      if List.exists (fun (s',_,_) -> s'=s) loc then par (loc_exp loc nm "") b e 
      else (exp' loc nm sz) b e
  | Fun (f, []) as e when depend_on_config f -> (exp' loc nm sz) b e 
  | e -> par (exp' loc nm sz) b e

and pexp loc nm b e = pexp' loc nm "" b e 

(* like pexp but prints numbers as integers (not words) *)
and num_exp loc nm b = function
  | Num s -> (*num b s*) bprintf b "n%s" s
  | e -> pexp loc nm b e

(* convert an expression into a register number using the Coq function
   mk_regnum except if it is a number or a variable *)

and regnum_exp loc nm b = function
  | Num s -> regnum b s
  | Var s -> string b s
  | e -> bprintf b "(mk_regnum %a)" (pexp loc nm) e

(* convert an expression into an address using the Coq function
   mk_address *)
(*REMOVE: and address b e = bprintf b "(mk_address %a)" pexp e *)

(* convert an expression into a Coq natural number using the Coq
   function nat_of_Z *)
and nat_exp loc nm b e = bprintf b "(nat_of_Z %a)" (pexp loc nm) e

and loc_exp loc nm hl b = function
  | Var s ->
      begin
        try 
          let name, tp, id = List.find (fun (s',_,_) -> s'=s) loc in
          let size = if tp = "long" then "64" else "" in
            bprintf b "get_loc%s%s n%d (*%s*) loc" size hl id name
        with Not_found -> raise (Failure "inside loc_exp")
      end
  | e -> pexp loc nm b e

and exp loc nm b e = exp' loc nm "" b e

and exp' loc nm sz b = function
    (* convert numbers into Coq words *)
  | Bin s -> word bin b s
  | Hex s -> word hex b s
  | Num s -> word num b s
  | Float_zero as e -> todo_word b e (*FIXME: float not supported yet*)
  | Var s -> string b s

  (*FIXME: functions not supported yet*)
  | Coproc_exp _ as e -> todo_word b e

  (* optimization: since, in SimSoC-Cert, everything is represented by
     words, zero-extension is always done (implicitly) and does not
     need to be applied explicitly *)
  | Fun ("ZeroExtend", e :: _) -> bprintf b "(*ZeroExtend*)%a" (pexp loc nm) e

  (* Add a conversion from word to bool *)
  | Fun ("not", [Range _ as e]) ->
      bprintf b "%a %a" fun_name "not" (pexp loc nm) (Fun ("bool_of_word", [e]))

  (* system coprocessor register bits *)
  | Fun (f, _) when is_cp15_reg1 f ->
      bprintf b "(CP15_reg1 st)[%s]" (String.sub f 10 (String.length f - 10))

  (* print no parenthesis if there is no argument (functions are
     curryfied in Coq) *)
  | Fun (f, []) -> fun_name b f
  (* for saturation functions, add a cast to nat if the second
     argument is not a number *)

  | Fun ("SignedSat"|"SignedDoesSat"|"UnsignedSat"|"UnsignedDoesSat" as f,
         [e1; e2]) when is_not_num e2 -> (* add a cast *)
      bprintf b "%a %a %a" fun_name f (pexp loc nm) e1 (nat_exp loc nm) e2
  (* default printing of function calls *)
  | Fun (f, es) -> bprintf b "%a %a" fun_name f (list " " (num_exp loc nm)) es

  | BinOp (e1, "<", Num "0") -> bprintf b "lt_0 %a" (pexp loc nm) e1
  | BinOp (e1, ">=", Num "0") -> bprintf b "ge_0 %a" (pexp loc nm) e1

  (* optimization avoiding a call to repr *)
  | BinOp (e1, ("==" as f), Num n) ->
      bprintf b "%a %a %a" binop f (pexp loc nm) e1 num n


  (* default printing of binary operators (like function calls) *)
  | BinOp (e1, f, e2) ->
      begin match nm with
        | "SMMLA" | "SMMLS" | "SMMUL" ->
            begin match f with
              | "+" | "<<" | "-" ->
                  bprintf b "%a64 %a %a" 
                    binop f (pexp' loc nm sz) e1 (pexp' loc nm sz) e2
              | "*" -> bprintf b "signed_%a64 %a %a" 
                  binop f (pexp' loc nm sz) e1 (pexp' loc nm sz) e2 
              | _ -> bprintf b "%a%s %a %a" 
                  binop f sz (pexp' loc nm sz) e1 (pexp' loc nm sz) e2
            end
        | _ ->
            bprintf b "%a%s %a %a" 
              binop f sz (pexp' loc nm sz) e1 (pexp' loc nm sz) e2
      end

  | If_exp (e1, e2, e3) ->
      bprintf b "if %a then %a else %a" (exp loc nm) e1 (exp loc nm) e2 (exp loc nm) e3
  | CPSR -> begin match nm with
      | "SETEND"|"Immediate"|"Register"|"Logical_shift_left_by_immediate"
      | "Logical_shift_right_by_register"|"Rotate_right_by_immediate"
      | "Logical_shift_left_by_register"|"Arithmetic_shift_right_by_immediate"
      | "Arithmetic_shift_right_by_register"|"Rotate_right_by_register"
      | "Rotate_right_with_extend"| "Scaled_register_offset" 
      | "Scaled_register_pre_indexed"|"Scaled_register_post_indexed"-> string b "cpsr s0"
      | _ -> string b "cpsr st"
    end
  | Range (e, r) -> 
      begin match e, r with
        | BinOp (e1, "*", e2) , Bits (n1, n2) ->
            begin match String.get nm 0 with
              | 'U' -> bprintf b "bits_of_unsigned_mul64 %a %a n%a n%a"
                  (pexp loc nm) e1 (pexp loc nm) e2 num n1 num n2 
              | 'S' -> bprintf b "bits_of_signed_mul64 %a %a n%a n%a"
                  (pexp loc nm) e1 (pexp loc nm) e2 num n1 num n2
              | _ -> bprintf b "(mul %a %a)[%a]"
                  (pexp loc nm) e1 (pexp loc nm) e2 (range loc nm) r
            end 
        | e, Bits (h, l) ->
            let signed = if nm.[0] = 'S' ||nm.[0] =  'Q' then "signed_" 
            else "" in
            begin match h, l with
              | "7","0" -> bprintf b "get_%sbyte0 %a" signed (pexp loc nm) e
              | "15","8" -> bprintf b "get_%sbyte1 %a" signed (pexp loc nm) e
              | "23","16" -> bprintf b "get_%sbyte2 %a" signed (pexp loc nm) e
              | "31","24" -> bprintf b "get_%sbyte3 %a" signed (pexp loc nm) e
              | "15","0" -> bprintf b "get_%shalf0 %a" signed (pexp loc nm) e
              | "31","16" -> bprintf b "get_%shalf1 %a" signed (pexp loc nm) e
              | "63", "32" -> bprintf b "get_hi %a" (pexp loc nm) e
              | "31", "0" -> bprintf b "get_lo %a" (pexp loc nm) e
              | _ -> bprintf b "%a[%a]" (pexp loc nm) e (range loc nm) r
            end
        | _ -> bprintf b "%a[%a]" (pexp loc nm) e (range loc nm) r
      end
  | Memory (e, n) -> bprintf b "read st %a %a" (pexp loc nm) e size n

  | SPSR None -> string b "spsr st em"
  | SPSR (Some m) -> bprintf b "spsr st %a" exn_mode m
  | Reg (Var s, None) -> 
      if List.mem s input_registers
      then bprintf b "reg_content s0 %s" s
      else bprintf b "reg_content st %s" s
  | Reg (e, None) -> 
      bprintf b "reg_content st %a" (regnum_exp loc nm) e
  | Reg (e, Some m) ->
      bprintf b "reg_content_mode st %a %a" mode m (regnum_exp loc nm) e

  | Unpredictable_exp | Unaffected -> invalid_arg "Gencoq.exp"

and range loc nm b = function
  (* convert the flag named s into the pre-defined Coq constant sbit *)
  | Flag (s, _) -> bprintf b "%sbit" s
  (* add a cast to nat when the index is a complex expression *)
  | Index (BinOp (_, "-", _) as e) -> (nat_exp loc nm) b e
  | Index e -> (num_exp loc nm) b e
  (* convert a bit range into a Coq bit range *)
  | Bits (n1, n2) -> bprintf b "n%a#n%a" num n1 num n2;;

(*****************************************************************************)
(** instructions *)
(*****************************************************************************)

(*REMOVE when finished! *)
let todo s f b x = bprintf b "todo %s (* %a *)" s f x;;

let try_todo msg f b i =
  let b_try = Buffer.create 500 in 
  match try Some (f b_try) with Not_found -> None with
    | None -> todo msg (Genpc.inst 0) b i
    | Some () -> Buffer.add_buffer b b_try

let case bin loc nm k b (n, i) =
  match i with
    | Affect (_, e) -> indent b k; bprintf b "| %a => %a\n" bin n (exp loc nm) e
    | _ -> raise Not_found;;

let rec inst loc nm k b i = indent b k; inst_aux loc nm k b i

and decl_loc f b x = bprintf b "(fun loc b st => %a loc b st)" f x

and decl_loc_postfix f b x = bprintf b "(fun loc b st => %a loc b st) ::" f x

and pinst loc nm k b i = indent b k; decl_loc (inst_aux loc nm k) b i

and loc_v i = snd (V.vars i)

and inst_cons loc nm k b = function
  (*| Affect (Var _, _) as i -> inst k b i*)
  | i -> indent b k; decl_loc_postfix (inst_aux loc nm k) b i

and inst_aux loc nm k b = function
  (*FIXME: to be done*)
  | Proc ("Start_opcode_execution_at", _) as i ->
      todo "StartOpcodeExecutionAt" (Genpc.inst 0) b i
  | While _ as i -> todo "While" (Genpc.inst 0) b i
  | Coproc _ as i -> todo "Coproc" (Genpc.inst 0) b i

  | Assert _ -> invalid_arg "Gencoq.inst_aux"

  | Unpredictable -> string b "unpredictable EmptyMessage"
      (*FIXME: replace empty string by program name*)

  | Block [] -> string b "block nil"
  | Block is ->
      bprintf b "block (\n%a\n%anil)"
        (list "\n" (inst_cons loc nm (k+2))) is indent (k+2)

  | Let (_, _, is, _) -> 
      bprintf b "%a" (inst_aux loc nm k) (Block is)

  | If (e, i1, None) ->
      bprintf b "if_then %a\n%a" (pexp loc nm) e (pinst loc nm (k+2)) i1

  | If (e, i1, Some i2) ->
      begin match e, i1 with
        | Fun ("CurrentModeHasSPSR", _), _ -> 
            bprintf b "if_CurrentModeHasSPSR (fun em =>\n%a)"
              (pinst loc nm (k+2)) i1
        | _, Affect (_, SPSR None) -> 
            bprintf b 
              "if_then_else %a (if_CurrentModeHasSPSR (fun em =>\n%a))\n%a"
              (pexp loc nm) e (pinst loc nm (k+2)) i1 (pinst loc nm (k+2)) i2
        | _ ->
            bprintf b "if_then_else %a\n%a\n%a"
              (pexp loc nm) e (pinst loc nm (k+2)) i1 (pinst loc nm (k+2)) i2
      end

  (* try to generate the code of an affectation; in case of failure,
     output a "todo" *)

  (*| Affect (e, BinOp (BinOp (e2, "<<", Num "32"), "OR", e1)) -> *)
      

  | Affect (e, v) as i ->
      try_todo "Affect" (fun b -> affect' b v loc nm e) b i

  (* adhoc treatment of case's: as case's are only used for defining
     the variable index, we convert a case which branches define index
     into a let index := followed by a Coq match *)
  | Case (e, nis, oi) as i ->
      try_todo "Case" (fun b -> bprintf b
        "let index :=\n%amatch unsigned %a with\n%a%a%a\n%aend in"
        indent (k+2) (exp loc nm) e (list "" (case bin loc nm (k+4))) nis indent (k+4) 
        (fun b -> function 
          | None -> bprintf b "| _ => repr 0"
          | Some i -> case string loc nm (k+4) b ("_", i)) oi indent (k+2)) b i

  | For (x, p, q, i) ->
      bprintf b "loop %s n%s (fun %s => \n%a)" p q x (inst loc nm (k+2)) i
        
  (* print no parenthesis if there is no argument (functions are
     curryfied in Coq) *)
  | Proc (f, []) -> fun_name b f
  (* default printing of function calls *)
  | Proc (f, es) -> bprintf b "%a %a" fun_name f (list " " (num_exp loc nm)) es
  | Return e -> bprintf b "return_ (%a)" (exp loc nm) e

and affect' b v loc nm = function
  (* otherwise, we use some Coq update function *)
  | Var s ->
      begin
        try
          let name, tp, id = List.find (fun (s',_,_) -> s=s') loc in
          let sz = if tp = "long" then "64" else "" in 
              bprintf b "update_loc%s n%d (*%s*) %a" 
                sz id name (pexp' loc nm sz) v
        with Not_found -> bprintf b "let %s := %a in" s (pexp loc nm) v
      end
  (* affectation of a CPSR bit requires a special case *)
  | Range (CPSR, Flag (s, _)) -> 
      bprintf b "set_cpsr_bit %sbit %a" s (pexp loc nm) v
  | Range (e, r) -> 
      bprintf b "%a (%a %a %a)" 
        (set' loc nm) e (range loc nm) r (pexp loc nm) v (pexp loc nm) e
  | e -> bprintf b "%a %a" (set' loc nm) e (pexp loc nm) v

and set' loc nm b = function
  | Reg (e, None) -> bprintf b "set_reg %a" 
      (regnum_exp loc nm) e
  | Reg (e, Some m) -> bprintf b "set_reg_mode %a %a" mode m (regnum_exp loc nm) e
  | CPSR -> bprintf b "set_cpsr"
  | SPSR None -> bprintf b "set_spsr em"
  | SPSR (Some m) -> bprintf b "set_spsr %a" exn_mode m
  | Memory (e, n) -> bprintf b "write %a %a" (pexp loc nm) e size n
  | _ -> raise Not_found

and range loc nm b = function
  | Flag (s, _) -> bprintf b "set_bit %sbit" s
  | Index i -> bprintf b "set_bit %a" (num_exp loc nm) i
  | Bits (p, q) -> bprintf b "set_bits n%s n%s" p q
;;

(*****************************************************************************)
(** semantic function of a program *)
(*****************************************************************************)

(* program name *)

let ident b i =
  bprintf b "%s%a%a" i.iname (list "" string) i.iparams
    (option "" string) i.ivariant;;

let name b p =
  match p.pkind with
    | InstARM -> ident b p.pident
    | InstThumb -> bprintf b "Thumb_%a" ident p.pident
    | Mode m -> bprintf b "%a_%a" addr_mode m ident p.pident;;

(* result type of a program *)

let mode_var_typ b = function
(*REMOVE?  | "shifter_carry_out" -> string b " * bool"*)
  | _ -> string b " * word";;

let result b p =
  match p.pkind with
    | InstARM | InstThumb -> ()
    | Mode k -> list "" mode_var_typ b (mode_vars k);;

(* split an instruction block into two blocks:
- the prefix of the block consisting of the affectations and cases
- the remainder of the instructions *)

let is_affect = function Affect _ | Case _ -> true | _ -> false;;

let split = function
  | Block is -> firsts is_affect is
  | Affect _ as i -> [i], []
  | i -> [], [i];;

let block nm k b i =
  let is1, is2 = split i in
    List.iter (endline (inst [] nm k) b) is1;
    bprintf b "%alet r := %a nil true s0 in" indent k (inst_aux [] nm k) (Block is2);;

(* default result component value *)
let default b _ = string b ", repr 0";;

let mode_var b = function
(*REMOVE?  | "shifter_carry_out" as s -> bprintf b ", zne 0 %s" s*)
  | s -> bprintf b ", %s" s;;

(* FIXME: programs which normalized form do not consist of affectations only
  are not handled yet. Moreover, they use while-loops... *)
let problems = set_of_list ["A5.5.2";"A5.5.3";"A5.5.4";"A5.5.5"];;

let add_index l =
  let rec aux n = function
    | [] -> []
    | (a,b) :: tl -> (a,b,n) :: aux (n+1) tl
  in aux 0 l;;

let pinst b p =
  match p.pkind with
    | InstARM -> 
        let loc = add_index (snd (V.vars p.pinst)) in
        bprintf b "%a nil true s0" (inst loc (p.pident.iname) 2) p.pinst
    | InstThumb -> () (* TODO: Thumb mode *)
    | Mode k ->
        let ls = mode_vars k in
          if StrSet.mem p.pref problems then
            bprintf b "  let r := %a nil true s0 in\n    (r%a)"
              (todo "ComplexSemantics" (Genpc.inst 0)) p.pinst
              (list "" default) ls
        else
          match p.pinst with
            | If (e, i, None) ->
                bprintf b "  if %a then\n%a\n    (r%a)\n  else (Ok false st%a)"
                  (exp [] (p.pident.iname)) e (block (p.pident.iname) 4) i
                  (list "" mode_var) ls (list "" default) ls
            | i ->
                bprintf b "%a\n    (r%a)" (block (p.pident.iname) 2) i
                  (list "" mode_var) ls;;

let arg_typ b (x, t) = bprintf b " (%s : %s)" x t;;

let semfun b p gs =
  match p.pkind with
    | InstARM | Mode _ ->
        bprintf b
          "(* %s %a *)\nDefinition %a_step (s0 : state)%a : result%a :=\n%a.\n\n"
          p.pref Genpc.name p name p (list "" arg_typ) gs result p pinst p
    | InstThumb -> ();; (* TODO: Thumb mode *)

(*****************************************************************************)
(** constructor declaration corresponding to a program *)
(*****************************************************************************)

let constr bcons_inst bcons_mode p gs =
  match p.pkind with
    | InstARM -> let b = bcons_inst in
        begin match addr_mode_of_prog p gs with
          | Some k ->
              bprintf b "\n| %a (m_ : mode%d)%a"
                name p k (list "" arg_typ) (remove_mode_vars gs)
                (* mode variables are not constructor arguments since
                   they are computed from the mode argument *)
          | None -> bprintf b "\n| %a%a" name p (list "" arg_typ) gs
        end
    | InstThumb -> () (* TODO: Thumb mode *)
    | Mode k -> let b = bcons_mode.(k-1) in
        bprintf b "\n| %a%a" name p (list "" arg_typ) gs;;

(*****************************************************************************)
(** call to the semantics function of some instruction *)
(*****************************************************************************)

(* we rename some argument names to avoid name clashes or warnings in Coq *)
let string_of_arg =
  let set = set_of_list
    ["S";"R";"I";"mode";"StateMask";"PrivMask";"shift"] in
    fun s -> if StrSet.mem s set then s ^ "_" else s;;

let arg b (x, _) = bprintf b " %s" (string_of_arg x);;

let args = list "" arg;;

let call bcall_inst bcall_mode p gs =
  match p.pkind with
    | InstARM -> let b = bcall_inst in
        begin match addr_mode_of_prog p gs with
          | None ->
              bprintf b "    | %a%a =>" name p args gs;
              bprintf b " %a_step s0%a\n" name p args gs
          | Some k ->
              bprintf b "    | %a m_%a =>" name p args (remove_mode_vars gs);
              bprintf b
                "\n      match mode%d_step s0 m_ with (r%a) =>\n"
                k (list "" mode_var) (mode_vars k);
              bprintf b "        match r with\n";
              bprintf b "          | Ok _ _ s1 =>";
              bprintf b " %a_step s1%a\n" name p args gs;
              bprintf b "          | _ => r\n        end\n      end\n"
        end
    | InstThumb -> () (* TODO: Thumb mode *)
    | Mode k -> let b = bcall_mode.(k-1) in
        bprintf b "    | %a%a =>" name p args gs;
        bprintf b " %a_step s0%a\n" name p args gs;;

(*****************************************************************************)
(** Main coq generation function.
For each instruction:
- generate its semantic function
- generate the corresponding constructor for the type of instructions
- generate the call to its semantics function *)
(*****************************************************************************)

let lib b ps =
  let bcons_inst = Buffer.create 5000
  and bcons_mode = Array.init 5 (fun _ -> Buffer.create 1000)
  and bcall_inst = Buffer.create 5000
  and bcall_mode = Array.init 5 (fun _ -> Buffer.create 1000)
  and bsem = Buffer.create 100000
  and bsem_head = Buffer.create 100000 in
  let prog p =
    let gs, _ = V.vars p.pinst in
      semfun bsem p gs;
      constr bcons_inst bcons_mode p gs;
      call bcall_inst bcall_mode p gs
  in
    (* generate code *)

    (let open C2pc.Traduction in 
     begin
       (* print __get function *)
       StringMap.iter (fun s _ -> bprintf bsem_head "Parameter __get_%s : word -> word.\n" s) !map_affect;
       bprintf bsem_head "\n";

       (* print __get_special function *)
       StringMap.iter (fun s _ -> bprintf bsem_head "Parameter __get_special_%s : word -> word.\n" s) !map_affect_spec;
       bprintf bsem_head "\n";

       (* *)
       StringMap.iter (fun s _ -> bprintf bsem_head "Parameter %s : %s.\n" s "regnum") !map_param;
       bprintf bsem_head "\n";
     end);
    (if ps.header = [] then
      ()
     else
      begin
        bprintf bsem_head "%s" (List.fold_left (sprintf "%s%s\n") "" [ (* (* FIXME float support *) "Parameter nat_of_word : word -> nat."
                                                                     ; *) "Definition succ := add (repr 1)."
                                                                     ; "Definition pred x := sub x (repr 1)."
                                                                     ; "Definition opp := sub (repr 0)."
                                                                     ; "Parameter Sbit : nat."
                                                                     ; "Parameter FPSCR_MASK : nat. (* := 0x003FFFFF *)"
                                                                     ; ""]);
      end);
    List.iter (function (Let ((ty, n), ns, is, _)) ->
      (*let gs, _ = V.vars i in*)
      let string_of_ty = function
        | Tint -> "(* 1 *) nat" 
        | Tlong -> "(* 2 *) Type" 
        | Tfloat -> "(* 3 *) Type" 
        | Tdouble -> "(* 4 *) Type"
        | Tvoid -> "(* 5 *) result" 
        | Tunsigned_long -> "(* 6 *) word" 
        | Tchar -> "(* 7 *) Type"
        | Tunsigned_char -> "(* 8 *) word"
        | Tunsigned_short -> "(* 9 *) word"
        | Tbool -> "(* 10 *) bool"
        | Tunsigned_int -> "(* 11 *) word" 
        | Tunsigned -> "(* 12 *) word" in

      (if is = [] then
         if ty = Tvoid then
           if ns = [] then
             bprintf bsem_head "Parameter %s : local -> bool -> state -> result.\n" n 
           else
             bprintf bsem_head "Parameter %s : %a -> local -> bool -> state -> result.\n" n 
               (list " -> " (fun b (ty, _) -> string b (string_of_ty ty) )) ns
         else
           bprintf bsem_head "Parameter %s : %a -> %s.\n" n 
             (list " -> " (fun b (ty, _) -> string b (string_of_ty ty) )) (if ns = [] then assert false else ns)
             (string_of_ty ty)
       else ()
         (* (* FIXME floating point specific operation *) 
           let f x = bprintf bsem_head "Definition %s %a :=\n%a.\n\n" n   
           (list " " (fun b (ty, s) -> 
             string b (sprintf "(%s : %s)" (if s = "" then "_" else s) (string_of_ty ty)) )) ns x in
         if ty = Tvoid then
           f (decl_loc (inst (add_index (snd (V.vars (Block is)))) "" 2)) (Block is)
         else 
           match is with 
             | [Return e] -> f (pexp (add_index (snd (V.vars (Block is)))) "") e 
             | _ -> f (inst (add_index (snd (V.vars (Block is)))) "" 2) (Block is)*) )
        
      | _ -> assert false (* by construction of SH4, this never happens *)) ps.header;
    List.iter prog ps.body;

    (* print preamble *)
    bprintf b
"(* File generated by SimSoC-Cert. It provides the definitions of the types\nof ARMv6 addressing modes and instructions, and their semantics. *)\n\nRequire Import Bitvec List Util Functions Config Arm SCC State Semantics ZArith Message.\n\n";
    
    (* print header *)
    bprintf b "%a" Buffer.add_buffer bsem_head;
    (* print type definitions *)
    for k = 1 to 5 do
      bprintf b "(* Addressing mode %d *)\nInductive mode%d : Type :=%a.\n\n"
        k k Buffer.add_buffer bcons_mode.(k-1)
    done;
    bprintf b "(* Instructions *)\nInductive inst : Type :=%a.\n\n" Buffer.add_buffer bcons_inst;
    (* print semantic functions *)
    bprintf b "(* Semantic functions of addressing modes and instructions *)\nModule InstSem (Import C : CONFIG).\n\n";
    Buffer.add_buffer b bsem;
    for k = 1 to 5 do
      if Buffer.length bcall_mode.(k-1) = 0 then () else 
      bprintf b "(* Semantic function for addressing mode %d *)\nDefinition mode%d_step (s0 : state) (m : mode%d) :=\n  match m with\n%aend.\n\n" k k k Buffer.add_buffer bcall_mode.(k-1)
    done;
    bprintf b "(* Semantic function for instructions *)\nDefinition step (s0 : state) (i : inst) : result :=\n  match i with\n%aend.\n\n" Buffer.add_buffer bcall_inst;
    bprintf b "End InstSem.\n";;
