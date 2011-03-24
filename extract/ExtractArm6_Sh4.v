(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Extraction of the arm6 simulator.
*)

Require Iteration.
Require Floats.
Require RTLgen.
Require Coloring.
Require Allocation.
Require Compiler.
Require Initializers.

(* Standard lib *)
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

(* Float *)
Extract Inlined Constant Floats.float => "float".
Extract Constant Floats.Float.zero   => "0.".
Extract Constant Floats.Float.neg => "( ~-. )".
Extract Constant Floats.Float.abs => "abs_float".
Extract Constant Floats.Float.singleoffloat => "Floataux.singleoffloat".
Extract Constant Floats.Float.intoffloat => "Floataux.intoffloat".
Extract Constant Floats.Float.intuoffloat => "Floataux.intuoffloat".
Extract Constant Floats.Float.floatofint => "Floataux.floatofint".
Extract Constant Floats.Float.floatofintu => "Floataux.floatofintu".
Extract Constant Floats.Float.add => "( +. )".
Extract Constant Floats.Float.sub => "( -. )".
Extract Constant Floats.Float.mul => "( *. )".
Extract Constant Floats.Float.div => "( /. )".
Extract Constant Floats.Float.cmp => "Floataux.cmp".
Extract Constant Floats.Float.eq_dec => "fun (x: float) (y: float) -> x = y".
Extract Constant Floats.Float.bits_of_double => "Floataux.bits_of_double".
Extract Constant Floats.Float.double_of_bits => "Floataux.double_of_bits".
Extract Constant Floats.Float.bits_of_single => "Floataux.bits_of_single".
Extract Constant Floats.Float.single_of_bits => "Floataux.single_of_bits".

(* Memdata *)
Extract Constant Memdata.big_endian => "Memdataaux.big_endian".

(* Memory - work around an extraction bug. *)
Extraction NoInline Memory.Mem.valid_pointer.

(* Errors *)
Extraction Inline Errors.bind Errors.bind2.

(* Iteration *)
Extract Constant Iteration.dependent_description' =>
  "fun x -> assert false".

Extract Constant Iteration.GenIter.iterate =>
  "let rec iter f a =
     match f a with Coq_inl b -> Some b | Coq_inr a' -> iter f a'
   in iter".

(* RTLgen *)
Extract Constant RTLgen.compile_switch => "RTLgenaux.compile_switch".
Extract Constant RTLgen.more_likely => "RTLgenaux.more_likely".
Extraction Inline RTLgen.ret RTLgen.error RTLgen.bind RTLgen.bind2.

(* RTLtyping *)
Extract Constant RTLtyping.infer_type_environment => "RTLtypingaux.infer_type_environment".

(* Coloring *)
Extract Constant Coloring.graph_coloring => "Coloringaux.graph_coloring".

(* Linearize *)
Extract Constant Linearize.enumerate_aux => "Linearizeaux.enumerate_aux".

(* SimplExpr *)
Extraction Inline SimplExpr.ret SimplExpr.error SimplExpr.bind SimplExpr.bind2.

(* Compiler *)
Extract Constant Compiler.print_Csyntax => "PrintCsyntax.print_if".
Extract Constant Compiler.print_Clight => "PrintClight.print_if".
Extract Constant Compiler.print_Cminor => "PrintCminor.print_if".
Extract Constant Compiler.print_RTL => "PrintRTL.print_rtl".
Extract Constant Compiler.print_RTL_tailcall => "PrintRTL.print_tailcall".
Extract Constant Compiler.print_RTL_castopt => "PrintRTL.print_castopt".
Extract Constant Compiler.print_RTL_constprop => "PrintRTL.print_constprop".
Extract Constant Compiler.print_RTL_cse => "PrintRTL.print_cse".
Extract Constant Compiler.print_LTLin => "PrintLTLin.print_if".
Extract Constant Compiler.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".
(*Extraction Inline Compiler.apply_total Compiler.apply_partial.*)

(* Processor-specific extraction directives *)

Load extractionMachdep.

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Go! *)
(* we assume we are in the extract directory *)
Cd "tmp".

Require arm6dec.
Extract Constant arm6dec.decode_addr_mode1 => "Arm6mldec.decode_addr_mode1". 
Extract Constant arm6dec.decode_addr_mode2 => "Arm6mldec.decode_addr_mode2". 
Extract Constant arm6dec.decode_addr_mode3 => "Arm6mldec.decode_addr_mode3". 
Extract Constant arm6dec.decode_addr_mode4 => "Arm6mldec.decode_addr_mode4". 
Extract Constant arm6dec.decode_addr_mode5 => "Arm6mldec.decode_addr_mode5". 
Extract Constant arm6dec.decode_unconditional => "Arm6mldec.decode_unconditional".
Extract Constant arm6dec.decode_conditional => "Arm6mldec.decode_conditional".
Extract Constant arm6dec.decode => "Arm6mldec.decode".

Require Semantics.
Extraction NoInline Arm_Functions.Semantics.if_CurrentModeHasSPSR.

(*Print Extraction Inline.*)

Require arm6.

Extraction Library Bitvec.
Extraction Library Util.
Extraction Library Message.
Extraction Library Semantics.
Extraction Library Simul.

(* *)

Extraction Library Arm.
Extraction Library Arm_Config.
Extraction Library Arm_Proc.
Extraction Library Arm_SCC.
Extraction Library Arm_State.
Extraction Library Arm_Exception.
Extraction Library Arm_Functions.

Extraction Library arm6.
Extraction Library arm6dec.
Extraction Library arm6inst.

(* *)

Require sh4dec.
Require sh4.

Extraction Library Sh4.
Extraction Library Sh4_Config.
Extraction Library Sh4_Proc.
(*Extraction Library Sh4_SCC.*)
Extraction Library Sh4_State.
(*Extraction Library Sh4_Exception.*)
Extraction Library Sh4_Functions.

Extraction Library sh4.
Extraction Library sh4dec.
Extraction Library sh4inst.
