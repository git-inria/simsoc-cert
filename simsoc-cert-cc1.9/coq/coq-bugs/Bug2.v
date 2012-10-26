(* extraction problem in 8.3 *)

Set Implicit Arguments.

Section S.

Definition message := nat.
Definition word := nat.
Definition mode := nat.
Definition opcode := nat.

Variable condition : word -> option opcode.

Section decoder_result.

 Variable inst : Type.

 Inductive decoder_result : Type :=
 | DecUndefined : decoder_result
 | DecUnpredictable : decoder_result
 | DecInst : inst -> decoder_result
 | DecError : message -> decoder_result.

End decoder_result.

Definition decode_cond_mode (mode : Type) (f : word -> decoder_result mode)
  (w : word) (inst : Type) (g : mode -> opcode -> inst) :
  decoder_result inst :=
  match condition w with
    | Some oc =>
      match f w with
        | DecInst i => DecInst (g i oc)
        | DecError m => @DecError inst m
        | DecUndefined => @DecUndefined inst
        | DecUnpredictable => @DecUnpredictable inst
      end
    | None => @DecUndefined inst
  end.

End S.

Extraction "bug2.ml" decoder_result decode_cond_mode.

(* Problem: in this extraction, the 3 cases that transform a
(decoder_result mode) into a (decoder_result inst):

        | DecError m => @DecError inst m
        | DecUndefined => @DecUndefined inst
        | DecUnpredictable => @DecUnpredictable inst

are replaced by:
                    | x -> x.

So, from the point of view of ML, the input and output types are the
same. Yet, the extractor gives different types in bug2.mli.

Solution: extract as in the Coq code by just erasing types:

		    | DecUnpredictable -> DecUnpredictable
		    | DecUndefined -> DecUndefined
		    | DecError m -> DecError m
*)

(* bug2.mli:

val decode_cond_mode :
  (word -> opcode option) -> (word -> 'a1 decoder_result) -> word -> ('a1 ->
  opcode -> 'a2) -> 'a2 decoder_result
*)

(* bug.ml:

type 'inst decoder_result =
  | DecUndefined
  | DecUnpredictable
  | DecInst of 'inst
  | DecError of message

(** val decode_cond_mode :
    (word -> opcode option) -> (word -> 'a1 decoder_result) -> word -> ('a1
    -> opcode -> 'a2) -> 'a2 decoder_result **)

let decode_cond_mode condition f w g =
  match condition w with
    | Some oc -> (match f w with
                    | DecInst i -> DecInst (g i oc)
                    | x -> x)
    | None -> DecUndefined
*)

(* ocamlc -i bug2.ml:

val decode_cond_mode :
  ('a -> 'b option) ->
  ('a -> 'c decoder_result) -> 'a -> ('c -> 'b -> 'c) -> 'c decoder_result
*)
