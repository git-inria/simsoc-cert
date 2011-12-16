(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

open Patch

module type PATCH = 
sig
  val main : (action * pos list) list
end

let comment_first s = 
  Replace_first (S s, Printf.sprintf "/* %s */" s)

let p = BatList.map (fun x -> P x)
let r = BatList.map (fun (x, y) -> R (x, y))

module Syntax = 
struct
  module Header_float : PATCH =
  struct
    let r_459_4 = R (459, 4)
    let main = 
      BatList.flatten
        [ [ Comment, [ R (160, 2) ; R (167, 2) ; P 172 ; P 179 ; P 191 ; P 204 ; P 208 ; P 211 ] ]

        ; [ Replace_first (S "d", "#d"), [ P 194 ]
          ; Replace_first (S "x)", "x"), [ P 427 ]
          ; Replace_first (S "()", "(m, n)"), [ r_459_4 ] (* FIXME m or n ? *)
          ; Replace_first (S "(c", "c"), [ P 460 ] ]

        ; [ Replace_all (",", ", int "), p [ 319 ; 324 ; 394 ; 434 ; 561 ; 572 ; 577 ; 588 ; 618 ; 624 ; 630 ] 
          ; Replace_all (",", ", float "), p [ 492 ; 522 ] ] (* missing type declaration *)
          
        ; (let l = p [ 579 ; 581 ; 583 ; 585 ; 590 ; 591 ; 593 ; 595 ] in
          [ Replace_first (S "check_ ", "check_"), r_459_4 :: P 572 :: P 577 :: P 588 :: l
          ; Replace_first (S "((", "("), l ])
          
        ; [ Replace_first (S "0", "0)"), p [ 608 ; 621 ]
          ; Add_char_end " {", p [ 537 ] ] ]
  end

  let add_int_type = Replace_first (S "m,n", "m, int n")

  module Body : PATCH =
  struct
    let main = BatList.flatten
      [ [ Replace_tilde 2, p [ 1434 ; 1439 ; 4276 ; 4279 ]
        ; Replace_tilde 1, p [ 5424 ; 6115 ; 6277 ] ]
      ; [ Add_char_end ";", p [ 1502 ; 6932 ]
        ; Replace_first (S ",", ";"), p [ 3871 ]
        ; Replace_first (S "Lo", "lo"), p [ 3955 ]
        ; Replace_first (S "}", "{"), p [ 4555 ]
        ; Replace_first (S "long n", "long n)"), p [ 4979 ]
        ; Replace_first (S "((", "("), p [ 5280 ]
        ; Replace_all ("–=", "-="), [ R (6713, 151) ]
        ; Replace_first (S "H'", "H_"), p [ 7302 ] ]

      ; [ add_int_type, p [ 6103 ; 6269 ]
        ; Replace_first (S "d, n", "int d, int n"), p [ 4746 ] ] ]
  end

  module Body_float : PATCH =
  struct
    let main = BatList.flatten
      [ [ Replace_first (S ",", ", int "), p [ 1754 ; 1854 ; 1862 ; 1876 ; 2176 ; 2223 ; 2357 ; 2560 ; 2638 ]
        ; add_int_type, [ R (2795, 252) ; P 3384 ]

        ; Replace_first (S "pc", "PC"), [ R (1715, 1775) ]
        ; Replace_first (S "case", "switch"), p [ 1995 ; 2004 ; 2091 ; 2098 ; 3492 ; 3504 ]
        ; Replace_first (S "((", "("), p [ 1995 ; 2091 ]
        ; Add_char_beg "case", r [ 1996, 2 ; 2005, 4 ; 2014, 4 ; 2092, 2 ; 2099, 7 ; 3493, 3 ; 3505, 3 ] ]

      ; [ Add_line_aft "int data_type_of_2(int n1, int n2) {
  return 0 ;
}", p [ 2039 ] (* FIXME écrire la fonction *)
        ; Replace_first (S "f", "f_2"), p [ 2004 ] ]

      ; [ Add_char_end ";", p [ 2219 ; 2633 ; 3060 ] ]

      ; (let add s nb = Add_char_beg (s ^ (String.make (4 (* minimal space such that the decoder processing accepts it as a new column *) - String.length s) ' ')), [ P nb ] in
         [ add "PR" 2417
         ; add "0" 2418
         ; add "1" 2419 ]) (* information missing for the decoder processing *)
        
      ; [ Replace_first (S "))", ")"), p [ 2035 ]
        ; Replace_first (S ")", "))"), p [ 2572 ; 3036 ]

        ; comment_first ", float *FPUL", p [ 2460 ; 3342 ]
        ; Replace_first (S "*FPUL", "FPUL"), p [ 1997 ; 2007 ; 2093 ; 2462 ; 3344 ]
        ; Replace_first (S ")", ", FPUL)"), [ R (3494, 2) ; R (3506, 2) ]
          
        ; Replace_first (S ";", ", src;"), p [ 2115 ]
        ; Add_char_end "}", p [ 2605 ]
        ; Replace_first (S "SUB", "FSUB"), p [ 3396 ]
        ; Replace_first (S "FSUB", "FSUB_"), p [ 3384 ] (* FSUB is a "#define" symbol, so we have to rename the name of this function *)
        ; Replace_first (S "gn", "ng"), p [ 3511 ] 
        ; Replace_first (S ";", ",j;"), p [ 3638 ] 
        ; Replace_first (S "4j", "4*j"), p [ 3647 ] ]
      ; [ Replace_first (S "normal_ ", "normal_"), p [ 2007 ; 3245 ] 
        ; Replace_first (S "single_ ", "single_"), p [ 3492 ] ]
      ]
  end
end

module Semantic_gcc = 
struct
  module Header_float : PATCH =
  struct
    let main = 
      BatList.flatten
        [ [ Replace_first (Re "unsigned [a-z]+", "void"), [ R (164, 3) ]

          ; Replace_first (S "unsigned long", "int" (* FIXME determine if "int" can really be a substitute for "unsigned long". To put in compcert ? *)), [ R (183, 7) ]
          ; Comment, [ P 183 ; R (186, 2) ]

          ; Add_char_beg "void ", p [ 171 ; 207 ] ] (* change output type *)

        ; [ Add_line_aft "#define SPSCR_RM          FPSCR&1", p [ 255 ]
          ; Add_line_aft "#define DR_HEX            frf.l[ FPSCR_FR]", p [ 256 ] ] (* FIXME existence *)

        ; [ Replace_first (S "((", "("), p [ 303 ] ]
        ; [ Add_line_aft "int dst_d;", p [ 330 ] 
          ; Replace_first (S "dst.d", "dst_d"), p [ 385; 389 ; 391 ] ] (* FIXME do we have to declare dst_d ? *) ]
  end

  module Body : PATCH =
  struct
    let main = BatList.flatten
      [ [ Replace_all ("&&", "&"), p [ 1065 ]
        ; Replace_all ("(long i)", "i"), [ R (1077, 2) ] ]

      (* fpul *)
      ; [ comment_first ", int *FPUL", p [ 4003 ; 4008 ; 6913 ; 6918 ]
        ; Replace_first (S "*FPUL", "FPUL"), p [ 4005 ; 4010 ; 6915 ; 6921 ] ]

      ; [ Replace_all ("TLB[MMUCR. URC] ", "TLB_MMUCR_URC"), [ R (4162, 13) ] ]

      (* the following functions are already defined before, so we have to rename the name of this new declarations *)
      ; [ Replace_first (S "MACL", "MACL_"), p [ 4222 ]
        ; Replace_first (S "STS", "STS_"), p [ 6924 ] ]

      (* type error *)
      ; [ Replace_first (S "MACH&0x00008000", "bool_of_word(MACH&0x00008000)"), p [ 4290 ] ]


      (* simplifying *)
      ; [ Replace_first (All, "if_is_write_back_memory_and_look_up_in_operand_cache_eq_miss_then_allocate_operand_cache_block(R[n]);"), [ R (5133, 3) ]
        ; Replace_first (Re "(is_dirty_block(R\\[n\\])) +write_back(R\\[n\\]);?", "_is_dirty_block_then_write_back(R[n]);"), p [ 5502 ; 5543 ] ]

      ; [ Replace_first (S "R15", "R[15]"), p [ 7297 ] ]

      ; [ Replace_all ("SR.", "SR_"), [ R (7298, 3) ] ] ]
  end

  module Body_float : PATCH =
  struct
    let main = BatList.flatten
      [ [ Replace_first (S "= FR[n]", "= ((int) FR[n])"), p [ 1714 ] (* FIXME s'agit-il de convertir FR[n] en int ou l'autre nombre en float ? *) ]
      ; [ Replace_first (S "FADD", "FADD_"), p [ 1754 ] (* FADD is a "#define" symbol, so we have to rename the name of this function *)
        ; Replace_first (S "ADD", "FADD"), p [ 1766 ] (* ? *) ] ]
  end
end

module Semantic_compcert =
struct
  module Header_float : PATCH = 
  struct

    let main = BatList.flatten
      [ [ Add_line_aft "void Sleep_standby(void);
/*void allocate_operand_cache_block(unsigned long);*/

void fpu_exception_trap(void);
void inexact(void);
void invalidate_operand_cache_block(unsigned long);
void if_is_dirty_block_then_write_back(unsigned long);
void if_is_write_back_memory_and_look_up_in_operand_cache_eq_miss_then_allocate_operand_cache_block(unsigned long);
void load_int(int, int);
void load_quad(int, int);
float sqrt(float);
void store_int(int, int);
void store_quad(int, int);
void undefined_operation(void);
/*void write_back(unsigned long);*/", p [ 155 ]
        ; Add_line_aft "union {
    int ASID, VPN, PPN, SZ, SH, PR, WT, C, D, V, SA, TC;
  } TLB_MMUCR_URC; unsigned long PTEH, PTEL, PTEA;", p [ 175 ] (* FIXME existence *)
        ; Add_line_aft "unsigned long SSR, SPC, DBR, SGR, R0_BANK, R1_BANK, R2_BANK, R3_BANK, R4_BANK, R5_BANK, R6_BANK, R7_BANK, TRA, SR_MD, SR_BL, SR_RB, EXPEVT, H_00000100;", p [ 176 ] (* FIXME existence *)
        ; Add_line_aft "float FPUL;", p [ 178 ] (* TODO move this to gcc *) ]
      ; [ Add_line_aft "int i;", p [ 463 ] ] 
        
      ; [ Replace_first (Re "\\( +\\)\\(.+\\)\\( +\\)\\(.+\\)\\( +\\)\\(.+\\)", "\\1\\2\\3\\4\\5nat_of_word(\\6)"), p [ 251 ]
        ; Replace_first (Re "\\( +\\)\\(.+\\)\\( +\\)\\(.+\\)\\( +\\)\\(.+\\)", "\\1\\2\\3\\4\\5bool_of_word(\\6)"), p [ 252 ; 253 ]
        ; Replace_first (S "n+1", "nat_of_word(n+1)"), p [ 303 ; 311 ]
        ; Replace_first (S "FPSCR_PR", "bool_of_word(FPSCR_PR)"), p [ 628 ]
        ; comment_first "long", p [ 340 ; 410 ] (* "long double" compcert unsupported *) ] (* add conv type *) ]
  end

  let fundef_order = [ "sign_of" ; "zero" ; "data_type_of" ; "register_copy" ; "set_V" ; "set_O" ; "set_U" ; "set_I" ; "qnan" ; "invalid" ; "inf" ; "check_single_exception" ; "check_double_exception" ; "normal_faddsub" ; "normal_fmul" ; "check_product_infinity" ; "check_negative_infinity" ; "check_positive_infinity" ; "check_product_invalid" ; "fipr" ; "clear_cause" ; "set_E" ; "set_Z" ; "dz" ] (** ENHANCEMENT generate this list automatically by repetitively running compcert and parsing its error messages to get the dependency *)

  module Body_float =
  struct
    let main = 
      [ Replace_first (S "FPSCR.PR", "FPSCR_PR"), p [ 1995 ; 2517 ; 3491 ] 
      ; comment_first "int", p [ 2239 ; 2641 ; 3274 ] (* "int double" compcert unsupported *) ]
  end
end


let patch_head_nooffset = 
  BatList.flatten [ Syntax.Header_float.main ; Semantic_gcc.Header_float.main ; Semantic_compcert.Header_float.main ]

let patch_nooffset =
  BatList.flatten [ Syntax.Body.main ; Semantic_gcc.Body.main ; Syntax.Body_float.main ; Semantic_gcc.Body_float.main ; Semantic_compcert.Body_float.main ]

let patch = 
  let offset = 9000 in
  let offset_body = 9600 (* to simplify our process of localizing errors, the section 9 has been approximated to a position which begin at this number *) in

  let decal offset = BatList.map (function act, l_pos -> act, BatList.map (function R (pos, len) -> R (offset + pos, len) | P pos -> P (offset + pos)) l_pos) in

  BatList.flatten
    (BatList.map (fun (o, l) -> decal o (BatList.flatten l))

       [ offset, [ Syntax.Header_float.main 
                 ; Semantic_gcc.Header_float.main
                 ; Semantic_compcert.Header_float.main ]
         
       ; offset_body, [ Syntax.Body.main
                      ; Semantic_gcc.Body.main
                        
                      ; Syntax.Body_float.main
                      ; Semantic_gcc.Body_float.main
                      ; Semantic_compcert.Body_float.main ] ])
    
