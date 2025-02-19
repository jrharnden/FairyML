(*
  The REPL puts some restrictions on what decs are acceptable as user input.
  This file defines what those restrictions are.
*)
open preamble
open semanticsPropsTheory evaluateTheory semanticPrimitivesTheory
open ast_extrasTheory

val _ = Parse.hide "types"

val _ = new_theory "repl_decs_allowed";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* definition *)

Definition safe_exp_def:
  safe_exp = every_exp $ λx.
               case x of
                | _ => T
End

Theorem safe_exp_simps[simp] =
   [“safe_exp (Raise e)”,
    “safe_exp (Handle e pes)”,
    “safe_exp (Lit lit)”,
    “safe_exp (Con opt xs)”,
    “safe_exp (Var n)”,
    “safe_exp (Fun n x)”,
    “safe_exp (App op xs)”,
    “safe_exp (Log lop x y)”,
    “safe_exp (If x y z)”,
    “safe_exp (Mat e pes)”,
    “safe_exp (Let opt x y)”,
    “safe_exp (Letrec f x)”,
    “safe_exp (Tannot e t)”,
    “safe_exp (Lannot e l)”]
  |> map (SIMP_CONV (srw_ss()) [safe_exp_def])
  |> map (SIMP_RULE (srw_ss()) [GSYM safe_exp_def, SF ETA_ss])
  |> LIST_CONJ;

Definition safe_dec_def:
  safe_dec = every_dec $ λd.
               case d of
                 Dlet locs pat x => safe_exp x
               | Dletrec locs funs => EVERY safe_exp (MAP (SND o SND) funs)
               | _ => T
End

Theorem safe_dec_simps[simp] =
  [“safe_dec (Dlet l p x)”,
   “safe_dec (Dletrec l f)”,
   “safe_dec (Dtype l tds)”,
   “safe_dec (Dtabbrev l ns n t)”,
   “safe_dec (Dexn l n ts)”,
   “safe_dec (Dmod mn ds)”,
   “safe_dec (Dlocal ds1 ds2)”,
   “safe_dec (Denv n)”]
  |> map (SIMP_CONV (srw_ss()) [safe_dec_def])
  |> map (SIMP_RULE (srw_ss()) [GSYM safe_dec_def, SF ETA_ss])
  |> LIST_CONJ;


Definition decs_allowed_def:
  decs_allowed (decs:ast$dec list) = EVERY safe_dec decs
End

(* pmatch lemmas *)

Triviality safe_exp_pmatch_lemma:
  safe_exp =
     every_exp $ λx. case x of
                     | _ => T
Proof
  CONV_TAC(ONCE_DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ rw [safe_exp_def,FUN_EQ_THM]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw [safe_exp_def,FUN_EQ_THM]
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
QED

Theorem safe_exp_pmatch = safe_exp_pmatch_lemma
  |> SIMP_RULE std_ss [IN_UNION,IN_INSERT,NOT_IN_EMPTY,GSYM CONJ_ASSOC]

val _ = export_theory();
