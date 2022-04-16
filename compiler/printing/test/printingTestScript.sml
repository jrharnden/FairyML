(*
  This file creates some sample declarations and runs the pretty
  printer adjustments over them, confirms that the adjusted decs
  still type check, and exports the s-expressions so that the
  printed strings can be checked with the binary compiler.

  This builds on the inferencer run over the basis in
  basisTypeCheckTheory.
*)

open preamble basicComputeLib inferenceComputeLib basisTypeCheckTheory
open ml_translatorLib ml_progLib basisFunctionsLib
open addPrintValsTheory addTypePPTheory printTweaksTheory
local open fromSexpTheory in end
local open astToSexprLib in end

val _ = new_theory "printingTest"

val _ = translation_extends "basisProg"
val _ = (use_full_type_names := false);


Datatype:
  example = Ex_A num (example list) | Ex_B num
End

Definition muddle_def:
  muddle i xs (Ex_A j ys) = Ex_A (i + j) (TAKE 2 xs ++
    DROP 2 (MAP (muddle (i + 1) (DROP 2 xs ++ TAKE 2 ys)) ys)) /\
  muddle i xs (Ex_B n) = Ex_A (i + n) xs
Termination
  WF_REL_TAC `measure (example_size o SND o SND)`
End

Definition x1_def:
  x1 = Ex_A 42 [Ex_B 5; Ex_B 7]
End

Definition x2_def:
  x2 = muddle 3 [x1] x1
End

Definition x3_def:
  x3 = [muddle 17 [x2; x1] x2]
End

Definition x4_def:
  x4 = SOME (Ex_A 3 x3)
End

Definition x_list_bool_def:
  x_list_bool = [T; F; T]
End

Definition x_list_chars_def:
  x_list_chars = ["hello"; "there"] ++
    GENLIST (\n. if n < 32 then "dummy" else [CHR n]) 127
End

Theorem x_list_chars_thm = EVAL ``x_list_chars``

Definition x_list_strs_def:
  x_list_strs = MAP implode x_list_chars ++ [implode (FLAT x_list_chars)]
End

Definition x_maps_def:
  x_maps = [(1i, mlmap$fromList (mlint$int_cmp) [(1i, "x"); (2, "y")])]
End

val res = register_type ``: example``;
val res = translate TAKE_def;
val res = translate DROP_def;
val res = translate muddle_def;

val res = translate x1_def;
val res = translate x2_def;
val res = translate x3_def;
val res = translate x4_def;

val res = translate x_list_bool_def;
val res = translate x_list_chars_thm;
val res = translate x_list_strs_def;

val res = translate x_maps_def;

val dlet_empty = ``Dlet unknown_loc (Pvar "x_app_list_empty") (Con (SOME (Short "Nil")) [])``

val _ = ml_prog_update remove_snocs;

val prog = get_prog (get_ml_prog_state ());

val new_prog_eval = EVAL ``DROP (LENGTH basis) (^prog ++ [^dlet_empty])``;
val test_prog = rhs (concl new_prog_eval)

Definition test_prog_def:
  test_prog = ^test_prog
End

val basis_tn_eval = EVAL ``init_type_names basis_ienv``;
val basis_tn = basis_tn_eval |> concl |> rhs

val with_pp_eval = EVAL ``add_pp_decs ^basis_tn.pp_fixes test_prog``;
val with_pp = rhs (concl with_pp_eval);

Definition test_prog_pp_def:
  test_prog_pp = ^with_pp
End

(* copied from basisTypeCheck *)
val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [inferenceComputeLib.add_inference_compset,
      basicComputeLib.add_basic_compset
      ],
     computeLib.Defs
      [test_prog_def, test_prog_pp_def, basis_ienv_def
      ],
    computeLib.Tys
    [    ]
    ] cmp
val inf_eval = computeLib.CBV_CONV cmp

val _ = (max_print_depth := 20);

val start_st_eval = EVAL ``(init_infer_state <| next_id := basis_infer_st.next_id |>)``
val start_st = start_st_eval |> concl |> rhs

val _ = print "Setup done, doing type inference of program.\n";

val infer_example_eval = inf_eval ``infer_ds basis_ienv test_prog_pp ^start_st``

val infer_example_ienv = concl infer_example_eval |> rhs
    |> dest_pair |> fst |> rand
val infer_example = concl infer_example_eval |> rhs
val infer_example_st = infer_example |> dest_pair |> snd

val _ = if can (match_term ``(infer$Success _, _)``) infer_example then () else
    (print_term infer_example; failwith ("type inference failed on example prog"))

val _ = print "Fetching type-name info and adding print statements.\n"

val example_prints_eval = EVAL ``val_prints ^basis_tn basis_ienv ^infer_example_ienv``
val example_print_decs = concl example_prints_eval |> rhs |> dest_pair |> fst

val _ = print "Type-checking extended program.\n"

val infer_with_prints_eval = inf_eval
    ``infer_ds (extend_dec_ienv ^infer_example_ienv basis_ienv)
        ^example_print_decs ^infer_example_st``
val infer_with_prints = concl infer_with_prints_eval |> rhs

val _ = if can (match_term ``(infer$Success _, _)``) infer_with_prints then () else
    (print_term infer_with_prints;
        failwith ("type inference failed on example prog with prints"))

val _ = print "Combining to single theorem.\n"

(* show the above is a step-by-step evaluation of add_print_features *)
val assembled = ``add_print_features (^basis_tn, basis_ienv, basis_infer_st.next_id) test_prog``
  |> (SIMP_CONV (srw_ss ()) [add_print_features_def, LET_THM,
        REWRITE_RULE [GSYM test_prog_pp_def] with_pp_eval,
        start_st_eval, infer_example_eval, example_prints_eval,
        infer_with_prints_eval]
  )

val prog_rhs = assembled |> concl |> rhs
val _ = if can (match_term ``(infer$Success _)``) prog_rhs then () else
    (print_term prog_rhs;
        failwith ("test printing/inference assembly failed"))

val _ = print "Writing sexp output.\n"

val upd_prog = rand prog_rhs |> dest_pair |> fst
val full_prog_eval = EVAL ``basis ++ ^upd_prog``;
val full_prog = rhs (concl full_prog_eval);

val res = astToSexprLib.write_ast_to_file "example_print.sexp" full_prog;

val _ = print "Success.\n";

val _ = export_theory ();

