(*
  Produces a verified CakeML program that checks VIPR proofs
*)
open preamble basis basisProgTheory cfLib basisFunctionsLib milpTheory;

val _ = new_theory "viprProg"

val _ = translation_extends "basisProg";

Datatype:
  reader_state = Init
               | ReadingProblem (mlstring list)
               | Error mlstring
End

Definition init_state_def:
  init_state = Init
End

Definition checker_step_def:
  checker_step (line:mlstring) (s:reader_state) = s
End

Definition print_outcome_def:
  print_outcome (s:reader_state) = strlit "TODO"
End

Definition usage_message_def:
  usage_message = concat [strlit "Usage:\n";
                          strlit "to read from stdin:   cake_vipr\n";
                          strlit "to read from a file:  cake_vipr FILE\n"]
End

val init_state_v_thm = translate init_state_def;
val checker_step_v_thm = translate checker_step_def;

val r = translate print_outcome_def;
val r = translate (usage_message_def |> CONV_RULE (RAND_CONV EVAL));
val r = translate oHD_def;

val _ = (append_prog o process_topdecs) `
  fun main u =
    let
      val cl = CommandLine.arguments ()
      val r = TextIO.foldLines checker_step init_state (ohd cl)
    in print (print_outcome (Option.valOf r)) end
    handle e => TextIO.output TextIO.stdErr usage_message`;

val main_v_def = fetch "-" "main_v_def";

Definition run_vipr_def:
  run_vipr lines =
    print_outcome (foldl checker_step init_state lines)
End

Theorem main_spec_stdin:
   hasFreeFD fs ∧ stdin_content fs = SOME text ∧ LENGTH cl < 2
   ⇒
   app (p:'ffi ffi_proj) main_v
     [Conv NONE []]
     (STDIO fs * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv *
                STDIO (add_stdout (fastForwardFD fs 0) $
                         run_vipr (lines_of (implode text))) *
                COMMANDLINE cl)
Proof
  strip_tac
  \\ xcf_with_def () main_v_def
  \\ reverse $ xhandle ‘(POSTv uv. &UNIT_TYPE () uv *
                STDIO (add_stdout (fastForwardFD fs 0) $
                         run_vipr (lines_of (implode text))) *
                COMMANDLINE cl)’
  >- xsimpl
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)
  \\ fs[wfcl_def]
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ assume_tac checker_step_v_thm
  \\ assume_tac init_state_v_thm
  \\ drule_then drule foldLines_NONE
  \\ disch_then $ drule_at $ Pos last
  \\ rename [‘OPTION_TYPE STRING_TYPE (oHD (TL cl)) vvv’]
  \\ ‘OPTION_TYPE FILENAME NONE vvv’ by
    (Cases_on ‘cl’ \\ fs [] \\ Cases_on ‘t’ \\ fs [std_preludeTheory.OPTION_TYPE_def])
  \\ disch_then $ qspec_then ‘p’ mp_tac
  \\ disch_then drule
  \\ strip_tac
  \\ xlet ‘(POSTv retv.
             STDIO (fastForwardFD fs 0) * COMMANDLINE cl *
             &OPTION_TYPE VIPRPROG_READER_STATE_TYPE
               (SOME
                  (foldl checker_step init_state (lines_of (implode text))))
               retv)’
  >- (xapp \\ xsimpl)
  \\ qpat_x_assum ‘app _ _ _ _ _’ kall_tac
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ xsimpl
  \\ pop_assum $ irule_at $ Pos hd
  \\ fs [GSYM run_vipr_def]
  \\ qexists_tac ‘fastForwardFD fs 0’
  \\ xsimpl
QED

Theorem vipr_stdin_whole_prog_spec:
   hasFreeFD fs ∧ stdin_content fs = SOME text ∧ LENGTH cl < 2 ⇒
   whole_prog_spec main_v cl fs NONE ((=) $ add_stdout (fastForwardFD fs 0) $
                                              run_vipr (lines_of (implode text)))
Proof
  rw[whole_prog_spec_def]
  \\ irule_at Any app_wgframe
  \\ irule_at Any main_spec_stdin
  \\ fs []
  \\ rpt $ first_assum $ irule_at Any
  \\ xsimpl
  \\ qexists_tac ‘(add_stdout (fastForwardFD fs 0)
               (run_vipr (lines_of (implode text))))’
  \\ gvs [] \\ xsimpl
  \\ gvs [GSYM add_stdo_with_numchars,with_same_numchars]
  \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ gvs [IO_fs_component_equality]
QED

val (sem_thm,prog_tm) = whole_prog_thm
                          (get_ml_prog_state())
                          "main"
                          (UNDISCH vipr_stdin_whole_prog_spec)

Definition vipr_prog_def:
  vipr_prog = ^prog_tm
End

Triviality clean_up:
  (b' ⇒ c) ⇒ ∀b. (b ⇒ b') ⇒ b ⇒ c
Proof
  fs []
QED

Theorem vipr_semantics =
  sem_thm |> REWRITE_RULE[GSYM vipr_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO]
  |> MATCH_MP clean_up
  |> Q.SPEC ‘stdin_content fs = SOME text ∧ LENGTH cl < 2 ∧ wfcl cl ∧
             wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs’
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (srw_ss()) []))
  |> (fn th => MATCH_MP th TRUTH);

val _ = export_theory();
