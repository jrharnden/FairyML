(*
  Proves an end-to-end correctness theorem for the bootstrapped compiler.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     compiler64ProgTheory x64BootstrapTheory replProofTheory

val _ = new_theory"x64BootstrapProof";

Triviality with_clos_conf_simp:
    (mc_init_ok (x64_backend_config with <| clos_conf := z ; bvl_conf updated_by
                    (λc. c with <|inline_size_limit := t1; exp_cut := t2|>) |>) =
     mc_init_ok x64_backend_config) /\
    (x.max_app <> 0 /\ (case x.known_conf of NONE => T | SOME k => k.val_approx_spt = LN) ==>
     (backend_config_ok (x64_backend_config with clos_conf := x) =
      backend_config_ok x64_backend_config))
Proof
  fs [mc_init_ok_def,FUN_EQ_THM,backend_config_ok_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ EVAL_TAC
QED

Definition compiler_instance_def:
  compiler_instance =
    <| init_state := config_to_inc_config info;
       compiler_fun := compile_inc_progs_for_eval x64_config ;
       config_dom := UNIV ;
       config_v := BACKEND_INC_CONFIG_v ;
       decs_dom := decs_allowed ;
       decs_v := LIST_v AST_DEC_v |>
End

Triviality compiler_instance_lemma:
  INJ compiler_instance.config_v 𝕌(:inc_config) 𝕌(:semanticPrimitives$v) ∧
  compiler_instance.init_state = config_to_inc_config info ∧
  compiler_instance.compiler_fun = compile_inc_progs_for_eval x64_config
Proof
  fs [compiler_instance_def]
QED

Theorem info_asm_conf:
  info.lab_conf.asm_conf = x64_config
Proof
  assume_tac $ cj 1 compiler64_compiled
  \\ drule compile_asm_config_eq
  \\ gvs [backendTheory.set_oracle_def]
  \\ strip_tac \\ EVAL_TAC
QED

Theorem set_asm_conf_init_conf:
  set_asm_conf init_conf x64_config = init_conf
Proof
  gvs [init_conf_def,backendTheory.set_asm_conf_def,
       x64_targetTheory.x64_config_def,
       x64_configTheory.x64_backend_config_def,
       backendTheory.config_component_equality]
QED

Theorem backend_config_ok_init_conf:
  backend_config_ok init_conf
Proof
  assume_tac x64_backend_config_ok
  \\ gvs [backendProofTheory.backend_config_ok_def,init_conf_def]
  \\ EVAL_TAC
QED

Theorem mc_init_ok_init_conf:
  mc_init_ok init_conf mc = mc_init_ok x64_backend_config mc
Proof
  simp [mc_init_ok_def,init_conf_def]
QED

val cake_io_events_def = new_specification("cake_io_events_def",["cake_io_events"],
  semantics_compiler64_prog
  |> SRULE [ml_progTheory.prog_syntax_ok_semantics, compiler64_compiled]
  |> Q.INST[‘eval_state_var’|->‘the_EvalDecs (mk_init_eval_state compiler_instance)’]
  |> SIMP_RULE (srw_ss()) [source_evalProofTheory.mk_init_eval_state_def,the_EvalDecs_def]
  |> SIMP_RULE (srw_ss()) [GSYM source_evalProofTheory.mk_init_eval_state_def
                           |> SIMP_RULE (srw_ss()) []]
  |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (cake_sem,cake_output) = cake_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (cake_not_fail,cake_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail cake_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct_eval (cj 1 compiler64_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,
                         GSYM AND_IMP_INTRO,set_asm_conf_init_conf,with_clos_conf_simp]
  |> Q.INST [‘ev’|->‘SOME compiler_instance’]
  |> SIMP_RULE (srw_ss()) [add_eval_state_def,opt_eval_config_wf_def,
                           compiler_instance_lemma,info_asm_conf,mc_init_ok_init_conf]
  |> C MATCH_MP cake_not_fail
  |> C MATCH_MP backend_config_ok_init_conf
  |> REWRITE_RULE[cake_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem cake_compiled_thm =
  CONJ compile_correct_applied cake_output
  |> DISCH_ALL

val _ = print "Checking that no cheats were used in the proofs.\n";
val _ = cake_compiled_thm |> check_thm;

val _ = export_theory();
