(*Generated by Lem from bigStep.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasives_extraTheory libTheory astTheory semanticPrimitivesTheory smallStepTheory;

val _ = numLib.prefer_num();



val _ = new_theory "bigStep"

(*open import Pervasives_extra*)
(*open import Lib*)
(*open import Ast*) 
(*open import SemanticPrimitives*)

(* To get the definition of expression divergence to use in defining definition
 * divergence *)
(*open import SmallStep*)

(* ------------------------ Big step semantics -------------------------- *)

(* If the first argument is true, the big step semantics counts down how many
   functions applications have happened, and raises an exception when the counter
   runs out. *)

val _ = type_abbrev((*  'a *) "count_store" , ``: num # 'a store``);

val _ = Hol_reln ` (! ck env l s.
T
==>
evaluate ck env s (Lit l) (s, Rval (Litv l)))

/\ (! ck env e s1 s2 v.
(evaluate ck s1 env e (s2, Rval v))
==>
evaluate ck s1 env (Raise e) (s2, Rerr (Rraise v)))

/\ (! ck env e s1 s2 err.
(evaluate ck s1 env e (s2, Rerr err))
==>
evaluate ck s1 env (Raise e) (s2, Rerr err))

/\ (! ck s1 s2 env e v pes.
(evaluate ck s1 env e (s2, Rval v))
==>
evaluate ck s1 env (Handle e pes) (s2, Rval v))

/\ (! ck s1 s2 env e pes v bv.
(evaluate ck env s1 e (s2, Rerr (Rraise v)) /\
evaluate_match ck env s2 v pes v bv)
==>
evaluate ck env s1 (Handle e pes) bv)

/\ (! ck s1 s2 env e pes err.
(evaluate ck env s1 e (s2, Rerr err) /\
((err = Rtimeout_error) \/ (err = Rtype_error)))
==>
evaluate ck env s1 (Handle e pes) (s2, Rerr err))

/\ (! ck env cn es vs s s' v.
(do_con_check (all_env_to_cenv env) cn (LENGTH es) /\
((build_conv (all_env_to_cenv env) cn vs = SOME v) /\
evaluate_list ck env s es (s', Rval vs)))
==>
evaluate ck env s (Con cn es) (s', Rval v))

/\ (! ck env cn es s.
(~ (do_con_check (all_env_to_cenv env) cn (LENGTH es)))
==>
evaluate ck env s (Con cn es) (s, Rerr Rtype_error))

/\ (! ck env cn es err s s'.
(do_con_check (all_env_to_cenv env) cn (LENGTH es) /\
evaluate_list ck env s es (s', Rerr err))
==>
evaluate ck env s (Con cn es) (s', Rerr err))

/\ (! ck env n v s.
(lookup_var_id n env = SOME v)
==>
evaluate ck env s (Var n) (s, Rval v))

/\ (! ck env n s.
(lookup_var_id n env = NONE)
==>
evaluate ck env s (Var n) (s, Rerr Rtype_error))

/\ (! ck env n e s.
T
==>
evaluate ck env s (Fun n e) (s, Rval (Closure env n e)))

/\ (! ck env es vs env' e bv s1 s2 count.
(evaluate_list ck env s1 es ((count,s2), Rval vs) /\
((do_opapp vs = SOME (env', e)) /\
((ck ==> ~ (count =( 0))) /\
evaluate ck env' ((if ck then count -  1 else count),s2) e bv)))
==>
evaluate ck env s1 (App Opapp es) bv)

/\ (! ck env es vs env' e s1 s2 count.
(evaluate_list ck env s1 es ((count,s2), Rval vs) /\
((do_opapp vs = SOME (env', e)) /\
((count = 0) /\
ck)))
==>
evaluate ck env s1 (App Opapp es) (( 0,s2), Rerr Rtimeout_error))

/\ (! ck env es vs s1 s2.
(evaluate_list ck env s1 es (s2, Rval vs) /\
(do_opapp vs = NONE))
==>
evaluate ck env s1 (App Opapp es) (s2, Rerr Rtype_error))

/\ (! ck env op es vs res s1 s2 s3 count.
(evaluate_list ck env s1 es ((count,s2), Rval vs) /\
((do_app s2 op vs = SOME (s3, res)) /\
(op <> Opapp)))
==>
evaluate ck env s1 (App op es) ((count,s3), res))

/\ (! ck env op es vs s1 s2 count.
(evaluate_list ck env s1 es ((count,s2), Rval vs) /\
((do_app s2 op vs = NONE) /\
(op <> Opapp)))
==>
evaluate ck env s1 (App op es) ((count,s2), Rerr Rtype_error))

/\ (! ck env op es err s1 s2.
(evaluate_list ck env s1 es (s2, Rerr err))
==>
evaluate ck env s1 (App op es) (s2, Rerr err))

/\ (! ck env op e1 e2 v e' bv s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
((do_log op v e2 = SOME e') /\
evaluate ck env s2 e' bv))
==>
evaluate ck env s1 (Log op e1 e2) bv)

/\ (! ck env op e1 e2 v s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
(do_log op v e2 = NONE))
==>
evaluate ck env s1 (Log op e1 e2) (s2, Rerr Rtype_error))

/\ (! ck env op e1 e2 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (Log op e1 e2) (s', Rerr err))

/\ (! ck env e1 e2 e3 v e' bv s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
((do_if v e2 e3 = SOME e') /\
evaluate ck env s2 e' bv))
==>
evaluate ck env s1 (If e1 e2 e3) bv)

/\ (! ck env e1 e2 e3 v s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
(do_if v e2 e3 = NONE))
==>
evaluate ck env s1 (If e1 e2 e3) (s2, Rerr Rtype_error))

/\ (! ck env e1 e2 e3 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (If e1 e2 e3) (s', Rerr err))

/\ (! ck env e pes v bv s1 s2.
(evaluate ck env s1 e (s2, Rval v) /\
evaluate_match ck env s2 v pes (Conv (SOME ("Bind", TypeExn (Short "Bind"))) []) bv)
==>
evaluate ck env s1 (Mat e pes) bv)

/\ (! ck env e pes err s s'.
(evaluate ck env s e (s', Rerr err))
==>
evaluate ck env s (Mat e pes) (s', Rerr err))

/\ (! ck menv cenv env n e1 e2 v bv s1 s2.
(evaluate ck (menv,cenv,env) s1 e1 (s2, Rval v) /\
evaluate ck (menv,cenv,opt_bind n v env) s2 e2 bv)
==>
evaluate ck (menv,cenv,env) s1 (Let n e1 e2) bv)

/\ (! ck env n e1 e2 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (Let n e1 e2) (s', Rerr err))

/\ (! ck menv cenv env funs e bv s.
(ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) /\
evaluate ck (menv,cenv,build_rec_env funs (menv,cenv,env) env) s e bv)
==>
evaluate ck (menv,cenv,env) s (Letrec funs e) bv)

/\ (! ck env funs e s.
(~ (ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs)))
==>
evaluate ck env s (Letrec funs e) (s, Rerr Rtype_error))

/\ (! ck env s.
T
==>
evaluate_list ck env s [] (s, Rval []))

/\ (! ck env e es v vs s1 s2 s3.
(evaluate ck env s1 e (s2, Rval v) /\
evaluate_list ck env s2 es (s3, Rval vs))
==>
evaluate_list ck env s1 (e::es) (s3, Rval (v::vs)))

/\ (! ck env e es err s s'.
(evaluate ck env s e (s', Rerr err))
==>
evaluate_list ck env s (e::es) (s', Rerr err))

/\ (! ck env e es v err s1 s2 s3.
(evaluate ck env s1 e (s2, Rval v) /\
evaluate_list ck env s2 es (s3, Rerr err))
==>
evaluate_list ck env s1 (e::es) (s3, Rerr err))

/\ (! ck env v err_v s.
T
==>
evaluate_match ck env s v [] err_v (s, Rerr (Rraise err_v)))

/\ (! ck menv cenv env env' v p pes e bv err_v s count.
(ALL_DISTINCT (pat_bindings p []) /\
((pmatch cenv s p v env = Match env') /\
evaluate ck (menv,cenv,env') (count,s) e bv))
==>
evaluate_match ck (menv,cenv,env) (count,s) v ((p,e)::pes) err_v bv)

/\ (! ck menv cenv env v p e pes bv s count err_v.
(ALL_DISTINCT (pat_bindings p []) /\
((pmatch cenv s p v env = No_match) /\
evaluate_match ck (menv,cenv,env) (count,s) v pes err_v bv))
==>
evaluate_match ck (menv,cenv,env) (count,s) v ((p,e)::pes) err_v bv)

/\ (! ck menv cenv env v p e pes s count err_v.
(pmatch cenv s p v env = Match_type_error)
==>
evaluate_match ck (menv,cenv,env) (count,s) v ((p,e)::pes) err_v ((count,s), Rerr Rtype_error))

/\ (! ck env v p e pes s err_v.
(~ (ALL_DISTINCT (pat_bindings p [])))
==>
evaluate_match ck env s v ((p,e)::pes) err_v (s, Rerr Rtype_error))`;

(* The set tid_or_exn part of the state tracks all of the types and exceptions
 * that have been declared *)
val _ = Hol_reln ` (! ck mn env p e v env' s1 s2 count tdecs.
(evaluate ck env s1 e ((count,s2), Rval v) /\
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch (all_env_to_cenv env) s2 p v emp = Match env')))
==>
evaluate_dec ck mn env (s1,tdecs) (Dlet p e) (((count,s2),tdecs), Rval (emp, env')))

/\ (! ck mn env p e v s1 s2 count tdecs.
(evaluate ck env s1 e ((count,s2), Rval v) /\
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch (all_env_to_cenv env) s2 p v emp = No_match)))
==>
evaluate_dec ck mn env (s1,tdecs) (Dlet p e) (((count,s2), tdecs), Rerr (Rraise (Conv (SOME ("Bind", TypeExn (Short "Bind"))) []))))

/\ (! ck mn env p e v s1 s2 count tdecs.
(evaluate ck env s1 e ((count,s2), Rval v) /\
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch (all_env_to_cenv env) s2 p v emp = Match_type_error)))
==>
evaluate_dec ck mn env (s1,tdecs) (Dlet p e) (((count,s2),tdecs), Rerr Rtype_error))

/\ (! ck mn env p e s.
(~ (ALL_DISTINCT (pat_bindings p [])))
==>
evaluate_dec ck mn env s (Dlet p e) (s, Rerr Rtype_error))

/\ (! ck mn env p e err s s' tdecs.
(evaluate ck env s e (s', Rerr err) /\
ALL_DISTINCT (pat_bindings p []))
==>
evaluate_dec ck mn env (s,tdecs) (Dlet p e) ((s',tdecs), Rerr err))

/\ (! ck mn env funs s.
(ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs))
==>
evaluate_dec ck mn env s (Dletrec funs) (s, Rval (emp, build_rec_env funs env emp)))

/\ (! ck mn env funs s.
(~ (ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs)))
==>
evaluate_dec ck mn env s (Dletrec funs) (s, Rerr Rtype_error))

/\ (! ck mn env tds s tdecs new_tdecs.
(check_dup_ctors tds /\
((new_tdecs = type_defs_to_new_tdecs mn tds) /\
(DISJOINT new_tdecs tdecs /\
ALL_DISTINCT (MAP (\ (tvs,tn,ctors) .  tn) tds))))
==>
evaluate_dec ck mn env (s,tdecs) (Dtype tds) ((s,(new_tdecs UNION tdecs)), Rval (build_tdefs mn tds, emp)))

/\ (! ck mn env tds s tdecs.
(~ (check_dup_ctors tds) \/
(~ (DISJOINT (type_defs_to_new_tdecs mn tds) tdecs) \/
~ (ALL_DISTINCT (MAP (\ (tvs,tn,ctors) .  tn) tds))))
==>
evaluate_dec ck mn env (s,tdecs) (Dtype tds) ((s,tdecs), Rerr Rtype_error))

/\ (! ck mn env cn ts s tdecs.
(~ (TypeExn (mk_id mn cn) IN tdecs))
==>
evaluate_dec ck mn env (s,tdecs) (Dexn cn ts) ((s, ({TypeExn (mk_id mn cn)} UNION tdecs)), Rval (bind cn (LENGTH ts, TypeExn (mk_id mn cn)) emp, emp)))

/\ (! ck mn env cn ts s tdecs.
(TypeExn (mk_id mn cn) IN tdecs)
==>
evaluate_dec ck mn env (s,tdecs) (Dexn cn ts) ((s,tdecs), Rerr Rtype_error))`;

val _ = Hol_reln ` (! ck mn env s.
T
==>
evaluate_decs ck mn env s [] (s, emp, Rval emp))

/\ (! ck mn s1 s2 env d ds e.
(evaluate_dec ck mn env s1 d (s2, Rerr e))
==>
evaluate_decs ck mn env s1 (d::ds) (s2, emp, Rerr e))

/\ (! ck mn s1 s2 s3 menv cenv env d ds new_tds' new_tds new_env r.
(evaluate_dec ck mn (menv,cenv,env) s1 d (s2, Rval (new_tds,new_env)) /\
evaluate_decs ck mn (menv, merge_envC (emp,new_tds) cenv, merge new_env env) s2 ds (s3, new_tds', r))
==>
evaluate_decs ck mn (menv,cenv,env) s1 (d::ds) (s3, merge new_tds' new_tds, combine_dec_result new_env r))`;

(*val no_dup_types : list dec -> bool*)
val _ = Define `
 (no_dup_types ds =  
(ALL_DISTINCT (FLAT (MAP (\ d .  
        (case d of 
            Dtype tds => MAP (\ (tvs,tn,ctors) .  tn) tds
          | _ => [] ))
     ds))))`;
 

val _ = Hol_reln ` (! ck s1 s2 env d new_tds new_env tdecls1 tdecls2 mdecls.
(evaluate_dec ck NONE env (s1,tdecls1) d ((s2,tdecls2), Rval (new_tds, new_env)))
==>
evaluate_top ck env (s1,tdecls1,mdecls) (Tdec d) ((s2,tdecls2,mdecls), (emp,new_tds), Rval (emp, new_env)))

/\ (! ck s1 s2 env d err tdecls1 tdecls2 mdecls.
(evaluate_dec ck NONE env (s1,tdecls1) d ((s2,tdecls2), Rerr err))
==>
evaluate_top ck env (s1,tdecls1,mdecls) (Tdec d) ((s2,tdecls2,mdecls), (emp,emp), Rerr err))

/\ (! ck s1 s2 env ds mn specs new_tds new_env tdecls1 tdecls2 mdecls.
(~ (mn IN mdecls) /\
(no_dup_types ds /\
evaluate_decs ck (SOME mn) env (s1,tdecls1) ds ((s2,tdecls2), new_tds, Rval new_env)))
==>
evaluate_top ck env (s1,tdecls1,mdecls) (Tmod mn specs ds) ((s2,tdecls2,({mn} UNION mdecls)), ([(mn,new_tds)], emp), Rval ([(mn,new_env)], emp)))

/\ (! ck s1 s2 env ds mn specs new_tds err tdecls1 tdecls2 mdecls.
(~ (mn IN mdecls) /\
(no_dup_types ds /\
evaluate_decs ck (SOME mn) env (s1,tdecls1) ds ((s2,tdecls2), new_tds, Rerr err)))
==>
evaluate_top ck env (s1,tdecls1,mdecls) (Tmod mn specs ds) ((s2,tdecls2,({mn} UNION mdecls)), ([(mn,new_tds)], emp), Rerr err))

/\ (! ck s1 env ds mn specs tdecls1 mdecls.
(~ (no_dup_types ds))
==>
evaluate_top ck env (s1,tdecls1,mdecls) (Tmod mn specs ds) ((s1,tdecls1,mdecls), (emp, emp), Rerr Rtype_error))

/\ (! ck env s mn specs ds tdecls mdecls.
(mn IN mdecls)
==>
evaluate_top ck env (s,tdecls,mdecls) (Tmod mn specs ds) ((s,tdecls,mdecls), (emp,emp), Rerr Rtype_error))`;

val _ = Hol_reln ` (! ck env s.
T
==>
evaluate_prog ck env s [] (s, (emp,emp), Rval (emp, emp)))

/\ (! ck s1 s2 s3 menv cenv env top tops new_mods new_tds new_tds' new_env r.
(evaluate_top ck (menv,cenv,env) s1 top (s2, new_tds, Rval (new_mods,new_env)) /\
evaluate_prog ck (merge new_mods menv, merge_envC new_tds cenv, merge new_env env) s2 tops (s3,new_tds',r))
==>
evaluate_prog ck (menv,cenv,env) s1 (top::tops) (s3, merge_envC new_tds' new_tds, combine_mod_result new_mods new_env r))

/\ (! ck s1 s2 env top tops err new_tds.
(evaluate_top ck env s1 top (s2, new_tds, Rerr err))
==>
evaluate_prog ck env s1 (top::tops) (s2, new_tds, Rerr err))`;

val _ = Define `
 (dec_diverges env (st,tdecs) d =  
((case d of
      Dlet p e => ALL_DISTINCT (pat_bindings p []) /\ e_diverges env st e
    | Dletrec funs => F
    | Dtype tds => F
    | Dexn cn ts => F
  )))`;


val _ = Hol_reln ` (! mn st env d ds.
(dec_diverges env st d)
==>
decs_diverges mn env st (d::ds)) 

/\ (! mn s1 s2 menv cenv env d ds new_tds new_env count tdecs tdecs'.
(evaluate_dec F mn (menv,cenv,env) ((count,s1),tdecs) d (((count,s2),tdecs'), Rval (new_tds, new_env)) /\
decs_diverges mn (menv,merge_envC (emp,new_tds) cenv, merge new_env env) (s2,tdecs') ds)
==>
decs_diverges mn (menv,cenv,env) (s1,tdecs) (d::ds))`;

val _ = Hol_reln ` (! st env d tdecls mdecls.
(dec_diverges env (st,tdecls) d)
==>
top_diverges env (st,tdecls,mdecls) (Tdec d))

/\ (! env s1 ds mn specs tdecls mdecls.
(~ (mn IN mdecls) /\
(no_dup_types ds /\
decs_diverges (SOME mn) env (s1,tdecls) ds))
==>
top_diverges env (s1,tdecls,mdecls) (Tmod mn specs ds))`;

val _ = Hol_reln ` (! st env top tops.
(top_diverges env st top)
==>
prog_diverges env st (top::tops))

/\ (! s1 s2 menv cenv env top tops new_mods new_tds new_env tdecs tdecs' mods mods' count.
(evaluate_top F (menv,cenv,env) ((count,s1),tdecs,mods) top (((count,s2), tdecs',mods'), new_tds, Rval (new_mods, new_env)) /\
prog_diverges (merge new_mods menv, merge_envC new_tds cenv, merge new_env env) (s2,tdecs',mods') tops)
==>
prog_diverges (menv,cenv,env) (s1,tdecs,mods) (top::tops))`;
val _ = export_theory()

