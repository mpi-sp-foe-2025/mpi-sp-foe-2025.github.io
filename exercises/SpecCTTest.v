Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import SpecCT.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From PLF Require Import SpecCT.
Import Check.

Goal True.

idtac "-------------------  cct_insecure_prog'_is_not_cct_secure  --------------------".
idtac " ".

idtac "#> cct_insecure_prog'_is_not_cct_secure".
idtac "Possible points: 2".
check_type @cct_insecure_prog'_is_not_cct_secure (
(~ cct_secure XYZpub APpub cct_insecure_prog')).
idtac "Assumptions:".
Abort.
Print Assumptions cct_insecure_prog'_is_not_cct_secure.
Goal True.
idtac " ".

idtac "-------------------  label_of_exp  --------------------".
idtac " ".

idtac "#> label_of_exp".
idtac "Possible points: 1".
check_type @label_of_exp ((pub_vars -> exp -> label)).
idtac "Assumptions:".
Abort.
Print Assumptions label_of_exp.
Goal True.
idtac " ".

idtac "-------------------  label_of_exp_sound  --------------------".
idtac " ".

idtac "#> label_of_exp_sound".
idtac "Possible points: 1".
check_type @label_of_exp_sound (
(forall (P : pub_vars) (e : exp), P |- e \in label_of_exp P e)).
idtac "Assumptions:".
Abort.
Print Assumptions label_of_exp_sound.
Goal True.
idtac " ".

idtac "-------------------  label_of_exp_unique  --------------------".
idtac " ".

idtac "#> label_of_exp_unique".
idtac "Possible points: 1".
check_type @label_of_exp_unique (
(forall (P : pub_vars) (e : exp) (l : label),
 P |- e \in l -> l = label_of_exp P e)).
idtac "Assumptions:".
Abort.
Print Assumptions label_of_exp_unique.
Goal True.
idtac " ".

idtac "-------------------  cct_typechecker  --------------------".
idtac " ".

idtac "#> cct_typechecker".
idtac "Possible points: 2".
check_type @cct_typechecker ((pub_vars -> pub_vars -> com -> bool)).
idtac "Assumptions:".
Abort.
Print Assumptions cct_typechecker.
Goal True.
idtac " ".

idtac "-------------------  cct_typechecker_sound  --------------------".
idtac " ".

idtac "#> cct_typechecker_sound".
idtac "Possible points: 2".
check_type @cct_typechecker_sound (
(forall (P PA : pub_vars) (c : com),
 cct_typechecker P PA c = true -> P;; PA |-ct- c)).
idtac "Assumptions:".
Abort.
Print Assumptions cct_typechecker_sound.
Goal True.
idtac " ".

idtac "-------------------  cct_typechecker_complete  --------------------".
idtac " ".

idtac "#> cct_typechecker_complete".
idtac "Possible points: 2".
check_type @cct_typechecker_complete (
(forall (P PA : pub_vars) (c : com),
 cct_typechecker P PA c = false -> ~ P;; PA |-ct- c)).
idtac "Assumptions:".
Abort.
Print Assumptions cct_typechecker_complete.
Goal True.
idtac " ".

idtac "-------------------  cct_insecure_prog_ill_typed  --------------------".
idtac " ".

idtac "#> cct_insecure_prog_ill_typed".
idtac "Possible points: 1".
check_type @cct_insecure_prog_ill_typed ((~ XYZpub;; APpub |-ct- cct_insecure_prog)).
idtac "Assumptions:".
Abort.
Print Assumptions cct_insecure_prog_ill_typed.
Goal True.
idtac " ".

idtac "-------------------  cct_insecure_prog'_ill_typed  --------------------".
idtac " ".

idtac "#> cct_insecure_prog'_ill_typed".
idtac "Possible points: 1".
check_type @cct_insecure_prog'_ill_typed ((~ XYZpub;; APpub |-ct- cct_insecure_prog')).
idtac "Assumptions:".
Abort.
Print Assumptions cct_insecure_prog'_ill_typed.
Goal True.
idtac " ".

idtac "-------------------  cct_well_typed_div  --------------------".
idtac " ".

idtac "#> Manually graded: Div.cct_well_typed_div".
idtac "Possible points: 1".
print_manual_grade Div.manual_grade_for_cct_well_typed_div.
idtac " ".

idtac "-------------------  cct_well_typed_div_noninterferent  --------------------".
idtac " ".

idtac "#> Div.cct_well_typed_div_noninterferent".
idtac "Possible points: 2".
check_type @Div.cct_well_typed_div_noninterferent (
(forall (P : pub_vars) (PA : pub_arrs) (c : Div.com)
   (st1 st2 : Maps.total_map nat) (ast1 ast2 : Maps.total_map (list nat))
   (st1' st2' : state) (ast1' ast2' : astate) (os1 os2 : Div.obs),
 Div.cct_well_typed P PA c ->
 @pub_equiv P nat st1 st2 ->
 @pub_equiv PA (list nat) ast1 ast2 ->
 Div.cteval c st1 ast1 st1' ast1' os1 ->
 Div.cteval c st2 ast2 st2' ast2' os2 ->
 @pub_equiv P nat st1' st2' /\ @pub_equiv PA (list nat) ast1' ast2')).
idtac "Assumptions:".
Abort.
Print Assumptions Div.cct_well_typed_div_noninterferent.
Goal True.
idtac " ".

idtac "-------------------  cct_well_typed_div_secure  --------------------".
idtac " ".

idtac "#> Div.cct_well_typed_div_secure".
idtac "Possible points: 2".
check_type @Div.cct_well_typed_div_secure (
(forall (P : pub_vars) (PA : pub_arrs) (c : Div.com),
 Div.cct_well_typed P PA c -> Div.cct_secure P PA c)).
idtac "Assumptions:".
Abort.
Print Assumptions Div.cct_well_typed_div_secure.
Goal True.
idtac " ".

idtac "-------------------  speculation_bit_monotonic  --------------------".
idtac " ".

idtac "#> speculation_bit_monotonic".
idtac "Possible points: 1".
check_type @speculation_bit_monotonic (
(forall (c : com) (s : state) (a : astate) (b : bool) 
   (ds : dirs) (s' : state) (a' : astate) (b' : bool) 
   (os : obs),
 <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )> -> b = true -> b' = true)).
idtac "Assumptions:".
Abort.
Print Assumptions speculation_bit_monotonic.
Goal True.
idtac " ".

idtac "-------------------  ct_well_typed_seq_spec_eval_ct_secure  --------------------".
idtac " ".

idtac "#> ct_well_typed_seq_spec_eval_ct_secure".
idtac "Possible points: 1".
check_type @ct_well_typed_seq_spec_eval_ct_secure (
(forall (P : pub_vars) (PA : pub_arrs) (c : com)
   (st1 st2 : Maps.total_map nat) (ast1 ast2 : Maps.total_map (list nat))
   (st1' st2' : state) (ast1' ast2' : astate) (os1 os2 : obs),
 P;; PA |-ct- c ->
 @pub_equiv P nat st1 st2 ->
 @pub_equiv PA (list nat) ast1 ast2 ->
 seq_spec_eval c st1 ast1 st1' ast1' os1 ->
 seq_spec_eval c st2 ast2 st2' ast2' os2 -> os1 = os2)).
idtac "Assumptions:".
Abort.
Print Assumptions ct_well_typed_seq_spec_eval_ct_secure.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 20".
idtac "Max points - advanced: 20".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- cct_insecure_prog'_is_not_cct_secure ---------".
Print Assumptions cct_insecure_prog'_is_not_cct_secure.
idtac "---------- label_of_exp ---------".
Print Assumptions label_of_exp.
idtac "---------- label_of_exp_sound ---------".
Print Assumptions label_of_exp_sound.
idtac "---------- label_of_exp_unique ---------".
Print Assumptions label_of_exp_unique.
idtac "---------- cct_typechecker ---------".
Print Assumptions cct_typechecker.
idtac "---------- cct_typechecker_sound ---------".
Print Assumptions cct_typechecker_sound.
idtac "---------- cct_typechecker_complete ---------".
Print Assumptions cct_typechecker_complete.
idtac "---------- cct_insecure_prog_ill_typed ---------".
Print Assumptions cct_insecure_prog_ill_typed.
idtac "---------- cct_insecure_prog'_ill_typed ---------".
Print Assumptions cct_insecure_prog'_ill_typed.
idtac "---------- cct_well_typed_div ---------".
idtac "MANUAL".
idtac "---------- Div.cct_well_typed_div_noninterferent ---------".
Print Assumptions Div.cct_well_typed_div_noninterferent.
idtac "---------- Div.cct_well_typed_div_secure ---------".
Print Assumptions Div.cct_well_typed_div_secure.
idtac "---------- speculation_bit_monotonic ---------".
Print Assumptions speculation_bit_monotonic.
idtac "---------- ct_well_typed_seq_spec_eval_ct_secure ---------".
Print Assumptions ct_well_typed_seq_spec_eval_ct_secure.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2025-07-16 18:56 *)
