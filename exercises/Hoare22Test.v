Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Hoare22.

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

From PLF Require Import Hoare22.
Import Check.

Goal True.

idtac "-------------------  reverse_incorrect  --------------------".
idtac " ".

idtac "#> reverse_incorrect".
idtac "Possible points: 3".
check_type @reverse_incorrect (
(~
 (forall (d : dcom) (P : Assertion),
  {{P}} (erase d) {{post d}} -> verification_conditions P d))).
idtac "Assumptions:".
Abort.
Print Assumptions reverse_incorrect.
Goal True.
idtac " ".

idtac "-------------------  div_mod_outer_triple_valid  --------------------".
idtac " ".

idtac "#> div_mod_outer_triple_valid".
idtac "Possible points: 2".
check_type @div_mod_outer_triple_valid (
(forall m : nat, outer_triple_valid (div_mod_dec' m))).
idtac "Assumptions:".
Abort.
Print Assumptions div_mod_outer_triple_valid.
Goal True.
idtac " ".

idtac "-------------------  sqrt_dec  --------------------".
idtac " ".

idtac "#> sqrt_dec".
idtac "Possible points: 2".
check_type @sqrt_dec ((nat -> decorated)).
idtac "Assumptions:".
Abort.
Print Assumptions sqrt_dec.
Goal True.
idtac " ".

idtac "-------------------  two_loops  --------------------".
idtac " ".

idtac "#> two_loops".
idtac "Possible points: 3".
check_type @two_loops ((forall a b c : nat, outer_triple_valid (two_loops_dec a b c))).
idtac "Assumptions:".
Abort.
Print Assumptions two_loops.
Goal True.
idtac " ".

idtac "-------------------  minimum_correct  --------------------".
idtac " ".

idtac "#> minimum_correct".
idtac "Possible points: 3".
check_type @minimum_correct ((forall a b : nat, outer_triple_valid (minimum_dec a b))).
idtac "Assumptions:".
Abort.
Print Assumptions minimum_correct.
Goal True.
idtac " ".

idtac "-------------------  wp  --------------------".
idtac " ".

idtac "#> Manually graded: wp".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_wp.
idtac " ".

idtac "-------------------  is_wp_example  --------------------".
idtac " ".

idtac "#> is_wp_example".
idtac "Advanced".
idtac "Possible points: 3".
check_type @is_wp_example (
(is_wp (Hoare11.Aexp_of_aexp (AId Y) <= Hoare11.Aexp_of_nat 4)
   <{ X := (AId Y) + (ANum 1) }>
   (Hoare11.Aexp_of_aexp (AId X) <= Hoare11.Aexp_of_nat 5))).
idtac "Assumptions:".
Abort.
Print Assumptions is_wp_example.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 18".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "CSeq_congruence".
idtac "fold_constants_bexp_sound".
idtac "succ_hastype_nat__hastype_nat".
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
idtac "---------- reverse_incorrect ---------".
Print Assumptions reverse_incorrect.
idtac "---------- div_mod_outer_triple_valid ---------".
Print Assumptions div_mod_outer_triple_valid.
idtac "---------- sqrt_dec ---------".
Print Assumptions sqrt_dec.
idtac "---------- two_loops ---------".
Print Assumptions two_loops.
idtac "---------- minimum_correct ---------".
Print Assumptions minimum_correct.
idtac "---------- wp ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- is_wp_example ---------".
Print Assumptions is_wp_example.
Abort.

(* 2025-05-14 18:55 *)
