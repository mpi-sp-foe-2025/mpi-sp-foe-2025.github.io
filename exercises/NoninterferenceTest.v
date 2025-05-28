Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Noninterference.

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

From PLF Require Import Noninterference.
Import Check.

Goal True.

idtac "-------------------  prove_or_disprove_obvious_f1  --------------------".
idtac " ".

idtac "#> prove_or_disprove_obvious_f1".
idtac "Possible points: 1".
check_type @prove_or_disprove_obvious_f1 (
(@noninterferent nat nat nat nat obvious_f1 \/
 ~ @noninterferent nat nat nat nat obvious_f1)).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_obvious_f1.
Goal True.
idtac " ".

idtac "-------------------  prove_or_disprove_obvious_f2  --------------------".
idtac " ".

idtac "#> prove_or_disprove_obvious_f2".
idtac "Possible points: 1".
check_type @prove_or_disprove_obvious_f2 (
(@noninterferent nat nat nat nat obvious_f2 \/
 ~ @noninterferent nat nat nat nat obvious_f2)).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_obvious_f2.
Goal True.
idtac " ".

idtac "-------------------  prove_or_disprove_less_obvious_f4  --------------------".
idtac " ".

idtac "#> prove_or_disprove_less_obvious_f4".
idtac "Possible points: 2".
check_type @prove_or_disprove_less_obvious_f4 (
(@noninterferent nat nat nat nat less_obvious_f4 \/
 ~ @noninterferent nat nat nat nat less_obvious_f4)).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_less_obvious_f4.
Goal True.
idtac " ".

idtac "-------------------  prove_or_disprove_less_obvious_f5  --------------------".
idtac " ".

idtac "#> prove_or_disprove_less_obvious_f5".
idtac "Possible points: 2".
check_type @prove_or_disprove_less_obvious_f5 (
(@noninterferent nat nat nat nat less_obvious_f5 \/
 ~ @noninterferent nat nat nat nat less_obvious_f5)).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_less_obvious_f5.
Goal True.
idtac " ".

idtac "-------------------  prove_or_disprove_less_obvious_f6  --------------------".
idtac " ".

idtac "#> prove_or_disprove_less_obvious_f6".
idtac "Possible points: 2".
check_type @prove_or_disprove_less_obvious_f6 (
(@noninterferent nat nat nat nat less_obvious_f6 \/
 ~ @noninterferent nat nat nat nat less_obvious_f6)).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_less_obvious_f6.
Goal True.
idtac " ".

idtac "-------------------  sme_another_insecure_f2  --------------------".
idtac " ".

idtac "#> sme_another_insecure_f2".
idtac "Possible points: 1".
check_type @sme_another_insecure_f2 (
(forall pi si : nat,
 @sme nat nat nat nat 0 another_insecure_f2 pi si = (pi, pi + si))).
idtac "Assumptions:".
Abort.
Print Assumptions sme_another_insecure_f2.
Goal True.
idtac " ".

idtac "-------------------  sme_another_insecure_f3  --------------------".
idtac " ".

idtac "#> sme_another_insecure_f3".
idtac "Possible points: 2".
check_type @sme_another_insecure_f3 (
(forall pi si : nat,
 @sme nat nat nat nat 0 another_insecure_f3 pi si = (pi, pi + si))).
idtac "Assumptions:".
Abort.
Print Assumptions sme_another_insecure_f3.
Goal True.
idtac " ".

idtac "-------------------  noninterferent_secure_com_exercise  --------------------".
idtac " ".

idtac "#> noninterferent_secure_com_exercise".
idtac "Possible points: 2".
check_type @noninterferent_secure_com_exercise (
(noninterferent_no_while xpub secure_com_exercise)).
idtac "Assumptions:".
Abort.
Print Assumptions noninterferent_secure_com_exercise.
Goal True.
idtac " ".

idtac "-------------------  interferent_insecure_com_explicit  --------------------".
idtac " ".

idtac "#> interferent_insecure_com_explicit".
idtac "Possible points: 2".
check_type @interferent_insecure_com_explicit (
(~ noninterferent_no_while xpub insecure_com_explicit)).
idtac "Assumptions:".
Abort.
Print Assumptions interferent_insecure_com_explicit.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 15".
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
idtac "---------- prove_or_disprove_obvious_f1 ---------".
Print Assumptions prove_or_disprove_obvious_f1.
idtac "---------- prove_or_disprove_obvious_f2 ---------".
Print Assumptions prove_or_disprove_obvious_f2.
idtac "---------- prove_or_disprove_less_obvious_f4 ---------".
Print Assumptions prove_or_disprove_less_obvious_f4.
idtac "---------- prove_or_disprove_less_obvious_f5 ---------".
Print Assumptions prove_or_disprove_less_obvious_f5.
idtac "---------- prove_or_disprove_less_obvious_f6 ---------".
Print Assumptions prove_or_disprove_less_obvious_f6.
idtac "---------- sme_another_insecure_f2 ---------".
Print Assumptions sme_another_insecure_f2.
idtac "---------- sme_another_insecure_f3 ---------".
Print Assumptions sme_another_insecure_f3.
idtac "---------- noninterferent_secure_com_exercise ---------".
Print Assumptions noninterferent_secure_com_exercise.
idtac "---------- interferent_insecure_com_explicit ---------".
Print Assumptions interferent_insecure_com_explicit.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2025-05-28 23:56 *)
