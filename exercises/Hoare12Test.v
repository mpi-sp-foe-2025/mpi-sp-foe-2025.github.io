Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Hoare12.

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

From PLF Require Import Hoare12.
Import Check.

Goal True.

idtac "-------------------  hoare_asgn_examples_2  --------------------".
idtac " ".

idtac "#> assertion_sub_ex2'".
idtac "Possible points: 1".
check_type @assertion_sub_ex2' (
({{Hoare11.Aexp_of_nat 0 <= Hoare11.Aexp_of_nat 3 /\
   Hoare11.Aexp_of_nat 3 <= Hoare11.Aexp_of_nat 5}} 
 X := (ANum 3)
 {{Hoare11.Aexp_of_nat 0 <= Hoare11.Aexp_of_aexp (AId X) /\
   Hoare11.Aexp_of_aexp (AId X) <= Hoare11.Aexp_of_nat 5}})).
idtac "Assumptions:".
Abort.
Print Assumptions assertion_sub_ex2'.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_example4  --------------------".
idtac " ".

idtac "#> hoare_asgn_example4".
idtac "Possible points: 2".
check_type @hoare_asgn_example4 (
({{Hoare11.assert_of_Prop True}} X := (ANum 1); Y := (ANum 2)
 {{Hoare11.Aexp_of_aexp (AId X) = Hoare11.Aexp_of_nat 1 /\
   Hoare11.Aexp_of_aexp (AId Y) = Hoare11.Aexp_of_nat 2}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_example4.
Goal True.
idtac " ".

idtac "-------------------  if_minus_plus  --------------------".
idtac " ".

idtac "#> if_minus_plus".
idtac "Possible points: 2".
check_type @if_minus_plus (
({{Hoare11.assert_of_Prop True}} if (AId X) <= (AId Y)
                                 then Z := (AId Y) - (AId X)
                                 else Y := (AId X) + (AId Z) end
 {{Hoare11.Aexp_of_aexp (AId Y) =
   Hoare11.Aexp_of_aexp (AId X) + Hoare11.Aexp_of_aexp (AId Z)}})).
idtac "Assumptions:".
Abort.
Print Assumptions if_minus_plus.
Goal True.
idtac " ".

idtac "-------------------  if1_ceval  --------------------".
idtac " ".

idtac "#> If1.if1true_test".
idtac "Possible points: 1".
check_type @If1.if1true_test (
(If1.ceval (If1.CIf1 <{ (AId X) = (ANum 0) }> (If1.CAsgn X (ANum 1)))
   empty_st (X !-> 1))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.if1true_test.
Goal True.
idtac " ".

idtac "#> If1.if1false_test".
idtac "Possible points: 1".
check_type @If1.if1false_test (
(If1.ceval (If1.CIf1 <{ (AId X) = (ANum 0) }> (If1.CAsgn X (ANum 1)))
   (X !-> 2) (X !-> 2))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.if1false_test.
Goal True.
idtac " ".

idtac "-------------------  hoare_if1  --------------------".
idtac " ".

idtac "#> Manually graded: If1.hoare_if1".
idtac "Possible points: 2".
print_manual_grade If1.manual_grade_for_hoare_if1.
idtac " ".

idtac "-------------------  hoare_if1_good  --------------------".
idtac " ".

idtac "#> If1.hoare_if1_good".
idtac "Possible points: 2".
check_type @If1.hoare_if1_good (
(If1.valid_hoare_triple
   (Hoare11.Aexp_of_aexp (AId X) + Hoare11.Aexp_of_aexp (AId Y) =
    Hoare11.Aexp_of_aexp (AId Z))
   (If1.CIf1 <{ (AId Y) <> (ANum 0) }> (If1.CAsgn X <{ (AId X) + (AId Y) }>))
   (Hoare11.Aexp_of_aexp (AId X) = Hoare11.Aexp_of_aexp (AId Z)))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.hoare_if1_good.
Goal True.
idtac " ".

idtac "-------------------  hoare_add_loop  --------------------".
idtac " ".

idtac "#> hoare_add_loop".
idtac "Possible points: 3".
check_type @hoare_add_loop (
(forall m n : nat,
 {{Hoare11.Aexp_of_aexp (AId X) = Hoare11.Aexp_of_nat m /\
   Hoare11.Aexp_of_aexp (AId Y) = Hoare11.Aexp_of_nat n}} 
 while (AId Y) > (ANum 0) do X := (AId X) + (ANum 1); Y := (AId Y) - (ANum 1)
 end
 {{Hoare11.Aexp_of_aexp (AId X) =
   Hoare11.Aexp_of_nat m + Hoare11.Aexp_of_nat n}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_add_loop.
Goal True.
idtac " ".

idtac "-------------------  hoare_repeat  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_repeat".
idtac "Advanced".
idtac "Possible points: 6".
print_manual_grade manual_grade_for_hoare_repeat.
idtac " ".

idtac " ".

idtac "Max points - standard: 14".
idtac "Max points - advanced: 20".
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
idtac "---------- assertion_sub_ex2' ---------".
Print Assumptions assertion_sub_ex2'.
idtac "---------- hoare_asgn_example4 ---------".
Print Assumptions hoare_asgn_example4.
idtac "---------- if_minus_plus ---------".
Print Assumptions if_minus_plus.
idtac "---------- If1.if1true_test ---------".
Print Assumptions If1.if1true_test.
idtac "---------- If1.if1false_test ---------".
Print Assumptions If1.if1false_test.
idtac "---------- hoare_if1 ---------".
idtac "MANUAL".
idtac "---------- If1.hoare_if1_good ---------".
Print Assumptions If1.hoare_if1_good.
idtac "---------- hoare_add_loop ---------".
Print Assumptions hoare_add_loop.
idtac "".
idtac "********** Advanced **********".
idtac "---------- hoare_repeat ---------".
idtac "MANUAL".
Abort.

(* 2025-04-30 10:21 *)
