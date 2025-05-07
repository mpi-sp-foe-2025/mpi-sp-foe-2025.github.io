Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Hoare21.

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

From PLF Require Import Hoare21.
Import Check.

Goal True.

idtac "-------------------  if_minus_plus_reloaded  --------------------".
idtac " ".

idtac "#> Manually graded: if_minus_plus_reloaded".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_if_minus_plus_reloaded.
idtac " ".

idtac "-------------------  slow_assignment  --------------------".
idtac " ".

idtac "#> Manually graded: slow_assignment".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_slow_assignment.
idtac " ".

idtac "-------------------  division_example  --------------------".
idtac " ".

idtac "#> division_example".
idtac "Possible points: 2".
check_type @division_example (
(forall m : nat,
 {{Hoare11.Aexp_of_aexp (AId X) = Hoare11.Aexp_of_nat m}} 
 Y := (ANum 0);
 while (AId Z) <= (AId X) do X := (AId X) - (AId Z); Y := (AId Y) + (ANum 1)
 end
 {{Hoare11.Aexp_of_aexp (AId Z) * Hoare11.Aexp_of_aexp (AId Y) +
   Hoare11.Aexp_of_aexp (AId X) = Hoare11.Aexp_of_nat m /\
   Hoare11.Aexp_of_aexp (AId X) < Hoare11.Aexp_of_aexp (AId Z)}})).
idtac "Assumptions:".
Abort.
Print Assumptions division_example.
Goal True.
idtac " ".

idtac "-------------------  slow_assignment_formal  --------------------".
idtac " ".

idtac "#> slow_assignment_formal".
idtac "Possible points: 2".
check_type @slow_assignment_formal (
(forall m : nat,
 {{Hoare11.Aexp_of_aexp (AId X) = Hoare11.Aexp_of_nat m}} 
 Y := (ANum 0);
 while (AId X) <> (ANum 0)
 do X := (AId X) - (ANum 1); Y := (AId Y) + (ANum 1) end
 {{Hoare11.Aexp_of_aexp (AId Y) = Hoare11.Aexp_of_nat m}})).
idtac "Assumptions:".
Abort.
Print Assumptions slow_assignment_formal.
Goal True.
idtac " ".

idtac "-------------------  parity  --------------------".
idtac " ".

idtac "#> parity".
idtac "Possible points: 3".
check_type @parity ((nat -> nat)).
idtac "Assumptions:".
Abort.
Print Assumptions parity.
Goal True.
idtac " ".

idtac "-------------------  parity_decorated_formal  --------------------".
idtac " ".

idtac "#> Manually graded: parity_decorated_formal".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_parity_decorated_formal.
idtac " ".

idtac " ".

idtac "Max points - standard: 14".
idtac "Max points - advanced: 14".
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
idtac "---------- if_minus_plus_reloaded ---------".
idtac "MANUAL".
idtac "---------- slow_assignment ---------".
idtac "MANUAL".
idtac "---------- division_example ---------".
Print Assumptions division_example.
idtac "---------- slow_assignment_formal ---------".
Print Assumptions slow_assignment_formal.
idtac "---------- parity ---------".
Print Assumptions parity.
idtac "---------- parity_decorated_formal ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2025-05-07 14:00 *)
