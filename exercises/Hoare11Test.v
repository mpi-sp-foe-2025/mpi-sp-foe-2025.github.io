Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Hoare11.

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

From PLF Require Import Hoare11.
Import Check.

Goal True.

idtac "-------------------  hoare_post_true  --------------------".
idtac " ".

idtac "#> hoare_post_true".
idtac "Possible points: 1".
check_type @hoare_post_true (
(forall (P Q : Assertion) (c : com),
 (forall st : state, Q st) -> {{P}} c {{Q}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_post_true.
Goal True.
idtac " ".

idtac "-------------------  hoare_pre_false  --------------------".
idtac " ".

idtac "#> hoare_pre_false".
idtac "Possible points: 1".
check_type @hoare_pre_false (
(forall (P Q : Assertion) (c : com),
 (forall st : state, ~ P st) -> {{P}} c {{Q}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_pre_false.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_examples1  --------------------".
idtac " ".

idtac "#> hoare_asgn_examples1".
idtac "Possible points: 2".
check_type @hoare_asgn_examples1 (
(exists P : Assertion,
   {{P}} X := (ANum 2) * (AId X) {{Aexp_of_aexp (AId X) <= Aexp_of_nat 10}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_examples1.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_examples2  --------------------".
idtac " ".

idtac "#> hoare_asgn_examples2".
idtac "Possible points: 2".
check_type @hoare_asgn_examples2 (
(exists P : Assertion,
   {{P}} X := (ANum 3)
   {{Aexp_of_nat 0 <= Aexp_of_aexp (AId X) /\
     Aexp_of_aexp (AId X) <= Aexp_of_nat 5}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_examples2.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_wrong  --------------------".
idtac " ".

idtac "#> hoare_asgn_wrong".
idtac "Possible points: 2".
check_type @hoare_asgn_wrong (
(exists a : aexp,
   ~
   ({{assert_of_Prop True}} X := a {{Aexp_of_aexp (AId X) = Aexp_of_aexp a}}))).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_wrong.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_fwd  --------------------".
idtac " ".

idtac "#> hoare_asgn_fwd".
idtac "Advanced".
idtac "Possible points: 3".
check_type @hoare_asgn_fwd (
(forall (m : nat) (a : aexp) (P : state -> Prop),
 {{fun st : state => P st /\ st X = m}} X := a
 {{fun st : state =>
   P (@Maps.t_update nat st X m) /\
   st X = aeval (@Maps.t_update nat st X m) a}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_fwd.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_fwd_exists  --------------------".
idtac " ".

idtac "#> hoare_asgn_fwd_exists".
idtac "Advanced".
idtac "Possible points: 2".
check_type @hoare_asgn_fwd_exists (
(forall (a : aexp) (P : state -> Prop),
 {{fun st : state => P st}} X := a
 {{fun st : state =>
   exists m : nat,
     P (@Maps.t_update nat st X m) /\
     st X = aeval (@Maps.t_update nat st X m) a}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_fwd_exists.
Goal True.
idtac " ".

idtac "-------------------  assertion_sub_example1  --------------------".
idtac " ".

idtac "#> assertion_sub_example1".
idtac "Possible points: 1".
check_type @assertion_sub_example1 (
({{assert_of_Prop True}} X := (ANum 1)
 {{Aexp_of_aexp (AId X) = Aexp_of_nat 1}})).
idtac "Assumptions:".
Abort.
Print Assumptions assertion_sub_example1.
Goal True.
idtac " ".

idtac "-------------------  hoare_add_consecutively  --------------------".
idtac " ".

idtac "#> hoare_add_consecutively".
idtac "Possible points: 2".
check_type @hoare_add_consecutively (
(forall m n : nat,
 {{fun st : state => st X = m /\ st Y = n /\ st Z = 0}} 
 Z := (AId Z) + (AId X); Z := (AId Z) + (AId Y)
 {{fun st : state => st Z = m + n}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_add_consecutively.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 11".
idtac "Max points - advanced: 16".
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
idtac "---------- hoare_post_true ---------".
Print Assumptions hoare_post_true.
idtac "---------- hoare_pre_false ---------".
Print Assumptions hoare_pre_false.
idtac "---------- hoare_asgn_examples1 ---------".
Print Assumptions hoare_asgn_examples1.
idtac "---------- hoare_asgn_examples2 ---------".
Print Assumptions hoare_asgn_examples2.
idtac "---------- hoare_asgn_wrong ---------".
Print Assumptions hoare_asgn_wrong.
idtac "---------- assertion_sub_example1 ---------".
Print Assumptions assertion_sub_example1.
idtac "---------- hoare_add_consecutively ---------".
Print Assumptions hoare_add_consecutively.
idtac "".
idtac "********** Advanced **********".
idtac "---------- hoare_asgn_fwd ---------".
Print Assumptions hoare_asgn_fwd.
idtac "---------- hoare_asgn_fwd_exists ---------".
Print Assumptions hoare_asgn_fwd_exists.
Abort.

(* 2025-04-23 12:09 *)
