(** * RelHoare: Relational Hoare Logic *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import Equiv.
From PLF Require Import Hoare22.
Set Default Goal Selector "!".

Definition FILL_IN_HERE := <{True}>.

(** The [Hoare] chapters have developed a logical framework for
    program verification based on Hoare logic.

      - On the one hand, a Hoare triple [{{P}} c {{Q}}] posits that
        a program [c] satisfies the specification given by precondition
        [P] and postcondition [Q].

      - On the other, the rules of the logic allow us to formally
        prove valid Hoare triples.

    So Hoare logic lets us _state_ and _prove_ formally _properties_
    of programs. These properties relate the initial and final states
    of an execution.

    The ability to reason about programs written in languages of our
    choice is very useful!  But there are many useful properties that
    _can't_ be expressed using Hoare logic.

    In this chapter we begin to explore what are these richer
    properties and how to formally reason about them.

*)

(** The first thing to note is that Hoare triples talk about a
    _single_ execution of a given program, but we're often interested
    in properties that can only be expressed in terms of _multiple_
    executions.

      - A fundamental property of this kind is _determinism_, which
        states that the final state obtained by running a program [c]
        is uniquely determined by the initial state:

st =[ c ]=> st1' -> st =[ c ]=> st2' -> st1' = st2'

        Clearly, we need to run a program twice with the same initial
        state before we can check the equality of the final states.
        So this property cannot be expressed in Hoare logic.

        In the case of Imp, the language itself is deterministic, as
        we proved in the [Imp] chapter of _Logical
        Foundations_, so this always holds in our simple setting.

      - Many common properties follow a similar pattern. For instance,
        we can define that a computation [c] is _monotonic_ with
        respect to the value of some variable [X] as follows:

st1 X <= st2 X -> st1 =[ c ]=> st1' -> st2 =[ c ]=> st2' -> st1' X <= st2' X

        For example, the command [X := X + 42] is monotonic in [X].

      - Finally, as explained in Noninterference.v, confidentiality is
        commonly expressed as a property called noninterference.

        Simply stated, in our setting, we can divide the variables of
        a program as either public or secret. A public observer can
        only inspect the values of public variables, not secret ones.

        A program is noninterferent if, when it runs from a pair of
        states with equal public variables, those public variables
        remain equal in the pair of final states (assuming both runs
        terminate). We formally defined this as follows in
        Noninterference.v:

Definition noninterferent_while pub c := forall s1 s2 s1' s2',
  pub_equiv pub s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv pub s1' s2'.

        Again, noninterference requires reasoning about how the
        program states vary between two program executions.
        So noninterference cannot be expressed in Hoare logic.

*)

(** A second important observation is that Hoare triples don't help us
    relate the behaviors of _different_ commands. Even for showing
    noninterference, where we start with a single program, we often
    still need to relate different parts of the program to each other,
    but this is not something we can properly do with Hoare logic.

    Another case where we would like to formally relate the behavior
    of different programs is proving program equivalence, for instance
    for showing the correctness of program transformations. Again,
    this is not something we can properly do with Hoare logic.

    So far, the [Imp] and [Equiv] chapters have presented
    some small arithmetic optimizations and proved directly from the
    semantics that optimized programs behave exactly like the originals.

    We could prove these transformations correct directly from the
    semantics because they were very simple. In particular, our
    language of arithmetic expressions includes an evaluation
    _function_ and properties about this function were relatively easy
    to prove, and they lifted trivially to commands. For verifying the
    correctness of less trivial transformations of commands, which are
    stateful and can loop, Relational Hoare Logic will generally work
    much better than the operational semantics.
*)

(** Moreover, Relational Hoare Logic will allow us to specify and
    prove more flexible notions of program equivalence.

    The [Equiv] chapter introduces a notion of program
    equivalence that lets us relate different programs when they
    "behave exactly the same." But this is too restrictive in practice.

    Take the Imp program that swaps the values of variables [X] and
    [Y] using an auxiliary variable, here [Z].

*)

Definition swap_aux :=
  <{ Z := X;
     X := Y;
     Y := Z }>.

(** The program that swaps the values of [X] and [Y] using arithmetic
    operations intuitively achieves the same thing.

*)

Definition swap_arith :=
  <{ X := X + Y;
     Y := X - Y;
     X := X - Y }>.

(** However, these two programs are _not_ equivalent with respect to
    the restrictive program equivalence notion from [Equiv]:

    - In the first program, the final value of [Z] equals the initial
      value of [X].

    - In the second program, the value of [Z] does not change.

    The problem is that the restrictive notion of program equivalence from
    [Equiv] doesn't allow _any_ variables to differ in the final
    states, even if we may intuitively not care about the final values
    of some auxiliary variables (like [Z] above).
*)

(** Even simpler transformations, like renaming the auxiliary variable
    (here, [W] instead of [X], are enough to invalidate program
    equivalence.

*)

Definition swap_aux' :=
  <{ W := X;
     X := Y;
     Y := W }>.

(** To compare different programs and have anything meaningful to say
    about them, we're going to need more general and flexible tools.

*)

(** So a natural question is how to _generalize_ Hoare logic to state
    and prove properties that _relate_ two executions, each possibly
    of a different program.

    _Relational Hoare Logic_ (commonly RHL) is an inference system
    that achieves just this. In this chapter, we build and use this
    logic for Imp, based on what we learned from the [Hoare] chapters.

    The literature has different versions of the RHL rules, some quite
    complex, but in this chapter we stick to a relatively simple version.

*)

(* ################################################################# *)
(** * Relational Assertions *)

(** In the relational setting, an assertion is a logical property of
    two [state]s (of two potentially different programs).

*)

Definition RAssertion := state -> state -> Prop.

(** In other words, it is a _binary relation_ between states.
    (Binary relations are discussed in more detail in the [Rel]
    optional chapter of _Logical Foundations_.)

    Basic assertions work much like they did in Hoare Logic. For example,

      - [fun st1 st2 => True] holds for every two states, and

      - [fun st1 st2 => False] holds for no two states, as before.

      - [fun st1 st2 => st1 X = 3] holds when the value of [X] in the
        _first_ state is [3],

      - [fun st1 st2 => st2 Y = 5] holds when the value of [Y] in the
        _second_ state is [5], and

      - [fun st1 st2 => st1 X = 3 /\ st2 Y = 5] holds when the value
        of [X] in the first state is [3] and the value of [Y] in the
        second state is [5],

*)

(** More interestingly, now we can write relational assertions that
    connect the contents of the two states to each other in a more
    direct way:

      - [fun st1 st2 => st1 X = st2 X] holds when the value of
        variable [X] is the same in the two executions.

        We will use such equality assertions to specify that a program
        is noninterferent and that two programs are equivalent.
        For instance, for specifying that two versions of swap are
        equivalent we will use the following relational assertion:
        [fun st1 st2 => st1 X = st2 X /\ st1 Y = st2 Y].

      - [fun st1 st2 => st1 X <= st2 X] holds when the value of [X] in
        the first execution is smaller than the value of [X] in the
        second execution. We will use this in the precondition and
        postcondition to define that a command is monotonic in [X].

*)

Declare Scope hoare_spec_scope.

(* ================================================================= *)
(** ** Notations for Relational Assertions *)

(** As in the [Hoare] chapter, we introduce Coq notations to
    write more readable assertions, as in pen and paper proofs.

    The key difference is that, in a relational assertion, each
    reference to a variable must refer explicitly to one of the two
    program states. We will write [X{1}] to refer to the value of [X]
    in the first state, and [X{2}] to refer to the value of [X] in the
    second state.

      - [X{1} = 3 /\ Y{2} = 5]

      - [X{1} = X{2}]

      - [X{1} = X{2} /\ Y{1} = Y{2}]

      - [X{1} <= X{2}]
*)

(** We try to keep notations as close as possible to those used
    for Hoare logic, but separated in a dedicated scope of their own.

    Implications look exactly as they did before.

*)

Definition rassert_implies (P Q : RAssertion) : Prop :=
  forall st1 st2, P st1 st2 -> Q st1 st2.

Declare Scope rhoare_spec_scope.
Notation "P ->> Q" := (rassert_implies P Q)
                      (at level 80) : rhoare_spec_scope.
Open Scope rhoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : rhoare_spec_scope.

(** As usual, coercions and annotation scopes are used to lift the
    various types of expressions to the level of relational assertions.

    We need to be a bit more careful now when treating arithmetic
    expressions, as we need to ensure that they're evaluated in the
    right state.

    There are now two ways to evaluate an expression, either in the
    first state or in the second state. This distinction needs to be
    made explicitly: a simple coercion couldn't decide which way to go!

*)

Definition Aexp : Type := state -> state -> nat.

Definition rassert_of_Prop (P : Prop) : RAssertion := fun _ _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ _ => n.

Definition Aexp_of_aexp_1 (a : aexp) : Aexp := fun st1 _   => aeval st1 a.
Definition Aexp_of_aexp_2 (a : aexp) : Aexp := fun _   st2 => aeval st2 a.

Coercion rassert_of_Prop : Sortclass >-> RAssertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Add Printing Coercion Aexp_of_nat rassert_of_Prop.

Arguments rassert_of_Prop /.
Arguments Aexp_of_nat /.
Add Printing Coercion Aexp_of_nat rassert_of_Prop.

Declare Scope rassertion_scope.
Bind Scope rassertion_scope with RAssertion.
Bind Scope rassertion_scope with Aexp.
Delimit Scope rassertion_scope with rassertion.

Notation rassert P := (P%rassertion : RAssertion).
Notation mkAexp a := (a%rassertion : Aexp).

Notation "~ P" := (fun st1 st2 => ~ rassert P st1 st2) : rassertion_scope.
Notation "P /\ Q" := (fun st1 st2 => rassert P st1 st2 /\ rassert Q st1 st2) : rassertion_scope.
Notation "P \/ Q" := (fun st1 st2 => rassert P st1 st2 \/ rassert Q st1 st2) : rassertion_scope.
Notation "P -> Q" := (fun st1 st2 => rassert P st1 st2 ->  rassert Q st1 st2) : rassertion_scope.
Notation "P <-> Q" := (fun st1 st2 => rassert P st1 st2 <->  rassert Q st1 st2) : rassertion_scope.
Notation "a = b" := (fun st1 st2 => mkAexp a st1 st2 = mkAexp b st1 st2) : rassertion_scope.
Notation "a <> b" := (fun st1 st2 => mkAexp a st1 st2 <> mkAexp b st1 st2) : rassertion_scope.
Notation "a <= b" := (fun st1 st2 => mkAexp a st1 st2 <= mkAexp b st1 st2) : rassertion_scope.
Notation "a < b" := (fun st1 st2 => mkAexp a st1 st2 < mkAexp b st1 st2) : rassertion_scope.
Notation "a >= b" := (fun st1 st2 => mkAexp a st1 st2 >= mkAexp b st1 st2) : rassertion_scope.
Notation "a > b" := (fun st1 st2 => mkAexp a st1 st2 > mkAexp b st1 st2) : rassertion_scope.
Notation "a + b" := (fun st1 st2 => mkAexp a st1 st2 + mkAexp b st1 st2) : rassertion_scope.
Notation "a - b" := (fun st1 st2 => mkAexp a st1 st2 - mkAexp b st1 st2) : rassertion_scope.
Notation "a * b" := (fun st1 st2 => mkAexp a st1 st2 * mkAexp b st1 st2) : rassertion_scope.

Notation "a '{1}'" := (fun (st1 st2 : state)   => Aexp_of_aexp_1 a st1 st2) (at level 50) : rassertion_scope.
Notation "a '{2}'" := (fun (st1 st2 : state)   => Aexp_of_aexp_2 a st1 st2) (at level 50) : rassertion_scope.

Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st1 st2 => f (x st1 st2).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st1 : state) (st2 : state) :=
  f (x st1 st2) (y st1 st2).

(* ################################################################# *)
(** * Relational Judgments, Informally *)

(** A Hoare triple was a statement involving three parts
    (precondition, command and postcondition), and this becomes a
    "quadruple" in the relational world:

      - The precondition and the postcondition remain but become
        relational assertions.

      - Those now apply to two commands instead of one.

    We will call these relational judgments or simply judgments, and
    write them like so:

      |- c1 ~~ c2 : P => Q
*)

(** The interpretation of a judgment is a direct extension of that of
    Hoare triples:

      - If initial states [s1] and [s2] together satisfy the
        relational precondition [P],

      - and if [c1] runs from [s1] and eventually terminates in some
        state [s1'],

      - and if [c2] runs from [s2] and eventually terminates in some
        state [s2'],

      - then the final states [s1'] and [s2'] together satisfy the
        relational postcondition [Q].

*)

(** Let's return to some of the examples we discussed above and encode
    them as relational judgments.

      - We can state that command [X := X + 42] is monotonic in the
        variable [X] as follows:

        |- X := X + 42 ~~ X := X + 42 : (X{1} <= X{2}) => (X{1} <= X{2})

      - We can state that [swap_aux] and [swap_arith] are equivalent:

        |- swap_aux ~~ swap_arith : (X{1} = X{2} /\ Y{1} = Y{2}) =>
                                    (X{1} = X{2} /\ Y{1} = Y{2})

        Here we have the flexibility to ignore all variables other
        than [X] and [Y], which can be used as auxiliaries, but which
        don't store the arguments and result of the commands. *)

(** Now consider the following command (taken from Noninterference.v): *)

Definition secure_com : com := <{ X := X+1; Y := X+Y*2 }>.

(** If we assume that variable [X] is public and variable [Y] is
   secret, we can state noninterference for [secure_com] as follows:

        |- secure_com ~~ secure_com : (X{1} = X{2}) => (X{1} = X{2})

   As usual for noninterference, we assume that the public variables
   are equal in the precondition, and prove that the public variables
   are still equal after executing the command by encoding this in the
   postcondition.
 *)

(* ################################################################# *)
(** * Relational Judgments, Formally *)

(** Let us now formalize what it means for a relational judgment to be
    _valid_, that is, for the pair of programs to satisfy the
    specification given by the relational pre- and postconditions:

*)

Definition rhoare_judgment
           (P : RAssertion) (c1 c2 : com) (Q : RAssertion) : Prop :=
  forall st1 st2 st1' st2',
     st1 =[ c1 ]=> st1' ->
     st2 =[ c2 ]=> st2' ->
     P st1 st2  ->
     Q st1' st2'.

Notation "'|-' c1 '~~' c2 ':' P '=>' Q" :=
  (rhoare_judgment P c1 c2 Q)
    (at level 40,
      c1 custom com at level 99, c2 custom com at level 99,
      P constr, Q constr at next level)
    : rhoare_spec_scope.

(** Using this we can formalize all the statements above in a very
    direct way: *)

Definition add42_monotonic_spec : Prop :=
  |- X := X + 42 ~~ X := X + 42 : (X{1} <= X{2}) => (X{1} <= X{2}).

Definition swap_equiv_spec : Prop :=
  |- swap_aux ~~ swap_arith : (X{1} = X{2} /\ Y{1} = Y{2}) =>
                              (X{1} = X{2} /\ Y{1} = Y{2}).

Definition secure_com_noninterferent_spec : Prop :=
  |- secure_com ~~ secure_com : (X{1} = X{2}) => (X{1} = X{2}).

(* ################################################################# *)
(** * Proof Rules *)

(** The structure of _non-relational_ program logics like Hoare logic
    is rather simple:

      - Each syntactic construction of the language (assignments,
        conditionals, etc.) has an associated proof rule.

      - A small number of structural rules help with logical
        manipulations.

    In this way, proofs closely follow the structure of the programs
    being analyzed.

    In a relational setting, things get more complicated because in
    general we're trying to connect two programs that structurally may
    be similar or they may be different.

*)

(** Like Hoare logic, RHL is structured as a collection of inference
    rules. We can divide these into three main groups:

      - Two-sided rules for each syntactic form of the language, when
        the same form appears at the same point in both programs.

      - One-sided rules, also for each syntactic form, when we need to
        look at one of the two programs and leave the other unchanged.

      - Structural rules for program transformation and spec
        manipulation.

    Very roughly speaking, two-sided rules are used to relate
    syntactically similar programs (e.g, for noninterference or
    monotonicity we start with the same program on both sides).
    One-sided rules are used to relate dissimilar programs (e.g.,
    like [swap_aux] and [swap_arith] above, or like [mult_simple] and
    [mult_iter]).


*)

(* ================================================================= *)
(** ** Skip *)

(** To begin with, two programs that don't do anything trivially
    preserve any relational assertions between their states. *)

(**

      --------------------------------  (rhoare_skip)
      |- <{skip}> ~~ <{skip}> : P => P

*)

(** Formally:

*)

Theorem rhoare_skip : forall P,
    |- <{skip}> ~~ <{skip}> : P => P.
Proof.
  intros P st1 st2 st1' st2' H1 H2 HP.
  inversion H1; subst. inversion H2; subst. assumption.
Qed.

(* ================================================================= *)
(** ** Consequence *)

(** As in Hoare logic, we need structural rules to manipulate the pre-
    and postconditions of a pair of commands. These fill the gaps
    between the relational assertions we have and the ones needed by
    one- and two-sided rules. *)

Theorem rhoare_consequence_pre : forall (P P' Q : RAssertion) c1 c2,
  |- c1 ~~ c2 : P' => Q ->
  P ->> P' ->
  |- c1 ~~ c2 : P => Q.
Proof.
  unfold rhoare_judgment, "->>".
  intros P P' Q c1 c2 Hhoare Himp st1 st2 st1' st2' Heval1 Heval2 Hpre.
  apply Hhoare with (st1 := st1) (st2 := st2).
  - assumption.
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem rhoare_consequence_post : forall (P Q Q' : RAssertion) c1 c2,
  |- c1 ~~ c2 : P => Q' ->
  Q' ->> Q ->
  |- c1 ~~ c2 : P => Q.
Proof.
  unfold rhoare_judgment, "->>".
  intros P Q Q' c1 c2 Hhoare Himp st1 st2 st1' st2' Heval1 Heval2 Hpost.
  apply Himp.
  apply Hhoare with (st1 := st1) (st2 := st2).
  - assumption.
  - assumption.
  - assumption.
Qed.

(** The combined rule of consequence puts together relational
    assertion implications on both precondition and postcondition.

*)

Theorem rhoare_consequence : forall (P P' Q Q' : RAssertion) c1 c2,
  |- c1 ~~ c2 : P' => Q' ->
  P ->> P' ->
  Q' ->> Q ->
  |- c1 ~~ c2 : P => Q.
Proof.
  intros P P' Q Q' c1 c2 Htriple Hpre Hpost.
  apply rhoare_consequence_pre with (P' := P').
  - apply rhoare_consequence_post with (Q' := Q').
    + assumption.
    + assumption.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Assignment *)

(** To formalize the relational rules for assignment, we need to
    extend assertion substitution to relational assertions.

    In the same way that we evaluate arithmetic expressions inside
    relational assertions, a substitution takes place either in the
    first memory or in the second memory. Our operations make this
    choice explicit.

*)

Definition assn_sub_1 X a (P:RAssertion) : RAssertion :=
  fun (st1 st2 : state) =>
    P (X !-> aeval st1 a ; st1) st2.

Definition assn_sub_2 X a (P:RAssertion) : RAssertion :=
  fun (st1 st2 : state) =>
    P st1 (X !-> aeval st2 a ; st2).

Notation "P [ X {1} |-> a ]" := (assn_sub_1 X a P)
  (at level 10, X at next level, a custom com) : hoare_spec_scope.

Notation "P [ X {2} |-> a ]" := (assn_sub_2 X a P)
  (at level 10, X at next level, a custom com) : hoare_spec_scope.

(** We also redefine one of our automation tactics from [Hoare2],
    this time specialized for unfolding [rassert_implies],
    [assn_sub_1], and [assn_sub_2]. *)
Ltac verify_rassn_v1 :=
  repeat split;
  simpl;
  unfold rassert_implies;
  unfold ap in *; unfold ap2 in *;
  (* unfold bassn in *; unfold beval in *; unfold aeval in *; *)
  unfold assn_sub_1, assn_sub_2; intros;
  repeat (simpl in *;
          rewrite t_update_eq || rewrite t_update_same ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try lia.

(** Using the new substitution operations, we can define the two-sided
    proof rule for assignment:

*)

(**

      -----------------------------------------  (rhoare_asgn)
      |- <{X1 := a1}> ~~ <{X2 := a2}> :
           (Q [X1{1} |-> a1] [X2{2} |-> a2]) => Q
*)

(** Formally: *)

Theorem rhoare_asgn : forall Q X1 X2 a1 a2,
    |- <{X1 := a1}> ~~ <{X2 := a2}> : (Q [X1{1} |-> a1] [X2{2} |-> a2]) => Q.
Proof.
  unfold rhoare_judgment.
  intros Q X1 X2 a1 a2 st1 st2 st1' st2' HE1 HE2 HQ.
  inversion HE1. subst. inversion HE2. subst.
  unfold assn_sub_1, assn_sub_2 in HQ. assumption.  Qed.

(** This two-sided rule is all we need to prove monotonicity of the
    "add42" command: *)

Lemma add42_monotonic :
  |- X := X + 42 ~~ X := X + 42 : (X{1} <= X{2}) => (X{1} <= X{2}).
Proof.
  eapply rhoare_consequence_pre.
  - apply rhoare_asgn.
  - (* can also solve this whole case with verify_rassn_v1. *)
    unfold assn_sub_1, assn_sub_2, rassert_implies.
    simpl. intros st1 st2 H. repeat rewrite t_update_eq.
    (* crux of this proof in next goal:
       st1 X <= st2 X -> st1 X + 42 <= st2 X + 42 *)
    lia.
Qed.

(** The two-sided assignment rule is, perhaps, more general than we
    might have expected. Specifically, it doesn't require us to assign
    a value to the same variable on both sides.

    In fact, we're always able to take an arithmetic expression and
    substitute it for any instances of a variable in a relational
    assertion. If one of the variables belongs to the first program
    and the other to the second program, the two assignments are
    necessarily independent.

    This suggests several possibilities for one-sided rules. One of
    them is to combine an assignment and a [skip] into a sort of
    specialized two-sided rule without any additional premises.

*)

Theorem rhoare_asgn_1 : forall Q X a,
  |- <{X := a}> ~~ <{skip}> : (Q [X{1} |-> a]) => Q.
Proof.
  unfold rhoare_judgment.
  intros Q X a st1 st2 st1' st2' HE1 HE2 HQ.
  inversion HE1. subst. inversion HE2. subst.
  unfold assn_sub_1 in HQ. assumption.
Qed.

Theorem rhoare_asgn_2 : forall Q X a,
  |- <{skip}> ~~ <{X := a}>: (Q [X{2} |-> a]) => Q.
Proof.
  unfold rhoare_judgment.
  intros Q X a st1 st2 st1' st2' HE1 HE2 HQ.
  inversion HE1. subst. inversion HE2. subst.
  unfold assn_sub_2 in HQ. assumption.
Qed.

(** We will see more interesting examples below, but for now we can
    use [rhoare_asgn_1] to prove that the command [X := X] is
    equivalent to [skip]. *)

Lemma trivial_assignment_skip :
  |- X := X ~~ skip : (X{1} = X{2}) => (X{1} = X{2}).
Proof.
  eapply rhoare_consequence_pre.
  - apply rhoare_asgn_1.
  - verify_rassn_v1.
Qed.

(** Above we stated program equivalence only looking at the value of
    variable [X], but we can strengthen this to look at the values of
    _all_ variables (basically obtaining a termination-insensitive
    version of [cequiv] from [Equiv]): *)

Lemma trivial_assignment_skip' :
  |- X := X ~~ skip : (fun st1 st2 => st1 = st2) =>
                      (fun st1 st2 => st1 = st2).
Proof.
  eapply rhoare_consequence_pre.
  - apply rhoare_asgn_1.
  - verify_rassn_v1.
Qed.


(* ================================================================= *)
(** ** Sequencing *)

(** The two-sided sequencing rule for RHL is an extension of the Hoare
    sequencing rule: run the first pair of commands from the initial
    precondition to an intermediate assertion, then the second pair of
    commands from that assertion to the postcondition.

*)

(**

              |- c1 ~~ c2 : P => Q
              |- d1 ~~ d2 : Q => R
      ------------------------------------  (rhoare_seq)
      |- <{c1; d1}> ~~ <{c2; d2}> : P => R

*)

(** Formally:

*)

Theorem rhoare_seq : forall P Q R c1 c2 d1 d2,
    |- d1 ~~ d2 : Q => R ->
    |- c1 ~~ c2 : P => Q ->
    |- <{c1; d1}> ~~ <{c2; d2}> : P => R.
Proof.
  unfold rhoare_judgment.
  intros P Q R c1 c2 d1 d2 H1 H2 st1 st2 st1' st2' H1_1' H2_2' Pre.
  inversion H1_1'; subst. inversion H2_2'; subst.
  eauto.
Qed.

(** We can use this two-sided sequencing rule to relate two programs
    in lock-step. For instance for proving noninterference of
    [secure_com] we relate each assignment to itself: *)

Print secure_com. (* = <{ X := X + 1; Y := X + Y * 2 }> *)

Lemma secure_com_noninterferent :
  |- secure_com ~~ secure_com : (X{1} = X{2}) => (X{1} = X{2}).
Proof.
  unfold secure_com.
  eapply rhoare_consequence_pre.
  - eapply rhoare_seq.
    + apply rhoare_asgn.
    + apply rhoare_asgn.
  - verify_rassn_v1.
Qed.

(* ================================================================= *)
(** ** Alignment: Skip Consuming and Padding *)

(** Now we can begin to introduce one-sided rules that leave one of
    the two programs in a relational judgment untouched.

    Because we want to be able to relate programs with different
    control structures, we need to go beyond the simple two-sided
    rules, which closely resemble those of standard Hoare
    logic. Otherwise, we'll end up with a weak logical system.

    In particular, we need rules that allow us to manipulate the
    _alignment_ of which commands of one program we want to match to
    which commands of the other. These make up an essential part of
    any moderately complex proofs in RHL.

[skip; skip] and [skip]

    For this task, the sequencing operator will be our fulcrum.

*)

(** We can start by stating and proving one-sided rules for
    [skip]. These rules will unilaterally consume a [skip] command on
    one side, and leave the other unchanged. [skip] doesn't modify the
    state of its program and trivially preserves all
    assertions. Starting with the left program:

*)

(**

           |- c1 ~~ c2 : P => Q
      ------------------------------  (rhoare_skip_seq_1)
      |- <{skip; c1}> ~~ c2 : P => Q


           |- c1 ~~ c2 : P => Q
      ------------------------------  (rhoare_seq_skip_1)
      |- <{c1; skip}> ~~ c2 : P => Q

*)

(** Formally:

*)

Theorem rhoare_skip_seq_1 : forall P Q c1 c2,
  |- c1 ~~ c2 : P => Q ->
  |- <{skip; c1}> ~~ c2 : P => Q.
Proof.
  intros P Q c1 c2 Hhoare st1 st2 st1' st2' Heval1 Heval2 HP.
  inversion Heval1; subst; clear Heval1.
  inversion H1; subst; clear H1.
  eauto.
Qed.

Theorem rhoare_seq_skip_1 : forall P Q c1 c2,
  |- c1 ~~ c2 : P => Q ->
  |- <{c1; skip}> ~~ c2 : P => Q.
Proof.
  intros P Q c1 c2 Hhoare st1 st2 st1' st2' Heval1 Heval2 HP.
  inversion Heval1; subst; clear Heval1.
  inversion H4; subst; clear H4.
  eauto.
Qed.

(** Here is a simple example using this rule: *)

Example trivial_skip :
  |- <{X := X + 42; skip}> ~~  <{X := X + 42}> : (X{1} = X{2}) =>
                                                 (X{1} = X{2}).
Proof.
  simpl. eapply rhoare_seq_skip_1.
  - eapply rhoare_consequence_pre.
    + apply rhoare_asgn.
    + verify_rassn_v1.
Qed.

(** And similarly for the right side:

*)

(**

           |- c1 ~~ c2 : P => Q
      ------------------------------  (rhoare_skip_seq_2)
      |- c1 ~~ <{skip; c2}> : P => Q


           |- c1 ~~ c2 : P => Q
      ------------------------------  (rhoare_seq_skip_2)
      |- c1 ~~ <{c2; skip}> : P => Q

*)

(** Formally:

*)

Theorem rhoare_skip_seq_2 : forall P Q c1 c2,
  |- c1 ~~ c2 : P => Q ->
  |- c1 ~~ <{skip; c2}> : P => Q.
Proof.
  intros P Q c1 c2 Hhoare st1 st2 st1' st2' Heval1 Heval2 HP.
  inversion Heval2; subst; clear Heval2.
  inversion H1; subst; clear H1.
  eauto.
Qed.

Theorem rhoare_seq_skip_2 : forall P Q c1 c2,
  |- c1 ~~ c2 : P => Q ->
  |- c1 ~~ <{c2; skip}> : P => Q.
Proof.
  intros P Q c1 c2 Hhoare st1 st2 st1' st2' Heval1 Heval2 HP.
  inversion Heval2; subst; clear Heval2.
  inversion H4; subst; clear H4.
  eauto.
Qed.

(** We can be more general if we replace [skip] command with an
    arbitrary command related to a [skip] on the other side, and chain
    intermediate assertions as usual.

*)

Theorem rhoare_seq_1 : forall P Q R c1 d1 d2,
    |- d1 ~~ d2 : Q => R ->
    |- c1 ~~ <{skip}> : P => Q ->
    |- <{c1; d1}> ~~ d2 : P => R.
Proof.
  unfold rhoare_judgment.
  intros P Q R c1 d1 d2 H1 H2 st1 st2 st1' st2' H1_1' H2_2' Pre.
  inversion H1_1'; subst.
  eapply H1; eauto. eapply H2; eauto.
  constructor.
Qed.

Theorem rhoare_seq_2 : forall P Q R c2 d1 d2,
    |- d1 ~~ d2 : Q => R ->
    |- <{skip}> ~~ c2 : P => Q ->
    |- d1 ~~ <{c2; d2}> : P => R.
Proof.
  unfold rhoare_judgment.
  intros P Q R c2 d1 d2 H1 H2 st1 st2 st1' st2' H1_1' H2_2' Pre.
  inversion H2_2'; subst.
  eapply H1; eauto. eapply H2; eauto.
  constructor.
Qed.

(** Here is a simple example using these rules to remove a dead store
    and relate the live stores to each other: *)

Lemma dead_store_example :
  |- <{X := 0; X := 1}> ~~ <{ X := 1 }> : True => (X{1} = X{2}).
Proof.
  simpl. eapply rhoare_seq_1.
  - eapply rhoare_asgn.
  - eapply rhoare_consequence_pre.
    + apply rhoare_asgn_1.
    + verify_rassn_v1.
Qed.

(** We also use rules [rhoare_seq_1] and [rhoare_seq_2] when we want to
    relate commands that are syntactically dissimilar and we only want
    to separately reason about their effects on the state, as we were
    doing in Hoare logic. *)

(** Note that the two-sided skip rule can be used to finish a
    derivation by consuming two lined-up "empty" programs.

    By contrast, one-sided rules _can't_ be used to completely
    discharge a proof obligation, because one of the two programs
    always remains unfinished.

*)

(** If we need to, we can also add [skip]s to ease the task of
    aligning program structures.

*)

Lemma rhoare_equiv_skip_l_1' : forall P Q c1 c2,
  |- <{skip; c1}> ~~ c2 : P => Q ->
  |- c1 ~~ c2 : P => Q.
Proof.
  intros P Q c1 c2 Hhoare st1 st2 st1' st2' Heval1 Heval2 HP.
    eapply Hhoare; eauto.
  econstructor.
  - constructor.
  - apply Heval1.
Qed.


(* ================================================================= *)
(** ** Conditionals *)

(** To model conditional statements, once again we need to lift
    boolean expressions to the language of assertions.

    Here, as in the case of arithmetic expressions, we'll need to
    state explicitly in which of the two memories we intend to
    evaluate each expression.

*)

Definition bassn_1 b : RAssertion :=
  fun st1 st2 => (beval st1 b = true).

Definition bassn_2 b : RAssertion :=
  fun st1 st2 => (beval st2 b = true).

Notation "b '!1'" := (fun (st1 st2 : state)   => bassn_1 b st1 st2) (at level 50) : rassertion_scope.
Notation "b '!2'" := (fun (st1 st2 : state)   => bassn_2 b st1 st2) (at level 50) : rassertion_scope.

Arguments bassn_1 /.
Arguments bassn_2 /.

Lemma bexp_eval_false_1 : forall b st1 st2,
  beval st1 b = false -> ~ ((bassn_1 b) st1 st2).
Proof. congruence. Qed.

Lemma bexp_eval_false_2 : forall b st1 st2,
  beval st2 b = false -> ~ ((bassn_2 b) st1 st2).
Proof. congruence. Qed.

Hint Resolve bexp_eval_false_1 bexp_eval_false_2 : core.

(** We also update our automation tactic to unfold [bassn_1],
    [bassn_2], etc. *)
Ltac verify_rassn :=
  repeat split;
  simpl;
  unfold rassert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassn_1, bassn_2 in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub_1, assn_sub_2; intros;
  repeat (simpl in *;
          rewrite t_update_eq || rewrite t_update_same ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try lia.

(** The basic relational rule for conditionals resembles its Hoare
    logic counterpart: the spec of the joint conditional is satisfied
    if each of the branches satisfies it.

    As before, the proof of the spec for each branch is extended with
    corresponding assumption about the evaluation of the guard
    condition.

    The difference now is that we have two conditions, not one! How do
    we account for this in a two-sided rule? *)

(** The simplest two-sided rule for conditionals considers the case
    where the control flow of both conditionals is in _lockstep_. That
    is, the guard conditions are equivalent in their evaluation
    context.

    In this case, either the two then branches or the two else
    branches are taken.

*)

(**

      |- t1 ~~ t2 : (P /\   b1!1 /\   b2!2) => Q
      |- e1 ~~ e2 : (P /\ ~ b1!1 /\ ~ b2!2) => Q
      ------------------------------------------ (rhoare_if)
          |- <{if b1 then t1 else e1 end}> ~~
             <{if b2 then t2 else e2 end}> :
             (P /\ (b1!1 <-> b2!2)) => Q

*)

(** We can formalize this rule and prove it.

*)

Theorem rhoare_if : forall P Q (b1 b2:bexp) t1 t2 e1 e2,
  |- t1 ~~ t2 : (P /\ b1!1 /\ b2!2) => Q ->
  |- e1 ~~ e2 : (P /\ ~ b1!1 /\ ~ b2!2) => Q ->
  |- <{if b1 then t1 else e1 end}> ~~
     <{if b2 then t2 else e2 end}> : (P /\ (b1!1 <-> b2!2)) => Q.
Proof.
  intros P Q b1 b2 t1 t2 e1 e2 HTrue HFalse st1 st2 st1' st2' HE1 HE2 [HP Hb1_b2].
    inversion HE1; inversion HE2; subst.
  - eauto.
  - exfalso.
    apply (bexp_eval_false_2 _ st1 _ H11).
    apply Hb1_b2. auto.
  - exfalso.
    apply (bexp_eval_false_1 _ _ st2 H4).
    apply Hb1_b2. auto.
  - eapply HFalse; eauto.
Qed.

(** The two-sided rules for conditionals is useful for proving
    noninterference of programs that branch on public information, and
    where the two conditionals will execute in lockstep.

    For instance, assume that [X] and [Y] are public variables,
    and [Z] is a secret variable, then we can prove the following
    program [p1] is noninterferent: *)

Definition p1 := <{ if X <= Y then Y := X; Z := 1 else Z := 0 end }>.

Example noninterference_lockstep :
  |- p1 ~~ p1 : (X{1} = X{2} /\ Y{1} = Y{2}) => (X{1} = X{2} /\ Y{1} = Y{2}).
Proof.
  unfold p1.
  apply rhoare_consequence_pre
    with (P' := fun st1 st2 =>
            (st1 X = st2 X /\ st1 Y = st2 Y) /\
            (bassn_1 <{ X <= Y }> st1 st2 <-> bassn_2 <{ X <= Y }> st1 st2)).
  - apply rhoare_if.
    + eapply rhoare_seq.
      * apply rhoare_asgn.
      * eapply rhoare_consequence_pre.
        -- apply rhoare_asgn.
        -- verify_rassn.
    + eapply rhoare_consequence_pre.
      * apply rhoare_asgn.
      * verify_rassn.
  - verify_rassn.
Qed.

(** The one-sided rules for conditionals relate a conditional to an
    arbitrary command by relating that command to each of the branches
    of the conditional under appropriate conditions.

*)

Theorem rhoare_if_1 : forall P Q b1 t1 e1 c2,
  |- t1 ~~ c2 : (P /\ b1!1) => Q ->
  |- e1 ~~ c2 : (P /\ ~ b1!1) => Q ->
  |- <{if b1 then t1 else e1 end}> ~~ c2 : P => Q.
Proof.
  intros P Q b1 t1 e1 c2 Hthen Helse st1 st1' st2 st2' Heval1 Heval2 HP.
  inversion Heval1; subst; clear Heval1.
    - eapply Hthen; eauto.
  - eapply Helse; eauto.
Qed.

Theorem rhoare_if_2 : forall P Q c1 b2 t2 e2,
  |- c1 ~~ t2 : (P /\ b2!2) => Q ->
  |- c1 ~~ e2 : (P /\ ~ b2!2) => Q ->
  |- c1 ~~ <{if b2 then t2 else e2 end}> : P => Q.
Proof.
  intros P Q c1 b2 t2 e2 Hthen Helse st1 st1' st2 st2' Heval1 Heval2 HP.
  inversion Heval2; subst; clear Heval2.
  - eapply Hthen; eauto.
  - eapply Helse; eauto.
Qed.

(** The one-sided rules for conditionals allow us to reason about
    programs that branch on secrets, so the two conditionals will
    *not* run in lockstep.

    For instance, assuming that variable [X] is public and variable [Y]
    is secret then the following program [p2] is noninterferent: *)

Definition p2 := <{ if Y = 0 then X := Y else X := 0 end }>.

(** Intuitively, even if this program branches on the secret [Y], it
    always assigns the value [0] to [X], so no secret is leaked.

    To prove this we use the one-sided rules for conditionals to
    consider all the ways in which the two conditionals could execute
    (then-then, then-else, else-then, and else-else).

    This goes beyond what the simple type systems we will consider in
    this course can analyze (they will reject this noninterferent
    program as potentially insecure).
*)

Example noninterference_crossproduct :
  |- p2 ~~ p2 : (X{1} = X{2}) => (X{1} = X{2}).
Proof.
  unfold p2.
   apply rhoare_if_1.
  - apply rhoare_if_2.
    + eapply rhoare_consequence_pre.
      * apply rhoare_asgn.
      * verify_rassn.
    + eapply rhoare_consequence_pre.
      * apply rhoare_asgn.
      * verify_rassn.
  - apply rhoare_if_2.
    + eapply rhoare_consequence_pre.
      * apply rhoare_asgn.
      * verify_rassn.
    + eapply rhoare_consequence_pre.
      * apply rhoare_asgn.
      * verify_rassn.
Qed.

(** When the value of a branch condition can be statically known, we
    can use this fact to simplify the inference rules. Let's consider
    the one-sided versions of this.

*)

Theorem rhoare_if_true_1 : forall P Q (b1:bexp) t1 e1 c2,
  |- t1 ~~ c2 : P => Q ->
  |- <{if b1 then t1 else e1 end}> ~~ c2 : (P /\ b1!1) => Q.
Proof.
  intros P Q b1 t1 e1 c2 HE st1 st2 st1' st2' HE1 HE2 [HP Hb1].
  inversion HE1; subst; eauto; congruence.
Qed.

Theorem rhoare_if_false_1 : forall P Q (b1:bexp) t1 e1 c2,
  |- e1 ~~ c2 : P => Q ->
  |- <{if b1 then t1 else e1 end}> ~~ c2 : (P /\ ~ b1!1) => Q.
Proof.
  intros P Q b1 t1 e1 c2 HE st1 st2 st1' st2' HE1 HE2 [HP Hb1].
  inversion HE1; subst; eauto; congruence.
Qed.

Theorem rhoare_if_true_2 : forall P Q c1 (b2:bexp) t2 e2,
  |- c1 ~~ t2 : P => Q ->
  |- c1 ~~ <{if b2 then t2 else e2 end}> : (P /\ b2!2) => Q.
Proof.
  intros P Q c1 b2 t2 e2 HE st1 st2 st1' st2' HE1 HE2 [HP Hb2].
  inversion HE2; subst; eauto; congruence.
Qed.

Theorem rhoare_if_false_2 : forall P Q c1 (b2:bexp) t2 e2,
  |- c1 ~~ e2 : P => Q ->
  |- c1 ~~ <{if b2 then t2 else e2 end}> : (P /\ ~ b2!2) => Q.
Proof.
  intros P Q c1 b2 t2 e2 HE st1 st2 st1' st2' HE1 HE2 [HP Hb2].
  inversion HE2; subst; eauto; congruence.
Qed.

(* ================================================================= *)
(** ** While Loops *)

(** The rules for while extend loop invariants to relate the execution
    of the two programs.

    Here we will consider the two-sided rule where both loops iterate
    in lockstep. That is, whenever one loop iterates, so does the
    other, so they perform the same number of iterations.

    In proof terms, this means that:

      - The loop conditions agree before entering (or not) the loops,
        as well as after each iteration.

      - Both loop conditions are satisfied at the beginning of each
        iteration.

      - Both loop conditions are false when the loops end.

*)

(** Because the loops execute in lockstep, this rule looks similar to
    its Hoare logic counterpart, with added conditions to enforce
    synchronicity. *)

(**

      |- c1 ~~ c2 : (P /\ b1!1 /\ b2!2) => (P /\ (b1!1 <-> b2!2))
      ----------------------------------------------------------- (rhoare_while)
      |- <{while b1 do c1 end}> ~~ <{while b2 do c2 end}> :
         (P /\ (b1!1 <-> b2!2)) => (P /\ ~ b1!1 /\ ~ b2!2).

*)

(** Where [P] is the loop invariant. Formally:

*)

Theorem rhoare_while : forall P (b1 b2:bexp) c1 c2,
  |- c1 ~~ c2 : (P /\ b1!1 /\ b2!2) => (P /\ (b1!1 <-> b2!2)) ->
  |- <{while b1 do c1 end}> ~~ <{while b2 do c2 end}> :
     (P /\ (b1!1 <-> b2!2)) => (P /\ ~ b1!1 /\ ~ b2!2).
Proof.
  intros P b1 b2 c1 c2 Hhoare st1 st2 st1' st2' Heval1 Heval2 [HP Hb1_b2].
  remember <{while b1 do c1 end}> as original_command eqn:Horig.
  generalize dependent st2.
  induction Heval1;
    intros;
    inversion Horig; subst; clear Horig.
  - inversion Heval2; subst; clear Heval2.
    + auto.
    + exfalso.
      eapply bexp_eval_false_1; eauto.
      apply Hb1_b2; auto.
  - inversion Heval2; subst; clear Heval2.
    + exfalso.
      eapply bexp_eval_false_2; eauto.
      apply Hb1_b2; auto.
    + unfold rhoare_judgment in Hhoare.
      assert (Hhoare' := Hhoare _ _ _ _ Heval1_1 H3).
      destruct Hhoare'; auto.
      eapply IHHeval1_2; eauto.
Qed.

(** One-sided rules where a loop is matched to a skip are
    straightforward and very similar to the original Hoare logic
    rules.

*)

Theorem rhoare_while_1 : forall P (b1:bexp) c1,
  |- c1 ~~ <{skip}> : (P /\ b1!1) => P ->
  |- <{while b1 do c1 end}> ~~ <{skip}> : P => (P /\ ~ b1!1).
Proof.
  intros P b1 c1 Hhoare st1 st2 st1' st2' Heval1 Heval2 HP.
  inversion Heval2; subst; clear Heval2.
  remember <{while b1 do c1 end}> as original_command eqn:Horig.
  induction Heval1; subst;
    intros;
    inversion Horig; subst; clear Horig.
  - auto.
  - simpl in Hhoare.
    specialize (Hhoare _ _ _ _ Heval1_1 (E_Skip st2') (conj HP H)).
        auto.
Qed.

Theorem rhoare_while_2 : forall P (b2:bexp) c2,
  |- <{skip}> ~~ c2 : (P /\ b2!2) => P ->
  |- <{skip}> ~~ <{while b2 do c2 end}> : P => (P /\ ~ b2!2).
Proof.
  intros P b2 c2 Hhoare st1 st2 st1' st2' Heval1 Heval2 HP.
  inversion Heval1; subst; clear Heval1.
  remember <{while b2 do c2 end}> as original_command eqn:Horig.
  induction Heval2; subst;
    intros;
    inversion Horig; subst; clear Horig.
  - auto.
  - simpl in Hhoare.
    specialize (Hhoare _ _ _ _ (E_Skip st1') Heval2_1 (conj HP H)).
    auto.
Qed.

(** A more interesting problem is what happens when we want to relate
    the computations carried out by two loops, but where the loops
    don't iterate in lockstep. Consider the following examples:

*)

Definition fact_iter_fast :=
  <{ Y := X;
     Z := 1;
     while Y <> 0 do
       Z := Z * Y;
       Y := Y - 1
     end }>.

Definition fact_iter_slow :=
  <{ Y := X;
     Z := 1;
     W := 0;
     while Y <> 0 do
       if W = 0 then
         Z := Z * Y;
         Y := Y - 1
       else
         skip
       end;
       W := 1 - W
     end }>.

(**
*)

(** To prove properties of programs like these, we need rules with
    additional "knobs," for example letting us characterize:

      - When the two loops perform an iteration in lockstep.

      - When the first loop performs an iteration while the second
        loop waits for it.

      - When the second loop performs an iteration while the first
        loop waits for it.

*)



(* ################################################################# *)
(** * To Know More *)

(** Relational Hoare logic was introduced by Benton in his classic
    POPL paper.
    _EasyCrypt_ is a proof assistant based on a probabilistic version
    of relational Hoare logic.

    The literature has different versions of the RHL rules, some quite
    complex, but in this chapter we presented a relatively simple version.
*)

(* 2025-05-14 17:12 *)
