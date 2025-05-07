(** * Hoare21: Hoare Logic, Part 2.1 *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-intuition-auto-with-star".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.
From Coq Require Import Arith.
From Coq Require Import EqNat.
From Coq Require Import PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Export Hoare12.
Set Default Goal Selector "!".

Definition FILL_IN_HERE := <{True}>.

(* ################################################################# *)
(** * Decorated Programs *)

(** The beauty of Hoare Logic is that it is _structure-guided_: the
    structure of proofs exactly follows the structure of programs.

    We can record the essential ideas of a Hoare-logic proof --
    omitting low-level calculational details -- by "decorating" a
    program with appropriate assertions on each of its commands.

    Such a _decorated program_ carries within itself an argument for
    its own correctness. *)

(** For example, consider the program:

    X := m;
    Z := p;
    while X <> 0 do
      Z := Z - 1;
      X := X - 1
    end
*)
(** Here is one possible specification for this program, in the
    form of a Hoare triple:

    {{ True }}
    X := m;
    Z := p;
    while X <> 0 do
      Z := Z - 1;
      X := X - 1
    end
    {{ Z = p - m }}
*)
(** (Note the _parameters_ [m] and [p], which stand for
   fixed-but-arbitrary numbers.  Formally, they are simply Coq
   variables of type [nat].) *)

(** Here is a decorated version of this program, embodying a
    proof of this specification:

    {{ True }} ->>
    {{ m = m }}
      X := m
                         {{ X = m }} ->>
                         {{ X = m /\ p = p }};
      Z := p;
                         {{ X = m /\ Z = p }} ->>
                         {{ Z - X = p - m }}
      while X <> 0 do
                         {{ Z - X = p - m /\ X <> 0 }} ->>
                         {{ (Z - 1) - (X - 1) = p - m }}
        Z := Z - 1
                         {{ Z - (X - 1) = p - m }};
        X := X - 1
                         {{ Z - X = p - m }}
      end
    {{ Z - X = p - m /\ ~ (X <> 0) }} ->>
    {{ Z = p - m }}
*)

(** Concretely, a decorated program consists of the program's text
    interleaved with assertions (sometimes multiple assertions
    separated by implications). *)

(** A decorated program can be viewed as a compact representation of a
    proof in Hoare Logic: the assertions surrounding each command
    specify the Hoare triple to be proved for that part of the program
    using one of the Hoare Logic rules, and the structure of the
    program itself shows how to assemble all these individual steps
    into a proof for the whole program. *)

(** Our goal is to verify such decorated programs "mostly
    automatically."  But, before we can verify anything, we need to be
    able to _find_ a proof for a given specification, and for this we
    need to discover the right assertions. This can be done in an
    almost mechanical way, with the exception of finding loop
    invariants. In the remainder of this section we explain in detail
    how to construct decorations for several short programs, all of
    which are loop-free or have simple loop invariants. We'll return
    to finding more interesting loop invariants later in the chapter. *)

(* ================================================================= *)
(** ** Example: Swapping *)

(** Consider the following program, which swaps the values of two
    variables using addition and subtraction (instead of by assigning
    to a temporary variable).

       X := X + Y;
       Y := X - Y;
       X := X - Y

    We can give a proof, in the form of decorations, that this program is
    correct -- i.e., it really swaps [X] and [Y] -- as follows.

    (1)    {{ X = m /\ Y = n }} ->>
    (2)    {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
             X := X + Y
    (3)                     {{ X - (X - Y) = n /\ X - Y = m }};
             Y := X - Y
    (4)                     {{ X - Y = n /\ Y = m }};
             X := X - Y
    (5)    {{ X = n /\ Y = m }}

    The decorations can be constructed as follows:

      - We begin with the undecorated program (the unnumbered lines).

      - We add the specification -- i.e., the outer precondition (1)
        and postcondition (5). In the precondition, we use parameters
        [m] and [n] to remember the initial values of variables [X]
        and [Y] so that we can refer to them in the postcondition (5).

      - We work backwards, mechanically, starting from (5) and
        proceeding until we get to (2). At each step, we obtain the
        precondition of the assignment from its postcondition by
        substituting the assigned variable with the right-hand-side of
        the assignment. For instance, we obtain (4) by substituting
        [X] with [X - Y] in (5), and we obtain (3) by substituting [Y]
        with [X - Y] in (4).

    Finally, we verify that (1) logically implies (2) -- i.e., that
    the step from (1) to (2) is a valid use of the law of
    consequence -- by doing a bit of high-school algebra.
 *)

(* ================================================================= *)
(** ** Example: Simple Conditionals *)

(** Here is a simple decorated program using conditionals:

      (1)   {{ True }}
              if X <= Y then
      (2)                    {{ True /\ X <= Y }} ->>
      (3)                    {{ (Y - X) + X = Y \/ (Y - X) + Y = X }}
                Z := Y - X
      (4)                    {{ Z + X = Y \/ Z + Y = X }}
              else
      (5)                    {{ True /\ ~(X <= Y) }} ->>
      (6)                    {{ (X - Y) + X = Y \/ (X - Y) + Y = X }}
                Z := X - Y
      (7)                    {{ Z + X = Y \/ Z + Y = X }}
              end
      (8)   {{ Z + X = Y \/ Z + Y = X }}

These decorations can be constructed as follows:

  - We start with the outer precondition (1) and postcondition (8).

  - Following the format dictated by the [hoare_if] rule, we copy the
    postcondition (8) to (4) and (7). We conjoin the precondition (1)
    with the guard of the conditional to obtain (2). We conjoin (1)
    with the negated guard of the conditional to obtain (5).

  - In order to use the assignment rule and obtain (3), we substitute
    [Z] by [Y - X] in (4). To obtain (6) we substitute [Z] by [X - Y]
    in (7).

  - Finally, we verify that (2) implies (3) and (5) implies (6). Both
    of these implications crucially depend on the ordering of [X] and
    [Y] obtained from the guard. For instance, knowing that [X <= Y]
    ensures that subtracting [X] from [Y] and then adding back [X]
    produces [Y], as required by the first disjunct of (3). Similarly,
    knowing that [~ (X <= Y)] ensures that subtracting [Y] from [X]
    and then adding back [Y] produces [X], as needed by the second
    disjunct of (6). Note that [n - m + m = n] does _not_ hold for
    arbitrary natural numbers [n] and [m] (for example, [3 - 5 + 5 =
    5]). *)

(** **** Exercise: 2 stars, standard (if_minus_plus_reloaded)

    Fill in valid decorations for the following program: *)
(*
  {{ True }}
    if X <= Y then
              {{                         }} ->>
              {{                         }}
      Z := Y - X
              {{                         }}
    else
              {{                         }} ->>
              {{                         }}
      Y := X + Z
              {{                         }}
    end
  {{ Y = X + Z }}
*)
(**
    Briefly justify each use of [->>].
*)

(* Do not modify the following line: *)
Definition manual_grade_for_if_minus_plus_reloaded : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Example: Reduce to Zero *)

(** Here is a [while] loop that is so simple that [True] suffices
    as a loop invariant.

        (1)    {{ True }}
                 while X <> 0 do
        (2)                  {{ True /\ X <> 0 }} ->>
        (3)                  {{ True }}
                   X := X - 1
        (4)                  {{ True }}
                 end
        (5)    {{ True /\ ~(X <> 0) }} ->>
        (6)    {{ X = 0 }}

   The decorations can be constructed as follows:

     - Start with the outer precondition (1) and postcondition (6).

     - Following the format dictated by the [hoare_while] rule, we copy
       (1) to (4). We conjoin (1) with the guard to obtain (2). We also
       conjoin (1) with the negation of the guard to obtain (5).

     - Because the final postcondition (6) does not syntactically match (5),
       we add an implication between them.

     - Using the assignment rule with assertion (4), we trivially substitute
       and obtain assertion (3).

     - We add the implication between (2) and (3).

   Finally we check that the implications do hold; both are trivial. *)

(* ================================================================= *)
(** ** Example: Division *)

(** Let's do one more example of simple reasoning about a loop.

    The following Imp program calculates the integer quotient and
    remainder of parameters [m] and [n].

       X := m;
       Y := 0;
       while n <= X do
         X := X - n;
         Y := Y + 1
       end;

    If we replace [m] and [n] by concrete numbers and execute the program, it
    will terminate with the variable [X] set to the remainder when [m]
    is divided by [n] and [Y] set to the quotient. *)

(** In order to give a specification to this program we need to
    remember that dividing [m] by [n] produces a remainder [X] and a
    quotient [Y] such that [n * Y + X = m /\ X < n].

    It turns out that we get lucky with this program and don't have to
    think very hard about the loop invariant: the loop invariant is just
    the first conjunct, [n * Y + X = m], and we can use this to
    decorate the program.

      (1)  {{ True }} ->>
      (2)  {{ n * 0 + m = m }}
             X := m;
      (3)                     {{ n * 0 + X = m }}
             Y := 0;
      (4)                     {{ n * Y + X = m }}
             while n <= X do
      (5)                     {{ n * Y + X = m /\ n <= X }} ->>
      (6)                     {{ n * (Y + 1) + (X - n) = m }}
               X := X - n;
      (7)                     {{ n * (Y + 1) + X = m }}
               Y := Y + 1
      (8)                     {{ n * Y + X = m }}
             end
      (9)  {{ n * Y + X = m /\ ~ (n <= X) }} ->>
     (10)  {{ n * Y + X = m /\ X < n }}

    Assertions (4), (5), (8), and (9) are derived mechanically from
    the loop invariant and the loop's guard.  Assertions (8), (7), and (6)
    are derived using the assignment rule going backwards from (8)
    to (6).  Assertions (4), (3), and (2) are again backwards
    applications of the assignment rule.

    Now that we've decorated the program it only remains to check that
    the uses of the consequence rule are correct -- i.e., that (1)
    implies (2), that (5) implies (6), and that (9) implies (10). This
    is indeed the case:
      - (1) ->> (2):  trivial, by algebra.
      - (5) ->> (6):  because [n <= X], we are guaranteed that the
        subtraction in (6) does not get zero-truncated.  We can
        therefore rewrite (6) as [n * Y + n + X - n] and cancel the
        [n]s, which results in the left conjunct of (5).
      - (9) ->> (10):  if [~ (n <= X)] then [X < n].  That's straightforward
        from high-school algebra.
    So, we have a valid decorated program. *)

(** **** Exercise: 3 stars, standard (slow_assignment)

    A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea.  Fill in valid decorations. *)
  (*
  forall m.
  {{ X = m }}
    Y := 0;
                  {{                                }} ->>
                  {{                                }}
    while X <> 0 do
                  {{                                }} ->>
                  {{                                }}
        X := X - 1;
                  {{                                }}
        Y := Y + 1
                  {{                                }}
    end
  {{                                 }} ->>
  {{ Y = m }}
  *)

(* Do not modify the following line: *)
Definition manual_grade_for_slow_assignment : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** From Decorated Programs to Formal Proofs *)

(** From an informal proof in the form of a decorated program, it is
    "easy in principle" to read off a formal proof using the Coq
    theorems corresponding to the Hoare Logic rules, but these proofs
    can be a bit long and fiddly. *)

(** Note that we do _not_ unfold the definition of [valid_hoare_triple]
    anywhere in this proof: the point of the game we're playing now
    is to use the Hoare rules as a self-contained logic for reasoning
    about programs. *)

(** For example... *)
Definition reduce_to_zero : com :=
  <{ while X <> 0 do
       X := X - 1
     end }>.

Theorem reduce_to_zero_correct' :
  {{True}}
    reduce_to_zero
  {{X = 0}}.
Proof.
  unfold reduce_to_zero.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  - apply hoare_while.
    + (* Loop body preserves loop invariant *)
      (* Massage precondition so [hoare_asgn] applies *)
      eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * (* Proving trivial implication (2) ->> (3) *)
        unfold assertion_sub, "->>". simpl. intros.
        exact I.
  - (* Loop invariant and negated guard imply post *)
    intros st [Inv GuardFalse].
    unfold bassertion in GuardFalse. simpl in GuardFalse.
    rewrite not_true_iff_false in GuardFalse.
    rewrite negb_false_iff in GuardFalse.
    apply eqb_eq in GuardFalse.
    apply GuardFalse.
Qed.

(** In [Hoare] we introduced a series of tactics named
    [assertion_auto] to automate proofs involving assertions.

    The following declaration introduces a more sophisticated tactic
    that will help with proving assertions throughout the rest of this
    chapter.  You don't need to understand the details, but briefly:
    it uses [split] repeatedly to turn all the conjunctions into
    separate subgoals, tries to use several theorems about booleans
    and (in)equalities, then uses [eauto] and [lia] to finish off as
    many subgoals as possible. What's left after [verify_assertion] does
    its thing should be just the "interesting parts" of the proof --
    which, if we're lucky, might be nothing at all! *)

Ltac verify_assertion :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassertion in *; unfold beval in *; unfold aeval in *;
  unfold assertion_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
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

(** This makes it pretty easy to verify [reduce_to_zero]: *)

Theorem reduce_to_zero_correct''' :
  {{True}}
    reduce_to_zero
  {{X = 0}}.
Proof.
  unfold reduce_to_zero.
  eapply hoare_consequence_post.
  - apply hoare_while.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * verify_assertion.
  - verify_assertion.
Qed.

(** This example shows that it is conceptually straightforward to read
    off the main elements of a formal proof from a decorated program.
    Indeed, the process is so straightforward that it can be
    automated, as we will see next. *)

(** **** Exercise: 2 stars, standard (division_example)

    Provide a formal proof for the decorated program we developed in the lecture. (Note that this example is slightly different from the division example given in this book chapter.) *)

Example division_example : forall (m : nat),
  {{ X = m }}
    Y := 0;
    while Z <= X do
      X := X - Z;
      Y := Y + 1
    end
  {{ Z * Y + X = m /\ X < Z }}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (slow_assignment_formal)

    Turn the decorated program you provided for the [slow_assignment] exercise into a formal proof. *)

Example slow_assignment_formal : forall (m : nat),
  {{ X = m }}
    Y := 0;
    while X <> 0 do
      X := X - 1;
      Y := Y + 1
    end
  {{ Y = m }}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

  (* ####################################################### *)
(* ================================================================= *)
(** ** Example: Parity *)

(** Here is a cute way of computing the parity of a value initially
    stored in [X], due to Daniel Cristofani.

       {{ X = m }}
         while 2 <= X do
           X := X - 2
         end
       {{ X = parity m }}

    The [parity] function used in the specification is defined in
    Coq as follows: *)

    Fixpoint parity x :=
    match x with
    | 0 => 0
    | 1 => 1
    | S (S x') => parity x'
    end.

        (** The postcondition does not hold at the beginning of the loop,
      since [m = parity m] does not hold for an arbitrary [m], so we
      cannot hope to use that as a loop invariant.  To find a loop invariant
      that works, let's think a bit about what this loop does.  On each
      iteration it decrements [X] by [2], which preserves the parity of [X].
      So the parity of [X] does not change, i.e., it is invariant.  The initial
      value of [X] is [m], so the parity of [X] is always equal to the
      parity of [m]. Using [parity X = parity m] as an invariant we
      obtain the following decorated program:
    [[
        {{ X = m }} ->>                                         (a - OK)
        {{ parity X = parity m }}
          while 2 <= X do
                       {{ parity X = parity m /\ 2 <= X }} ->>  (c - OK)
                       {{ parity (X-2) = parity m }}
            X := X - 2
                       {{ parity X = parity m }}
          end
        {{ parity X = parity m /\ ~(2 <= X) }} ->>              (b - OK)
        {{ X = parity m }}
    ]]
      With this loop invariant, conditions (a), (b), and (c) are all
      satisfied. For verifying (b), we observe that, when [X < 2], we
      have [parity X = X] (we can easily see this in the definition of
      [parity]).  For verifying (c), we observe that, when [2 <= X], we
      have [parity X = parity (X-2)]. *)

        (** **** Exercise: 3 stars, standard (parity) *)
    (** Translate the above informal decorated program into a formal proof.

      Hint: There are actually several possible loop invariants that all
      lead to good proofs; one that leads to a particularly simple proof
      is [parity X = parity m] -- or more formally, using the
      [ap] operator to lift the application of the [parity] function
      into the syntax of assertions, [{{ ap parity X = parity m }}]. *)

        (** If you use the suggested loop invariant, you may find the following
      lemmas helpful (as well as [leb_complete] and [leb_correct]). *)

    Lemma parity_ge_2 : forall x,
    2 <= x ->
    parity (x - 2) = parity x.
    Proof.
    destruct x; intros; simpl.
    - reflexivity.
    - destruct x; simpl.
      + lia.
      + rewrite sub_0_r. reflexivity.
    Qed.

    Lemma parity_lt_2 : forall x,
    ~ 2 <= x ->
    parity x = x.
    Proof.
    induction x; intros; simpl.
    - reflexivity.
    - destruct x.
      + reflexivity.
      + lia.
    Qed.

    Theorem parity_correct : forall (m:nat),
    {{ X = m }}
      while 2 <= X do
        X := X - 2
      end
    {{  X = parity m }}.
    Proof.
    (* FILL IN HERE *) Admitted.
    (** [] *)

(* ################################################################# *)
(** * Formal Decorated Programs *)

(** Our informal conventions for decorated programs amount to a
    way of "displaying" Hoare triples, in which commands are annotated
    with enough embedded assertions that checking the validity of a
    triple is reduced to simple logical and algebraic calculations
    showing that some assertions imply others.

    In this section, we show that this presentation style can be made
    completely formal -- and indeed that checking the validity of
    decorated programs can be largely automated.  *)

(* ================================================================= *)
(** ** Syntax *)

(** The first thing we need to do is to formalize a variant of the
    syntax of Imp commands that includes embedded assertions, which
    we'll call "decorations."  We call the new commands _decorated
    commands_, or [dcom]s.

    The choice of exactly where to put assertions in the definition of
    [dcom] is a bit subtle.  The simplest thing to do would be to
    annotate every [dcom] with a precondition and postcondition --
    something like this... *)

Module DComFirstTry.

Inductive dcom : Type :=
| DCSkip (P : Assertion)
  (* {{ P }} skip {{ P }} *)
| DCSeq (P : Assertion) (d1 : dcom) (Q : Assertion)
        (d2 : dcom) (R : Assertion)
  (* {{ P }} d1 {{Q}}; d2 {{ R }} *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* etc. *)
| DCIf (P : Assertion) (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
| DCWhile (P : Assertion) (b : bexp)
          (P1 : Assertion) (d : dcom) (P2 : Assertion)
          (Q : Assertion)
| DCPre (P : Assertion) (d : dcom)
| DCPost (d : dcom) (Q : Assertion).

End DComFirstTry.

(** But this would result in _very_ verbose decorated programs with a
    lot of repeated annotations: even a simple program like
    [skip;skip] would be decorated like this,

        {{P}} ({{P}} skip {{P}}) ; ({{P}} skip {{P}}) {{P}}

    with pre- and post-conditions around each [skip], plus identical
    pre- and post-conditions on the semicolon! *)

(** In other words, we don't want both preconditions and
    postconditions on each command, because a sequence of two commands
    would contain redundant decorations--the postcondition of the
    first likely being the same as the precondition of the second.

    Instead, the formal syntax of decorated commands omits
    preconditions whenever possible, trying to embed just the
    postcondition. *)

(** - The [skip] command, for example, is decorated only with its
      postcondition

      skip {{ Q }}

      on the assumption that the precondition will be provided by the
      context.

      We carry the same assumption through the other syntactic forms:
      each decorated command is assumed to carry its own postcondition
      within itself but take its precondition from its context in
      which it is used. *)

(** - Sequences [d1 ; d2] need no additional decorations.

      Why?

      Because inside [d2] there will be a postcondition; this serves
      as the postcondition of [d1;d2].

      Similarly, inside [d1] there will also be a postcondition, which
      additionally serves as the _precondition_ for [d2]. *)

(** - An assignment [X := a] is decorated only with its postcondition:

      X := a {{ Q }}
*)

(** - A conditional [if b then d1 else d2] is decorated with a
      postcondition for the entire statement, as well as preconditions
      for each branch:

      if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }}
*)

(** - A loop [while b do d end] is decorated with its postcondition
      and a precondition for the body:

      while b do {{ P }} d end {{ Q }}

      The postcondition embedded in [d] serves as the loop invariant. *)

(** - Implications [->>] can be added as decorations either for a
      precondition

      ->> {{ P }} d

      or for a postcondition

      d ->> {{ Q }}

      The former is waiting for another precondition to be supplied by
      the context (e.g., [{{ P'}} ->> {{ P }} d]); the latter relies
      on the postcondition already embedded in [d]. *)

(** Putting this all together gives us the formal syntax of decorated
    commands: *)

Inductive dcom : Type :=
| DCSkip (Q : Assertion)
  (* skip {{ Q }} *)
| DCSeq (d1 d2 : dcom)
  (* d1 ; d2 *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* X := a {{ Q }} *)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
  (* if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }} *)
| DCWhile (b : bexp) (P : Assertion) (d : dcom)
          (Q : Assertion)
  (* while b do {{ P }} d end {{ Q }} *)
| DCPre (P : Assertion) (d : dcom)
  (* ->> {{ P }} d *)
| DCPost (d : dcom) (Q : Assertion)
  (* d ->> {{ Q }} *).

(** To provide the initial precondition that goes at the very top of a
    decorated program, we introduce a new type [decorated]: *)

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.

(** To avoid clashing with the existing [Notation]s for ordinary
    commands, we introduce these notations in a new grammar scope
    called [dcom]. *)

Declare Scope dcom_scope.
Notation "'skip' {{ P }}"
      := (DCSkip P)
           (in custom com at level 0, P constr) : dcom_scope.
Notation "l ':=' a {{ P }}"
      := (DCAsgn l a P)
           (in custom com at level 0, l constr at level 0,
            a custom com at level 85, P constr, no associativity)
           : dcom_scope.
Notation "'while' b 'do' {{ Pbody }} d 'end' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
           (in custom com at level 89, b custom com at level 99,
               Pbody constr, Ppost constr)
           : dcom_scope.
Notation "'if' b 'then' {{ P }} d 'else' {{ P' }} d' 'end' {{ Q }}"
      := (DCIf b P d P' d' Q)
           (in custom com at level 89, b custom com at level 99,
               P constr, P' constr, Q constr)
           : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
          (in custom com at level 12, right associativity, P constr)
          : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
           (in custom com at level 10, right associativity, P constr)
           : dcom_scope.
Notation " d ; d' "
      := (DCSeq d d')
           (in custom com at level 90, right associativity)
           : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
           (in custom com at level 91, P constr)
           : dcom_scope.

Local Open Scope dcom_scope.

Example dec0 : dcom :=
  <{ skip {{ True }} }>.
Example dec1 : dcom :=
  <{ while true do {{ True }} skip {{ True }} end {{ True }} }>.

(** Recall that you can [Set Printing All] to see how all that
    notation is desugared. *)
Set Printing All.
Print dec1.
Unset Printing All.

(** An example [decorated] program that decrements [X] to [0]: *)

Example dec_while : decorated :=
  <{
  {{ True }}
    while X <> 0
    do
                 {{ True /\ (X <> 0) }}
      X := X - 1
                 {{ True }}
    end
  {{ True /\  X = 0}} ->>
  {{ X = 0 }} }>.

(** **** Exercise: 2 stars, standard (parity_decorated_formal)

    Turn the decorated program from the parity exercise into a formal decorated program. *)

Definition parity_dec (m:nat) : decorated :=
  <{
  {{ X = m }} ->>
  {{ FILL_IN_HERE }}
    while 2 <= X do
                  {{ FILL_IN_HERE }} ->>
                  {{ FILL_IN_HERE }}
      X := X - 2
                  {{ FILL_IN_HERE }}
    end
  {{ FILL_IN_HERE }} ->>
  {{ X = parity m }} }>.

(* Do not modify the following line: *)
Definition manual_grade_for_parity_decorated_formal : option (nat*string) := None.
(** [] *)


(* 2025-05-07 14:00 *)
