(** * Hoare22: Hoare Logic, Part 2.2 *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Export Hoare21.
Include Hoare21.
Set Default Goal Selector "!".

Local Open Scope dcom_scope.

(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Fixpoint erase (d : dcom) : com :=
  match d with
  | DCSkip _           => CSkip
  | DCSeq d1 d2        => CSeq (erase d1) (erase d2)
  | DCAsgn X a _       => CAsgn X a
  | DCIf b _ d1 _ d2 _ => CIf b (erase d1) (erase d2)
  | DCWhile b _ d _    => CWhile b (erase d)
  | DCPre _ d          => erase d
  | DCPost d _         => erase d
  end.

Definition erase_d (dec : decorated) : com :=
  match dec with
  | Decorated P d => erase d
  end.

Example erase_while_ex :
    erase_d dec_while
  = <{while X <> 0 do X := X - 1 end}>.
Proof.
  unfold dec_while.
  reflexivity.
Qed.

(** It is also straightforward to extract the precondition and
    postcondition from a decorated program. *)

Definition precondition_from (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq _ d2              => post d2
  | DCAsgn _ _ Q            => Q
  | DCIf  _ _ _ _ _ Q       => Q
  | DCWhile _ _ _ Q         => Q
  | DCPre _ d               => post d
  | DCPost _ Q              => Q
  end.

Definition postcondition_from (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

Example precondition_from_while : precondition_from dec_while = True.
Proof. reflexivity. Qed.

Example postcondition_from_while : postcondition_from dec_while = (X = 0)%assertion.
Proof. reflexivity. Qed.

(** We can then express what it means for a decorated program to be
    correct as follows: *)

Definition outer_triple_valid (dec : decorated) :=
  {{precondition_from dec}} erase_d dec {{postcondition_from dec}}.

(** For example: *)

Example dec_while_triple_correct :
     outer_triple_valid dec_while
   =
     {{ True }}
       while X <> 0 do X := X - 1 end
     {{ X = 0 }}.
Proof. reflexivity. Qed.

(** The outer Hoare triple of a decorated program is just a [Prop];
    thus, to show that it is _valid_, we need to produce a proof of
    this proposition.

    We will do this by extracting "proof obligations" from the
    decorations sprinkled through the program.

    These obligations are often called _verification conditions_,
    because they are the facts that must be verified to see that the
    decorations are locally consistent and thus constitute a proof of
    validity of the outer triple. *)

(* ================================================================= *)
(** ** Extracting Verification Conditions *)

(** The function [verification_conditions] takes a decorated command
    [d] together with a precondition [P] and returns a _proposition_
    that, if it can be proved, implies that the triple

     {{P}} erase d {{post d}}

    is valid.

    It does this by walking over [d] and generating a big conjunction
    that includes

    - local consistency checks for each form of command, plus

    - uses of [->>] to bridge the gap between the assertions found
      inside a decorated command and the assertions imposed by the
      precondition from its context; these uses correspond to
      applications of the consequence rule. *)

(** _Local consistency_ is defined as follows... *)

(** - The decorated command

        skip {{Q}}

      is locally consistent with respect to a precondition [P] if
      [P ->> Q].
*)

(** - The sequential composition of [d1] and [d2] is locally
      consistent with respect to [P] if [d1] is locally consistent with
      respect to [P] and [d2] is locally consistent with respect to
      the postcondition of [d1]. *)

(** - An assignment

        X := a {{Q}}

      is locally consistent with respect to a precondition [P] if:

        P ->> Q [X |-> a]
*)

(** - A conditional

      if b then {{P1}} d1 else {{P2}} d2 end {{Q}}

      is locally consistent with respect to precondition [P] if

         (1) [P /\ b ->> P1]

         (2) [P /\ ~b ->> P2]

         (3) [d1] is locally consistent with respect to [P1]

         (4) [d2] is locally consistent with respect to [P2]

         (5) [post d1 ->> Q]

         (6) [post d2 ->> Q]
*)
(** - A loop

      while b do {{Q}} d end {{R}}

      is locally consistent with respect to precondition [P] if:

         (1) [P ->> post d]

         (2) [post d /\ b ->> Q]

         (3) [post d /\ ~b ->> R]

         (4) [d] is locally consistent with respect to [Q]
*)

(** - A command with an extra assertion at the beginning

       --> {{Q}} d

      is locally consistent with respect to a precondition [P] if:

        (1) [P ->> Q]

        (1) [d] is locally consistent with respect to [Q]
*)

(** - A command with an extra assertion at the end

         d ->> {{Q}}

      is locally consistent with respect to a precondition [P] if:

        (1) [d] is locally consistent with respect to [P]

        (2) [post d ->> Q]
*)

(** With all this in mind, we can write is a _verification condition
    generator_ that takes a decorated command and reads off a
    proposition saying that all its decorations are locally
    consistent.

    Formally, since a decorated command is "waiting for its
    precondition" the main VC generator takes a [dcom] plus a given
    predondition as arguments.
*)

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((P /\ b) ->> P1)%assertion
      /\ ((P /\ ~ b) ->> P2)%assertion
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Q d R =>
      (* post d is both the loop invariant and the initial
         precondition *)
      (P ->> post d)
      /\ ((post d  /\ b) ->> Q)%assertion
      /\ ((post d  /\ ~ b) ->> R)%assertion
      /\ verification_conditions Q d
  | DCPre P' d =>
      (P ->> P')
      /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d
      /\ (post d ->> Q)
  end.

(** The following key theorem states that [verification_conditions]
    does its job correctly.  Not surprisingly, each of the Hoare Logic
    rules gets used at some point in the proof. *)

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} erase d {{post d}}.
Proof.
  induction d; intros; simpl in *.
  - (* Skip *)
    eapply hoare_consequence_pre.
      + apply hoare_skip.
      + assumption.
  - (* Seq *)
    destruct H as [H1 H2].
    eapply hoare_seq.
      + apply IHd2. apply H2.
      + apply IHd1. apply H1.
  - (* Asgn *)
    eapply hoare_consequence_pre.
      + apply hoare_asgn.
      + assumption.
  - (* If *)
    destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse] ] ] ] ].
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_consequence; eauto.
      + eapply hoare_consequence; eauto.
  - (* While *)
    destruct H as [Hpre [Hbody1 [Hpost1  Hd] ] ].
    eapply hoare_consequence; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  - (* Pre *)
    destruct H as [HP Hd].
    eapply hoare_consequence_pre; eauto.
  - (* Post *)
    destruct H as [Hd HQ].
    eapply hoare_consequence_post; eauto.
Qed.

(** Now that all the pieces are in place, we can define what it means
    to verify an entire program. *)

Definition verification_conditions_from
              (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.

(** This brings us to the main theorem of this section: *)

Corollary verification_conditions_correct : forall dec,
  verification_conditions_from dec ->
  outer_triple_valid dec.
Proof.
  intros [P d]. apply verification_correct.
Qed.

(* ================================================================= *)
(** ** More Automation *)

(** The propositions generated by [verification_conditions] are fairly
    big and contain many conjuncts that are essentially trivial. *)

Eval simpl in verification_conditions_from dec_while.
(* ==>
   ((fun _ : state => True) ->>
           (fun _ : state => True)) /\
   ((fun st : state => True /\ negb (st X =? 0) = true) ->>
           (fun st : state => True /\ st X <> 0)) /\
   ((fun st : state => True /\ negb (st X =? 0) <> true) ->>
           (fun st : state => True /\ st X = 0)) /\
   (fun st : state => True /\ st X <> 0) ->>
           (fun _ : state => True) [X |-> X - 1]) /\
   (fun st : state => True /\ st X = 0) ->>
           (fun st : state => st X = 0)
: Prop
*)

(** Fortunately, our [verify_assertion] tactic can generally take care of
    most or all of them. *)
Example vc_dec_while : verification_conditions_from dec_while.
Proof. verify_assertion. Qed.

(** To automate the overall process of verification, we can use
    [verification_correct] to extract the verification conditions, use
    [verify_assertion] to verify them as much as it can, and finally tidy
    up any remaining bits by hand.  *)
Ltac verify :=
  intros;
  apply verification_correct;
  verify_assertion.

(** Here's the final, formal proof that dec_while is correct. *)

Theorem dec_while_correct :
  outer_triple_valid dec_while.
Proof. verify. Qed.


(** Similarly, here is the formal decorated program for the "swapping
    by adding and subtracting" example that we saw earlier. *)

Definition swap_dec (m n:nat) : decorated :=
  <{
    {{ X = m /\ Y = n}} ->>
         {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
    X := X + Y
         {{ X - (X - Y) = n /\ X - Y = m }};
    Y := X - Y
         {{ X - Y = n /\ Y = m }};
    X := X - Y
    {{ X = n /\ Y = m}}
  }>.

Theorem swap_correct : forall m n,
  outer_triple_valid (swap_dec m n).
Proof. verify. Qed.

(** And here is the formal decorated version of the "positive
    difference" program from earlier: *)

Definition positive_difference_dec :=
  <{
    {{True}}
    if X <= Y then
          {{True /\ X <= Y}} ->>
          {{(Y - X) + X = Y \/ (Y - X) + Y = X}}
      Z := Y - X
          {{Z + X = Y \/ Z + Y = X}}
    else
          {{True /\ ~(X <= Y)}} ->>
          {{(X - Y) + X = Y \/ (X - Y) + Y = X}}
      Z := X - Y
          {{Z + X = Y \/ Z + Y = X}}
    end
    {{Z + X = Y \/ Z + Y = X}}
  }>.

Theorem positive_difference_correct :
  outer_triple_valid positive_difference_dec.
Proof. verify. Qed.

(** **** Exercise: 3 stars, standard (reverse_incorrect)

    Prove that the reverse implication of theorem [verification_correct] is not correct. *)

Theorem reverse_incorrect : ~ forall d P,
{{P}} erase d {{post d}} -> verification_conditions P d.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (if_minus_plus_correct)

    Here is a skeleton of the formal decorated version of the
    [if_minus_plus] program that we saw earlier.  Replace all
    occurrences of [FILL_IN_HERE] with appropriate assertions and fill
    in the proof (which should be just as straightforward as in the
    examples above). *)

Definition if_minus_plus_dec :=
  <{
  {{True}}
  if (X <= Y) then
              {{ FILL_IN_HERE }} ->>
              {{ FILL_IN_HERE }}
    Z := Y - X
              {{ FILL_IN_HERE }}
  else
              {{ FILL_IN_HERE }} ->>
              {{ FILL_IN_HERE }}
    Y := X + Z
              {{ FILL_IN_HERE }}
  end
  {{ Y = X + Z}} }>.

Theorem if_minus_plus_correct :
  outer_triple_valid if_minus_plus_dec.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (div_mod_outer_triple_valid)

    Fill in appropriate assertions for the division program from last week and prove it with the verify tactic. *)

Definition div_mod_dec' (m : nat) : decorated :=
  <{
  {{ X = m }} ->>
  {{ FILL_IN_HERE }}
    Y := 0
             {{ FILL_IN_HERE }};
    while Z <= X do
             {{ FILL_IN_HERE }} ->>
             {{ FILL_IN_HERE }}
      X := X - Z
             {{ FILL_IN_HERE }};
      Y := Y + 1
             {{ FILL_IN_HERE }}
    end
  {{ FILL_IN_HERE }} ->>
  {{ Z * Y + X = m /\ X < Z }} }>.

Theorem div_mod_outer_triple_valid : forall m,
  outer_triple_valid (div_mod_dec' m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Finding Loop Invariants *)

(** Once the outermost precondition and postcondition are
    chosen, the only creative part of a verifying program using Hoare
    Logic is finding the right loop invariants.  The reason this is
    difficult is the same as the reason that inductive mathematical
    proofs are:

    - Strengthening a _loop invariant_ means that you have a stronger
      assumption to work with when trying to establish the
      postcondition of the loop body, but it also means that the loop
      body's postcondition is stronger and thus harder to prove.

    - Similarly, strengthening an _induction hypothesis_ means that
      you have a stronger assumption to work with when trying to
      complete the induction step of the proof, but it also means that
      the statement being proved inductively is stronger and thus
      harder to prove.

    This section explains how to approach the challenge of finding
    loop invariants through a series of examples and exercises. *)

(* ================================================================= *)
(** ** Example: Slow Subtraction *)

(** The following program subtracts the value of [X] from the value of
    [Y] by repeatedly decrementing both [X] and [Y].  We want to verify its
    correctness with respect to the pre- and postconditions shown:

           {{ X = m /\ Y = n }}
             while X <> 0 do
               Y := Y - 1;
               X := X - 1
             end
           {{ Y = n - m }}
*)

(** To verify this program, we need to find an invariant [Inv] for the
    loop.  As a first step we can leave [Inv] as an unknown and build a
    _skeleton_ for the proof by applying the rules for local
    consistency, working from the end of the program to the beginning,
    as usual, and without any thinking at all yet. *)

(** This leads to the following skeleton:

        (1)    {{ X = m /\ Y = n }}  ->>                   (a)
        (2)    {{ Inv }}
                 while X <> 0 do
        (3)              {{ Inv /\ X <> 0 }}  ->>          (c)
        (4)              {{ Inv [X |-> X-1] [Y |-> Y-1] }}
                   Y := Y - 1;
        (5)              {{ Inv [X |-> X-1] }}
                   X := X - 1
        (6)              {{ Inv }}
                 end
        (7)    {{ Inv /\ ~ (X <> 0) }}  ->>                (b)
        (8)    {{ Y = n - m }}
*)
(** By examining this skeleton, we can see that any valid [Inv] will
    have to respect three conditions:
    - (a) it must be _weak_ enough to be implied by the loop's
      precondition, i.e., (1) must imply (2);
    - (b) it must be _strong_ enough to imply the program's postcondition,
      i.e., (7) must imply (8);
    - (c) it must be _preserved_ by a single iteration of the loop, assuming
      that the loop guard also evaluates to true, i.e., (3) must imply (4). *)

(** These conditions are actually independent of the particular
    program and specification we are considering: every loop
    invariant has to satisfy them.

    One way to find a loop invariant that simultaneously satisfies these
    three conditions is by using an iterative process: start with a
    "candidate" invariant (e.g., a guess or a heuristic choice) and
    check the three conditions above; if any of the checks fails, try
    to use the information that we get from the failure to produce
    another -- hopefully better -- candidate invariant, and repeat.

    For instance, in the reduce-to-zero example above, we saw that,
    for a very simple loop, choosing [True] as a loop invariant did the
    job.  Maybe it will work here too.  To find out, let's try
    instantiating [Inv] with [True] in the skeleton above and
    see what we get...

        (1)    {{ X = m /\ Y = n }} ->>                    (a - OK)
        (2)    {{ True }}
                 while X <> 0 do
        (3)                   {{ True /\ X <> 0 }} ->>     (c - OK)
        (4)                   {{ True }}
                   Y := Y - 1;
        (5)                   {{ True }}
                   X := X - 1
        (6)                   {{ True }}
                 end
        (7)    {{ True /\ ~(X <> 0) }} ->>                 (b - WRONG!)
        (8)    {{ Y = n - m }}

    While conditions (a) and (c) are trivially satisfied,
    (b) is wrong: it is not the case that [True /\ X = 0] (7)
    implies [Y = n - m] (8).  In fact, the two assertions are
    completely unrelated, so it is very easy to find a counterexample
    to the implication (say, [Y = X = m = 0] and [n = 1]).

    If we want (b) to hold, we need to strengthen the loop invariant so
    that it implies the postcondition (8).  One simple way to do
    this is to let the loop invariant _be_ the postcondition.  So let's
    return to our skeleton, instantiate [Inv] with [Y = n - m], and
    try checking conditions (a) to (c) again.

    (1)    {{ X = m /\ Y = n }} ->>                        (a - WRONG!)
    (2)    {{ Y = n - m }}
             while X <> 0 do
    (3)                     {{ Y = n - m /\ X <> 0 }} ->>  (c - WRONG!)
    (4)                     {{ Y - 1 = n - m }}
               Y := Y - 1;
    (5)                     {{ Y = n - m }}
               X := X - 1
    (6)                     {{ Y = n - m }}
             end
    (7)    {{ Y = n - m /\ ~(X <> 0) }} ->>                (b - OK)
    (8)    {{ Y = n - m }}

    This time, condition (b) holds trivially, but (a) and (c) are
    broken. Condition (a) requires that (1) [X = m /\ Y = n]
    implies (2) [Y = n - m].  If we substitute [Y] by [n] we have to
    show that [n = n - m] for arbitrary [m] and [n], which is not
    the case (for instance, when [m = n = 1]).  Condition (c) requires
    that [n - m - 1 = n - m], which fails, for instance, for [n = 1]
    and [m = 0]. So, although [Y = n - m] holds at the end of the loop,
    it does not hold from the start, and it doesn't hold on each
    iteration; it is not a correct loop invariant.

    This failure is not very surprising: the variable [Y] changes
    during the loop, while [m] and [n] are constant, so the assertion
    we chose didn't have much chance of being a loop invariant!

    To do better, we need to generalize (7) to some statement that is
    equivalent to (8) when [X] is [0], since this will be the case
    when the loop terminates, and that "fills the gap" in some
    appropriate way when [X] is nonzero.  Looking at how the loop
    works, we can observe that [X] and [Y] are decremented together
    until [X] reaches [0].  So, if [X = 2] and [Y = 5] initially,
    after one iteration of the loop we obtain [X = 1] and [Y = 4];
    after two iterations [X = 0] and [Y = 3]; and then the loop stops.
    Notice that the difference between [Y] and [X] stays constant
    between iterations: initially, [Y = n] and [X = m], and the
    difference is always [n - m].  So let's try instantiating [Inv] in
    the skeleton above with [Y - X = n - m].

    (1)    {{ X = m /\ Y = n }} ->>                            (a - OK)
    (2)    {{ Y - X = n - m }}
             while X <> 0 do
    (3)                    {{ Y - X = n - m /\ X <> 0 }} ->>   (c - OK)
    (4)                    {{ (Y - 1) - (X - 1) = n - m }}
               Y := Y - 1;
    (5)                    {{ Y - (X - 1) = n - m }}
               X := X - 1
    (6)                    {{ Y - X = n - m }}
             end
    (7)    {{ Y - X = n - m /\ ~(X <> 0) }} ->>                (b - OK)
    (8)    {{ Y = n - m }}

    Success!  Conditions (a), (b) and (c) all hold now.  (To
    verify (c), we need to check that, under the assumption that
    [X <> 0], we have [Y - X = (Y - 1) - (X - 1)]; this holds for all
    natural numbers [X] and [Y].)

    Here is the final version of the decorated program: *)

Example subtract_slowly_dec (m : nat) (n : nat) : decorated :=
  <{
  {{ X = m /\  Y = n }} ->>
  {{ Y - X = n - m }}
    while X <> 0 do
                  {{ Y - X = n - m /\ X  <>  0 }} ->>
                  {{ (Y - 1) - (X - 1) = n - m }}
       Y := Y - 1
                  {{ Y - (X - 1) = n - m }} ;
       X := X - 1
                  {{ Y - X = n - m }}
    end
  {{ Y - X = n - m /\ X = 0 }} ->>
  {{ Y = n - m }} }>.

Theorem subtract_slowly_outer_triple_valid : forall m n,
  outer_triple_valid (subtract_slowly_dec m n).
Proof.
  verify. (* this grinds for a bit! *)
Qed.

(* ================================================================= *)
(** ** Example: Finding Square Roots *)

(** The following program computes the integer square root of [X]
    by naive iteration:

    {{ X=m }}
      Z := 0;
      while (Z+1)*(Z+1) <= X do
        Z := Z+1
      end
    {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
*)

(** As we did before, we can try to use the postcondition as a
    candidate loop invariant, obtaining the following decorated program:

    (1)  {{ X=m }} ->>               (a - second conjunct of (2) WRONG!)
    (2)  {{ 0*0 <= m /\ m<(0+1)*(0+1) }}
            Z := 0
    (3)            {{ Z*Z <= m /\ m<(Z+1)*(Z+1) }};
            while (Z+1)*(Z+1) <= X do
    (4)            {{ Z*Z<=m /\ m<(Z+1)*(Z+1)
                             /\ (Z+1)*(Z+1)<=X }} ->>   (c - WRONG!)
    (5)            {{ (Z+1)*(Z+1)<=m /\ m<((Z+1)+1)*((Z+1)+1) }}
              Z := Z+1
    (6)            {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
            end
    (7)  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) /\ ~((Z+1)*(Z+1)<=X) }} ->>  (b - OK)
    (8)  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}

    This didn't work very well: conditions (a) and (c) both failed.
    Looking at condition (c), we see that the second conjunct of (4)
    is almost the same as the first conjunct of (5), except that (4)
    mentions [X] while (5) mentions [m]. But note that [X] is never
    assigned in this program, so we should always have [X=m]. We
    didn't propagate this information from (1) into the loop
    invariant, but we could!

    Also, we don't need the second conjunct of (8), since we can
    obtain it from the negation of the guard -- the third conjunct
    in (7) -- again under the assumption that [X=m].  This allows
    us to simplify a bit.

    So we now try [X=m /\ Z*Z <= m] as the loop invariant:

    {{ X=m }} ->>                                           (a - OK)
    {{ X=m /\ 0*0 <= m }}
      Z := 0
                 {{ X=m /\ Z*Z <= m }};
      while (Z+1)*(Z+1) <= X do
                 {{ X=m /\ Z*Z<=m /\ (Z+1)*(Z+1)<=X }} ->>  (c - OK)
                 {{ X=m /\ (Z+1)*(Z+1)<=m }}
        Z := Z + 1
                 {{ X=m /\ Z*Z<=m }}
      end
    {{ X=m /\ Z*Z<=m /\ ~((Z+1)*(Z+1)<=X) }} ->>            (b - OK)
    {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}

    This works, since conditions (a), (b), and (c) are now all
    trivially satisfied.

    Very often, when a variable is used in a loop in a read-only
    fashion (i.e., it is referred to by the program or by the
    specification and it is not changed by the loop), it is necessary
    to record the fact that it doesn't change in the loop invariant. *)

(** **** Exercise: 2 stars, standard (sqrt_dec)

    Translate the above informal decorated program into a formal one
    and prove it correct. *)

Definition sqrt_dec (m:nat) : decorated :=
  <{
    {{ X = m }} ->>
    {{ FILL_IN_HERE }}
      Z := 0
                   {{ FILL_IN_HERE }};
      while ((Z+1)*(Z+1) <= X) do
                   {{ FILL_IN_HERE }} ->>
                   {{ FILL_IN_HERE }}
        Z := Z + 1
                   {{ FILL_IN_HERE }}
      end
    {{ FILL_IN_HERE }} ->>
    {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
  }>.

Theorem sqrt_correct : forall m,
  outer_triple_valid (sqrt_dec m).
Proof. (* FILL IN HERE *) Admitted.

(* ================================================================= *)
(** ** Example: Squaring *)

(** Here is a program that squares [X] by repeated addition:

  {{ X = m }}
    Y := 0;
    Z := 0;
    while Y <> X  do
      Z := Z + X;
      Y := Y + 1
    end
  {{ Z = m*m }}
*)

(** The first thing to note is that the loop reads [X] but doesn't
    change its value. As we saw in the previous example, it can be a good idea
    in such cases to add [X = m] to the loop invariant.  The other thing
    that we know is often useful in the loop invariant is the postcondition,
    so let's add that too, leading to the candidate loop invariant
    [Z = m * m /\ X = m].

    {{ X = m }} ->>                                       (a - WRONG)
    {{ 0 = m*m /\ X = m }}
      Y := 0
                   {{ 0 = m*m /\ X = m }};
      Z := 0
                   {{ Z = m*m /\ X = m }};
      while Y <> X do
                   {{ Z = m*m /\ X = m /\ Y <> X }} ->>   (c - WRONG)
                   {{ Z+X = m*m /\ X = m }}
        Z := Z + X
                   {{ Z = m*m /\ X = m }};
        Y := Y + 1
                   {{ Z = m*m /\ X = m }}
      end
    {{ Z = m*m /\ X = m /\ ~(Y <> X) }} ->>               (b - OK)
    {{ Z = m*m }}

    Conditions (a) and (c) fail because of the [Z = m*m] part.  While
    [Z] starts at [0] and works itself up to [m*m], we can't expect
    [Z] to be [m*m] from the start.  If we look at how [Z] progresses
    in the loop, after the 1st iteration [Z = m], after the 2nd
    iteration [Z = 2*m], and at the end [Z = m*m].  Since the variable
    [Y] tracks how many times we go through the loop, this leads us to
    derive a new loop invariant candidate: [Z = Y*m /\ X = m].

    {{ X = m }} ->>                                        (a - OK)
    {{ 0 = 0*m /\ X = m }}
      Y := 0
                    {{ 0 = Y*m /\ X = m }};
      Z := 0
                    {{ Z = Y*m /\ X = m }};
      while Y <> X do
                    {{ Z = Y*m /\ X = m /\ Y <> X }} ->>   (c - OK)
                    {{ Z+X = (Y+1)*m /\ X = m }}
        Z := Z + X
                    {{ Z = (Y+1)*m /\ X = m }};
        Y := Y + 1
                    {{ Z = Y*m /\ X = m }}
      end
    {{ Z = Y*m /\ X = m /\ ~(Y <> X) }} ->>                (b - OK)
    {{ Z = m*m }}

    This new loop invariant makes the proof go through: all three
    conditions are easy to check.

    It is worth comparing the postcondition [Z = m*m] and the [Z =
    Y*m] conjunct of the loop invariant. It is often the case that one has
    to replace parameters with variables -- or with expressions
    involving both variables and parameters, like [m - Y] -- when
    going from postconditions to loop invariants. *)

(** [] *)

(* ================================================================= *)
(** ** Exercise: Two Loops *)

(** **** Exercise: 3 stars, standard (two_loops)

    Here is a pretty inefficient way of adding 3 numbers:

     X := 0;
     Y := 0;
     Z := c;
     while X <> a do
       X := X + 1;
       Z := Z + 1
     end;
     while Y <> b do
       Y := Y + 1;
       Z := Z + 1
     end

    Show that it does what it should by completing the
    following decorated program. If done correctly, the [verify] tactic should be able to find the proof automatically.
*)
Definition two_loops_dec (a b c : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ FILL_IN_HERE }}
      X := 0
                   {{ FILL_IN_HERE }};
      Y := 0
                   {{ FILL_IN_HERE }};
      Z := c
                   {{ FILL_IN_HERE }};
      while X <> a do
                   {{ FILL_IN_HERE }} ->>
                   {{ FILL_IN_HERE }}
        X := X + 1
                   {{ FILL_IN_HERE }};
        Z := Z + 1
                   {{ FILL_IN_HERE }}
      end
                   {{ FILL_IN_HERE }} ->>
                   {{ FILL_IN_HERE }};
      while Y <> b do
                   {{ FILL_IN_HERE }} ->>
                   {{ FILL_IN_HERE }}
        Y := Y + 1
                   {{ FILL_IN_HERE }};
        Z := Z + 1
                   {{ FILL_IN_HERE }}
      end
    {{ FILL_IN_HERE }} ->>
    {{ Z = a + b + c }}
  }>.

Theorem two_loops : forall a b c,
  outer_triple_valid (two_loops_dec a b c).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Exercise: Minimum *)

(** **** Exercise: 3 stars, standard (minimum_correct)

    Fill in decorations for the following program and prove them
    correct.  Be careful about mathematical
    reasoning involving natural numbers, especially subtraction.

    Also, remember that applications of Coq functions in assertions
    need an [ap] or [ap2] to be parsed correctly.  E.g., [min a b]
    needs to be written [ap2 min a b] in an assertion.

    You may find [andb_true_eq] useful (perhaps after using symmetry
    to get an equality the right way around). *)

Definition minimum_dec (a b : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ FILL_IN_HERE }}
      X := a
             {{ FILL_IN_HERE }};
      Y := b
             {{ FILL_IN_HERE }};
      Z := 0
             {{ FILL_IN_HERE }};
      while X <> 0 && Y <> 0 do
             {{ FILL_IN_HERE }} ->>
             {{ FILL_IN_HERE }}
        X := X - 1
             {{ FILL_IN_HERE }};
        Y := Y - 1
             {{ FILL_IN_HERE }};
        Z := Z + 1
             {{ FILL_IN_HERE }}
      end
    {{ FILL_IN_HERE }} ->>
    {{ Z = min a b }}
  }>.

Theorem minimum_correct : forall a b,
  outer_triple_valid (minimum_dec a b).
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Exercise: Factorial *)

(** **** Exercise: 4 stars, advanced, optional (factorial_correct)

    Recall that [n!] denotes the factorial of [n] (i.e., [n! =
    1*2*...*n]).  Formally, the factorial function is defined
    recursively in the Coq standard library in a way that is
    equivalent to the following:

    Fixpoint fact (n : nat) : nat :=
      match n with
      | O => 1
      | S n' => n * (fact n')
      end.
*)

Compute fact 5. (* ==> 120 *)

(** First, write the Imp program [factorial] that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y].
*)

(** Using your definition [factorial] as a
    guide, write a formal decorated program [factorial_dec] that
    implements the factorial function.  Hint: recall the use of [ap]
    in assertions to apply a function to an Imp variable.

    Fill in the blanks and finish the proof of correctness. As with minimum, bear in mind that we are working with natural numbers, for which both division
    and subtraction can behave differently than with real numbers.
    Excluding both operations from your loop invariant is advisable!

    Then state a theorem named [factorial_correct] that says
    [factorial_dec] is correct, and prove the theorem.  If all goes
    well, [verify] will leave you with just two subgoals, each of
    which requires establishing some mathematical property of [fact],
    rather than proving anything about your program.

    Hint: if those two subgoals become tedious to prove, give some
    thought to how you could restate your assertions such that the
    mathematical operations are more amenable to manipulation in Coq.
    For example, recall that [1 + ...] is easier to work with than
    [... + 1]. *)

Example factorial_dec (m:nat) : decorated
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(* FILL IN HERE *)

Theorem factorial_correct: forall m,
  outer_triple_valid (factorial_dec m).
Proof. (* FILL IN HERE *) Admitted.
(** [] *)


(* ================================================================= *)
(** ** Exercise: Power Series *)

(** **** Exercise: 4 stars, standard, optional (dpow2)

    Here is a program that computes the series:
    [1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1]

    X := 0;
    Y := 1;
    Z := 1;
    while X <> m do
      Z := 2 * Z;
      Y := Y + Z;
      X := X + 1
    end

    Turn this into a decorated program and prove it correct. *)

Fixpoint pow2 n :=
  match n with
  | 0 => 1
  | S n' => 2 * (pow2 n')
  end.

Definition dpow2_dec (n : nat) :=
  <{
    {{ True }} ->>
    {{ FILL_IN_HERE }}
      X := 0
               {{ FILL_IN_HERE }};
      Y := 1
               {{ FILL_IN_HERE }};
      Z := 1
               {{ FILL_IN_HERE }};
      while X <> n do
               {{ FILL_IN_HERE }} ->>
               {{ FILL_IN_HERE }}
        Z := 2 * Z
               {{ FILL_IN_HERE }};
        Y := Y + Z
               {{ FILL_IN_HERE }};
        X := X + 1
               {{ FILL_IN_HERE }}
      end
    {{ FILL_IN_HERE }} ->>
    {{ Y = pow2 (n+1) - 1 }}
  }>.

(** Some lemmas that you may find useful... *)

Lemma pow2_plus_1 : forall n,
  pow2 (n+1) = pow2 n + pow2 n.
Proof.
  induction n; simpl.
  - reflexivity.
  - lia.
Qed.

Lemma pow2_le_1 : forall n, pow2 n >= 1.
Proof.
  induction n; simpl; [constructor | lia].
Qed.

(** The main correctness theorem: *)

Theorem dpow2_down_correct : forall n,
  outer_triple_valid (dpow2_dec n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced, optional (fib_eqn)

    The Fibonacci function is usually written like this:

      Fixpoint fib n :=
        match n with
        | 0 => 1
        | 1 => 1
        | _ => fib (pred n) + fib (pred (pred n))
        end.

   This doesn't pass Coq's termination checker, but here is a
   slightly clunkier definition that does: *)

Fixpoint fib n :=
  match n with
  | 0 => 1
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

(** Prove that [fib] satisfies the following equation.  You will need this
    as a lemma in the next exercise. *)

Lemma fib_eqn : forall n,
  n > 0 ->
  fib n + fib (pred n) = fib (1 + n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (fib)

    The following Imp program leaves the value of [fib n] in the
    variable [Y] when it terminates:

    X := 1;
    Y := 1;
    Z := 1;
    while X <> 1 + n do
      T := Z;
      Z := Z + Y;
      Y := T;
      X := 1 + X
    end

    Fill in the following definition of [dfib] and prove that it
    satisfies this specification:

      {{ True }} dfib {{ Y = fib n }}

    You will need many uses of [ap] in your assertions.
    If all goes well, your proof will be very brief.
*)

Definition T : string := "T".

Definition dfib (n : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ FILL_IN_HERE }}
    X := 1
                {{ FILL_IN_HERE }} ;
    Y := 1
                {{ FILL_IN_HERE }} ;
    Z := 1
                {{ FILL_IN_HERE }} ;
    while X <> 1 + n do
                  {{ FILL_IN_HERE }} ->>
                  {{ FILL_IN_HERE }}
      T := Z
                  {{ FILL_IN_HERE }};
      Z := Z + Y
                  {{ FILL_IN_HERE }};
      Y := T
                  {{ FILL_IN_HERE }};
      X := 1 + X
                  {{ FILL_IN_HERE }}
    end
    {{ FILL_IN_HERE }} ->>
    {{ Y = fib n }}
   }>.

Theorem dfib_correct : forall n,
  outer_triple_valid (dfib n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (improve_dcom)

    The formal decorated programs defined in this section are intended
    to look as similar as possible to the informal ones defined
    earlier.  If we drop this requirement, we can eliminate almost all
    annotations, just requiring final postconditions and loop
    invariants to be provided explicitly.  Do this -- i.e., define a
    new version of dcom with as few annotations as possible and adapt
    the rest of the formal development leading up to the
    [verification_correct] theorem. *)

(* FILL IN HERE

    [] *)

(* ################################################################# *)
(** * Weakest Preconditions *)

(** Some preconditions are more interesting than others.
    For example, the Hoare triple

      {{ False }}  X := Y + 1  {{ X <= 5 }}

    is _not_ very interesting: although it is perfectly valid , it
    tells us nothing useful.  Since the precondition isn't
    satisfied by any state, it doesn't describe any situations where
    we can use the command [X := Y + 1] to achieve the postcondition
    [X <= 5].

    By contrast,

      {{ Y <= 4 /\ Z = 0 }}  X := Y + 1 {{ X <= 5 }}

    has a useful precondition: it tells us that, if we can somehow
    create a situation in which we know that [Y <= 4 /\ Z = 0], then
    running this command will produce a state satisfying the
    postcondition.  However, this precondition is not as useful as it
    could be, because the [Z = 0] clause in the precondition actually
    has nothing to do with the postcondition [X <= 5].

    The _most_ useful precondition for this command is this one:

      {{ Y <= 4 }}  X := Y + 1  {{ X <= 5 }}

    The assertion [Y <= 4] is called the _weakest precondition_ of
    [X := Y + 1] with respect to the postcondition [X <= 5]. *)

(** Assertion [Y <= 4] is a _weakest precondition_ of command [X :=
    Y + 1] with respect to postcondition [X <= 5].  Think of _weakest_
    here as meaning "easiest to satisfy": a weakest precondition is
    one that as many states as possible can satisfy. *)

(** [P] is a weakest precondition of command [c] for postcondition [Q]
    if

      - [P] is a precondition, that is, [{{P}} c {{Q}}]; and
      - [P] is at least as weak as all other preconditions, that is,
        if [{{P'}} c {{Q}}] then [P' ->> P].
 *)

(** Note that weakest preconditions need not be unique.  For
    example, [Y <= 4] was a weakest precondition above, but so are the
    logically equivalent assertions [Y < 5], [Y <= 2 * 2], etc.
    It is easy to show that any two weakest preconditions [P] and [P']
    of a command [c] with respect to postcondition [Q] are logically
    equivalent; that is, [P <<->> P']. *)

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

(** **** Exercise: 2 stars, standard (wp)

    What are weakest preconditions of the following commands
    for the following postconditions?

  1) {{ ? }}  skip  {{ X = 5 }}

  2) {{ ? }}  X := Y + Z {{ X = 5 }}

  3) {{ ? }}  X := Y  {{ X = Y }}

  4) {{ ? }}
     if X = 0 then Y := Z + 1 else Y := W + 2 end
     {{ Y = 5 }}

  5) {{ ? }}
     X := 5
     {{ X = 0 }}

  6) {{ ? }}
     while true do X := 0 end
     {{ X = 0 }}
*)
(* FILL IN HERE *)
(* Do not modify the following line: *)
Definition manual_grade_for_wp : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, advanced (is_wp_example)

    Prove formally, using the definition of [valid_hoare_triple], that [Y <= 4]
    is indeed a weakest precondition of [X := Y + 1] with respect to
    postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (Y <= 4) <{X := Y + 1}> (X <= 5).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced, optional (hoare_asgn_weakest)

    Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) <{ X := a }> Q.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced, optional (hoare_havoc_weakest)

    Show that your [havoc_pre] function from the [himp_hoare] exercise
    in the [Hoare] chapter returns a weakest precondition. *)
Module Himp2.
Import Himp.

Lemma hoare_havoc_weakest : forall (P Q : Assertion) (X : string),
  {{ P }} havoc X {{ Q }} ->
  P ->> havoc_pre X Q.
Proof.
(* FILL IN HERE *) Admitted.
End Himp2.
(** [] *)

(* 2025-05-14 18:56 *)
