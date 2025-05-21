(** * Total: Total Correctness *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.
From Coq Require Import Arith.
From Coq Require Import EqNat.
From Coq Require Import PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import Hoare11.
From PLF Require Import Hoare12.
Set Default Goal Selector "!".

(* ################################################################# *)
(** * Total correctness, Informally *)

(** _Total correctness_ is a claim about the state before and
    after executing a command. The standard notation is

      [P] c [Q]

    meaning:

      - If command [c] begins execution in a state satisfying assertion [P],
      - then [c] terminates in some final state which satisfies the
        assertion [Q].

    Like for Hoare triples, assertion [P] is called the _precondition_, and [Q]
    is the _postcondition_.

    Notice that _Total Correctness_ is a stronger claim than a _Hoare triple_
    since for total correctness we need to prove that the program [c] terminates
    and that the final state satisfies the post-condition, while for Hoare
    triples the post-condition only holds _if_ the program terminates.
    This is why _Hoare Triples_ are also called _Partial correctness_.

    Because single and double brackets are already used for other things, we'll
    write Total Correctness with vertical bars:

       |P| c |Q|
*)

(** For example, [|X = 0| X := X + 1 |X = 1|] is valid Total Correctness judgement,
    stating when executed in a state in which [X = 0], command [X := X + 1]
    terminates in a state with [X = 1] *)

(** **** Exercise: 1 star, standard, optional (total)

    Paraphrase the following Total Correctness statement in English,
    and tell if there are _valid_ -- i.e., is the claimed relation between
    [P], [c], and [Q] true?

   1) |True| c |X = 5|

   2) |X <= Y| c |Y <= X|

   3) |True| c |False|

   4) |False| skip |True|

   5) |True| while true do skip end |False|

   6) |X = 0|
        while X = 0 do X := X + 1 end
      |X = 1|

*)
(* FILL IN HERE

    [] *)

(* ################################################################# *)
(** * Total correctness, Formally *)

(** We can formalize valid Total Correctness in Coq as follows: *)

Definition valid_total
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st, (P st) -> exists st',  st =[ c ]=> st' /\  (Q st').

(** And add a notation for Total Correctness *)

Hint Unfold valid_total : core.

Declare Scope total_spec_scope.

Notation "| P | c | Q |" := (valid_total P c Q)
                              (at level 90, c custom com at level 99)
                                  : total_spec_scope.

Open Scope total_spec_scope.

(** We start by proving that Total Correctness is equivalent to having both a
    _Hoare Triple_ {P} c {Q} and a proof that the program terminates under the
    assumption that the precondition [P] holds. *)

Lemma hoare_total P Q c :
 |P| c |Q| <->
 ({{P}} c {{Q}} /\
    forall st ,  P st -> (exists st', st =[ c ]=> st')).
Proof.
  split.
    + intros Ht;split.
     * intros st st' Heval1 HPre.
       specialize (Ht st HPre) as [st'' (Heval2 & Hq)].
       rewrite (ceval_deterministic c _ _ _ Heval1 Heval2).
       assumption.
     * intros st HPre.
       specialize (Ht st HPre) as [st'' (Heval2 & Hq)].
       eauto.
  + intros [Hp Hf] st HPre.
    specialize (Hf st HPre) as [st' He].
    exists st'. split.
    * assumption.
    * apply (Hp st);assumption.
Qed.

(* ################################################################# *)
(** * Proof Rules *)

(** The goal of Total Correctness is, like for Hoare Logic, to provide
    a _compositional_ method for proving the validity of specific triples.
    To this end, in the sections below, we'll introduce a rule for reasoning
    about each of the different syntactic forms of commands in Imp.

    Most rules are close to the rules of Hoare Logic, differing only in
    notation. Only the rule for _while_ will require some thinking and new
    concepts. This is to be expected, since the _while_ instruction is the only
    instruction in the _Imp_ language which can introduce non-termination.
 *)

(* ================================================================= *)
(** ** Skip *)

(** Since [skip] doesn't change the state, it preserves any
    assertion [P] and is anyway terminating:

      --------------------  (total_skip)
      | P | skip | P |
*)

Theorem total_skip : forall P,
     |P| skip |P|.
Proof.
  intros P st Pre. exists st.
  split;[apply E_Skip | assumption].
Qed.

(* ================================================================= *)
(** ** Sequencing *)

(** If command [c1] is executed in a state where [P] holds and terminates
    in a state where [Q] holds, and command [c2] is execuetd in a state where
    [Q] holds and terminates in a state where [R] holds, then
    executing [c1] followed by [c2] in a state where [P] holds will terminate
    in a state where [R] holds:

        | P | c1 | Q |
        | Q | c2 | R |
       ----------------------  (total_seq)
       | P | c1;c2 | R |
*)

Theorem total_seq : forall P Q R c1 c2,
     |Q| c2 |R| ->
     |P| c1 |Q| ->
     |P| c1; c2 |R|.
Proof.
  intros P Q R c1 c2 H2 H1 st Pre.
  specialize (H1 st Pre) as [st'' (He1 & Hq1)].
  specialize (H2 st'' Hq1) as [st' (He2 & Hq2)].
  exists st'.
  split;[eapply E_Seq;eauto| assumption].
Qed.

(* ================================================================= *)
(** ** Assignment *)

(** Since the evaluation of an expression
    and memory update always terminate, [X:=a]
    will always terminate. Moreover, like for _Hoare Logic_ we
    can use the substitution operation for the
    the proof rule for assignment:

       ----------------------  (total_asgn)
       | P[X |-> a] | X:= a | P |

 *)

Theorem total_asgn : forall Q X (a:aexp),
  |Q [X |-> a] | X := a |Q|.
Proof.
  intros Q X a st HQ.
  exists (X !-> ((a:Aexp) st); st).
  split;[apply E_Asgn; reflexivity | assumption].
Qed.

(* ================================================================= *)
(** ** Consequence *)

(** Like for _Hoare Logic_, we need for _Total Correctness_ a rule that allows
    weakening the precondition and strengthening the postcondition.


                |P'| c |Q'|
            P ->> P'    Q' ->> Q
         -----------------------------   (total_conseq)
                |P| c |Q|
*)

(** The proof of this rule is done in three steps. First, we prove the rule for
    weakening the preconditon. Second, we prove the rule for strengthening
    the postcondition. Lastly, we combine the two previous rules into one rule.
 *)

Theorem total_consequence_pre : forall (P P' Q : Assertion) c,
  |P'| c |Q| ->
  P ->> P' ->
  |P| c |Q|.
Proof.
  unfold valid_total, "->>".
  intros P P' Q c Hhoare Himp st Hpre.
  apply Hhoare with (st := st).
  apply Himp. assumption.
Qed.

Theorem total_consequence_post : forall (P Q Q' : Assertion) c,
  |P| c |Q'| ->
  Q' ->> Q ->
  |P| c |Q|.
Proof.
  unfold valid_total, "->>".
  intros P Q Q' c Hhoare Himp st Hpre.
  specialize (Hhoare st Hpre) as [st' (H1 & H2)].
  exists st'.
  split;[assumption | apply Himp;assumption].
Qed.

Theorem total_consequence : forall (P P' Q Q' : Assertion) c,
  |P'| c |Q'| ->
  P ->> P' ->
  Q' ->> Q ->
  |P| c |Q|.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply total_consequence_pre with (P' := P').
  - apply total_consequence_post with (Q' := Q'); assumption.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Conditionals

    If command [c1] is executed in a state where [P /\ b] holds and terminates
    in a state where [Q] holds, and, command [c2] is execuetd in a state where
    [P /\ ~b] holds and terminates in a state where [Q] holds, then
    executing the conditon in a state where [P] holds will terminate
    in a state where [R] holds:

              |P /\ b| c1 |Q|
              |P /\~b| c2 |Q|
      ---------------------------- (total_If)
      |P| if b then c1 else c2 |Q|
*)

Theorem total_if : forall P Q (b:bexp) c1 c2,
  | P /\ b | c1 |Q| ->
  | P /\ ~ b| c2 |Q| ->
  |P| if b then c1 else c2 end |Q|.
Proof.
  intros P Q b c1 c2 HTrue HFalse st HP.
  destruct (beval st b) eqn: Hb.
  * assert (HPTrue: P st /\ bassertion b st);[split;assumption|].
    specialize (HTrue st HPTrue) as [st' (He & Hq)].
    exists st'.
    split;[apply E_IfTrue;assumption | assumption].
  * assert (HPFalse: P st /\ ~bassertion b st);
    [split;[assumption|apply bexp_eval_false;assumption] |].
    specialize (HFalse st HPFalse) as [st' (He & Hq)].
    exists st'.
    split;[apply E_IfFalse;assumption | assumption].
Qed.

(* ================================================================= *)
(** ** While Loops *)

(** This is the hard case. In this rule, in addition to prove that
    the loop invariant is preseved by the loop body, one also proves
    that the loop terminates. To prove termination we will use
    a so called termination measure. The value [m]
    of the measure must strictly decreases with respect to a well-founded
    relation < on some domain set D during each iteration of the loop.
    Since < is well-founded, a strictly decreasing
    chain of members of D can have only finite length. Therefore, the loop
    cannot keep decreasing forever. Example of well-founded relation,
    is the usual order < on natural numbers N. However, the usual order <
    is not well-founded neither on the integers Z nor on positive real
    numbers R+.

    Using the measure [m] we can give a prove rule for the loop command of
    Imp. To keep track of the value of the measure in the initial state, we
    introduce a variable [z] and assign it to the mesure in the precondition.
    In the postcondition we ensure that the value of the measure in the
    resulting state satisfies the relation < with respect to the value
    of the measure in the initial state ([z]).


         forall z, |P /\ b /\ z = m | c |P /\ m < z|
         ------------------------------------------- (total_while)
              |P| while b do c end |P /\ ~b|
*)

(** For simplicity, we will consider the domain of natural numbers
    and define the measure as a function from state to natural numbers.
 **)

Definition measure : Type := state -> nat.

(** The measure can be seen as a natural number we assign to a state at every
    iteration of the loop. If we make sure that this value strictly decreases
    with each iteration, we can be sure that the loop terminates i.e.
    the loop can only do a finate number of iteration. This means,
    that after a certain number of iteration the loop condition must be false.
    We will use this fact in the proof of correctness of the while rule by
    defining a _unroll_ function which unroll the loop. By selecting the
    right number of unrolling we will be able to
    show that the loop condition will get false and thus the loop terminate,
    otherwise we have a contradition.

    The following definition of the _unroll_ function may look not natural,
    but is convenient for proofs by induction.
 **)

Fixpoint unroll (n: nat) (b: bexp) (p: com) :=
  match n with
  | 0 => CSkip
  | S n => CSeq (unroll n b p) (CIf b p CSkip)
  end.

(** We can prove certain properties of the _unroll_ function
    that will be important for what follows. One of these properties
    is that if the loop body terminates, preserves the loop invariant [P], and
    a measure decreases, then the command produced by _unroll_
    terminates and preserves the invariant [P]. In addition, after the command
    produced by _unroll_ if the loop condition is true, the measure of the
    resulting state is smaller then the measure of the inital state minus
    the number of unrolling. This is very important for the proof by
    contradiction.

      forall z, |P /\ b /\ z = m | c |P /\ m < z|
      --------------------------------------------
      forall z, |P /\ m = z /\ b| unroll n b c |P /\ (b -> m <= z - n)|
*)

Lemma total_unroll_c P var c b:
  (forall z: nat,
      let Pre := (fun st => P st /\ var st = z /\ bassertion b st) in
      let Post := (fun st' => P st' /\ var st' < z) in
      |Pre| c |Post|) ->
  forall n z,
    let Pre := (fun st => P st /\ var st = z /\ bassertion b st) in
    let Post := (fun st' => P st' /\ (bassertion b st' -> var st' <= z - n)) in
    |Pre| (unroll n b c) |Post|.
Proof.
  intros. unfold Pre, Post. simpl. clear Pre Post.
  induction n;intros st HPre.
  - exists st. simpl.
    split.
    + apply E_Skip.
    + destruct HPre.
      split;[assumption| intros;subst;Lia.lia].
  - specialize (IHn st HPre) as [st' (He & HPre' & Hm')].
    destruct (beval st' b) eqn : Hbst'.
    + specialize (Hm' Logic.eq_refl).
      assert (HPrex : P st' /\ var st' = var st' /\ bassertion b st');
      [split;[assumption |]; split;[apply Logic.eq_refl| assumption] | ].
      specialize (H (var st') st' HPrex) as [st'' (He'' & Hq'')].
      exists st'' ;simpl.
      split.
      * eapply E_Seq.
        -- apply He.
        -- apply E_IfTrue;[assumption|apply He''].
      * split;[apply Hq'' | intros; Lia.lia].
    + exists st';simpl.
      split.
      * eapply E_Seq.
        -- apply He.
        -- apply E_IfFalse ;[assumption| apply E_Skip].
      * split.
        -- apply HPre'.
        -- intros. rewrite H0 in Hbst'. inversion Hbst'.
Qed.

(** We can define an auxiliary lemma _aux_ that avoids making an assertion in
    the proof, and making the proof shorter.
 *)

Lemma aux P (var: measure) z b st :
  P st -> var st = z -> bassertion b st ->
  P st /\ var st = z /\ bassertion b st.
Proof.
  split;[assumption |split;assumption].
Qed.

Lemma total_unroll_c' P var c b:
  (forall z: nat,
      let Pre := (fun st => P st /\ var st = z /\ bassertion b st) in
      let Post := (fun st' => P st' /\ var st' < z) in
      |Pre| c |Post|) ->
  forall n z,
    let Pre := (fun st => P st /\ var st = z /\ bassertion b st) in
    let Post := (fun st' => P st' /\ (bassertion b st' -> var st' <= z - n)) in
    |Pre| (unroll n b c) |Post|.
Proof.
  intros. unfold Pre, Post. simpl. clear Pre Post.
  induction n;intros st HPre.
  - exists st. simpl.
    split.
    + apply E_Skip.
    + destruct HPre.
      split;[assumption| intros;subst;Lia.lia].
  - specialize (IHn st HPre) as [st' (He & HPre' & Hm')].
    destruct (beval st' b) eqn : Hbst'.
    + specialize (Hm' Logic.eq_refl).
      specialize (aux _ var (var st') b st' HPre' Logic.eq_refl Hbst') as HPrex.
      specialize (H (var st') st' HPrex) as [st'' (He'' & Hq'')].
      exists st'' ;simpl.
      split.
      * eapply E_Seq.
        -- apply He.
        -- apply E_IfTrue;[assumption|apply He''].
      * split;[apply Hq'' | intros; Lia.lia].
    + exists st';simpl.
      split.
      * eapply E_Seq.
        -- apply He.
        -- apply E_IfFalse ;[assumption| apply E_Skip].
      * split.
        -- apply HPre'.
        -- intros. rewrite H0 in Hbst'. inversion Hbst'.
Qed.

(** A second property we want to show about the _unroll_ function is stated in
    terms of the operational semantics:
    Adding the unroll function in front of a _while_ loop with
    the same body and condition will not influence the resulting state:
*)

Lemma unroll_while_while n b c: forall st st',
   st =[ (CSeq (unroll n b c) (CWhile b c)) ]=> st' ->
   st =[ (CWhile b c ) ]=> st'.
Proof.
  induction n;intros.
  - simpl in H.
    inversion H;subst.
    inversion H2;subst.
    assumption.
  - apply IHn.
    inversion H;subst.
    inversion H2;subst.
    apply (E_Seq _ _ _ _ _ H3).
    inversion H7;subst.
    + eapply E_WhileTrue;eauto.
    + inversion H10;subst.
      assumption.
Qed.

(** Using the previous two lemmas, we can prove the Total Correctness
    rule for _while_. The proof is done in two steps:
    - First, we use lemma [hoare_total] to split the proof in two parts.
      The first case is the Hoare rule for _while_, so we apply the
      lemma we proved in the previous chapter.
      It remains to prove that the loop terminates.
    - To prove that the loop terminates, we use lemma _unroll_while_while_ to
      add as many iterations of the loop as the value of measure. Then, we perform a case
      analysis on the last condition. If the condition is true, we have a
      contraction, since we have m < 0. If the condition is false,
      we apply lemma [E_WhileFalse] from the [Imp] chapter.
 *)

Theorem total_while : forall P (b:bexp) c measure,
  (forall z: nat,
      let Pre := (fun st => P st /\ measure st = z /\ bassertion b st) in
      let Post := (fun st' => P st' /\ measure st' < z) in
      |Pre| c |Post|) ->
      |P| while b do c end |P /\ ~ b|.
Proof.
  intros P b c measure Hhoare.
  apply hoare_total;split.
  - assert (HPP: |P /\ b| c |P|).
    { intros st (HPre & Hb).
      specialize (aux _ measure (measure st) _ _ HPre Logic.eq_refl Hb) as HPre'.
      specialize (Hhoare (measure st) st HPre') as [st' (He & (HPre'' & _))].
      exists st'. auto.
    }
    apply hoare_total in HPP as [HPP _ ].
    apply hoare_while.
    assumption.
  - intros st HPre.
    destruct (beval st b) eqn: Hb;[| exists st; apply E_WhileFalse;assumption].
    specialize (aux _ measure (measure st) _ _ HPre Logic.eq_refl Hb) as HPTrue.
    specialize (total_unroll_c _ _ _ _ Hhoare (measure st) (measure st) st HPTrue)
      as [st' (He & (HPre' & Hm))].
    exists st'.
    apply (unroll_while_while (measure st)).
    apply (E_Seq _ _ _ _ _ He).
    destruct (beval st' b) eqn: Hb'.
    + specialize (Hm Hb').
      rewrite sub_diag in Hm.
      inversion Hm.
      specialize (aux _ _ _ _ _ HPre' H0 Hb') as HP'.
      specialize (Hhoare 0 st' HP') as [st'' (_ & ( _ & Hm'' ))].
      inversion Hm''.
    + apply E_WhileFalse.
      assumption.
Qed.

(* ################################################################# *)
(** * Examples *)

(** For the first formal proof using the [total_while] rule, we can prove the
    following example from the previous Chapter. The is increment location
    [X] while the location is small or equal to 2. We want to proof that
    if the program is executed in a state where [X <= 3] holds then it terminates
    in a state where [X = 3] holds. If the inital state satisfies [X <= 3], the
    loop will require at most 3 iteration. Therefore the measure function will
    be [(fun s => 3 - (s X))].

 **)

Example while_example :
  |X <= 3|
    while (X <= 2) do
      X := X + 1
    end
  |X = 3|.
Proof.
  eapply total_consequence_post.
  - apply total_while with (measure:=(fun s => 3 - (s X))).
    intros z Pre Post;unfold Pre, Post; clear Pre Post.
    eapply total_consequence_pre.
    + apply total_asgn.
    + intros st H; destruct H; destruct H0.
      rewrite <- H0. apply leb_le in H1.
            split.
      * assertion_auto''.
      * rewrite t_update_eq.
        unfold aeval in *.
        Lia.lia.
  - assertion_auto''.
Qed.

(** In the following example, we prove that the program computes the greatest
    common divisor and terminates.
    For the functional correctness part, we take a mathematical definition
    of _gcd_ from the standard library as a reference implementation and
    proof that location [Z] contains the greatest common divisor of [X] and [Y].
    For the termination part, we can notice that the number of iteration of
    the loop can be bounded by [X + Y]. This is an over-approximation of
    the maximum number of iteration of the loop, but has the advantage of
    being simple.
 *)


Example gcd_example :
  |0 < X /\ 0 < Y|
    Z := X;
    W := Y;
    while (~ (Z = W)) do
      if (Z > W) then
        Z := Z - W
      else
        W := W - Z
      end
    end
  |fun st => st Z = gcd (st X) (st Y)|.
 Proof.
 eapply total_seq.
 - eapply total_seq.
   + eapply total_consequence_post.
     * apply total_while with
         (P:= (fun st => gcd (st Z) (st W) = gcd (st X) (st Y) /\
                        st Z > 0 /\ st W > 0))
         (measure:=(fun st => (st Z) + (st W))).
       intros z Pre Post;unfold Pre, Post; clear Pre Post.
       apply total_if.
       -- eapply total_consequence_pre.
          ++ apply total_asgn.
          ++ intros st H.
             destruct H. destruct H. destruct H.
             apply negb_true_iff, leb_complete_conv in H0.
                         split.
             ** assertion_auto''.
                split.
                --- rewrite <- H, gcd_comm.
                    rewrite gcd_sub_diag_r by Lia.lia.
                    rewrite gcd_comm; reflexivity.
                --- assertion_auto''.
             ** assertion_auto''.
       -- eapply total_consequence_pre.
          ++ apply total_asgn.
          ++ intros st H.
             destruct H. destruct H. destruct H. destruct H1. destruct H2.
             apply eq_true_negb_classical, leb_complete in H0.
             apply negb_true_iff, eqb_neq in H3.
                          split.
             ** assertion_auto''. split.
                --- rewrite <- H, gcd_sub_diag_r; assertion_auto''.
                --- assertion_auto''.
             ** simpl.
               assertion_auto''.
     * intros st H.
       destruct H as (H, H1). destruct H. destruct H0.
       apply eq_true_negb_classical, eqb_eq in H1.
       rewrite <- H.
              assertion_auto''.
       rewrite H1, gcd_diag; reflexivity.
   + apply total_asgn.
 - eapply total_consequence_pre.
   + apply total_asgn.
   + assertion_auto''.
 Qed.

(* 2025-05-20 19:53 *)
