(** * Noninterference: Defining Secrecy and Secure Multi-Execution *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From PLF Require Import Maps.
From PLF Require Import Imp.
Set Default Goal Selector "!".

(** Programmers have to be very careful about how information flows in
    the software they develop to prevent leaking secret data. For
    instance in Moodle students shouldn't be able to obtain
    information about other student's grades. Or in crypto protocols
    the crypto keys should be kept secret and not sent over the
    network in clear. *)

(** Information flow control tries to prevent leaking secret
    information.  But how does one formalize that a program doesn't
    leak any information about the secret inputs to public outputs? *)

(** We first investigate this question in the very simple setting of Coq
    functions taking two arguments, one we call the public input and the other
    one we call the secret input. Our functions return a pair where the first
    element is the public output and the second one the secret output. *)

(** Say we have the following function working on natural numbers: *)

Definition secure_f (pi si : nat) : nat*nat := (pi+1, pi+si*2).

(** This function seems intuitively secure, since the first output [pi+1], which
    we assume to be public, only depends on the public input [pi], but not on
    the secret input [si]. The second output [pi+si*2] depends on both the
    public input and the secret input, but that's okay, since we assume this
    second output to be secret. *)

(** Still, how can we mathematically define that this function is
    secure? Let's try it on a couple of inputs: *)

Example example1_secure_f : secure_f 0 0 = (1,0).
Proof. reflexivity. Qed.

Example example2_secure_f : secure_f 0 1 = (1,2).
Proof. reflexivity. Qed.

Example example3_secure_f : secure_f 1 2 = (2,5).
Proof. reflexivity. Qed.

(** In the last two cases the value of the public output is equal to the value
    of secret input. But that's just a coincidence, and has nothing to do with
    the public output leaking the secret input, which wasn't used at all in
    computing the public output. *)

(* ################################################################# *)
(** * Naive attempt at defining secrecy *)

(** So a naive security definition, which we'll only use as a strawman, is one
    that simply compares secret inputs with public outputs: *)

Definition broken_sec_def (f : nat -> nat -> nat*nat) :=
  forall pi si, fst (f pi si) <> si.

(** As discussed above, this definition would reject our secure
    function above as insecure: *)

Lemma broken_sec_def_rejects_secure_f : ~broken_sec_def secure_f.
Proof. intros Hc. apply (Hc 0 1). reflexivity. Qed.

(** Even worse, this broken definition of security would allow insecure
    functions, such as the following one whose public output is [si+1]: *)

Definition insecure_f (pi si : nat) : nat*nat := (si+1, pi+si*2).

(** This function's public output is never equal to its secret input, yet an
    attacker can easily compute one from the other by just subtracting [1]. So
    the secret is entirely leaked, yet our broken definition accepts this: *)

Lemma broken_sec_def_accepts_insecure_f : broken_sec_def insecure_f.
Proof.
  unfold broken_sec_def. intros pi si. induction si as [| si' IH].
  - simpl. intros contra. discriminate contra.
  - simpl in *. intro Hc. injection Hc as Hc. apply IH. apply Hc.
Qed.

(** This attempt at defining secure information flow by looking at how
    inputs and outputs are related for a single execution of the
    program was a complete failure. In fact, it is well known in the
    formal security research community that secure information flow
    _cannot_ be defined by looking at just one single program execution. *)

(* ################################################################# *)
(** * Noninterference for pure functions *)

(** The simplest correct way to define secure information flow is a
    property called _noninterference_, which in its most standard form
    looks at _two_ program executions: for two different secret inputs
    the public outputs should not change: *)

Definition noninterferent {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  forall (pi:PI) (si1 si2:SI), fst (f pi si1) = fst (f pi si2).

(** This definition prevents secret inputs from interfering with public
    outputs in any way. At the same time it allows secret inputs to
    influence secret outputs and also public inputs to influence both
    public and secret outputs. *)

(** The definition above defines noninterference for arbitrary types
    of inputs and outputs, so we can instantiate them to [nat] when
    looking at our example functions above: *)

Lemma noninterferent_secure_f : noninterferent secure_f.
Proof. unfold noninterferent. simpl. reflexivity. Qed.

Lemma interferent_insecure_f : ~noninterferent insecure_f.
Proof.
  unfold noninterferent. simpl. intros contra.
  specialize (contra 0 0 1). discriminate contra.
Qed.

(** The [secure_f] function above is quite obviously noninterferent,
    because the expression [pi+1] computing the public output doesn't
    syntactically mention the secret input at all. Since
    noninterference is a semantic property though (not a one syntactic
    one), functions where the expression computing the public input
    does syntactically mention the secret input can still be
    noninterferent. Here is a first example: *)

Definition less_obvious_f1 (pi si : nat) : nat*nat := (si * 0, pi+si).

(** This function is noninterferent; since the public output is
    constant [0], so it can't depend on [si], even if it syntactically
    mentions it: *)

Lemma noninterferent_less_obvious_f1 : noninterferent less_obvious_f1.
Proof.
  unfold noninterferent, less_obvious_f1. intros pi si1 si2.
  simpl. repeat rewrite <- mult_n_O. reflexivity.
Qed.

(** Here is a second example of a function that is noninterferent, even
    if this is not syntactically obvious: *)

Definition less_obvious_f2 (pi si : nat) : nat*nat :=
  (if Nat.eqb si 1 then si * pi else pi, pi+si).

Lemma aux_f2 : forall si pi, (if Nat.eqb si 1 then si * pi else pi) = pi.
Proof.
  intros si pi. destruct si; simpl.
  - reflexivity.
  - destruct si.
    + simpl. rewrite <- plus_n_O. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma noninterferent_less_obvious_f2 : noninterferent less_obvious_f2.
Proof.
  unfold noninterferent, less_obvious_f2. intros pi si1 si2.
  repeat rewrite aux_f2. simpl. reflexivity.
Qed.

(** Branching on a secret can, however, be dangerous, since one can
    easily leak the secret this way, even if both the [then] and the
    [else] branches are public. For instance the following function
    leaks whether [si] is zero or not, so it is not noninterferent. *)

Definition less_obvious_f3 (pi si : nat) : nat*nat :=
  (if Nat.eqb si 0 then 1 else 0, pi+si).

Lemma interferent_less_obvious_f3 : ~noninterferent less_obvious_f3.
Proof.
  unfold noninterferent, less_obvious_f3. simpl. intros contra.
  specialize (contra 1 1 0). simpl in contra. discriminate contra.
Qed.

(* ################################################################# *)
(** * A too strong secrecy definition *)

(** In the definition of noninterference above we pass the same public
    inputs to the two executions and this allows public outputs to
    depend on public inputs. To convince ourselves of this, let's look
    at the following too strong definition of security: *)

Definition too_strong_sec_def {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  forall (pi1 pi2:PI) (si1 si2:SI), fst (f pi1 si1) = fst (f pi2 si2).

(** This basically says that the public output of [f] can depend
    neither on the public input not on the secret input, so it has to
    be constant, which is not the case for our [secure_f]. *)

Lemma secure_f_rejected_again : ~too_strong_sec_def secure_f.
Proof.
  unfold too_strong_sec_def, secure_f. simpl. intros contra.
  specialize (contra 0 1 0 0). discriminate contra.
Qed.

(* ################################################################# *)
(** * Noninterferent implies splittable *)

(** Noninterference is still a very strong property though. In
    particular, [f] being noninterferent is equivalent to [f] being
    splittable into two different functions, one of which doesn't get
    the secret at all. *)

Definition splittable {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  exists (pf : PI -> PO) (sf : PI -> SI -> SO),
    forall pi si , f pi si = (pf pi, sf pi si).

Theorem splittable_noninterferent : forall PI SI PO SO : Type,
  forall f : PI -> SI -> PO*SO, splittable f -> noninterferent f.
Proof.
  unfold splittable, noninterferent.
  intros PI SI PO SO f [pf [sf H]] pi si1 si2.
  rewrite H. rewrite H. simpl. reflexivity.
Qed.

Theorem noninterferent_splittable : forall PI SI PO SO : Type,
  forall some_si : SI, (* we require SI to be an inhabited type! *)
  forall f : PI -> SI -> PO*SO, noninterferent f -> splittable f.
Proof.
  unfold splittable, noninterferent.
  intros PI SI PO SO some_si f Hni.
  (* we pass the SI inhabitant as a dummy secret value! *)
  exists (fun pi => fst (f pi some_si)).
  exists (fun pi si => snd (f pi si)).
  intros pi si. rewrite (Hni _ _ si).
  destruct (f pi si) as [po so]. reflexivity.
Qed.

(* ################################################################# *)
(** * Secure Multi-Execution (SME) *)

(** The previous proof also captures the key idea behind Secure Multi-Execution
    (SME), an enforcement mechanism that can make _any_ function
    noninterferent. To achieve this SME runs the function twice, once passing a
    dummy secret as input to obtain the public output, and once using the real
    secret input to obtain the secret output. *)

Definition sme {PI SI PO SO : Type} (some_si : SI)
  (f:PI->SI->PO*SO) : PI->SI->PO*SO :=
    fun pi si => (fst (f pi some_si), snd (f pi si)).

(** Functions protected by [sme] are guaranteed to satisfy noninterference: *)

Theorem noninterferent_sme :  forall PI SI PO SO : Type,
  forall some_si : SI,
  forall f : PI -> SI -> PO*SO,
    noninterferent (sme some_si f).
Proof. intros PI SI PO SO some_si f pi si1 si2. simpl. reflexivity. Qed.

(** Moreover, if the function we pass to [sme] is already noninterferent,
    then its behavior will not change; so we say that [sme] is a _transparent_
    enforcement mechanism for noninterference: *)

Theorem transparent_sme : forall PI SI PO SO : Type,
  forall some_si : SI,
  forall f : PI -> SI -> PO*SO,
    noninterferent f -> forall pi si, f pi si = sme some_si f pi si.
Proof.
  unfold noninterferent, sme. intros PI SI PO SP some_si f Hni pi si.
  rewrite (Hni _ _ si).
  destruct (f pi si) as [po so]. reflexivity.
Qed.

(** It is interesting to look at what [sme] does for _interferent_ functions,
    like [insecure_f], whose public output was one plus its secret input: *)

Example example1_sme_insecure_f: sme 0 insecure_f 0 0 = (1, 0).
Proof. reflexivity. Qed.

Example example2_sme_insecure_f: sme 0 insecure_f 0 1 = (1, 2).
Proof. reflexivity. Qed.

Example example3_sme_insecure_f: sme 0 insecure_f 1 1 = (1, 3).
Proof. reflexivity. Qed.

(** Now the public output of [sme insecure_f 0] is one plus the dummy
   constant [0], so always the constant [1]. *)

Lemma constant_sme_insecure_f: forall pi si,
  fst (sme 0 insecure_f pi si) = 1.
Proof. reflexivity. Qed.

(** This is a secure behavior, but it is different from that of the
    original [insecure_f] function. So we are giving up some
    correctness for security. There is no free lunch! *)

(** The other downside of [sme] is that we have to run the function
    twice for our two security levels, public and secret. In general,
    we need to run the program as many times as we have security
    levels, which is often an exponential number, say if we take our
    security levels to be sets of principals. This is inefficient!

    Other information flow control mechanisms overcome this downside,
    but have other downsides of their own, for instance:
        - by requiring nontrivial manual proofs for each individual
          program (e.g. Relational Hoare Logic), or
        - by using static overapproximations that reject some secure
          programs (security type systems), or
        - by using dynamic overapproximations that unnecessarily
          change program behavior, for instance forcefully terminating
          even some secure programs to prevent leaks, in which case
          they are not transparent (dynamic information flow control;
          an extension of dynamic taint tracking to also handle
          implicit flows).

    Again, there is no free lunch! *)


(* ################################################################# *)
(** * Noninterference for state transformers *)

(** The development above is quite easy to adapt to Coq functions that
    transform states ([state->state]), where we label each variable as
    either public or secret. *)

Print state. (* state = total_map nat = string -> nat *)

Definition pub_vars := total_map bool. (* = string -> bool *)

(** Instead of requiring that the first elements of two pairs are
    equal, we require that the two states have equal values on the
    variables labeled public by the [pub] map. *)

Definition pub_equiv (pub : pub_vars) (s1 s2 : state) :=
  forall x:string, pub x = true -> s1 x = s2 x.

(** This makes the definition more symmetric, since we can use
    [pub_equiv] both for the input states and the output states: *)

Definition noninterferent_state pub (f : state -> state) :=
  forall s1 s2, pub_equiv pub s1 s2 -> pub_equiv pub (f s1) (f s2).

(** We can prove an equivalence between [noninterferent_state] and our original
    [noninterferent] definition. For this we need to split and merge states.

    We also need a few helper lemmas. *)

(** The way we define [split_state] and [merge_state] is a good example of
    programming with higher-order functions, and there's more of this in
    [Maps].

    The [split_state] function takes a state [s] and zeroes out the variables
    [x] for which [pub x] is different than an argument bit [b]. So
    [split_state s pub true] keeps the public variables, and zeroes out the
    secret ones. Dually, [split_state s pub false] keeps the secret variables,
    and zeroes out the public ones.  *)

Definition split_state (s:state) (pub:pub_vars) (b:bool) : state :=
  fun x : string => if Bool.eqb (pub x) b then s x else 0.

(** The [merge_state] function takes in two states [s1] and [s2]
    and produces a new state that contains the public variables from
    [s1] and the private variables from [s2]. *)

Definition merge_states (s1 s2:state) (pub:pub_vars) : state :=
  fun x : string => if pub x then s1 x else s2 x.

Definition split_state_fun (pub : pub_vars) (mf : state -> state) :=
  fun s1 s2 : state =>
    let ms := mf (merge_states s1 s2 pub) in
    (split_state ms pub true, split_state ms pub false).

(** The technical development needed for the equivalence proof between
    [noninterferent_state] and our original [noninterferent]
    definition is not that interesting though, and one can skip
    directly to the [noninterferent_state_ni] statement on first read. *)

Definition pub_equiv_split (pub : pub_vars) (s1 s2 : state) :=
  forall x:string, (split_state s1 pub true) x = (split_state s2 pub true) x.

Theorem pub_equiv_split_iff : forall pub s1 s2,
  pub_equiv pub s1 s2 <-> pub_equiv_split pub s1 s2.
Proof.
  unfold pub_equiv, pub_equiv_split, split_state. intros. split.
  - intros H x. destruct (Bool.eqb_spec (pub x) true).
    + apply H. apply e.
    + reflexivity.
  - intros H x. specialize (H x). destruct (Bool.eqb_spec (pub x) true).
    + intros _. apply H.
    + contradiction.
Qed.

Theorem pub_equiv_merge_states : forall pub s z1 z2,
  pub_equiv pub (merge_states s z1 pub) (merge_states s z2 pub).
Proof.
  unfold pub_equiv, merge_states. intros pub s z1 z2 x Hx.
  rewrite Hx. reflexivity.
Qed.

Require Import FunctionalExtensionality.

Theorem merge_states_split_state : forall s pub,
  merge_states (split_state s pub true) (split_state s pub false) pub = s.
Proof.
  unfold merge_states, split_state. intros s pub.
  apply functional_extensionality. intro x.
  destruct (pub x) eqn:Heq; reflexivity.
Qed.

(** Now we can finally state our theorem about the equivalence between
    [non_interferent_state] and [noninterferent]: *)

Theorem noninterferent_state_ni : forall pub f,
  noninterferent_state pub f <->
  noninterferent (split_state_fun pub f).
Proof.
  unfold noninterferent_state, noninterferent, split_state_fun.
  intros pub f. split.
  - intros H s z1 z2. simpl.
    assert (H' : pub_equiv pub (merge_states s z1 pub) (merge_states s z2 pub)).
      { apply pub_equiv_merge_states. }
    apply H in H'. rewrite pub_equiv_split_iff in H'.
    unfold pub_equiv_split in H'. apply functional_extensionality. apply H'.
  - intros H s1 s2 Hequiv. simpl in H.
    rewrite pub_equiv_split_iff in Hequiv. unfold pub_equiv_split in Hequiv.
    rewrite pub_equiv_split_iff. unfold pub_equiv_split. intro x.
    specialize (H (split_state s1 pub true)
                  (split_state s1 pub false)
                  (split_state s2 pub false)).
    rewrite merge_states_split_state in H.
    apply functional_extensionality in Hequiv. rewrite Hequiv in H.
    rewrite merge_states_split_state in H.
    rewrite H. reflexivity.
Qed.

Definition merge_state_fun (pub : pub_vars) (sf : state -> state -> state*state) :=
  fun s : state =>
    let ps := sf (split_state s pub true) (split_state s pub false) in
    merge_states (fst ps) (snd ps) pub.

(* ################################################################# *)
(** * SME for state transformers *)

(** We can use the [split_state] and [merge_states] functions above to
    also define SME for state transformers.  *)

Definition sme_state (f : state -> state) (pub:pub_vars) :=
  fun s => merge_states (f (split_state s pub true)) (f s) pub.

(** We can prove the same two theorems as for [sme] above: *)

Theorem noninterferent_sme_state : forall pub f,
  noninterferent_state pub (sme_state f pub).
Proof.
  unfold noninterferent_state, sme_state.
  intros pub f s1 s2 Hequiv.
  rewrite pub_equiv_split_iff in Hequiv.
  unfold pub_equiv_split in Hequiv.
  apply functional_extensionality in Hequiv. rewrite Hequiv.
  apply pub_equiv_merge_states.
Qed.

Theorem transparent_sme_state : forall f pub,
  noninterferent_state pub f -> forall s, f s = sme_state f pub s.
Proof.
  unfold noninterferent_state, sme_state.
  intros f pub Hni s.
  unfold merge_states, split_state. unfold pub_equiv in Hni.
  apply functional_extensionality. intro x.
  destruct (pub x) eqn:Eq.
  - apply Hni.
    + intros x' Hx'.
      destruct (Bool.eqb_spec (pub x') true).
      * reflexivity.
      * contradiction.
    + assumption.
  - reflexivity.
Qed.

(** One thing to note in this proof is that we used the lemma
    [Bool.eqb_spec] to do case analysis on whether the [pub x'] is
    equal to [true]. For more details on how this works, please check
    out the explanations about the [reflect] inductive predicate in
    [IndProp]. *)

(* ################################################################# *)
(** * Noninterference for Imp programs without loops *)

(** For programs without loops the "failed attempt" evaluation function from
    [Imp] works well and allows us to easily define a state transformer
    function for each command. *)

Print ceval_fun_no_while.
Definition flip {A B C : Type} (f : A -> B -> C) := fun b a => f a b.
Definition cinterp : com -> state -> state := flip ceval_fun_no_while.

Definition noninterferent_no_while pub c : Prop :=
  noninterferent_state pub (cinterp c).

Definition xpub : pub_vars := (X !-> true; _ !-> false).

Definition secure_com : com :=
  <{ X := X+1;
     Y := (X-1)+Y*2 }>.

(** For proving [secure_com] noninterferent we first prove a few
    helper lemmas. *)

Lemma xpub_true : forall x, xpub x = true -> x = X.
Proof.
  unfold xpub. intros x Hx.
  destruct (eqb_spec x X).
  - subst. reflexivity.
  - rewrite t_update_neq in Hx.
    + rewrite t_apply_empty in Hx. discriminate.
    + intro contra. subst. contradiction.
Qed.

(** Here we are using the [t_update_neq] and [t_apply_empty] lemmas that were
    proved in [Maps] *)

Lemma xpubX : xpub X = true.
Proof. reflexivity. Qed.

(** Using these lemmas the noninterference proof for [secure_com] is easy: *)

Lemma noninterferent_secure_com :
  noninterferent_no_while xpub secure_com.
Proof.
  unfold noninterferent_no_while, noninterferent_state,
         secure_com, pub_equiv.
  intros s1 s2 H x Hx. simpl. apply xpub_true in Hx.
  subst. rewrite (H X xpubX). reflexivity.
Qed.

(** Now let's look at a couple of insecure commands: *)

Definition insecure_com1 : com :=
  <{ X := Y+1; (* <- bad explicit flow! *)
     Y := (X-1)+Y*2 }>.

(** An _explicit flow_ is when a command directly assigns an expression
    depending on secret variables to a public variable, like the [X := Y+1]
    assignment above. We can prove that this is insecure: *)

Lemma interferent_insecure_com1 :
  ~noninterferent_no_while xpub insecure_com1.
Proof.
  unfold noninterferent_no_while, noninterferent_state,
         insecure_com1, pub_equiv.
  intro Hc. simpl in Hc.
  specialize (Hc (X !-> 0 ; Y !-> 0) (X !-> 0 ; Y !-> 1)).
  assert (H: forall x, xpub x = true ->
                       (X !-> 0; Y !-> 0) x = (X !-> 0; Y !-> 1) x).
  { clear Hc. intros x H. apply xpub_true in H. subst. reflexivity. }
  specialize (Hc H X xpubX). simpl in Hc.
  repeat try rewrite t_update_eq in Hc.
  discriminate.
Qed.

(** Noninterference can be violated not only by explicit flows, but also by
    _implicit flows_, which leak secret information via the control-flow of the
    program. Here is a simple example: *)

Definition insecure_com2 : com :=
  <{ if Y = 0 then
       Y := 42
     else
       X := X+1 (* <- bad implicit flow! *)
     end }>.

(** Here the expression [X+1] we are assigning to [X] is public information, but
    we are doing this assignment after we branched on a secret condition [Y =
    0], so we are indirectly leaking information about the value of [Y]. In this
    case we can infer that if [X] gets incremented the value of [Y] is not [0]. *)

Lemma interferent_insecure_com2 :
  ~noninterferent_no_while xpub insecure_com2.
Proof.
  (* the same insecurity proof as for [insecure_com1] does the job *)
  unfold noninterferent_no_while, noninterferent_state,
         insecure_com2, pub_equiv.
  intro Hc. simpl in Hc.
  specialize (Hc (X !-> 0 ; Y !-> 0) (X !-> 0 ; Y !-> 1)).
  assert (H: forall x, xpub x = true ->
                       (X !-> 0; Y !-> 0) x = (X !-> 0; Y !-> 1) x).
  { clear Hc. intros x H. apply xpub_true in H. subst. reflexivity. }
  specialize (Hc H X xpubX). simpl in Hc.
  repeat try rewrite t_update_eq in Hc.
  discriminate.
Qed.

(* ################################################################# *)
(** * SME for Imp programs without loops *)

(** We can use [sme_state] to execute such programs to obtain a noninterferent
    state transformer by running them 2 times, once on a state without secrets
    and once on the original input state, and then merging the final states. *)

Definition sme_cmd c : pub_vars->state->state := sme_state (cinterp c).

(** The result of applying [sme_cmd] to a program is no longer a
    program, but a state transformer. We can prove all the state
    transformers obtained by [sme_cmd] noninterferent using our
    noninterference theorem about [sme_state]. *)

Theorem noninterferent_sme_cmd : forall c pub,
  noninterferent_state pub (sme_cmd c pub).
Proof. intros c p. apply noninterferent_sme_state. Qed.

Theorem transparent_sme_cmd : forall c pub,
    noninterferent_state pub (fun s => ceval_fun_no_while s c) ->
    forall s, cinterp c s = sme_cmd c pub s.
Proof.
  unfold sme_cmd. intros c pub NI. apply transparent_sme_state. apply NI.
Qed.

(* ################################################################# *)
(** * Noninterference for Imp programs with loops *)

(** In the presence of loops, we need to define noninterference using the
    evaluation relation ([ceval]) of Imp: *)

Definition noninterferent_while pub c := forall s1 s2 s1' s2',
  pub_equiv pub s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv pub s1' s2'.

Ltac invert H := inversion H; subst; clear H.

Lemma noninterferent_secure_com' :
  noninterferent_while xpub secure_com.
Proof.
  unfold noninterferent_while, secure_com, pub_equiv.
  intros s1 s2 s1' s2' H H1 H2 x Hx.
  apply xpub_true in Hx. subst.
  (* the proof is the same, but with some extra ugly [invert]s *)
  invert H1. invert H4. invert H7.
  invert H2. invert H3. invert H6. simpl.
  rewrite (H X xpubX). reflexivity.
Qed.

(* ################################################################# *)
(** * SME for Imp programs with loops *)

(** Now to define SME we also need to use a relation, of a similar type to
    [ceval]: *)

Check ceval : com -> state -> state -> Prop.

Definition sme_while (pub:pub_vars) (c:com) (s s':state) : Prop :=
  exists ps ss, split_state s pub true =[ c ]=> ps /\
    s =[ c ]=> ss /\
    merge_states ps ss pub = s'.

(** To state that sme_eval is secure, we need to generalize our noninterference
    definition, so that it works not only with [ceval], but with any evaluation
    relation, including [sme_while pub]. *)

Definition noninterferent_while_R (R:com->state->state->Prop) pub c :=
  forall s1 s2 s1' s2',
  pub_equiv pub s1 s2 ->
  R c s1 s1' ->
  R c s2 s2' ->
  pub_equiv pub s1' s2'.

(** The proof that [while_sme] is noninterferent is as before, but now it relies
    on the determinism of [ceval], which was obvious for state transformer
    functions, but is not obvious for evaluation relations. *)

Check ceval_deterministic : forall (c : com) (st st1 st2 : state),
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.

Theorem noninterferent_while_sme : forall pub c,
  noninterferent_while_R (sme_while pub) pub c.
Proof.
  unfold noninterferent_while_R, sme_while.
  intros pub c s1 s2 s1' s2' H [ps1 [ss1 [H1p [H1s H1m]]]]
                               [ps2 [ss2 [H2p [H2s H2m]]]].
  subst. rewrite pub_equiv_split_iff in H. unfold pub_equiv_split in H.
  apply functional_extensionality in H. rewrite H in H1p.
  rewrite (ceval_deterministic _ _ _ _ H1p H2p).
  apply pub_equiv_merge_states.
Qed.

(** Turns out we can only prove a weak version of transparency for
    noninterferent programs, and this has to do with nontermination
    (more later). *)

(** But first we need a few lemmas:  *)

Lemma pub_equiv_split_state : forall (pub:pub_vars) s,
  pub_equiv pub (split_state s pub true) s.
Proof.
  unfold pub_equiv, split_state.
  intros pub s x Hx. destruct (Bool.eqb_spec (pub x) true).
  - reflexivity.
  - contradiction.
Qed.

Lemma pub_equiv_sym : forall (pub:pub_vars) s1 s2,
  pub_equiv pub s1 s2 ->
  pub_equiv pub s2 s1.
Proof.
  unfold pub_equiv. intros pub s1 s2 H x Hx.
  rewrite H.
  - reflexivity.
  - assumption.
Qed.

Lemma merge_state_pub_equiv : forall pub ss ps,
  pub_equiv pub ss ps ->
  merge_states ps ss pub = ss.
Proof.
  unfold pub_equiv, merge_states.
  intros pub ss ps H. apply functional_extensionality.
  intros x. destruct (pub x) eqn:Heq.
  - rewrite H.
    + reflexivity.
    + assumption.
  - reflexivity.
Qed.

(** More specifically, we can only prove that [sme_while] execution implies
    [ceval]. *)

Theorem somewhat_transparent_while_sme : forall pub c,
  noninterferent_while pub c ->
  (forall s s', (sme_while pub) c s s' -> s =[ c ]=> s').
Proof.
  unfold noninterferent_while, sme_while.
  intros pub c Hni s s' [ps [ss [Hp [Hs Hm]]]]. subst s'.
    assert(H:pub_equiv pub s (split_state s pub true)).
    { apply pub_equiv_sym. apply pub_equiv_split_state. }
    specialize (Hni s (split_state s pub true) ss ps H Hs Hp).
    apply merge_state_pub_equiv in Hni. rewrite Hni. apply Hs.
Qed.

(** But we cannot prove the reverse implication, since a command
    terminating when starting in state [s], does not necessarily still
    terminates when starting in state [split_state s pub true], as
    would be needed for proving [sme_while]. *)

(** Yet it seems we can still do most of the things as in the setting
    without while loops, including SME (just not fully transparent).
    So is there anything special about loops and nontermination?

    Yes, there is! Let's look at our noninterference definition again:

Definition noninterferent_while pub c := forall s1 s2 s1' s2',
  pub_equiv pub s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv pub s1' s2'.

    It says that for any two _terminating_ executions, if the initial states
    agree on their public variables, then so do the final states. This is
    traditionally called _termination-insensitive_ noninterference (TINI),
    since it doesn't consider nontermination to be observable to an attacker. *)

(** In particular, the following program is _secure_ wrt TINI: *)

Definition termination_leak : com :=
  <{ if Y = 0 then
       Y := 42
     else
       while true do skip end (* <- leak secret by looping *)
     end }>.

(** And we can prove it ... *)

Lemma Y_neq_X : (Y <> X).
Proof. intro contra. discriminate. Qed.

(** This lemma is a homework exercise in Imp: *)
Check loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').

Definition tini_secure_termination_leak :
  noninterferent_while xpub termination_leak.
Proof.
  unfold noninterferent_while, termination_leak, pub_equiv.
  intros s1 s2 s1' s2' H H1 H2 x Hx. apply xpub_true in Hx.
  subst. specialize (H X xpubX).
  invert H1.
  + invert H8. simpl.
    rewrite (t_update_neq _ _ _ _ _ Y_neq_X).
    invert H2.
    * invert H8. simpl.
      rewrite (t_update_neq _ _ _ _ _ Y_neq_X). assumption.
    * apply loop_never_stops in H8. contradiction.
  + apply loop_never_stops in H8. contradiction.
Qed.

(* ################################################################# *)
(** * Termination-Sensitive Noninterference *)

(** We can give a stronger definition of security that disallows such
    nontermination leaks. It is traditionally called
    _termination-sensitive noninterference_ (TSNI) and it is defined
    as follows: *)

Definition tsni_while_R (R:com->state->state->Prop) pub c :=
  forall s1 s2 s1',
  R c s1 s1' ->
  pub_equiv pub s1 s2 ->
  (exists s2', R c s2 s2' /\ pub_equiv pub s1' s2').

(** We can prove that [termination_leak] doesn't satisfy TSNI: *)

Definition tsni_insecure_termination_leak :
  ~tsni_while_R ceval xpub termination_leak.
Proof.
  unfold tsni_while_R, termination_leak.
  intros Hc.
  specialize (Hc (X !-> 0 ; Y !-> 0) (X !-> 0 ; Y !-> 1)
                 (Y !-> 42; X !-> 0 ; Y !-> 0)).
  assert (HH : (X !-> 0; Y !-> 0) =[ termination_leak ]=>
               (Y !-> 42; X !-> 0; Y !-> 0)).
  { clear. unfold termination_leak. constructor.
    - reflexivity.
    - constructor. reflexivity. }
  specialize (Hc HH). clear HH.
  assert (H: forall x, xpub x = true ->
                       (X !-> 0; Y !-> 0) x = (X !-> 0; Y !-> 1) x).
  { clear Hc. intros x H. apply xpub_true in H. subst. reflexivity. }
  specialize (Hc H). clear H.
  destruct Hc as [s2' [Hc _]].
  invert Hc.
  - simpl in H4. discriminate.
  - apply loop_never_stops in H5. contradiction.
Qed.

(** More generally, we can prove that TSNI is strictly stronger than TINI
    (noninterferent_while) *)

Lemma tsni_noninterferent : forall pub c,
  tsni_while_R ceval pub c ->
  noninterferent_while_R ceval pub c.
Proof.
  unfold noninterferent_while_R, tsni_while_R.
  intros pub c Htsni s1 s2 s1' s2' Hequiv H1 H2.
  specialize (Htsni s1 s2 s1' H1 Hequiv).
  destruct Htsni as [s2'' [H2' Hequiv']].
  rewrite (ceval_deterministic _ _ _ _ H2 H2').
  apply Hequiv'.
Qed.

(** The reverse direction of the implication only works for programs that
    always terminate (such as most of our simple examples above). *)

Lemma terminating_noninterferent_tsni: forall pub c,
  (forall s, exists s', s =[ c ]=> s') ->
  noninterferent_while_R ceval pub c ->
  tsni_while_R ceval pub c.
Proof.
  unfold noninterferent_while_R, tsni_while_R.
  intros pub c Hterminating Hni s1 s2 s1' H Eq.
  destruct (Hterminating s2) as [s2' H'].
  exists s2'; split.
  - assumption.
  - apply Hni with (s1 := s1) (s2 := s2).
    + assumption.
    + assumption.
    + assumption.
Qed.

(** Now for a more interesting use of TSNI: it turns out that
    [sme_while] is transparent for programs satisfying TSNI. *)

Theorem tsni_transparent_while_sme : forall pub c,
  tsni_while_R ceval pub c ->
  (forall s s', s =[ c ]=> s' <-> (sme_while pub) c s s').
Proof.
  unfold tsni_while_R, sme_while.
  intros pub c Hni s s'.
  assert(HH:pub_equiv pub s (split_state s pub true)).
    { apply pub_equiv_sym. apply pub_equiv_split_state. }
  split.
  - intros H. specialize (Hni s (split_state s pub true) s' H HH).
    destruct Hni as [s'' [Heval Hequiv]].
    exists s''. exists s'. split.
    + assumption.
    + split.
      * assumption.
      * apply merge_state_pub_equiv. assumption.
  - intros [ps [ss [Hp [Hs Hm]]]]. subst s'.
    specialize (Hni s (split_state s pub true) ss Hs HH).
    destruct Hni as [s' [Hp' Hni]].
    rewrite (ceval_deterministic _ _ _ _ Hp Hp').
    apply merge_state_pub_equiv in Hni. rewrite Hni. apply Hs.
Qed.

(** Unfortunately [sme_while] does not _enforce_ TSNI, and this is hard
    to fix in our current setting, where programs only return a result
    in the end, a final state, so we had to merge the public and
    secret inputs into a single final state. Instead, SME is commonly
    defined in a setting with interactive IO, in which public outputs
    and secret outputs can be performed independently, during the
    execution. In that setting, it does transparently enforce a
    version of TSNI. *)

(* 2025-04-09 13:06 *)
