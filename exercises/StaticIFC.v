(** * StaticIFC: Information Flow Control Type Systems *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".

(* ################################################################# *)
(** * Noninterference *)

(** As explained in the [Noninterference] chapter, data
    confidentiality is most often expressed formally as a property
    called _noninterference_.

    To formalize this for Imp programs, we divide the variables as
    either public or secret by assuming a total map [P : pub_vars]
    between variables and Boolean labels: *)

Definition label := bool.

Definition public : label := true.
Definition secret : label := false.

Definition pub_vars := total_map label.

(** A noninterference attacker can only observe the final values of public
    variables, not of secret ones. We formalize this as a notion of
    _publicly equivalent states_ that agree on the values of all
    public variables, which are thus indistinguishable to an attacker: *)

Definition pub_equiv (P : pub_vars) {X:Type} (s1 s2 : total_map X) :=
  forall x:string, P x = public -> s1 x = s2 x.

(** For some total map [P] from variables to Boolean labels,
    [pub_equiv P] is an equivalence relation on states, so reflexive,
    symmetric, and transitive. *)

Lemma pub_equiv_refl : forall {X:Type} (P : pub_vars) (s : total_map X),
  pub_equiv P s s.
Proof. intros X P s x Hx. reflexivity. Qed.

Lemma pub_equiv_sym : forall {X:Type} (P : pub_vars) (s1 s2 : total_map X),
  pub_equiv P s1 s2 ->
  pub_equiv P s2 s1.
Proof. unfold pub_equiv. intros X P s1 s2 H x Px. rewrite H; auto. Qed.

Lemma pub_equiv_trans : forall {X:Type} (P : pub_vars) (s1 s2 s3 : total_map X),
  pub_equiv P s1 s2 ->
  pub_equiv P s2 s3 ->
  pub_equiv P s1 s3.
Proof. unfold pub_equiv. intros X P s1 s2 s3 H12 H23 x Px.
       rewrite H12; try rewrite H23; auto. Qed.

(** Program [c] is _noninterferent_ if whenever it has two terminating
    runs from two publicly equivalent initial states [s1] and [s2],
    the obtained final states [s1'] and [s2'] are also publicly equivalent. *)

Definition noninterferent P c := forall s1 s2 s1' s2',
  pub_equiv P s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv P s1' s2'.

(** Intuitively, [c] is noninterferent when the value of the public
    variables in the final state can only depend on the value of
    public variables in the initial state, and do not depend on the
    initial value of secret variables.

    In particular, changing the value of the secret variables in the
    initial state (as allowed by [pub_equiv P s1 s2]), should lead to
    no change in the final value of the public variables (as required
    by [pub_equiv P s1' s2']). *)

(** For instance, consider the following command
    (taken from [Noninterference]): *)

Definition secure_com : com := <{ X := X+1; Y := X+Y*2 }>.

(** If we assume that variable [X] is public and variable [Y] is
    secret, we can state noninterference for [secure_com] as follows: *)

Definition xpub : pub_vars := (X !-> public; _ !-> secret).

Definition noninterferent_secure_com :=
  noninterferent xpub secure_com.

(** We have already proved that [secure_com] is indeed noninterferent
    both directly using the semantics (in [Noninterference]).
    This proof was manual though, while in this chapter we will show
    how this proof can be done more syntactically and automatically
    using several _information flow control_ (IFC) type systems that
    enforce noninterference for all well-typed programs. *)

(** Not all programs are noninterferent though. For instance, a
    program that reads the contents of a secret variable and uses that
    to change the value of a public variable is unlikely to be
    noninterferent. We call this an _explicit flow_ and all our type
    systems will prevent _all_ explicit flows.

    Here is a program that has an explicit flow, which in this case
    breaks noninterference (as we proved in [Noninterference]): *)

Definition insecure_com1 : com :=
  <{ X := Y+1; (* <- bad explicit flow! *)
     Y := X+Y*2 }>.

Definition interferent_insecure_com1 :=
  ~noninterferent xpub insecure_com1.

(** Not all explicit flows break noninterference though. For instance,
    the following variant of [insecure_com1] is noninterferent even if
    it has an explicit flow. The reason for this is that the variable
    [X] is overwritten with public information in a subsequent assignment. *)

Definition secure_com1' : com :=
  <{ X := Y+1; (* <- harmless explicit flow (dead store) *)
     X := 42; (* <- X is overwritten afterwards *)
     Y := X+Y*2 }>.

(** Since our IFC type systems will prevent all explicit flows, they
    will also reject [secure_com1'], even if it is secure with respect
    to our simple attacker model for noninterference, in which the
    attacker only observes the _final_ values of public variables.

    Our type systems will only provide _sound syntactic
    overapproximations_ of the semantic noninterference property. *)

(** Explicit flows are not the only way to leak secrets: one can also
    leak secrets using the control flow of the program, by branching
    on secrets and then assigning to public variables. We call these
    leaks _implicit flows_. *)

Definition insecure_com2 : com :=
  <{ if Y = 0
     then Y := 42
     else X := X+1 (* <- bad implicit flow! *)
     end }>.

(** Here the expression [X+1] we are assigning to [X] is public
    information, but we are doing this assignment after we branched on
    a secret condition [Y = 0], so we are indirectly leaking
    information about the value of [Y]. In this case we can infer that
    if [X] gets incremented the value of [Y] is not [0]. This program
    is insecure (as proved in [Noninterference]), so it will be
    rejected by our type systems, which enforce noninterference by
    also preventing _all_ implicit flows. *)

(** Not all implicit flows break noninterference though. Here is a
    program that is noninterferent, even though it contains both an
    explicit and an implicit flow: *)

Definition secure_p2 :=
  <{ if Y = 0
     then X := Y (* <- harmless explicit flow *)
     else X := 0 (* <- harmless implicit flow *)
     end }>.

(** Intuitively, even if this program branches on the secret [Y], it
    always assigns the value [0] to [X], so no secret is
    leaked. Still, our type systems will reject programs containing
    any explicit or implicit flows, this one included. C'est la vie! *)

(* ################################################################# *)
(** * Type system for noninterference of expressions *)


(** We will build a type system that prevents all explicit and
    implicit flows.

    But first, let's start with something simpler, a type system for
    arithmetic expressions: our typing judgement [P |-a- a \in l]
    specifies the label [l] of an arithmetic expression [a] in terms
    of the labels of the variables read it reads.

    In particular, [P |-a- a \in public] says that expression [a]
    only reads public variables, so it computes a public value.
    [P |-a- a \in secret] says that expression [a] reads some secret
    variable, so it computes a value that may depend on secrets. *)

(** Here are some examples:
    - For a variable [X] we just look up its label in P, so
      [P |-a- X \in (P X)].
    - For a constant [n] the label is [public], so
      [P |-a n \in public].
    - Given variable [X1] with label [l1] and variable [X2] with
      label [l2], what should be the label of [X1 + X2] though? *)

(* ================================================================= *)
(** ** Combining labels *)

(** We need a way to combine the labels of two sub-expressions, which
    we call the _join_ (or least upper bound) of the two labels: *)

Definition join (l1 l2 : label) : label := l1 && l2.

(** Intuitively if we add up two expressions [e1] labeled [l2] and
    [e2] labeled [l2], the result of the addition will be labeled
    [join l1 l2], which is public iff [l1] is public _and_ [l2] is public. *)

Lemma join_commutative : forall {l1 l2},
  join l1 l2 = join l2 l1.
Proof. intros l1 l2. destruct l1; destruct l2; reflexivity. Qed.

Lemma join_public : forall {l1 l2},
  join l1 l2 = public -> l1 = public /\ l2 = public.
Proof. apply andb_prop. Qed.

Lemma join_public_l : forall {l},
  join public l = l.
Proof. reflexivity. Qed.

Lemma join_public_r : forall {l},
  join l public = l.
Proof. intros l. rewrite join_commutative. reflexivity. Qed.

Lemma join_secret_l : forall {l},
  join secret l = secret.
Proof. reflexivity. Qed.

(** We now define a set of rules for the IFC typing relation for
    arithmetic expressions [P |-a- a \in l], which we read as follows:
    "given the public variables [P] expression [a] has label [l]:" *)

(**
                          -------------------                  (T_Num)
                          P |-a- n \in public

                           -----------------                    (T_Id)
                           P |-a- X \in P X

                  P |-a- a1 \in l1    P |-a- a2 \in l2
                  ------------------------------------        (T_Plus)
                      P |-a- a1+a2 \in join l1 l2

                  P |-a- a1 \in l1    P |-a- a2 \in l2
                  ------------------------------------       (T_Minus)
                      P |-a- a1-a2 \in join l1 l2

                  P |-a- a1 \in l1    P |-a- a2 \in l2
                  ------------------------------------        (T_Mult)
                      P |-a- a1*a2 \in join l1 l2
*)

Reserved Notation "P '|-a-' a \in l" (at level 40).

Inductive aexp_has_label (P:pub_vars) : aexp -> label -> Prop :=
  | T_Num : forall n,
       P |-a- (ANum n) \in public
  | T_Id : forall X,
       P |-a- (AId X) \in (P X)
  | T_Plus : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-a- <{ a1 + a2 }> \in (join l1 l2)
  | T_Minus : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-a- <{ a1 - a2 }> \in (join l1 l2)
  | T_Mult : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-a- <{ a1 * a2 }> \in (join l1 l2)

where "P '|-a-' a '\in' l" := (aexp_has_label P a l).

(* ================================================================= *)
(** ** Computing labels of arithmetic expressions *)

(** Beyond _specifying_ when an expression has a certain label as an
    inductive relation, we can also easily _compute_ the label of an
    expression: *)

Fixpoint label_of_aexp (P:pub_vars) (a:aexp) : label :=
  match a with
  | ANum n => public
  | AId X => P X
  | <{ a1 + a2 }>
  | <{ a1 - a2 }>
  | <{ a1 * a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  end.

Lemma label_of_aexp_sound : forall P a,
    P |-a- a \in label_of_aexp P a.
Proof. intros P a. induction a; constructor; eauto. Qed.

Lemma label_of_aexp_unique : forall P a l,
  P |-a- a \in l ->
  l = label_of_aexp P a.
Proof.
  intros P a l H. induction H; simpl in *;
  (repeat match goal with
    | [Heql : _ = _ |- _] => rewrite Heql in *
   end); eauto.
Qed.

Theorem noninterferent_aexp : forall {P s1 s2 a},
  pub_equiv P s1 s2 ->
  P |-a- a \in public ->
  aeval s1 a = aeval s2 a.
Proof.
  intros P s1 s2 a Heq Ht. remember public as l.
  induction Ht; simpl.
  - reflexivity.
  - apply Heq. apply Heql.
  - destruct (join_public Heql) as [H1 H2].
    rewrite (IHHt1 H1). rewrite (IHHt2 H2). reflexivity.
  - destruct (join_public Heql) as [H1 H2].
    rewrite (IHHt1 H1). rewrite (IHHt2 H2). reflexivity.
  - destruct (join_public Heql) as [H1 H2].
    rewrite (IHHt1 H1). rewrite (IHHt2 H2). reflexivity.
Qed.

(**
                         ----------------------               (T_True)
                         P |-b- true \in public

                         -----------------------             (T_False)
                         P |-b- false \in public

                  P |-a- a1 \in l1    P |-a- a2 \in l2
                  ------------------------------------          (T_Eq)
                      P |-b- a1=a2 \in join l1 l2

...

                             P |-b- b \in l
                            ---------------                    (T_Not)
                            P |-b- ~b \in l

                  P |-b- b1 \in l1    P |-b- b2 \in l2
                  ------------------------------------         (T_And)
                      P |-b- b1&&b2 \in join l1 l2
*)

Reserved Notation "P '|-b-' b \in l" (at level 40).

Inductive bexp_has_label (P:pub_vars) : bexp -> label -> Prop :=
  | T_True :
       P |-b- <{ true }> \in public
  | T_False :
       P |-b- <{ false }> \in public
  | T_Eq : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-b- <{ a1 = a2 }> \in (join l1 l2)
  | T_Neq : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-b- <{ a1 <> a2 }> \in (join l1 l2)
  | T_Le : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-b- <{ a1 <= a2 }> \in (join l1 l2)
  | T_Gt : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-b- <{ a1 > a2 }> \in (join l1 l2)
  | T_Not : forall b l,
       P |-b- b \in l ->
       P |-b- <{ ~b }> \in l
  | T_And : forall b1 l1 b2 l2,
       P |-b- b1 \in l1 ->
       P |-b- b2 \in l2 ->
       P |-b- <{ b1 && b2 }> \in (join l1 l2)

where "P '|-b-' b '\in' l" := (bexp_has_label P b l).

(* ================================================================= *)
(** ** Computing labels of boolean expressions *)

Fixpoint label_of_bexp (P:pub_vars) (a:bexp) : label :=
  match a with
  | <{ true }> | <{ false }> => public
  | <{ a1 = a2 }>
  | <{ a1 <> a2 }>
  | <{ a1 <= a2 }>
  | <{ a1 > a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ ~b }> => label_of_bexp P b
  | <{ b1 && b2 }> => join (label_of_bexp P b1) (label_of_bexp P b2)
  end.

Lemma label_of_bexp_sound : forall P b,
    P |-b- b \in label_of_bexp P b.
Proof.
  intros P b. induction b; constructor;
    eauto using label_of_aexp_sound. Qed.

Lemma label_of_bexp_unique : forall P b l,
  P |-b- b \in l ->
  l = label_of_bexp P b.
Proof.
  intros P a l H. induction H; simpl in *;
  (repeat match goal with
    | [H : _ |-a- _ \in _ |- _] =>
        apply label_of_aexp_unique in H
    | [Heql : _ = _ |- _] => rewrite Heql in *
   end); eauto.
Qed.

Theorem noninterferent_bexp : forall {P s1 s2 b},
  pub_equiv P s1 s2 ->
  P |-b- b \in public ->
  beval s1 b = beval s2 b.
Proof.
  intros P s1 s2 b Heq Ht. remember public as l.
  induction Ht; simpl; try reflexivity;
    try (destruct (join_public Heql) as [H1 H2];
         rewrite H1 in *; rewrite H2 in *).
  - rewrite (noninterferent_aexp Heq H).
    rewrite (noninterferent_aexp Heq H0).
    reflexivity.
  - rewrite (noninterferent_aexp Heq H).
    rewrite (noninterferent_aexp Heq H0).
    reflexivity.
  - rewrite (noninterferent_aexp Heq H).
    rewrite (noninterferent_aexp Heq H0).
    reflexivity.
  - rewrite (noninterferent_aexp Heq H).
    rewrite (noninterferent_aexp Heq H0).
    reflexivity.
  - rewrite (IHHt Heql). reflexivity.
  - rewrite (IHHt1 Logic.eq_refl).
    rewrite (IHHt2 Logic.eq_refl). reflexivity.
Qed.

(* ################################################################# *)
(** * Restrictive type system prohibiting branching on secrets *)

(** For commands, we start with a simple type system that doesn't
    allow any branching on secrets, which is so strong that on its own
    prevents all implicit flows. *)

(** For preventing explicit flows when typing assignments, we need to
    define when it is okay for information to flow from an expression
    with label [l1] to a variable with label [l1]. *)

Definition can_flow (l1 l2 : label) : bool := l1 || negb l2.

(** One way to read this is as boolean implication from [l2] to [l1],
    so [l1] can flow to [l2] iff [l2] is public implies that [l1] is
    public as well. In particular, this disallows that the value of
    secret expressions be assigned to public variables: *)

Lemma cannot_flow_secret_public : can_flow secret public = false.
Proof. reflexivity. Qed.

(** This allows public information to flow everywhere, and secret
    information to flow to secret variables: *)

Lemma can_flow_public : forall l, can_flow public l = true.
Proof. reflexivity. Qed.
Lemma can_flow_secret : can_flow secret secret = true.
Proof. reflexivity. Qed.

Lemma can_flow_refl : forall l,
  can_flow l l = true.
Proof. intros [|]; reflexivity. Qed.

Lemma can_flow_trans : forall l1 l2 l3,
  can_flow l1 l2 = true ->
  can_flow l2 l3 = true ->
  can_flow l1 l3 = true.
Proof. intros l1 l2 l3 H12 H23.
  destruct l1; destruct l2; simpl in *; auto. discriminate H12. Qed.

Lemma can_flow_join_1 : forall l1 l2 l,
  can_flow (join l1 l2) l = true ->
  can_flow l1 l = true.
Proof. intros l1 l2 l. destruct l1; [reflexivity | auto ]. Qed.

Lemma can_flow_join_2 : forall l1 l2 l,
  can_flow (join l1 l2) l = true ->
  can_flow l2 l = true.
Proof. intros l1 l2 l. destruct l1; auto. destruct l2; auto. Qed.

Lemma can_flow_join_l : forall l1 l2 l,
  can_flow l1 l = true ->
  can_flow l2 l = true ->
  can_flow (join l1 l2) l = true.
Proof. intros l1 l2 l H1 H2. destruct l1; simpl in *; auto. Qed.

Lemma can_flow_join_r1 : forall l l1 l2,
  can_flow l l1 = true ->
  can_flow l (join l1 l2) = true.
Proof. intros l l1 l2 H. destruct l; destruct l1; simpl in *; auto.
       discriminate H. Qed.

Lemma can_flow_join_r2 : forall l l1 l2,
  can_flow l l2 = true ->
  can_flow l (join l1 l2) = true.
Proof. intros l l1 l2 H. destruct l; destruct l1; simpl in *; auto. Qed.

(** For commands we use the previous relations to define a
    [pc_well_typed] relation inductively using the following rules: *)

(**
                            ------------                    (PCWT_Skip)
                            P |-pc- skip

             P |-a- a \in l    can_flow l (P X) = true
             -----------------------------------------      (PCWT_Asgn)
                           P |-pc- X := a

                      P |-pc- c1    P |-pc- c2
                      ------------------------               (PCWT_Seq)
                            P |-pc- c1;c2

           P |-b- b \in public    P |-pc- c1    P |-pc- c2
           -----------------------------------------------    (PCWT_If)
                      P |-pc- if b then c1 else c2

                  P |-b- b \in public    P |-pc- c
                  --------------------------------         (PCWT_While)
                    P |-pc- while b then c end
*)

(** Intuitively, explicit flows are prevented by the [can_flow]
    requirement in the assignment rule and implicit flows are
    prevented by the requirement that the boolean condition of [if]
    and [while] has to be a public expression. *)

Reserved Notation "P '|-pc-' c" (at level 40).

Inductive pc_well_typed (P:pub_vars) : com -> Prop :=
  | PCWT_Com :
      P |-pc- <{ skip }>
  | PCWT_Asgn : forall X a l,
      P |-a- a \in l ->
      can_flow l (P X) = true ->
      P |-pc- <{ X := a }>
  | PCWT_Seq : forall c1 c2,
      P |-pc- c1 ->
      P |-pc- c2 ->
      P |-pc- <{ c1 ; c2 }>
  | PCWT_If : forall b c1 c2,
      P |-b- b \in public ->
      P |-pc- c1 ->
      P |-pc- c2 ->
      P |-pc- <{ if b then c1 else c2 end }>
  | PCWT_While : forall b c1,
      P |-b- b \in public ->
      P |-pc- c1 ->
      P |-pc- <{ while b do c1 end }>

where "P '|-pc-' c" := (pc_well_typed P c).

(* ================================================================= *)
(** ** Typechecker for [pc_well_typed] *)

Fixpoint pc_typechecker (P:pub_vars) (c:com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ X := a }> => can_flow (label_of_aexp P a) (P X)
  | <{ c1 ; c2 }> => pc_typechecker P c1 && pc_typechecker P c2
  | <{ if b then c1 else c2 end }> =>
      Bool.eqb (label_of_bexp P b) public &&
      pc_typechecker P c1 && pc_typechecker P c2
  | <{ while b do c1 end }> =>
      Bool.eqb (label_of_bexp P b) public && pc_typechecker P c1
  end.

(** This typechecker is sound and complete with respect to the
    [pc_well_typed] relation. *)

Lemma pc_typechecker_sound : forall P c,
  pc_typechecker P c = true ->
  P |-pc- c.
Proof.
  intros P c. induction c; simpl in *; econstructor;
    try rewrite andb_true_iff in *; try tauto;
    eauto using label_of_aexp_sound, label_of_bexp_sound.
  - destruct H as [H1 H2]. rewrite andb_true_iff in H1; try tauto.
    destruct H1 as [H11 H12]. apply Bool.eqb_prop in H11.
    rewrite <- H11. apply label_of_bexp_sound.
  - destruct H as [H1 H2]. rewrite andb_true_iff in H1; tauto.
  - destruct H as [H1 H2]. apply Bool.eqb_prop in H1.
    rewrite <- H1. apply label_of_bexp_sound.
Qed.

Lemma pc_typechecker_complete : forall P c,
  pc_typechecker P c = false ->
  ~P |-pc- c.
Proof.
  intros P c H Hc. induction Hc; simpl in *;
    try rewrite andb_false_iff in *;
    try tauto; try congruence.
  - apply label_of_aexp_unique in H0.
    rewrite H0 in *. congruence.
  - destruct H; eauto. rewrite andb_false_iff in H.
    destruct H; eauto. rewrite eqb_false_iff in H.
    apply label_of_bexp_unique in H0. congruence.
  - destruct H; eauto. rewrite eqb_false_iff in H.
    apply label_of_bexp_unique in H0. congruence.
Qed.

(* ================================================================= *)
(** ** Secure program that is [pc_well_typed]: *)

Example pc_wt_secure_com :
  xpub |-pc- <{ X := X+1;  (* check: can_flow public public (OK!)  *)
               Y := X+Y*2 (* check: can_flow secret secret (OK!)  *)
             }>.
Proof. apply pc_typechecker_sound. reflexivity. Qed.

(* ================================================================= *)
(** ** Explicit flow prevented by [pc_well_typed]: *)

Example not_pc_wt_insecure_com1 :
  ~ xpub |-pc- <{ X := Y+1;  (* check: can_flow secret public (FAILS!) *)
                 Y := X+Y*2 (* check: can_flow secret secret (OK!)  *)
               }>.
Proof. apply pc_typechecker_complete. reflexivity. Qed.

(* ================================================================= *)
(** ** Implicit flow prevented by [pc_well_typed]: *)

Example not_pc_wt_insecure_com2 :
  ~ xpub |-pc- <{ if Y=0  (* check: P |-b- Y=0 \in public (FAILS!) *)
                 then Y := 42
                 else X := X+1 (* <- bad implicit flow! *)
                 end }>.
Proof. apply pc_typechecker_complete. reflexivity. Qed.

(** We show that all [pc_well_typed] commands are [noninterferent]. *)

Theorem pc_well_typed_noninterferent : forall P c,
  P |-pc- c ->
  noninterferent P c.
Proof.
  intros P c Hwt s1 s2 s1' s2' Heq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  induction Heval1; intros s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - assumption.
  - intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq.
      unfold can_flow in H8. apply orb_prop in H8. destruct H8 as [Hl | Hx].
      * rewrite Hl in *. apply (noninterferent_aexp Heq H7).
      * subst. rewrite Hy in Hx. discriminate Hx.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - eapply IHHeval1_2; try eassumption. eapply IHHeval1_1; eassumption.
  - eapply IHHeval1; eassumption.
  - rewrite (noninterferent_bexp Heq H10) in H.
    rewrite H in H5. discriminate H5.
  - rewrite (noninterferent_bexp Heq H10) in H.
    rewrite H in H5. discriminate H5.
  - eapply IHHeval1; eassumption.
  - assumption.
  - rewrite (noninterferent_bexp Heq H9) in H.
    rewrite H in H2. discriminate H2.
  - rewrite (noninterferent_bexp Heq H7) in H.
    rewrite H in H4. discriminate H4.
  - eapply IHHeval1_2; try eassumption. eapply IHHeval1_1; eassumption.
Qed.

(** Remember the definition of [noninterferent] is as follows:

forall s1 s2 s1' s2',
  pub_equiv P s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv P s1' s2'.

   The main intuition is that the two executions will proceed "in
   lockstep", because all the branch conditions are enforced to be
   public, so they will execute to the same Boolean in both executions. *)

(** The proof is by induction on [s1 =[ c ]=> s1'] and inversion
    on [s2 =[ c ]=> s2'] and [P |-pc- c]. Here is a sketch of the two
    most interesting cases:

    - In the conditional case we have that [c] is [if b then c1 else c2],
      [P |-pc- c1], [P |-pc- c2], and [P |-b- b \in public]. Given this
      last fact we can apply noninterference of boolean expressions to
      show that [beval st1 b = beval st2 b]. If they are both [true],
      we use the induction hypothesis for [c1], and if they are both
      false we use the induction hypothesis for [c2] to conclude.

    - In the assignment case we have that [c] is [X := a],
      [P |-a- a \in l], and [can_flow l (P X) = true], which expands out
      to [l == public \/ P X == secret].

      If [l == public] then by noninterference of arithmetic
      expressions then [aeval st1 a = aeval s2 a], so we are
      assigning the same value to X, which leads to public equivalent
      final states (since the initial states were public equivalent).

      If [P X == secret] then the value of [X] doesn't matter
      for determining whether the final states are [pub_equiv]. *)

(* ================================================================= *)
(** ** [pc_well_typed] too strong for noninterference *)

(** While we have just proved that [pc_well_typed] implies
    noninterference, this is too strong a restriction for just
    noninterference. For instance, the following program contains no
    explicit flows and no implicit flows, so it is intuitively
    noninterferent, yet it is still rejected by the type system just
    because it branches on a secret: *)

Example not_pc_wt_noninterferent_com :
  ~ xpub |-pc- <{ if Y=0 (* check: P |-b- Y=0 \in public (fails!) *)
                 then Z := 0
                 else skip
                 end }>.
Proof. apply pc_typechecker_complete. reflexivity. Qed.

Example not_pc_wt_noninterferent_com_is_noninterferent:
  noninterferent xpub <{ if Y=0
                         then Z := 0
                         else skip
                         end }>.
Proof.
  unfold noninterferent.
  intros s1 s2 s1' s2' H red1 red2.
  inversion red1; inversion red2; subst; clear red1 red2.
  - inversion H6; subst; clear H6.
    inversion H13; subst; clear H13.
    intros x Px.
    destruct (String.eqb_spec x Z); subst.
    + discriminate.
    + rewrite !t_update_neq; auto.
  - inversion H6; subst; clear H6.
    inversion H13; subst; clear H13.
    intros x Px.
    destruct (String.eqb_spec x Z); subst.
    + discriminate.
    + rewrite !t_update_neq; auto.
  - inversion H6; subst; clear H6.
    inversion H13; subst; clear H13.
    intros x Px.
    destruct (String.eqb_spec x Z); subst.
    + discriminate.
    + rewrite !t_update_neq; auto.
  - inversion H6; subst; clear H6.
    inversion H13; subst; clear H13.
    intros x Px. eapply H; eauto.
Qed.

(** We will later show that [pc_well_typed] enforces a security
    notion called program counter security, which prevents some
    side-channel attacks and which also serves as the base for
    cryptographic constant-time. *)

(* ################################################################# *)
(** * IFC type system allowing branching on secrets *)

(** We now instead extend this to a more permissive type system for
    noninterference in which we do allow branching on secrets.

    Now to prevent implicit flows we need to track whether we have
    branched on secrets. We do this with a _program counter_ ([pc])
    label, which records the labels of the branches we have taken at
    the current point in the execution (joined together). *)

(**
                      ----------------                      (WT_Skip)
                      P ;; pc |-- skip

       P |-a- a \in l   can_flow (join pc l) (P X) = true
       --------------------------------------------------   (WT_Asgn)
                     P ;; pc |-- X := a

                P ;; pc |-- c1    P ;; pc |-- c2
                --------------------------------             (WT_Seq)
                      P ;; pc |-- c1;c2

           P |-b- b \in l    P ;; join pc l |-- c1
                             P ;; join pc l |-- c2
           ---------------------------------------            (WT_If)
                P ;; pc |-- if b then c1 else c2

              P |-b- b \in l    P ;; join pc l |-- c
              --------------------------------------       (WT_While)
                P ;; pc |-- while b then c end
*)

Reserved Notation "P ';;' pc '|--' c" (at level 40).

Inductive well_typed (P:pub_vars) : label -> com -> Prop :=
  | WT_Com : forall pc,
      P ;; pc |-- <{ skip }>
  | WT_Asgn : forall pc X a l,
      P |-a- a \in l ->
      can_flow (join pc l) (P X) = true ->
      P ;; pc |-- <{ X := a }>
  | WT_Seq : forall pc c1 c2,
      P ;; pc |-- c1 ->
      P ;; pc |-- c2 ->
      P ;; pc |-- <{ c1 ; c2 }>
  | WT_If : forall pc b l c1 c2,
      P |-b- b \in l ->
      P ;; (join pc l) |-- c1 ->
      P ;; (join pc l) |-- c2 ->
      P ;; pc |-- <{ if b then c1 else c2 end }>
  | WT_While : forall pc b l c1,
      P |-b- b \in l ->
      P ;; (join pc l) |-- c1 ->
      P ;; pc |-- <{ while b do c1 end }>

where "P ';;' pc '|--' c" := (well_typed P pc c).

(** We now allow branching on arbitrary boolean expressions in [if]
    and [while], but join the label of the branch expression to the
    [pc]. Then in the assignment rule we require that also the [pc]
    label flows to the label of the assigned variable, in order to
    still prevent implicit flows. *)

(* ================================================================= *)
(** ** Typechecker for this [well_typed] relation. *)

Fixpoint wt_typechecker (P:pub_vars) (pc:label) (c:com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ X := a }> => can_flow (join pc (label_of_aexp P a)) (P X)
  | <{ c1 ; c2 }> => wt_typechecker P pc c1 && wt_typechecker P pc c2
  | <{ if b then c1 else c2 end }> =>
      wt_typechecker P (join pc (label_of_bexp P b)) c1 &&
      wt_typechecker P (join pc (label_of_bexp P b)) c2
  | <{ while b do c1 end }> =>
      wt_typechecker P (join pc (label_of_bexp P b)) c1
  end.

Lemma wt_typechecker_sound : forall P pc c,
  wt_typechecker P pc c = true ->
  P ;; pc |-- c.
Proof.
  intros P pc c. generalize dependent pc.
  induction c; intros pc H; simpl in *; econstructor;
    try rewrite andb_true_iff in *;
    try destruct H; try tauto;
    eauto using label_of_aexp_sound, label_of_bexp_sound.
Qed.

Lemma wt_typechecker_complete : forall P pc c,
  wt_typechecker P pc c = false ->
  ~ P ;; pc |-- c.
Proof.
  intros P pc c H Hc. induction Hc; simpl in *;
    try rewrite andb_false_iff in *; try tauto; try congruence.
  - apply label_of_aexp_unique in H0.
    rewrite H0 in *. congruence.
  - destruct H; apply label_of_bexp_unique in H0; subst; eauto.
  - destruct H; apply label_of_bexp_unique in H0; subst; eauto.
Qed.

(** With this more permissive type system we can accept more
    noninterferent programs that were rejected by [pc_well_typed]. *)

Example wt_noninterferent_com :
  xpub ;; public |--
    <{ if Y=0 (* raises pc label from public to secret *)
       then Z := 0 (* check: [can_flow secret secret] (OK!) *)
       else skip
       end }>.
Proof. apply wt_typechecker_sound. reflexivity. Qed.

(** And we still prevent implicit flows: *)

Example not_wt_insecure_com2 :
  ~ xpub ;; public |--
    <{ if Y=0  (* raises pc label from public to secret *)
       then Y := 42
       else X := X+1 (* check: [can_flow secret public] (FAILS!)  *)
       end }>.
Proof. apply wt_typechecker_complete. reflexivity. Qed.

Lemma weaken_pc : forall {P pc1 pc2 c},
  P;; pc1 |-- c ->
  can_flow pc2 pc1 = true->
  P;; pc2 |-- c.
Proof.
  intros P pc1 pc2 c H. generalize dependent pc2.
  induction H; subst; intros pc2 Hcan_flow.
  - constructor.
  - econstructor; try eassumption. apply can_flow_join_l.
    + apply can_flow_join_1 in H0. eapply can_flow_trans; eassumption.
    + apply can_flow_join_2 in H0. assumption.
  - constructor; auto.
  - econstructor; try eassumption.
    + apply IHwell_typed1. apply can_flow_join_l.
      * apply can_flow_join_r1. assumption.
      * apply can_flow_join_r2. apply can_flow_refl.
    + apply IHwell_typed2. apply can_flow_join_l.
      * apply can_flow_join_r1. assumption.
      * apply can_flow_join_r2. apply can_flow_refl.
  - econstructor; try eassumption. apply IHwell_typed. apply can_flow_join_l.
      * apply can_flow_join_r1. assumption.
      * apply can_flow_join_r2. apply can_flow_refl.
Qed.

(* ================================================================= *)
(** ** Dealing with unsynchronized executions running different code *)

(** The [different_code] corollary below is crucial for proving that
    the type system above still enforces noninterference even if it
    allows branching on secrets, and its proof follows easily from the
    following basic lemma: *)

Lemma secret_run : forall {P c s s'},
  P;; secret |-- c ->
  s =[ c ]=> s' ->
  pub_equiv P s s'.
Proof.
  intros P c s s' Hwt Heval. induction Heval; inversion Hwt;
    subst; eauto using pub_equiv_trans, pub_equiv_refl.
  - (* assignment case: crucial for preventing implicit flows *)
    intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + (* assigned variable being public leads to contradiction:
         type system prevents public variables from being assigned *)
      subst. rewrite join_secret_l in H4. rewrite Hy in H4. discriminate H4.
    + rewrite t_update_neq; auto.
Qed.

Corollary different_code : forall P c1 c2 s1 s2 s1' s2',
  P;; secret |-- c1 ->
  P;; secret |-- c2 ->
  pub_equiv P s1 s2 ->
  s1 =[ c1 ]=> s1' ->
  s2 =[ c2 ]=> s2' ->
  pub_equiv P s1' s2'.
Proof.
  intros P c1 c2 s1 s2 s1' s2' Hwt1 Hwt2 Hequiv Heval1 Heval2.
  eapply secret_run in Hwt1; [| eassumption].
  eapply secret_run in Hwt2; [| eassumption].
  apply pub_equiv_sym in Hwt1.
  eapply pub_equiv_trans; try eassumption.
  eapply pub_equiv_trans; eassumption.
Qed.

(* ================================================================= *)
(** ** We show that [well_typed] commands are [noninterferent]. *)

Theorem well_typed_noninterferent : forall P c,
  P;; public |-- c ->
  noninterferent P c.
Proof.
  intros P c Hwt s1 s2 s1' s2' Heq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  induction Heval1; intros s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst; try rewrite join_public_l in *.
  - assumption.
  - intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq.
      unfold can_flow in H9.
      apply orb_prop in H9. destruct H9 as [Hl | Hx].
      * rewrite Hl in *. apply (noninterferent_aexp Heq H8).
      * subst. rewrite Hy in Hx. discriminate Hx.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - eapply IHHeval1_2; try eassumption. eapply IHHeval1_1; eassumption.
  - (* if true-true *)
    eapply IHHeval1; try eassumption.
    eapply weaken_pc; try eassumption. apply can_flow_public.
  - (* if true-false *) destruct l.
    + rewrite (noninterferent_bexp Heq H11) in H.
      rewrite H in H5. discriminate H5.
    + eapply different_code with (c1:=c1) (c2:=c2); eassumption.
  - (* if false-true *) destruct l.
    + rewrite (noninterferent_bexp Heq H11) in H.
      rewrite H in H5. discriminate H5.
    + eapply different_code with (c1:=c2) (c2:=c1); eassumption.
  - (* if false-false *)
    eapply IHHeval1; try eassumption.
    eapply weaken_pc; try eassumption. apply can_flow_public.
  - (* while false-false *) assumption.
  - (* while false-true *) destruct l.
    + rewrite (noninterferent_bexp Heq H10) in H.
      rewrite H in H2. discriminate H2.
    + eapply different_code with (c1:=<{skip}>) (c2:=<{c;while b do c end}>);
        repeat (try eassumption; try econstructor).
  - (* while true-false *) destruct l.
    + rewrite (noninterferent_bexp Heq H8) in H.
      rewrite H in H4. discriminate H4.
    + eapply different_code with (c1:=<{c;while b do c end}>) (c2:=<{skip}>);
        repeat (try eassumption; try econstructor).
  - (* while true-true *)
    eapply IHHeval1_2; try eassumption. eapply IHHeval1_1; try eassumption.
    eapply weaken_pc; try eassumption. apply can_flow_public.
Qed.

(** The noninterference proof is still relatively simple, since the
    cases in which we take different branches based on secret
    information are all handled by the [different_code] lemma.

    Another key ingredient for having a simple noninterference proof
    is working with a big-step semantics for Imp. *)

(* ################################################################# *)
(** * Type system for termination-sensitive noninterference *)

(** The noninterference notion we used above was "termination
    insensitive". If we prevent loop conditions depending on secrets
    we can actually enforce termination-sensitive noninterference
    (TSNI), which we defined in [Noninterference] as follows: *)

Definition tsni P c :=
  forall s1 s2 s1',
  s1 =[ c ]=> s1' ->
  pub_equiv P s1 s2 ->
  (exists s2', s2 =[ c ]=> s2' /\ pub_equiv P s1' s2').

(** We could prove that [pc_well_typed] enforces TSNI, but that typing
    relation is too restrictive, since for TSNI we can allow
    if-then-else conditions to depend on secrets. So we define a new
    type system that only prevents _loop_ conditions from depending on
    secrets. *)

(* ================================================================= *)
(** ** We just need to update the while rule of [well_typed]: *)

(** Old rule for noninterference:

              P |-b- b \in l    P ;; join pc l |-- c
              --------------------------------------       (WT_While)
                P ;; pc |-- while b then c end

    New rule for termination-sensitive noninterference:

          P |-b- b \in public    P ;; public |-ts- c
          ------------------------------------------       (TS_While)
             P ;; public |-ts- while b then c end

   Beyond requiring the label of [b] to be [public], this rule also
   requires that once one branches on secrets with if-then-else
   (i.e. pc=secret) no while loops are allowed.
*)

Reserved Notation "P ';;' pc '|-ts-' c" (at level 40).

Inductive ts_well_typed (P:pub_vars) : label -> com -> Prop :=
  | TS_Com : forall pc,
      P;; pc |-ts- <{ skip }>
  | TS_Asgn : forall pc X a l,
      P |-a- a \in l ->
      can_flow (join pc l) (P X) = true ->
      P;; pc |-ts- <{ X := a }>
  | TS_Seq : forall pc c1 c2,
      P;; pc |-ts- c1 ->
      P;; pc |-ts- c2 ->
      P;; pc |-ts- <{ c1 ; c2 }>
  | TS_If : forall pc b l c1 c2,
      P |-b- b \in l ->
      P;; (join pc l) |-ts- c1 ->
      P;; (join pc l) |-ts- c2 ->
      P;; pc |-ts- <{ if b then c1 else c2 end }>
  | TS_While : forall b c1,
      P |-b- b \in public -> (* <-- NEW *)
      P;; public |-ts- c1 -> (* <-- ONLY pc=public *)
      P;; public |-ts- <{ while b do c1 end }>

where "P ';;' pc '|-ts-' c" := (ts_well_typed P pc c).

(* ================================================================= *)
(** ** We prove that [ts_well_typed] enforces TSNI. *)

(** For this we show that [ts_well_typed] implies [well_typed], so
    by our previous theorem also [noninterference].

    Then we show that [P;; secret |-ts- c] implies termination.

    We use this to show that [ts_well_typed] implies equitermination, which
    together with noninterference implies termination-sensitive noninterference.
 *)

Theorem ts_well_typed_well_typed : forall P c pc,
  P;; pc |-ts- c ->
  P;; pc |-- c.
Proof.
  intros P c pc H. induction H; econstructor; eassumption.
Qed.

Theorem ts_well_typed_noninterferent : forall P c,
  P;; public |-ts- c ->
  noninterferent P c.
Proof.
  intros P c H. apply well_typed_noninterferent.
  apply ts_well_typed_well_typed. apply H.
Qed.

Lemma ts_secret_run_terminating : forall {P c s},
  P;; secret |-ts- c ->
  exists s', s =[ c ]=> s'.
Proof.
  intros P c s Hwt. remember secret as l.
  generalize dependent s. induction Hwt; intro s.
  - eexists. econstructor.
  - eexists. econstructor. reflexivity.
  - destruct (IHHwt1 Heql s) as  [s' IH1].
    destruct (IHHwt2 Heql s') as [s''IH2]. eexists. econstructor; eassumption.
  - rewrite Heql in *. rewrite join_secret_l in *.
    destruct (IHHwt1 Logic.eq_refl s) as [s1 IH1].
    destruct (IHHwt2 Logic.eq_refl s) as [s2 IH2].
    destruct (beval s b) eqn:Heq; eexists; econstructor; eassumption.
  - discriminate Heql.
Qed.

Theorem ts_well_typed_equitermination : forall {P c s1 s2 s1'},
  P;; public |-ts- c ->
  s1 =[ c ]=> s1' ->
  pub_equiv P s1 s2 ->
  exists s2', s2 =[ c ]=> s2'.
Proof.
  intros P C s1 s2 s1' Hwt Heval. generalize dependent s2.
  induction Heval; intros s2 Heq; inversion Hwt; subst.
  - eexists. constructor.
  - eexists. econstructor. reflexivity.
  - destruct (IHHeval1 H2 _ Heq) as [s2' IH1].
    assert (Heq' : pub_equiv P st' s2').
    { eapply ts_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption]. assumption. }
    destruct (IHHeval2 H3 _ Heq') as [s2'' IH2].
    eexists. econstructor; eassumption.
  - rewrite join_public_l in *. destruct l.
    + destruct (IHHeval H5 _ Heq) as [s2' IH1].
      eexists. apply E_IfTrue; [ | eassumption ].
      * eapply noninterferent_bexp in Heq; [ | eassumption ]. congruence.
    + eapply ts_secret_run_terminating in H5. destruct H5 as [s1' H5].
      eapply ts_secret_run_terminating in H6. destruct H6 as [s2' H6].
      destruct (beval s2 b) eqn:Heq2; eexists; econstructor; eassumption.
  - rewrite join_public_l in *. destruct l.
    + destruct (IHHeval H6 _ Heq) as [s2' IH1].
      eexists. apply E_IfFalse; [ | eassumption ].
      * eapply noninterferent_bexp in Heq; [ | eassumption ]. congruence.
    + eapply ts_secret_run_terminating in H5. destruct H5 as [s1' H5].
      eapply ts_secret_run_terminating in H6. destruct H6 as [s2' H6].
      destruct (beval s2 b) eqn:Heq2; eexists; econstructor; eassumption.
  - eapply noninterferent_bexp in Heq; [ | eassumption ].
    eexists. apply E_WhileFalse. congruence.
  - destruct (IHHeval1 H3 _ Heq) as [s2' IH1].
    assert (Heq' : pub_equiv P st' s2').
    { eapply ts_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption]. assumption. }
    destruct (IHHeval2 Hwt _ Heq') as [s2'' IH2].
    eapply noninterferent_bexp in Heq; [ | eassumption ].
    eexists. eapply E_WhileTrue; try congruence; eassumption.
Qed.

Corollary ts_well_typed_tsni : forall P c,
  P;; public |-ts- c ->
  tsni P c.
Proof.
  intros P c Hwt s1 s2 s1' Heval1 Heq.
  destruct (ts_well_typed_equitermination Hwt Heval1 Heq) as [s2' Heval2].
  exists s2'. split; [assumption| ].
  eapply ts_well_typed_noninterferent; eassumption.
Qed.

(* ################################################################# *)
(** * Program counter security *)

(** Especially for cryptographic code one is also worried about
    side-channel attacks, in which secrets are for instance leaked via
    the execution time of the program. For instance, most processors
    have instruction caches, which make executing cached instructions
    faster than non-cached ones.

    To prevent such attacks, cryptographic code is normally written
    without branching on any secrets. To formalize this we introduce a
    new security notion called _program counter security_, which
    considers the program's branching visible to the attacker. More
    precisely, we instrument the operational semantics of [Imp] to
    also record the control-flow decisions of the program. *)

Definition branches := list bool.

(* ================================================================= *)
(** ** Instrumented semantics with branches

                     ---------------------                         (E_Skip)
                     st =[ skip ]=> st, []

                       aeval st a = n
               -----------------------------------                 (E_Asgn)
               st =[ x := a ]=> (x !-> n ; st), []

      st  =[ c1 ]=> st', bs1   st' =[ c2 ]=> st'', bs2
      ------------------------------------------------              (E_Seq)
               st =[ c1;c2 ]=> st'', (bs1++bs2)

            beval st b = true     st =[ c1 ]=> st', bs1
        -------------------------------------------------        (E_IfTrue)
        st =[ if b then c1 else c2 end ]=> st', true::bs1

            beval st b = false    st =[ c2 ]=> st', bs2
       --------------------------------------------------       (E_IfFalse)
       st =[ if b then c1 else c2 end ]=> st', false::bs2

  st =[ if b then c; while b do c end else skip end ]=> st, os
  ------------------------------------------------------------    (E_While)
            st =[ while b do c end ]=> st, os
*)

Reserved Notation
         "st '=[' c ']=>' st' , bs"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive pceval : com -> state -> state -> branches -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st, []
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st), []
  | E_Seq : forall c1 c2 st st' st'' bs1 bs2,
      st  =[ c1 ]=> st', bs1  ->
      st' =[ c2 ]=> st'', bs2 ->
      st  =[ c1 ; c2 ]=> st'', (bs1++bs2)
  | E_IfTrue : forall st st' b c1 c2 bs1,
      beval st b = true ->
      st =[ c1 ]=> st', bs1 ->
      st =[ if b then c1 else c2 end]=> st', (true::bs1)
  | E_IfFalse : forall st st' b c1 c2 bs1,
      beval st b = false ->
      st =[ c2 ]=> st', bs1 ->
      st =[ if b then c1 else c2 end]=> st', (false::bs1)
  | E_While : forall b st os c, (* <- Nice trick; from small-step semantics *)
      st =[ if b then c; while b do c end else skip end ]=> st, os ->
      st =[ while b do c end ]=> st, os

  where "st =[ c ]=> st' , bs" := (pceval c st st' bs).

Lemma pceval_ceval : forall c st st' bs,
  st =[ c ]=> st', bs ->
  st =[ c ]=> st'.
Proof.
  intros c st st' bs H. induction H; try (econstructor; eassumption).
  - (* need to justify the while trick *)
    inversion IHpceval.
    + inversion H6. subst. eapply E_WhileTrue; eauto.
    + eapply E_WhileFalse; eauto.
Qed.

(* ================================================================= *)
(** ** Program counter security definition *)

(** Using the instrumented semantics we define program counter security: *)

Definition pc_secure P c := forall s1 s2 s1' s2' bs1 bs2,
  pub_equiv P s1 s2 ->
  s1 =[ c ]=> s1', bs1 ->
  s2 =[ c ]=> s2', bs2 ->
  bs1 = bs2.

(** Program counter security is mostly orthogonal to noninterference and
    instead of relating the final states it requires the branches of
    the program to be independent of secrets.

    Our restrictive [pc_well_typed] relation enforces both
    noninterference (as we already proved above) and program counter security: *)

Theorem pc_well_typed_pc_secure : forall P c,
  P |-pc- c ->
  pc_secure P c.
Proof.
  intros P c Hwt s1 s2 s1' s2' bs1 bs2 Heq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent bs2.
  induction Heval1; intros bs2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - reflexivity.
  - reflexivity.
  - erewrite IHHeval1_2; [erewrite IHHeval1_1 | | |];
      try reflexivity; try eassumption.
    (* the proof does rely on noninterference for the sequencing case *)
    eapply pc_well_typed_noninterferent;
      [ | eassumption | eapply pceval_ceval; eassumption
                      | eapply pceval_ceval; eassumption ]; eassumption.
  - f_equal. eapply IHHeval1; try eassumption.
  - rewrite (noninterferent_bexp Heq H11) in H.
    rewrite H in H6. discriminate H6.
  - rewrite (noninterferent_bexp Heq H11) in H.
    rewrite H in H6. discriminate H6.
  - f_equal. eapply IHHeval1; eassumption.
  - eapply IHHeval1; try eassumption. repeat constructor; eassumption.
Qed.

(** The proof does rely on [pc_well_typed] implying noninterference
    for the sequencing case (and indirectly for the while case too,
    since in our semantics while evaluates to a sequence). *)

(* 2025-04-09 13:06 *)
