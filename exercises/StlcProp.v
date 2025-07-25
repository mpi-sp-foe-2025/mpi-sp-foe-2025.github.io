(** * StlcProp: Properties of STLC *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Stlc.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".
Module STLCProp.
Import STLC.

(** In this chapter, we develop the fundamental theory of the Simply
    Typed Lambda Calculus -- in particular, the type safety
    theorem. *)

(* ################################################################# *)
(** * Canonical Forms *)

(** As we saw for the very simple language in the [Types]
    chapter, the first step in establishing basic properties of
    reduction and types is to identify the possible _canonical
    forms_ (i.e., well-typed values) belonging to each type.  For
    [Bool], these are again the boolean values [true] and [false]; for
    arrow types, they are lambda-abstractions. *)

(** Formally, we will need these lemmas only for terms that are not
    only well typed but _closed_ -- i.e., well typed in the empty
    context. *)

Lemma canonical_forms_bool : forall t,
  empty |-- t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; auto.
  inversion HT.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |-- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal as [x ? t1| |] ; inversion HT; subst.
  exists x, t1. reflexivity.
Qed.

(* ################################################################# *)
(** * Progress *)

(** The _progress_ theorem tells us that closed, well-typed
    terms are not stuck: either a well-typed term is a value, or it
    can take a reduction step.  The proof is a relatively
    straightforward extension of the progress proof we saw in the
    [Types] chapter.  We give the proof in English first, then
    the formal version. *)

Theorem progress : forall t T,
  empty |-- t \in T ->
  value t \/ exists t', t --> t'.

(** _Proof_: By induction on the derivation of [|-- t \in T].

    - The last rule of the derivation cannot be [T_Var], since a
      variable is never well typed in an empty context.

    - The [T_True], [T_False], and [T_Abs] cases are trivial, since in
      each of these cases we can see by inspecting the rule that [t]
      is a value.

    - If the last rule of the derivation is [T_App], then [t] has the
      form [t1 t2] for some [t1] and [t2], where [|-- t1 \in T2 -> T]
      and [|-- t2 \in T2] for some type [T2].  The induction hypothesis
      for the first subderivation says that either [t1] is a value or
      else it can take a reduction step.

        - If [t1] is a value, then consider [t2], which by the
          induction hypothesis for the second subderivation must also
          either be a value or take a step.

            - Suppose [t2] is a value.  Since [t1] is a value with an
              arrow type, it must be a lambda abstraction; hence [t1
              t2] can take a step by [ST_AppAbs].

            - Otherwise, [t2] can take a step, and hence so can [t1
              t2] by [ST_App2].

        - If [t1] can take a step, then so can [t1 t2] by [ST_App1].

    - If the last rule of the derivation is [T_If], then [t = if
      t1 then t2 else t3], where [t1] has type [Bool].  The first IH
      says that [t1] either is a value or takes a step.

        - If [t1] is a value, then since it has type [Bool] it must be
          either [true] or [false].  If it is [true], then [t] steps to
          [t2]; otherwise it steps to [t3].

        - Otherwise, [t1] takes a step, and therefore so does [t] (by
          [ST_If]). *)
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
  (* auto solves all three cases in which t is a value *)
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an
       empty context *)
    discriminate H.

  - (* T_App *)
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        eapply canonical_forms_fun in Ht1; [|assumption].
        destruct Ht1 as [x [t0 H1]]. subst.
        exists (<{ [x:=t2]t0 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists (<{t1 t2'}>)...

    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists (<{t1' t2}>)...

  - (* T_If *)
    right. destruct IHHt1...

    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.

    + (* t1 also steps *)
      destruct H as [t1' Hstp]. exists <{if t1' then t2 else t3}>...
Qed.

(** **** Exercise: 3 stars, advanced, optional (progress_from_term_ind)

    Show that progress can also be proved by induction on terms
    instead of induction on typing derivations. *)

Theorem progress' : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof.
  intros t.
  induction t; intros T Ht; auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Preservation *)

(** The other half of the type soundness property is the
    preservation of types during reduction.  For this part, we'll need
    to develop some technical machinery for reasoning about variables
    and substitution.  Working from top to bottom (from the high-level
    property we are actually interested in to the lowest-level
    technical lemmas that are needed by various cases of the more
    interesting proofs), the story goes like this:

      - The _preservation theorem_ is proved by induction on a typing
        derivation and case analysis on the step relation,
        pretty much as we did in the [Types] chapter.
        The one case that is significantly different is the one for
        the [ST_AppAbs] rule, whose definition uses the substitution
        operation.  To see that this step preserves typing, we need to
        know that the substitution itself does.  So we prove a...

      - _substitution lemma_, stating that substituting a (closed,
        well-typed) term [s] for a variable [x] in a term [t]
        preserves the type of [t].  The proof goes by induction on the
        form of [t] and requires looking at all the different cases in
        the definition of substitition.  This time, for the variables
        case, we discover that we need to deduce from the fact that a
        term [s] has type S in the empty context the fact that [s] has
        type S in every context. For this we prove a...

      - _weakening_ lemma, showing that typing is preserved under
        "extensions" to the context [Gamma].

   To make Coq happy, of course, we need to formalize the story in the
   opposite order, starting with weakening... *)

(* ================================================================= *)
(** ** The Weakening Lemma *)

(** First, we show that typing is preserved under "extensions" to the
    context [Gamma].  (Recall the definition of "includedin" from
    Maps.v.) *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

(** The following simple corollary is what we actually need below. *)

Lemma weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* ================================================================= *)
(** ** The Substitution Lemma *)

(** Now we come to the conceptual heart of the proof that reduction
    preserves types -- namely, the observation that _substitution_
    preserves types. *)

(** Formally, the so-called _substitution lemma_ says this:
    Suppose we have a term [t] with a free variable [x], and suppose
    we've assigned a type [T] to [t] under the assumption that [x] has
    some type [U].  Also, suppose that we have some other term [v] and
    that we've shown that [v] has type [U].  Then, since [v] satisfies
    the assumption we made about [x] when typing [t], we can
    substitute [v] for each of the occurrences of [x] in [t] and
    obtain a new term that still has type [T]. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  x |-> U ; Gamma |-- t \in T ->
  empty |-- v \in U   ->
  Gamma |-- [x:=v]t \in T.

(** The substitution lemma can be viewed as a kind of "commutation
    property."  Intuitively, it says that substitution and typing can
    be done in either order: we can either assign types to the terms
    [t] and [v] separately (under suitable contexts) and then combine
    them using substitution, or we can substitute first and then
    assign a type to [ [x:=v] t ]; the result is the same either
    way.

    _Proof_: We show, by induction on [t], that for all [T] and
    [Gamma], if [x|->U; Gamma |-- t \in T] and [|-- v \in U], then
    [Gamma |-- [x:=v]t \in T].

      - If [t] is a variable there are two cases to consider,
        depending on whether [t] is [x] or some other variable.

          - If [t = x], then from the fact that [x|->U; Gamma |-- x \in
            T] we conclude that [U = T].  We must show that [[x:=v]x =
            v] has type [T] under [Gamma], given the assumption that
            [v] has type [U = T] under the empty context.  This
            follows from the weakening lemma.

          - If [t] is some variable [y] that is not equal to [x], then
            we need only note that [y] has the same type under [x|->U;
            Gamma] as under [Gamma].

      - If [t] is an abstraction [\y:S, t0], then [T = S->T1] and
        the IH tells us, for all [Gamma'] and [T0], that if [x|->U;
        Gamma' |-- t0 \in T0], then [Gamma' |-- [x:=v]t0 \in T0].
        Moreover, by inspecting the typing rules we see it must be
        the case that [y|->S; x|->U; Gamma |-- t0 \in T1].

        The substitution in the conclusion behaves differently
        depending on whether [x] and [y] are the same variable.

        First, suppose [x = y].  Then, by the definition of
        substitution, [[x:=v]t = t], so we just need to show [Gamma |--
        t \in T].  Using [T_Abs], we need to show that [y|->S; Gamma
        |-- t0 \in T1]. But we know [y|->S; x|->U; Gamma |-- t0 \in T1],
        and the claim follows since [x = y].

        Second, suppose [x <> y]. Again, using [T_Abs],
        we need to show that [y|->S; Gamma |-- [x:=v]t0 \in T1].
        Since [x <> y], we have
        [y|->S; x|->U; Gamma = x|->U; y|->S; Gamma]. So
        we have [x|->U; y|->S; Gamma |-- t0 \in T1]. Then, the
        the IH applies (taking [Gamma' = y|->S; Gamma]), giving us
        [y|->S; Gamma |-- [x:=v]t0 \in T1], as required.

      - If [t] is an application [t1 t2], the result follows
        straightforwardly from the definition of substitution and the
        induction hypotheses.

      - The remaining cases are similar to the application case. *)

Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

(** One technical subtlety in the statement of the above lemma is that
    we assume [v] has type [U] in the _empty_ context -- in other
    words, we assume [v] is closed.  (Since we are using a simple
    definition of substition that is not capture-avoiding, it doesn't
    make sense to substitute non-closed terms into other terms.
    Fortunately, closed terms are all we need!)
 *)

(** **** Exercise: 3 stars, advanced (substitution_preserves_typing_from_typing_ind)

    Show that substitution_preserves_typing can also be
    proved by induction on typing derivations instead
    of induction on terms. *)
Lemma substitution_preserves_typing_from_typing_ind : forall Gamma x U t v T,
  x |-> U ; Gamma |-- t \in T ->
  empty |-- v \in U   ->
  Gamma |-- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
 (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Main Theorem *)

(** We now have the ingredients we need to prove preservation: if a
    closed, well-typed term [t] has type [T] and takes a step to [t'],
    then [t'] is also a closed term with type [T].  In other words,
    the small-step reduction relation preserves types. *)

Theorem preservation : forall t t' T,
  empty |-- t \in T  ->
  t --> t'  ->
  empty |-- t' \in T.

(** _Proof_: By induction on the derivation of [|-- t \in T].

    - We can immediately rule out [T_Var], [T_Abs], [T_True], and
      [T_False] as final rules in the derivation, since in each of these
      cases [t] cannot take a step.

    - If the last rule in the derivation is [T_App], then [t = t1 t2],
      and there are subderivations showing that [|-- t1 \in T2->T] and
      [|-- t2 \in T2] plus two induction hypotheses: (1) [t1 --> t1']
      implies [|-- t1' \in T2->T] and (2) [t2 --> t2'] implies [|-- t2'
      \in T2].  There are now three subcases to consider, one for
      each rule that could be used to show that [t1 t2] takes a step
      to [t'].

        - If [t1 t2] takes a step by [ST_App1], with [t1] stepping to
          [t1'], then, by the first IH, [t1'] has the same type as
          [t1] ([|-- t1' \in T2->T]), and hence by [T_App] [t1' t2] has
          type [T].

        - The [ST_App2] case is similar, using the second IH.

        - If [t1 t2] takes a step by [ST_AppAbs], then [t1 =
          \x:T0,t0] and [t1 t2] steps to [[x0:=t2]t0]; the desired
          result now follows from the substitution lemma.

    - If the last rule in the derivation is [T_If], then [t = if
      t1 then t2 else t3], with [|-- t1 \in Bool], [|-- t2 \in T1], and
      [|-- t3 \in T1], and with three induction hypotheses: (1) [t1 -->
      t1'] implies [|-- t1' \in Bool], (2) [t2 --> t2'] implies [|-- t2'
      \in T1], and (3) [t3 --> t3'] implies [|-- t3' \in T1].

      There are again three subcases to consider, depending on how [t]
      steps.

        - If [t] steps to [t2] or [t3] by [ST_IfTrue] or
          [ST_IfFalse], the result is immediate, since [t2] and [t3]
          have the same type as [t].

        - Otherwise, [t] steps by [ST_If], and the desired
          conclusion follows directly from the first induction
          hypothesis. *)

Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
Qed.

(** **** Exercise: 2 stars, standard, especially useful (subject_expansion_stlc)

    An exercise in the [Types] chapter asked about the _subject
    expansion_ property for the simple language of arithmetic and
    boolean expressions.  This property did not hold for that language,
    and it also fails for STLC.  That is, it is not always the case that,
    if [t --> t'] and [empty |-- t' \in T], then [empty |-- t \in T].
    Show this by giving a counter-example that does _not involve
    conditionals_. *)

(* FILL IN HERE *)

Theorem not_subject_expansion:
  exists t t' T, t --> t' /\ (empty |-- t' \in T) /\ ~ (empty |-- t \in T).
Proof.
  (* Write "exists <{ ... }>" to use STLC notation. *)
  (* FILL IN HERE *) Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_subject_expansion_stlc : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Type Soundness *)

(** **** Exercise: 2 stars, standard, optional (type_soundness)

    Put progress and preservation together and show that a well-typed
    term can _never_ reach a stuck state.  *)

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary type_soundness : forall t t' T,
  empty |-- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Uniqueness of Types *)

(** **** Exercise: 3 stars, standard (unique_types)

    Another nice property of the STLC is that types are unique: a
    given term (in a given context) has at most one type. *)

Theorem unique_types : forall Gamma e T T',
  Gamma |-- e \in T ->
  Gamma |-- e \in T' ->
  T = T'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Context Invariance (Optional) *)

(** Another standard technical lemma associated with typed languages
    is _context invariance_. It states that typing is preserved under
    "inessential changes" to the context [Gamma] -- in particular,
    changes that do not affect any of the free variables of the
    term. In this section, we establish this property for our system,
    introducing some other standard terminology on the way.  *)

(** First, we need to define the _free variables_ in a term -- i.e.,
    variables that are used in the term in positions that are _not_ in
    the scope of an enclosing function abstraction binding a variable
    of the same name.

    More technically, a variable [x] _appears free in_ a term _t_ if
    [t] contains some occurrence of [x] that is not under an
    abstraction labeled [x]. For example:
      - [y] appears free, but [x] does not, in [\x:T->U, x y]
      - both [x] and [y] appear free in [(\x:T->U, x y) x]
      - no variables appear free in [\x:T->U, \y:T, x y]

      Formally: *)

Inductive appears_free_in (x : string) : tm -> Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 t2}>
  | afi_app2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 t2}>
  | afi_abs : forall y T1 t1,
      y <> x  ->
      appears_free_in x t1 ->
      appears_free_in x <{\y:T1, t1}>
  | afi_if1 : forall t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if2 : forall t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if3 : forall t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x <{if t1 then t2 else t3}>.

Hint Constructors appears_free_in : core.

(** The _free variables_ of a term are just the variables that appear
    free in it.  This gives us another way to define _closed_ terms --
    arguably a better one, since it applies even to ill-typed
    terms.  Indeed, this is the standard definition of the term
    "closed." *)

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(** Conversely, an _open_ term is one that may contain free
    variables.  (I.e., every term is an open term; the closed terms
    are a subset of the open ones.  "Open" precisely means "possibly
    containing free variables.") *)

(** **** Exercise: 1 star, standard, optional (afi)

    (Officially optional, but strongly recommended!) In the space
    below, write out the rules of the [appears_free_in] relation in
    informal inference-rule notation.  (Use whatever notational
    conventions you like -- the point of the exercise is just for you
    to think a bit about the meaning of each rule.)  Although this is
    a rather low-level, technical definition, understanding it is
    crucial to understanding substitution and its properties, which
    are really the crux of the lambda-calculus. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_afi : option (nat*string) := None.
(** [] *)

(** Next, we show that if a variable [x] appears free in a term [t],
    and if we know [t] is well typed in context [Gamma], then it
    must be the case that [Gamma] assigns a type to [x]. *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |-- t \in T ->
   exists T', Gamma x = Some T'.

(** _Proof_: We show, by induction on the proof that [x] appears free
    in [t], that, for all contexts [Gamma], if [t] is well typed under
    [Gamma], then [Gamma] assigns some type to [x].

    - If the last rule used is [afi_var], then [t = x], and from the
      assumption that [t] is well typed under [Gamma] we have
      immediately that [Gamma] assigns a type to [x].

    - If the last rule used is [afi_app1], then [t = t1 t2] and [x]
      appears free in [t1].  Since [t] is well typed under [Gamma], we
      can see from the typing rules that [t1] must also be, and the IH
      then tells us that [Gamma] assigns [x] a type.

    - Almost all the other cases are similar: [x] appears free in a
      subterm of [t], and since [t] is well typed under [Gamma], we
      know the subterm of [t] in which [x] appears is well typed under
      [Gamma] as well, and the IH gives us exactly the conclusion we
      want.

    - The only remaining case is [afi_abs].  In this case [t =
      \y:T1,t1] and [x] appears free in [t1], and we also know that
      [x] is different from [y].  The difference from the previous
      cases is that, whereas [t] is well typed under [Gamma], its body
      [t1] is well typed under [y|->T1; Gamma], so the IH allows us
      to conclude that [x] is assigned some type by the extended
      context [y|->T1; Gamma].  To conclude that [Gamma] assigns a
      type to [x], we appeal to lemma [update_neq], noting that [x]
      and [y] are different variables. *)

(** **** Exercise: 2 stars, standard (free_in_context)

    Complete the following proof. *)

Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  induction H as [| | |y T1 t1 H H0 IHappears_free_in| | |];
         intros; try solve [inversion H0; eauto].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** From the [free_in_context] lemma, it immediately follows that any
    term [t] that is well typed in the empty context is closed (it has
    no free variables). *)

(** **** Exercise: 2 stars, standard, optional (typable_empty__closed) *)
Corollary typable_empty__closed : forall t T,
    empty |-- t \in T  ->
    closed t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Finally, we establish _context_invariance_.  It is useful in cases
    when we have a proof of some typing relation [Gamma |-- t \in T],
    and we need to replace [Gamma] by a different context [Gamma'].
    When is it safe to do this?  Intuitively, it must at least be the
    case that [Gamma'] assigns the same types as [Gamma] to all the
    variables that appear free in [t]. In fact, this is the only
    condition that is needed. *)

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |-- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |-- t \in T.

(** _Proof_: By induction on the derivation of [Gamma |-- t \in T].

    - If the last rule in the derivation was [T_Var], then [t = x] and
      [Gamma x = T].  By assumption, [Gamma' x = T] as well, and hence
      [Gamma' |-- t \in T] by [T_Var].

    - If the last rule was [T_Abs], then [t = \y:T2, t1], with [T =
      T2 -> T1] and [y|->T2; Gamma |-- t1 \in T1].  The induction
      hypothesis states that for any context [Gamma''], if [y|->T2;
      Gamma] and [Gamma''] assign the same types to all the free
      variables in [t1], then [t1] has type [T1] under [Gamma''].
      Let [Gamma'] be a context which agrees with [Gamma] on the free
      variables in [t]; we must show [Gamma' |-- \y:T2, t1 \in T2 -> T1].

      By [T_Abs], it suffices to show that [y|->T2; Gamma' |-- t1 \in
      T1].  By the IH (setting [Gamma'' = y|->T2;Gamma']), it
      suffices to show that [y|->T2;Gamma] and [y|->T2;Gamma'] agree
      on all the variables that appear free in [t1].

      Any variable occurring free in [t1] must be either [y] or some
      other variable.  [y|->T2; Gamma] and [y|->T2; Gamma'] clearly
      agree on [y].  Otherwise, note that any variable other than [y]
      that occurs free in [t1] also occurs free in [t = \y:T2, t1],
      and by assumption [Gamma] and [Gamma'] agree on all such
      variables; hence so do [y|->T2; Gamma] and [y|->T2; Gamma'].

    - If the last rule was [T_App], then [t = t1 t2], with [Gamma |--
      t1 \in T2 -> T] and [Gamma |-- t2 \in T2].  One induction
      hypothesis states that for all contexts [Gamma'], if [Gamma']
      agrees with [Gamma] on the free variables in [t1], then [t1] has
      type [T2 -> T] under [Gamma']; there is a similar IH for [t2].
      We must show that [t1 t2] also has type [T] under [Gamma'],
      given the assumption that [Gamma'] agrees with [Gamma] on all
      the free variables in [t1 t2].  By [T_App], it suffices to show
      that [t1] and [t2] each have the same type under [Gamma'] as
      under [Gamma].  But all free variables in [t1] are also free in
      [t1 t2], and similarly for [t2]; hence the desired result
      follows from the induction hypotheses. *)

(** **** Exercise: 3 stars, standard, optional (context_invariance)

    Complete the following proof. *)
Proof.
  intros.
  generalize dependent Gamma'.
  induction H as [| ? x0 ????? | | | |]; intros; auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The context invariance lemma can actually be used in place of the
    weakening lemma to prove the crucial substitution lemma stated
    earlier. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 1 star, standard, optional (progress_preservation_statement)

    (Officially optional, but strongly recommended!) Without peeking
    at their statements above, write down the progress and
    preservation theorems for the simply typed lambda-calculus (as Coq
    theorems).  You can write [Admitted] for the proofs. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_progress_preservation_statement : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (stlc_variation1)

    Suppose we add a new term [zap] with the following reduction rule

                         ---------                  (ST_Zap)
                         t --> zap

and the following typing rule:

                      -------------------           (T_Zap)
                      Gamma |-- zap \in T

    Which of the following properties of the STLC remain true in
    the presence of these rules?  For each property, write either
    "remains true" or "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_stlc_variation1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (stlc_variation2)

    Suppose instead that we add a new term [foo] with the following
    reduction rules:

                       -----------------                (ST_Foo1)
                       (\x:A, x) --> foo

                         ------------                   (ST_Foo2)
                         foo --> true

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_stlc_variation2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (stlc_variation3)

    Suppose instead that we remove the rule [ST_App1] from the [step]
    relation. Which of the following properties of the STLC remain
    true in the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_stlc_variation3 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (stlc_variation4)

    Suppose instead that we add the following new rule to the
    reduction relation:

            ----------------------------------        (ST_FunnyIfTrue)
            (if true then t1 else t2) --> true

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (stlc_variation5)

    Suppose instead that we add the following new rule to the typing
    relation:

                 Gamma |-- t1 \in Bool->Bool->Bool
                     Gamma |-- t2 \in Bool
                 ---------------------------------       (T_FunnyApp)
                    Gamma |-- t1 t2 \in Bool

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (stlc_variation6)

    Suppose instead that we add the following new rule to the typing
    relation:

                    Gamma |-- t1 \in Bool
                    Gamma |-- t2 \in Bool
                    ------------------------            (T_FunnyApp')
                    Gamma |-- t1 t2 \in Bool

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (stlc_variation7)

    Suppose we add the following new rule to the typing relation
    of the STLC:

                         ---------------------- (T_FunnyAbs)
                         |-- \x:Bool,t \in Bool

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)
(** [] *)

End STLCProp.

(* ================================================================= *)
(** ** Exercise: STLC with Arithmetic *)

(** To see how the STLC might function as the core of a real
    programming language, let's extend it with a concrete base
    type of numbers and some constants and primitive
    operators. *)

Module STLCArith.
Import STLC.

(** To types, we add a base type of natural numbers (and remove
    booleans, for brevity). *)

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty.

(** To terms, we add natural number constants, along with
    successor, predecessor, multiplication, and zero-testing. *)

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_const  : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0 : tm -> tm -> tm -> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'Nat'" := Ty_Nat (in custom stlc at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.

(** In this extended exercise, your job is to finish formalizing the
    definition and properties of the STLC extended with arithmetic.
    Specifically:

    Fill in the core definitions for STLCArith, by starting with the rules
    and terms which are the same as STLC.

    Then, you can try proving the key lemmas and theorems we provide.
    Doing so is particularly useful to check that you didn't make a
    mistake in the definitions.
    You will need to define and prove helper lemmas, as before.

    It will be necessary to also fill in "Reserved Notation", "Notation",
    and "Hint Constructors".

    Hint: If you get an error "STLC.tm" found instead of term "tm" then Coq
    is picking up the old notation for ie: subst instead of the new
    notation for STLCArith, so you need to overwrite the old with the
    notation before you can use it.

    Make sure Coq accepts the whole file before submitting. *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

(** **** Exercise: 5 stars, standard (arith_subst) *)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** (You'll need to add remove the period at the end of this
    definition and add

    where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

    when you fill it in.) *)

Inductive value : tm -> Prop :=
  (* FILL IN HERE *)
.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  (* FILL IN HERE *)
where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

(* An example *)

Example Nat_step_example : exists t,
<{(\x: Nat, \y: Nat, x * y ) 3 2 }> -->* t.
Proof. (* FILL IN HERE *) Admitted.

(* Typing *)

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 101, t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* FILL IN HERE *)
where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

(* An example *)

Example Nat_typing_example :
   empty |-- ( \x: Nat, \y: Nat, x * y ) 3 2 \in Nat.
Proof.
  (* FILL IN HERE *) Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_arith_subst : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** The Technical Theorems *)

(** The next lemmas are proved _exactly_ as before. *)

(** **** Exercise: 4 stars, standard, optional (STLCArith.weakening) *)
Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof. (* FILL IN HERE *) Admitted.

(* FILL IN HERE *)

(** [] *)

(* Preservation *)
(* Hint: You will need to define and prove the same helper lemmas we used before *)

(** **** Exercise: 4 stars, standard, optional (STLCArith.preservation) *)
Theorem preservation : forall t t' T,
  empty |-- t \in T  ->
  t --> t'  ->
  empty |-- t' \in T.
Proof with eauto. (* FILL IN HERE *) Admitted.

(** [] *)

(* Progress *)

(** **** Exercise: 4 stars, standard, optional (STLCArith.progress) *)
Theorem progress : forall t T,
  empty |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof with eauto. (* FILL IN HERE *) Admitted.
(** [] *)

End STLCArith.

(* 2025-07-02 13:10 *)
