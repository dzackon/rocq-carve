From Coq Require Import Logic.FunctionalExtensionality.
From Hammer Require Import Hammer.
From VST.msl Require Import sepalg functors sepalg_functors sepalg_generators.
Import CovariantFunctor.
Import CovariantFunctorLemmas.
Import CovariantFunctorGenerator.

(* Decidable equality *)
Class EqDec (A : Type) : Type :=
  {
    eq_dec : forall x y : A, {x = y} + {x <> y}
  }.

Section TotalFunCtx.
  Variable D: Type. (* Function domain *)
  Variable R: Type. (* Resources *)
  Variable A: Type. (* Resource Algebra *)
  Variable JA: Join A.
  Variable CA: Canc_alg A.
  Variable PA: Perm_alg A.
  Variable SA: Sep_alg A.
  #[global] Generalizable All Variables.

  Definition tfctx : Type := (D -> R * A).

  #[global] Instance Join_tfctx : Join tfctx :=
    Join_fun _ _ (Join_prod _ (Join_equiv _) _ JA).

  #[global] Instance Perm_alg_tfctx : Perm_alg tfctx.
  Proof.
    sauto use: Perm_fun, Perm_prod, Perm_equiv.
  Defined.
  #[global] Instance Canc_alg_tfctx : Canc_alg tfctx :=
    Canc_fun _ _ _ (Canc_prod _ (Join_equiv _) _ JA).
  #[global] Instance Sep_alg_tfctx : Sep_alg tfctx.
  Proof.
    sauto use: Sep_fun, Perm_fun, Sep_prod, Perm_prod, Sep_equiv, Perm_equiv.
  Defined.

  Definition exh (hal: A -> Prop): tfctx -> Prop :=
    fun C => forall r, hal (snd (C r)).

  Definition empty_tfctx default : tfctx := fun _ => default.
  
  Definition lookup_tfctx : tfctx -> D -> R * A :=
    fun C x => C x.

  Definition update_tfctx `{EqDec D} : tfctx -> D -> R -> A -> tfctx :=
    fun C x r a x' => if eq_dec x x' then (r, a) else C x'.

  (* Generic relational update — no EqDec required *)
  Definition update_tfctx_rel (C : tfctx) (x : D) (r : R) (a : A) (C' : tfctx) : Prop :=
    forall x',
      (x' = x -> C' x' = (r, a)) /\
      (x' <> x -> C' x' = C x').

  (* The functional update satisfies the relational spec *)
  Lemma update_tfctx_rel_self `{EqDec D} :
    forall (C : tfctx) (x : D) (r : R) (a : A),
      update_tfctx_rel C x r a (update_tfctx C x r a).
  Proof.
    intros C x r a x'. split.
    - intros ->. unfold update_tfctx.
      destruct (eq_dec x x) as [_|contra]; [reflexivity|contradiction].
    - intros Hneq. unfold update_tfctx.
      destruct (eq_dec x x') as [Heq|_]; [congruence|reflexivity].
  Qed.

  (* Relational ↔ functional equivalence (requires EqDec + functional extensionality) *)
  Lemma update_tfctx_rel_iff_fun `{EqDec D} :
    forall (C : tfctx) (x : D) (r : R) (a : A) (C' : tfctx),
      update_tfctx_rel C x r a C' <-> C' = update_tfctx C x r a.
  Proof.
    intros C x r a C'. split.
    - intros Hrel. apply functional_extensionality; intro x'.
      destruct (eq_dec x x') as [->|Hneq].
      + specialize (Hrel x') as [Hit _]. hauto unfold: update_tfctx.
      + specialize (Hrel x') as [_ Hmiss]. hauto unfold: update_tfctx.
    - intros ->. apply update_tfctx_rel_self.
  Qed.

  (* Handy lookup lemmas *)
  Lemma lookup_update_hit `{EqDec D} :
    forall (C : tfctx) (x : D) (r : R) (a : A),
      (update_tfctx C x r a) x = (r, a).
  Proof.
    intros. unfold update_tfctx.
    destruct (eq_dec x x) as [_|contra]; [reflexivity|contradiction].
  Qed.

  Lemma lookup_update_miss `{EqDec D} :
    forall (C : tfctx) (x y : D) (r : R) (a : A),
      x <> y ->
      (update_tfctx C x r a) y = C y.
  Proof.
    intros ? ? ? ? ? Hneq. unfold update_tfctx.
    destruct (eq_dec x y) as [Heq|_]; [congruence|reflexivity].
  Qed.

  (* Same lookup facts stated via the relational view (no EqDec needed) *)
  Lemma update_tfctx_rel_hit :
    forall (C : tfctx) (x : D) (r : R) (a : A) (C' : tfctx),
      update_tfctx_rel C x r a C' -> C' x = (r, a).
  Proof.
    intros C x r a C' Hrel. specialize (Hrel x) as [Hit _]. now apply Hit.
  Qed.

  Lemma update_tfctx_rel_miss :
    forall (C : tfctx) (x y : D) (r : R) (a : A) (C' : tfctx),
      update_tfctx_rel C x r a C' -> x <> y -> C' y = C y.
  Proof.
    intros C x y r a C' Hrel Hneq.
    specialize (Hrel y) as [_ Hmiss]. now apply Hmiss.
  Qed.

End TotalFunCtx.