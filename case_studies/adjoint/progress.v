(* ======================================================= *)
(* Progress for the adjoint natural deduction calculus     *)
(* ======================================================= *)

From Stdlib Require Import Program.Equality.
From Hammer Require Import Tactics.
From Autosubst Require Import fintype adjnd.
From VST Require Import sepalg.
From CARVe Require Import total_fun genv resalg adjoint.
Require Import adjnd.

Section Progress.
Variable A : Type.
Variable JA : Join A.
Variable SA : Sep_alg A.
Variable M : ModeStructure A.

(* Canonical forms lemmas *)

Lemma canonical_forms_fun {default} (e : tm 0) m T1 T2 :
  has_type (emptyG default) e (T1 ⊸ T2, m) ->
  value e ->
  exists e' U, e = lam U e'.
Proof. sauto lq: on rew: off. Qed.

Lemma canonical_forms_up {default} (e : tm 0) k m T :
  has_type (emptyG default) e (ty_up k m T, m) ->
  value e ->
  exists e', e = lift k m e'.
Proof. sauto lq: on. Qed.

Lemma canonical_forms_down {default} (e : tm 0) k m T :
  has_type (emptyG default) e (ty_down m k T, k) ->
  value e ->
  exists e', e = drop m k e' /\ value e'.
Proof. sauto lq: on rew: off. Qed.

(* Progress *)

Lemma progress {default} (e : tm 0) T :
  has_type (emptyG default) e T ->
  value e \/ exists e', step e e'.
Proof.
  dependent induction e; intros.
  - eauto.
  - left; constructor.
  - inversion H.
    destruct (join_emptyG H5); sintuition.
    destruct (IHe1 e1 eq_refl JMeq_refl _ H2);
    sauto lq: on use: canonical_forms_fun.
  - left; constructor.
  - inversion H.
    destruct (join_emptyG H10); sintuition.
    destruct (IHe e eq_refl JMeq_refl _ H9);
    sauto lq: on use: canonical_forms_up.
  - inversion H.
    destruct (join_emptyG H10); subst Δ2.
    destruct (IHe e eq_refl JMeq_refl _ H9);
    sauto lq: on.
  - inversion H.
    destruct (join_emptyG H9); subst Δ1.
    destruct (IHe1 _ eq_refl JMeq_refl _ H6);
    sauto lq: on use: canonical_forms_down.
Qed.

End Progress.