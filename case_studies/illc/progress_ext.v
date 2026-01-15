(* ======================================================= *)
(* Weak normalization for linear λ-calculus with !, Unit   *)
(* ======================================================= *)

(* Imports *)
From Coq Require Import Unicode.Utf8.
From Hammer Require Import Hammer.
From CARVe Require Import contexts.total_fun algebras.dill.
From Autosubst Require Import stlc_ext step_ext.
Require Import tenv_ext typing_ext.

(* ------------------------------------- *)
(* Canonical forms lemma                 *)
(* ------------------------------------- *)

Lemma canonical_forms_fun :
  ∀ (M : tm 0) T1 T2,
    has_type emptyT M (Fun T1 T2) →
    value M →
    exists N U, M = (lam U N).
Proof. sauto lq: on . Qed.

(* Canonical lemma for Unit *)
Lemma canonical_forms_unit :
  ∀ (M : tm 0),
    has_type emptyT M Unit →
    value M →
    M = unit.
Proof. sauto lq: on . Qed.

(* Canonical form lemma for Bang *)
Lemma canonical_forms_bang :
  ∀ (M : tm 0) A,
    has_type emptyT M (Bang A) →
    value M →
    exists N, M = bang N.
Proof. sauto lq: on . Qed.

(* ------------------------------------- *)
(* Progress                              *)
(* ------------------------------------- *)

Lemma progress (M : tm 0) : ∀ T,
  has_type emptyT M T → value M ∨ exists M', step M M'.
Proof.
  dependent induction M; intros; try sfirstorder.
  - (* elimunit *)
    right. inversion H; subst.
    apply join_emptyT in H5; sintuition.
    destruct (IHM1 M1 eq_refl JMeq_refl Unit H2).
     + (* t1 is a value *)
      apply canonical_forms_unit in H2; [ | assumption]; subst.
      destruct (IHM2 M2 eq_refl JMeq_refl T H3); [ | destruct H0]; eauto.
    + (* t1 can step *)
      destruct H0. eauto.
  - (* app *)
    right. inversion H; subst.
    apply join_emptyT in H5; sintuition.
    destruct (IHM1 M1 eq_refl JMeq_refl (Fun T2 T) H2).
    + (* t1 is a value *)
      apply canonical_forms_fun in H2; [ | assumption].
      destruct H2 as [x [t H2]]; subst.
      destruct (IHM2 M2 eq_refl JMeq_refl T2 H3); [ | destruct H0]; eauto.
    + (* t1 can step *)
      destruct H0. eauto.
      - (* bang *) sauto.
      - (* letbang *) right. inversion H; subst.
    apply join_emptyT in H5; sintuition.
    destruct (IHM1 M1 eq_refl JMeq_refl (Bang A) H2).
    + (* t1 is a value *)
      apply canonical_forms_bang in H2; [ | assumption].
      sauto lq: on .
    + (* t1 can step *)
      destruct H0. eauto.
Qed.