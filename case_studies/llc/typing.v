(* ======================================================= *)
(* Typing and progress for the linear λ-calculus           *)
(* (contexts as total maps)                                *)
(* ======================================================= *)

(* Imports *)
From Coq Require Import Lia Logic.FunctionalExtensionality Unicode.Utf8.
From Hammer Require Import Tactics.
From VST.msl Require Import sepalg functors.
From CARVe Require Import contexts.total_fun algebras.purely_linear.
From Autosubst Require Import ARS core fintype stlc step.
Require Import tenv.
Import ScopedNotations.

(* General settings *)
Set Implicit Arguments.

(* -------------------------------------------- *)
(* Typing judgment                              *)
(* -------------------------------------------- *)

Inductive has_type {n} (Δ : tenv n) : tm n → ty → Prop :=

| t_Var :
    forall (T : ty) (fn : fin n),
      lookup_tfctx _ _ _ Δ fn = (T, one) ->
      exh _ _  _ hal (update_tfctx _ _ _ Δ fn T zero) ->
      has_type Δ (var_tm fn) T

| t_Abs :
    forall (T1 T2 : ty) e1,
      has_type (scons (T2, one) Δ) e1 T1 →
      has_type Δ (lam T2 e1) (Fun T2 T1)

| t_App :
    forall (Δ1 Δ2 : tenv n) (T1 T2 : ty) (e1 e2 : tm n),
      has_type Δ1 e1 (Fun T2 T1) →
      has_type Δ2 e2 T2 →
      join Δ1 Δ2 Δ →
      has_type Δ (Core.app e1 e2) T1.

Notation "Δ '⊢' e ':' T" := (has_type Δ e T) (at level 40).

(* -------------------------------------------- *)
(* Canonical forms lemma                        *)
(* -------------------------------------------- *)

Lemma canonical_forms_fun : forall (M : tm 0) T1 T2,
  has_type emptyT M (Fun T1 T2) →
  value M →
  exists N U, M = (lam U N).
Proof. sauto lq: on . Qed.

(* -------------------------------------------- *)
(* Progress                                     *)
(* -------------------------------------------- *)

Lemma progress (M : tm 0) : forall T,
  has_type emptyT M T → value M ∨ exists M', step M M'.  
Proof.
  dependent induction M; intros; try sfirstorder.
  - (* app case *)
    right. inversion H; subst.
    apply join_emptyT in H5; sintuition.
    destruct (IHM1 M1 eq_refl JMeq_refl (Fun T2  T) H2).
    + (* t1 is a value *)
      apply canonical_forms_fun in H2; [ | assumption].
      destruct H2 as [x [t H2]]; subst.
      destruct (IHM2 M2 eq_refl JMeq_refl T2 H3); [ | destruct H0]; eauto.
    + (* t1 can step *)
      destruct H0. eauto.
Qed.