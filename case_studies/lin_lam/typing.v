(* ======================================================= *)
(* Typing and progress for pure llc      *)
(* (contexts as total maps)                                *)
(* ======================================================= *)


Require Import ARS core fintype stlc step tenv.
Import ScopedNotations.
From Coq Require Import Unicode.Utf8.
From Coq Require Import Lia.
From Hammer Require Import Tactics.
From Coq Require Import Logic.FunctionalExtensionality.

(* Separation logic / CARVe imports *)
Require Import VST.msl.sepalg.
Require Import VST.msl.functors.
From CARVe.contexts Require Import total_fun.
From CARVe.algebras Require Import purely_linear.

(* General settings *)
Set Implicit Arguments.

(* ----------------------------------- *)
(* Typing judgment                     *)
(* ----------------------------------- *)

Inductive has_type {n} (Δ : tenv n) : tm n → ty → Prop :=

| t_Var :
  forall (T : ty) (fn : fin n),
    lookup_tfctx _ _ _ Δ fn = (T, one) ->
    exh _ _  _ hal
                  (update_tfctx
                     _ _
                     _ Δ fn T
                     zero) ->
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

Notation "Δ '|-' e ':' T" := (has_type Δ e T) (at level 40).

(* If Δ₁ ⋈ Δ₂ = Δ, then types must match at each input x *)
Lemma join_types_match :
  forall {n} {Δ Δ1 Δ2 : tenv n} (x : fin n),
    join Δ1 Δ2 Δ →
    fst (Δ x) = fst (Δ1 x) ∧ fst (Δ x) = fst (Δ2 x).
Proof.
  intros n Δ Δ1 Δ2 x Hjoin.
  specialize (Hjoin x).
  destruct (Δ1 x) as [t1 m1].
  destruct (Δ2 x) as [t2 m2].
  destruct (Δ x) as [t m].
  (* From the definition of join, t = t1 and t = t2 *)
  cbn. sauto q: on.
Qed.


(* ------------------------------------- *)
(* Canonical forms lemma                 *)
(* ------------------------------------- *)

Lemma canonical_forms_fun : forall (M : tm 0) T1 T2,
  has_type emptyT M (Fun T1 T2) →
  value M →
  exists N U, M = (lam U N).
Proof. sauto lq: on . Qed.    

(* Progress *)
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
