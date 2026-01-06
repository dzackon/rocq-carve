(* ======================================================= *)
(* Typing, context morphism lemmas, and preservation       *)
(* (contexts as total maps)                                *)
(* ======================================================= *)

(* Imports *)
From Coq Require Import Logic.FunctionalExtensionality Unicode.Utf8.
From Hammer Require Import Tactics.
From CARVe Require Import contexts.total_fun algebras.linear.
From Autosubst Require Import fintype stlc step.
Require Import tenv typing.

(* ------------------------------------- *)
(* Canonical forms lemma                 *)
(* ------------------------------------- *)

Lemma canonical_forms_fun : ∀ (M : tm 0) T1 T2,
  has_type emptyT M (Fun T1 T2) →
  value M →
  ∃ N U, M = lam U N.
Proof. sauto lq: on. Qed.

(* ------------------------------------- *)
(* Theorem                               *)
(* ------------------------------------- *)

(** Progress *)

Lemma progress (M : tm 0) : ∀ T,
  has_type emptyT M T →
  value M ∨ ∃ M', step M M'.
Proof.
  dependent induction M; intros; try sfirstorder.
  - right. inversion H; subst.
    apply join_emptyT in H5; sintuition.
    sauto use: (IHM1 M1 eq_refl JMeq_refl (Fun T2 T) H2), canonical_forms_fun.
Qed.