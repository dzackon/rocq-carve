(* ======================================================= *)
(* Typing for generic substructural λ-calculus             *)
(* (contexts as total maps)                                *)
(* ======================================================= *)

From VST Require Import sepalg.
From CARVe Require Import total_fun genv resalg.
From Autosubst Require Import fintype stlc.
Import ScopedNotations.
Set Implicit Arguments.

Section GenSubstructLC.
Variable A : Type. (* Resource algebra elements *)
Variable JA : Join A.
Variable SA : Sep_alg A.
Variable RA : Res_alg A.

(* Contexts *)

Definition tenv n := @genv ty A n.
Definition emptyT (default : A) := emptyG (Unit, default).
Definition hasW_if {n} (Δ : tenv n) m := (hasW m -> ctx_forall hasW Δ).
Definition hasC_if {n} (Δ : tenv n) m := (hasC m -> ctx_forall hasC Δ).

(* Typing judgment *)

Inductive has_type {n} (Δ : tenv n) : tm n -> ty * A -> Prop :=

| t_Var :
    forall (T : ty) (fn : fin n) (m : A),
      nonzero m ->
      lookup Δ fn = (T, m) ->
      ctx_forall hasW (upd Δ fn (T, core m)) ->
      hasW_if Δ m ->
      hasC_if Δ m ->
      has_type Δ (var fn) (T, m)

| t_Abs :
    forall (T1 T2 : ty) (e1 : tm (S n)) (m : A),
      has_type (scons (T2, m) Δ) e1 (T1, m) ->
      has_type Δ (lam T2 e1) (Fun T2 T1, m)

| t_App :
    forall (Δ1 Δ2 : tenv n) (T1 T2 : ty) (e1 e2 : tm n) (m : A),
      has_type Δ1 e1 (Fun T2 T1, m) ->
      has_type Δ2 e2 (T2, m) ->
      join Δ1 Δ2 Δ ->
      has_type Δ (app e1 e2) (T1, m).

(** Typing conversion property *)

Property typing_conversion {n} {Δ : tenv n} {M N : tm n} {p : ty * A} :
  has_type Δ M p -> M = N -> has_type Δ N p. intros; subst; assumption. Defined.

End GenSubstructLC.

Global Arguments tenv {A}.
Global Arguments has_type {A JA SA RA n}.
Global Arguments hasW_if {A JA RA n}.
Global Arguments hasC_if {A JA RA n}.
Global Notation "Δ '⊢' e ':' T" := (has_type Δ e T) (at level 40).
Global Notation "'hasCᶜ' Δ" := (ctx_forall hasC Δ) (at level 40).
Global Notation "'hasWᶜ' Δ" := (ctx_forall hasW Δ) (at level 40).