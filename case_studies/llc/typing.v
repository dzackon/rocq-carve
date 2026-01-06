(* ======================================================= *)
(* Typing and progress for the linear λ-calculus           *)
(* (contexts as total maps)                                *)
(* ======================================================= *)

(* Imports *)
From Coq Require Import Logic.FunctionalExtensionality Unicode.Utf8.
From Hammer Require Import Tactics.
From VST.msl Require Import sepalg.
From CARVe Require Import contexts.total_fun algebras.linear.
From Autosubst Require Import fintype stlc step.
Require Import tenv.
Import ScopedNotations.

(* General settings *)
Set Implicit Arguments.

(* -------------------------------------------- *)
(* Typing judgment                              *)
(* -------------------------------------------- *)

Inductive has_type {n} (Δ : tenv n) : tm n → ty → Prop :=

| t_Var :
    ∀ (T : ty) (fn : fin n),
      lookup Δ fn = (T, one) ->
      exh hal (upd Δ fn (T, zero)) ->
      has_type Δ (var_tm fn) T

| t_Abs :
    ∀ (T1 T2 : ty) e1,
      has_type (scons (T2, one) Δ) e1 T1 →
      has_type Δ (lam T2 e1) (Fun T2 T1)

| t_App :
    ∀ (Δ1 Δ2 : tenv n) (T1 T2 : ty) (e1 e2 : tm n),
      has_type Δ1 e1 (Fun T2 T1) →
      has_type Δ2 e2 T2 →
      join Δ1 Δ2 Δ →
      has_type Δ (Core.app e1 e2) T1.

Notation "Δ '⊢' e ':' T" := (has_type Δ e T) (at level 40).