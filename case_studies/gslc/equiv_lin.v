(* ======================================================= *)
(* Equivalence of linear λ-calculus with generic calculus  *)
(* instantiated with linearity algebra                     *)
(* ======================================================= *)

From Stdlib Require Import Program.Equality.
From Hammer Require Import Tactics.
From Autosubst Require Import fintype stlc.
From VST Require Import sepalg.
From CARVe Require Import total_fun genv resalg linear.
Require Import gslc.

(* Linear typing judgment *)

Inductive has_type_l {n} (Δ : tenv n) : tm n -> ty -> Prop :=

| t_Var :
  forall {T : ty} {fn : fin n},
    lookup Δ fn = (T, one) ->
    exh (upd Δ fn (T, zero)) ->
    has_type_l Δ (var fn) T

| t_Abs :
  forall {T1 T2 : ty} {e1},
    has_type_l (scons (T2, one) Δ) e1 T1 ->
    has_type_l Δ (lam T2 e1) (Fun T2 T1)

| t_App :
  forall {Δ1 Δ2 : tenv n} {T1 T2 : ty} {e1 e2 : tm n},
    has_type_l Δ1 e1 (Fun T2 T1) ->
    has_type_l Δ2 e2 T2 ->
    join Δ1 Δ2 Δ ->
    has_type_l Δ (app e1 e2) T1.

(* Equivalence *)

Lemma equiv_lin {n} (Δ : tenv n) (e : tm n) T :
  has_type Δ e (T, one) <->
  has_type_l Δ e T.
Proof.
  split; revert T; induction e; intros * H; inversion H; econstructor; eauto.
  sfirstorder. all: scongruence.
Qed.