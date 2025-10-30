(** Common type enviroments abbreviations for llc

. note: needs constants for purely_linear. Shoud be abstracted better
 *)

From Autosubst Require Import ARS core fintype stlc.
Import ScopedNotations.
From Coq Require Import Unicode.Utf8.
From Coq Require Import Logic.FunctionalExtensionality.

(* Separation logic / CARVe imports *)
Require Import VST.msl.sepalg.
Require Import VST.msl.functors.
From CARVe.contexts Require Import total_fun.
 From CARVe.algebras Require Import purely_linear. 

(* General settings *)
Set Implicit Arguments.

(* This should be in fintype, but it's not  *)

Lemma fin_eq {n} (x y : fin n) : {x = y} + {x <> y}.
Proof. induction n; [destruct x | decide equality]. Qed.

(** An EqDec instance for fin n *)

#[global] Program Instance EqDec_fin (n : nat) : EqDec (fin n) :=
  {| eq_dec := @fin_eq n |}.

Definition tenv n := tfctx (fin n) ty mult.

Definition emptyT := empty_tfctx (fin 0) _ _ (Unit, zero).

(* can this go in total_fun ? How? *)
Property join_emptyT: forall Δ₁ Δ₂, join Δ₁ Δ₂ emptyT → Δ₁ = emptyT ∧ Δ₂ = emptyT.
Proof.
  split; apply functional_extensionality; intro x; contradiction.
Qed.

(* put here other properties of interest not linked to a specific type system*)
