(* ======================================================= *)
(* Common type environments abbreviations for extended LLC *)
(* ======================================================= *)

(* Imports *)
From Coq Require Import Logic.FunctionalExtensionality Unicode.Utf8.
From VST.msl Require Import sepalg.
From CARVe Require Import contexts.total_fun algebras.dill.
From Autosubst Require Import fintype stlc_ext.

(* -------------------------------------------- *)
(* Definitions                                  *)
(* -------------------------------------------- *)

(* An EqDec instance for fin n *)
#[global] Program Instance EqDec_fin (n : nat) : EqDec (fin n) :=
  {| eq_dec := @fin_eq n |}.

Definition tenv n := tfctx (fin n) ty mult.

Definition emptyT := empty_tfctx (fin 0) _ _ (Unit, zero).

#[global] Arguments lookup {D R A} _ _.
#[global] Arguments exh {D R A} _ _.
#[global] Arguments upd {D R A H} _ _ _ _.

(* -------------------------------------------- *)
(* Properties                                   *)
(* -------------------------------------------- *)

(* If Δ₁ ⋈ Δ₂ = ⋅, then Δ₁ = Δ₂ = ⋅ *)
Property join_emptyT :
  forall Δ1 Δ2,
    join Δ1 Δ2 emptyT → Δ1 = emptyT ∧ Δ2 = emptyT.
Proof. split; apply functional_extensionality; intro x; contradiction. Qed.