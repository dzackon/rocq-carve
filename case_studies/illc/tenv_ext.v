(* ======================================================= *)
(* Common type environments abbreviations for extended LLC *)
(* ======================================================= *)

(* Imports *)
From Coq Require Import Unicode.Utf8 Logic.FunctionalExtensionality.
From VST.msl Require Import sepalg functors.
From CARVe Require Import contexts.total_fun algebras.dill.
From Autosubst Require Import ARS core fintype stlc_ext.
Import ScopedNotations.

(* -------------------------------------------- *)
(* Definitions                                  *)
(* -------------------------------------------- *)

(* An EqDec instance for fin n *)
#[global] Program Instance EqDec_fin (n : nat) : EqDec (fin n) :=
  {| eq_dec := @fin_eq n |}.

Definition tenv n := tfctx (fin n) ty mult.

Definition emptyT := empty_tfctx (fin 0) _ _ (Unit, zero).

(* -------------------------------------------- *)
(* Properties                                   *)
(* -------------------------------------------- *)

(* If Δ₁ ⋈ Δ₂ = ⋅, then Δ₁ = Δ₂ = ⋅ *)
Property join_emptyT :
  forall Δ₁ Δ₂,
    join Δ₁ Δ₂ emptyT → Δ₁ = emptyT ∧ Δ₂ = emptyT.
Proof.
  split; apply functional_extensionality; intro x; contradiction.
Qed.

(* If Δ₁ ⋈ Δ₂ = Δ, then types must match at each input x *)
Lemma join_types_match :
  forall {n} {Δ Δ1 Δ2 : tenv n} (x : fin n),
    join Δ1 Δ2 Δ →
    fst (Δ x) = fst (Δ1 x) ∧ fst (Δ x) = fst (Δ2 x).
Proof.
  intros ? Δ Δ1 Δ2 x Hjoin.
  specialize (Hjoin x).
  destruct (Δ1 x) as [? ?].
  destruct (Δ2 x) as [? ?].
  destruct (Δ x) as [? ?].
  inversion Hjoin. inversion H. rewrite H1, H2. auto.
Qed.