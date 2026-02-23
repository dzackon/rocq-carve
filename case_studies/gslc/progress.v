(* ======================================================= *)
(* Progress for generic substructural λ-calculus           *)
(* ======================================================= *)

From Hammer Require Import Tactics.
From VST Require Import sepalg.
From CARVe Require Import genv resalg.
From Autosubst Require Import stlc step.
Require Import gslc.

Section Progress.
Variable A : Type.
Variable JA : Join A.
Variable SA : Sep_alg A.
Variable RA : Res_alg A.

(* Canonical forms lemma *)

Lemma canonical_forms_fun {default} (M : tm 0) m T1 T2 :
  has_type (emptyG default) M (Fun T1 T2, m) ->
  value M ->
  exists N U, M = lam U N.
Proof. sauto lq: on. Qed.

(* Progress *)

Lemma progress {default} (M : tm 0) T :
  has_type (emptyG default) M T ->
  value M \/ exists M', step M M'.
Proof.
  dependent induction M; intros.
  - eauto.
  - sauto lq: on rew: off.
  - right. inversion H; subst.
    destruct (join_emptyG H5); sintuition.
    specialize (IHM1 M1 eq_refl JMeq_refl _ H2).
    hauto l: on use: canonical_forms_fun.
Qed.

End Progress.