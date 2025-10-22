(* ======================================================= *)
(* Typing, context morphism lemmas, and preservation       *)
(* (contexts as total maps)                                *)
(* ======================================================= *)

(* Library imports *)
Require Import core fintype stlc step.
Import ScopedNotations.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Unicode.Utf8.
From Coq Require Import Lia.
From Hammer Require Import Hammer.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.JMeq.
From Coq Require Import Logic.FunctionalExtensionality.

(* Separation logic / CARVe imports *)
Require Import VST.msl.sepalg.
Require Import VST.msl.functors.
From CARVe.contexts Require Import total_fun.
From CARVe.algebras Require Import purely_linear.

(* ----------------------------------- *)
(* Notation                            *)
(* ----------------------------------- *)

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -o T" := (Fun  S T) (in custom stlc at level 50, right associativity).
Notation "x ^ y" := (Core.app x y) (in custom stlc at level 1, left associativity).
Notation "/\ T e " :=
  (lam T e) (in custom stlc at level 90,
        e custom stlc at level 99,
        left associativity).
        
(* ----------------------------------- *)
(* Contexts                            *)
(* ----------------------------------- *)

(* TODO: move to contexts/func.v *)
 
Definition tenv n := tfctx (fin n) ty mult.

Definition shift_tenv {n : nat} (T : ty) (m : mult) (e : tenv n) : tenv (S n) := scons (T, m) e.

Definition fin_eq {n} (x y : fin n) : {x = y} + {x <> y}.
Proof. induction n; [destruct x | decide equality]. Qed.

Definition upd {n} (Δ : tenv n) (x : fin n)
  (ty_old ty_new : ty) (m_old m_new : mult) (Δ' : tenv n) : Prop :=
  forall y : fin n,
    if fin_eq x y then
      Δ y = (ty_old, m_old) ∧ Δ' y = (ty_new, m_new)
    else
      Δ y = Δ' y.

Definition emptyT := fun x : fin 0 => (Base, zero).

Property join_emptyT: forall Δ₁ Δ₂, join Δ₁ Δ₂ emptyT → Δ₁ = emptyT ∧ Δ₂ = emptyT.
Proof.
  split; apply functional_extensionality; intro x; contradiction.
Qed.

Require Import Coq.Vectors.Fin.

Property upd_head_inv {n} {Δ : tenv n} {Δ' : tenv (S n)} {x s t t' m m'} :
  upd ((s, m) .: Δ) x t t' m m' Δ' →
  @exh _ _ mult hal Δ' →
  ~ hal m → hal m' →
  s = t ∧ Δ' = ((t', m') .: Δ).
Proof.
  intros Hupd Hex Hnm Hm'.
  destruct x as [x'|].
  - specialize (Hupd (Some x')) as Hupd'. simpl in Hupd'.  
    admit.
  - specialize (Hupd None) as Hupd'. specialize (Hex None).
    destruct (fin_eq (None : fin (S n)) (None : fin (S n))).
    + simpl in *.
      (* pose proof (f_equal fst Hupd') as Hfst. *)
      admit.
    + contradiction.
Admitted.
  (*
  specialize (Hupd None).
  destruct (fin_eq x None) as [Heq|Hneq].
  - destruct Hupd as [Hhead_eq HΔ']. subst.
    inversion Hhead_eq; subst.
    split; [reflexivity|].
    extensionality y. destruct y; simpl; auto.
    auto.
    admit.
  - specialize (Hex None).
    rewrite <- Hupd in Hex; simpl in Hex.
    contradiction.
  *)
Admitted.

(* Property upd_head_inv {n} {Δ : tenv n} {Δ' : tenv (S n)} {x s t t' m m'} :
  upd ((s, m) .: Δ) x t t' m m' Δ' →
  @exh _ _ mult hal Δ' →
  ~ hal m → hal m' →
  s = t ∧ Δ' = ((t', m') .: Δ).
Proof.
  - (* s = t *)
    specialize (H x).
    (* unfold upd in Hupd.
    specialize (Hupd F1).
    (* fin_eq F1 F1 = true *)
    rewrite fin_eq_refl in Hupd.
    destruct Hupd as [Hs _].
    exact Hs. *)
    admit.
  - apply functional_extensionality. intros y.
    specialize (H y).
    induction (fin_eq x y) eqn:Exy; subst.
    + admit.
    + destruct H.
Admitted.
 *)

Property upd_exh_inv {n} {Δ : tenv n} {Δ' : tenv (S n)} {x s t t' m m'} :
  upd ((s, m) .: Δ) x t t' m m' Δ' →
  @exh _ _ mult hal Δ' →
  ~ hal m → hal m' →
  Δ' = (fun y => if fin_eq x y then (t', m') else ((s, m) .: Δ) y).
Proof.
  intros.
  apply functional_extensionality. intros y.
  specialize (H y).
  destruct (fin_eq x y); destruct H; auto.  
Qed.

(* ------------------------------------- *)
(* Typing judgment                       *)
(* ------------------------------------- *)

Inductive has_type {n} (Δ : tenv n) : tm n → ty → Prop :=

| t_Var :
  forall (Δ' : tenv n) (T : ty) (fn : fin n),
    upd Δ fn T T one zero Δ' →
    @exh _ _ mult hal Δ' →
    has_type Δ (var_tm fn) T

| t_Abs :
  forall (T1 T2 : ty) e1,
    has_type (scons (T2, one) Δ) e1 T1 →
    has_type Δ (lam T2 e1) (Fun T2 T1)

| t_App :
  forall (Δ₁ Δ₂ : tenv n) (T1 T2 : ty) (e1 e2 : tm n),
    has_type Δ₁ e1 (Fun T2 T1) →
    has_type Δ₂ e2 T2 →
    join Δ₁ Δ₂ Δ →
    has_type Δ (Core.app e1 e2) T1.

Notation "Δ '|-' e ':' T" := (has_type Δ e T) (at level 40).    

(* ------------------------------------- *)
(* Lemmas                                *)
(* ------------------------------------- *)

Lemma canonical_forms_fun : forall (M : tm 0) T1 T2,
  has_type emptyT M (Fun T1 T2) →
  value M →
  exists N U, M = (lam U N).
Proof. sauto lq: on . Qed.    

(* Need to prove exchange, weakening / strengthening of 0 assumptions *)
Lemma lin_subst {n} :
  forall {Δ₁ Δ₂ Δ : tenv n} {e1 e2 T1 T2},
    has_type ((T2, one) .: Δ₁) e1 T1 →
    has_type Δ₂ e2 T2 →
    join Δ₁ Δ₂ Δ →
    has_type Δ e1[e2..] T1.
Proof.
  intros. dependent induction H.
  - (* var *)
    assert (nhalo : ¬ hal one) by sauto.
    assert (Heq := upd_exh_inv H H0 nhalo halz); subst.
Admitted.

(* ------------------------------------- *)
(* Theorems                              *)
(* ------------------------------------- *)

(* Progress *)
Lemma progress (M : tm 0) : forall T,
  has_type emptyT M T → value M ∨ exists M', step M M'.  
Proof.
  dependent induction M; intros; try sfirstorder.
  - (* app case *)
    right. inversion H; subst.
    apply join_emptyT in H5; sintuition.
    destruct (IHM1 M1 eq_refl JMeq_refl <{ T2 -o T }> H2).
    + (* t1 is a value *)
      apply canonical_forms_fun in H2; [ | assumption].
      destruct H2 as [x [t H2]]; subst.
      destruct (IHM2 M2 eq_refl JMeq_refl T2 H3); [ | destruct H0]; eauto.
    + (* t1 can step *)
      destruct H0. eauto.
Qed.

(* Preservation *)
Lemma preservation (n : nat) (Δ : tenv n) (M : tm n) T :
  has_type Δ M T → forall M', step M M' → has_type Δ M' T.
Proof.
  induction 1; intros M' H'; inv H'; try eapply t_App; eauto.
  - econstructor. now apply IHhas_type.
  - inv H. apply (lin_subst H H0 H1).
Qed.