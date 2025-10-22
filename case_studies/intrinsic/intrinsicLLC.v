(* ============================================ *)
(* Weak normalization, with redn. under binders *)
(* ============================================ *)

(* Library imports *)
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Unicode.Utf8.
From Coq Require Import Lia.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.

(* Separation logic imports *)
Require Import VST.msl.functors.
Require Import VST.msl.sepalg.

(* CARVe imports *)
From CARVe.contexts Require Import list.
From CARVe.algebras Require Import purely_linear.

(* General settings *)
Set Implicit Arguments.

(* Tactics *)
Ltac inv H := dependent destruction H; subst; clear H; trivial.

(* ----------------------------------- *)
(* Types and typing environments       *)
(* ----------------------------------- *)

Inductive ty : Type :=
| ty_Unit  : ty
| ty_Arrow : ty → ty → ty.

Definition tenv := lctx ty mult.

(* ----------------------------------- *)
(* Terms                               *)
(* ----------------------------------- *)

(* TODO: add other constructors and generalize algebra*)
Inductive tm (Δ : tenv) : ty → Type :=
| var  : forall t Δ', upd Δ t t one zero Δ' → exh hal Δ' → tm Δ t
| ut   : exh hal Δ → tm Δ ty_Unit
| llam : forall t1 t2, tm ((t1, one) :: Δ) t2 → tm Δ (ty_Arrow t1 t2)
| lapp : forall t1 t2 Δ₁ Δ₂,
    tm Δ₁ (ty_Arrow t1 t2) →
    tm Δ₂ t1 →
    merge Δ₁ Δ₂ Δ →
    tm Δ t2.

(* ----------------------------------- *)
(* Notation                            *)
(* ----------------------------------- *)

Declare Custom Entry stlc.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -o T" := (ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x ^ y" := (lapp x y) (in custom stlc at level 1, left associativity).
Notation "/\ y" := (llam y) (in custom stlc at level 90,
                             y custom stlc at level 99,
                             left associativity).

Notation "'Unit'" := ty_Unit (in custom stlc at level 0).
Notation "'unit'" := ut (in custom stlc at level 0).

(* ----------------------------------- *)
(* Substitution                        *)
(* ----------------------------------- *)

(* Exchange at the top level of the context [@TODO] *)

Parameter tm_exch_top :
  forall {Δ A₁ A₂ α₁ α₂ B},
    tm ((A₁, α₁) :: (A₂, α₂) :: Δ) B →
    tm ((A₂, α₂) :: (A₁, α₁) :: Δ) B →
    Prop.

(* Weakening / strengthening of terms [@TODO] *)

Parameter tm_weak :
  forall {Δ B α},
    tm Δ B →
    forall (A : ty), hal α →
    tm ((A, α) :: Δ) B →
    Prop.

Parameter tm_str :
  forall {Δ A B},
    tm ((A, zero) :: Δ) B →
    tm Δ B →
    Prop.

(* Linear substitution *)

Inductive lsubst : forall {A B Δ₁ Δ₂ Δ},
  tm ((A, one) :: Δ₁) B → tm Δ₂ A → merge Δ₁ Δ₂ Δ → tm Δ B → Prop :=

  | lsubst_lvar :
      forall {Δ' Δ A}
             (e : exh hal Δ')
             (N : tm Δ A)
             (μ : merge Δ' Δ Δ),
        lsubst
          (var (upd_t Δ' A A one zero) (exh_c hal A e halz)) N μ N

  | lsubst_llam :
      forall {Δ₁ Δ₂ Δ A B₁ B₂}
             (M   : tm ((B₁, one) :: ((A, one) :: Δ₁)) B₂)
             (M'  : tm ((A, one) :: ((B₁, one) :: Δ₁)) B₂)
             (M'' : tm ((B₁, one) :: Δ) B₂)
             (N   : tm Δ₂ A)
             (N'  : tm ((B₁, zero) :: Δ₂) A)
             (μ   : merge Δ₁ Δ₂ Δ),
        tm_exch_top M M' →
        tm_weak N halz N' → (* not accepting B₁ as argument? *)
        lsubst M' N' (mg_c B₁ m_10 μ) M'' →
        lsubst (llam M) N μ (llam M'')

  (* Case 1: A¹ is 'sent to the left' *)
  | lsubst_lapp1 :
      forall {A B₁ B₂ Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₁₃ Δ}
             (M₁  : tm ((A, one) :: Δ₁) (ty_Arrow B₁ B₂))
             (M₁' : tm Δ₁₃ (ty_Arrow B₁ B₂))
             (M₂  : tm ((A, zero) :: Δ₂) B₁)
             (M₂' : tm Δ₂ B₁)
             (N   : tm Δ₃ A)
             (μ1  : merge Δ₁ Δ₂ Δ₁₂)
             (μ2  : merge Δ₁₂ Δ₃ Δ)
             (μ3  : merge Δ₁ Δ₃ Δ₁₃)
             (μ4  : merge Δ₁₃ Δ₂ Δ),
        lsubst M₁ N μ3 M₁' →
        tm_str M₂ M₂' →
        lsubst (lapp M₁ M₂ (mg_c A m_10 μ1)) N μ2 (lapp M₁' M₂' μ4)

  (* Case 2: A¹ is 'sent to the right' *)
  | lsubst_lapp2 :
      forall {A B₁ B₂ Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₂₃ Δ}
             (M₁  : tm ((A, zero) :: Δ₁) (ty_Arrow B₁ B₂))
             (M₁' : tm Δ₁ (ty_Arrow B₁ B₂))
             (M₂  : tm ((A, one) :: Δ₂) B₁)
             (M₂' : tm Δ₂₃ B₁)
             (N   : tm Δ₃ A)
             (μ1  : merge Δ₁ Δ₂ Δ₁₂)
             (μ2  : merge Δ₁₂ Δ₃ Δ)
             (μ3  : merge Δ₂ Δ₃ Δ₂₃)
             (μ4  : merge Δ₁ Δ₂₃ Δ),
        tm_str M₁ M₁' →
        lsubst M₂ N μ3 M₂' →
        lsubst (lapp M₁ M₂ (mg_c A m_01 μ1)) N μ2 (lapp M₁' M₂' μ4).

(* and this to be proven *)
Lemma lsubst_total :
  forall A B Δ₁ Δ₂ Δ
         (M : tm ((A, one) :: Δ₁) B)
         (N : tm Δ₂ A)
         (μ : merge Δ₁ Δ₂ Δ),
    exists M', lsubst M N μ M'.
Admitted.

(* ----------------------------------- *)
(* Operational semantics               *)
(* ----------------------------------- *)

Inductive step : forall Δ A, tm Δ A → tm Δ A → Prop :=

  | S_Beta_App :
      forall (Δ Δ₁ Δ₂ : tenv) (A B : ty)
             (M  : tm ((A, one) :: Δ₁) B)
             (N  : tm Δ₂ A)
             (μ  : merge Δ₁ Δ₂ Δ)
             (M' : tm Δ B),
        lsubst M N μ M' →
        step (lapp (llam M) N μ) M'

  | S_App1 :
      forall (Δ Δ₁ Δ₂ : tenv) (A B : ty)
             (M M' : tm Δ₁ (ty_Arrow A B))
             (N    : tm Δ₂ A)
             (μ    : merge Δ₁ Δ₂ Δ),
        step M M' →
        step (lapp M N μ) (lapp M' N μ)

  | S_App2 :
      forall (Δ Δ₁ Δ₂ : tenv) (A B : ty)
             (M    : tm Δ₁ (ty_Arrow A B))
             (N N' : tm Δ₂ A)
             (μ    : merge Δ₁ Δ₂ Δ),
        step N N' →
        step (lapp M N μ) (lapp M N' μ)

  | S_Abs :
      forall (Δ : tenv) (A B : ty)
             (M M' : tm ((A, one) :: Δ) B),
        step M M' →
        step (llam M) (llam M').

(* Multi-step relation *)

Inductive mstep : forall Δ A, tm Δ A → tm Δ A → Prop :=
  | ms_refl :
      forall Δ A (M : tm Δ A), mstep M M
  | ms_step :
      forall Δ A (M N P : tm Δ A),
        step M N →
        mstep N P →
        mstep M P.

(* ----------------------------------- *)
(* Values                              *)
(* ----------------------------------- *)

Definition value {A} (e : tm [] A) : Prop :=
  match e with
  | llam  _
  | ut _ => True
  | _ => False
  end.

Lemma value_arrow_llam :
  forall A B (e : tm [] (ty_Arrow A B)),
    value e → exists M, e = llam M.
Proof.
  intros A B e. dependent destruction e; sfirstorder.
Qed.

(* ----------------------------------- *)
(* Progress                            *)
(* ----------------------------------- *)

(* to put in the algebra
Lemma merge_nil_nil :
  forall (Δ₁ Δ₂ : tenv) (H: merge Δ₁ Δ₂ []), Δ₁ = [] ∧ Δ₂ = [].
  intros. now inv H.
Qed.
*)

Lemma progress (A : ty) (M : tm [] A) :
  value M ∨ exists (M' : tm [] A), step M M'. 
Proof.
  dependent induction M; intros.
  - (* var *) inv u.
  - (* unit *) sfirstorder.
  - (* lam *) sfirstorder.
  - (* app *)
    right.
    assert (m0 := m).
    dependent destruction m0.
    destruct (IHM1 M1 JMeq_refl JMeq_refl).
    destruct (IHM2 M2 JMeq_refl JMeq_refl).
    + (* M1 is a value *)
      destruct (value_arrow_llam M1 H) as [Mb ->].
      destruct (lsubst_total Mb M2 m) as [Mb' Hβ].
      exists Mb'. constructor; exact Hβ.
    + sauto lq: on.
    + sauto lq: on.
Qed.

(* ----------------------------------- *)
(* Neutral and normal forms            *)
(* ----------------------------------- *)

Inductive neutral : forall Δ A, tm Δ A → Prop :=
  | ne_var :
      forall Δ A Δ' (u : upd Δ A A one zero Δ') (h : exh hal Δ'),
        neutral (var u h)
  | ne_app :
      forall Δ A B Δ₁ Δ₂
             (M : tm Δ₁ (ty_Arrow A B))
             (N : tm Δ₂ A)
             (μ : merge Δ₁ Δ₂ Δ),
        neutral M →
        normal N →
        neutral (lapp M N μ)

with normal : forall Δ A, tm Δ A → Prop :=
  | n_neut :
      forall Δ A (M : tm Δ A),
        neutral M →
        normal M
  | n_unit :
      forall Δ (h : exh hal Δ),
        normal (ut h)
  | n_lam :
      forall Δ A B (M : tm ((A, one) :: Δ) B),
        normal M →
        normal (llam M).

(* Small sanity: make constructors easy to use *)
Arguments ne_var {Δ A Δ'} u h.
Arguments ne_app {Δ A B Δ₁ Δ₂ M N} μ _ _.
Arguments n_neut {Δ A} _ _.
Arguments n_unit {Δ} h.
Arguments n_lam  {Δ A B} M.

(* ----------------------------------- *)
(* Halting terms                       *)
(* ----------------------------------- *)

Inductive Halts : forall Δ A, tm Δ A → Prop :=
  | Halts_c :
      forall Δ A (M V : tm Δ A),
        mstep M V → normal V → Halts M.
   
(* ----------------------------------- *)
(* Logical predicate                   *)
(* ----------------------------------- *)

(* by structural recursion on the type *)
Fixpoint Reduce (A : ty) {Δ} (M : tm Δ A) : Prop :=
  match A as A0 return tm Δ A0 → Prop with
  | ty_Unit =>
      fun M0 => Halts M0
  | ty_Arrow A1 A2 =>
      fun M0 =>
        (* 1) the term itself halts *)
        Halts M0 ∧
        (* 2) closure under application to any reducible argument,
              along any context split *)
        forall Δ' Δ'' (N : tm Δ' A1) (μ : merge Δ Δ' Δ''),
          Reduce N →
          Reduce (lapp M0 N μ)
  end M.

Notation "M ∈ A" := (Reduce A M) (at level 40).

(* ----------------------------------- *)
(* Backwards-closed lemmas             *)
(* ----------------------------------- *)

(* Helper: Halts is backwards closed w.r.t. one step *)

Lemma Halts_backwards_closed :
  forall Δ A (M M' : tm Δ A),
    step M M' →
    Halts M' →
    Halts M.
Proof.
  intros Δ A M M' Hs Hh.
  destruct Hh as [V Hms Hn]. (* Halts_c *)
  eapply Halts_c.
  - (* mstep from M to V: one step, then the chain from Hms *)
    eapply ms_step; eauto.
  - exact H0.
Qed.

(* Main lemma: Reduce is backwards closed w.r.t. one step *)

Lemma Reduce_backwards_closed :
  forall Δ A (M M' : tm Δ A),
    step M M' →
    Reduce M' →
    Reduce M.
Proof.
  (* structural induction on the type A, matching the Fixpoint Reduce *)
  induction A as [| A1 IHA1 A2 IHA2]; intros M M' Hs Hred.
  - (* A = ty_Unit *)
    cbn in *. (* Reduce ty_Unit M' = Halts M' *)
    eapply Halts_backwards_closed; eauto.
  - (* A = ty_Arrow A1 A2 *)
    cbn in Hred. destruct Hred as [Hhalt Hclos]. (* Halts M' ∧ closure *)
    split.
    + (* Halts M *)
      eapply Halts_backwards_closed; eauto.
    + (* Closure: for any split and reducible arg, the application reduces *)
      intros Δ' Δ'' N μ HN.
      (* Hclos gives reducibility for lapp M' N μ; step-congruence S_App1
         and the IH on A2 give reducibility for lapp M N μ. *)
      specialize (Hclos Δ' Δ'' N μ HN) as Happ'.
      Fail eapply (IHA2 (lapp M N μ)).
      (* we need a lemma for merge/Reduce *)
      (*
      * exact (S_App1 (Δ:=Δ) (Δ₁:=_) (Δ₂:=_) (A:=A1) (B:=A2) M M' N μ Hs).
      * exact Happ'. *)
Admitted.
