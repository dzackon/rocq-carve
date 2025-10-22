(* ============================================= *)
(* Weak normalization for linear λ-calculus      *)
(* (without reductions under binders)            *)
(* ============================================= *)

(* Library imports *)
From autosubst Require Import ARS core fintype stlc step algebra.
Import ScopedNotations.
From Coq Require Import Unicode.Utf8.
From Coq Require Import Lia.
From Hammer Require Import Hammer.
From Coq Require Import Logic.FunctionalExtensionality.

(* General settings *)
Set Implicit Arguments.

(* ----------------------------------- *)
(* Typing judgment                     *)
(* ----------------------------------- *)

Inductive has_type {n} (Δ : tenv n) : tm n → ty → Prop :=

| t_Var :
  forall (Δ' : tenv n) (T : ty) (fn : fin n),
    upd Δ fn T T One Zero Δ' →
    @exh _ _ mult hal Δ' →
    has_type Δ (var_tm fn) T

| t_Abs :
  forall (T1 T2 : ty) e1,
    has_type (scons (T2, One) Δ) e1 T1 →
    has_type Δ (lam T2 e1) (Fun T2 T1)

| t_App :
  forall (Δ1 Δ2 : tenv n) (T1 T2 : ty) (e1 e2 : tm n),
    has_type Δ1 e1 (Fun T2 T1) →
    has_type Δ2 e2 T2 →
    join Δ1 Δ2 Δ →
    has_type Δ (Core.app e1 e2) T1.

Notation "Δ '|-' e ':' T" := (has_type Δ e T) (at level 40).

(* ----------------------------------- *)
(* Multi-step reduction and halting    *)
(* ----------------------------------- *)

(* Definition mstep{n} (s t : tm n) := star step s t. *)

Inductive mstep : tm 0 → tm 0 → Prop :=
| ms_refl :
  forall (M : tm 0), mstep M M
| ms_step :
  forall (M N P : tm 0),
    step M N →
    mstep N P →
    mstep M P.

Inductive Halts : tm 0 → Prop :=
| Halts_c :
  forall (M V : tm 0),
    mstep M V → value V → Halts M.

Lemma Halts_lam : forall T e,
  Halts (lam T e).
Proof.
  intros T e.
  apply Halts_c with (V := lam T e).
  - apply ms_refl.
  - simpl. exact I.
Qed.

(* ----------------------------------- *)
(* Logical predicate                   *)
(* ----------------------------------- *)

(* by structural recursion on the type *)
Fixpoint Reduce (A : ty) (M : tm 0) : Prop :=
  match A with
  | Base => Halts M
  | Fun A1 A2 =>
    (* 1) the term itself halts *)
    Halts M ∧
    (* 2) closure under application to any reducible argument,
          along any context split *)
    (forall (N : tm 0),
      Reduce A1 N →
      Reduce A2 (Core.app M N))
  end.

Notation "M ∈ A" := (Reduce A M) (at level 40).

(* ----------------------------------- *)
(* Lemmas                              *)
(* ----------------------------------- *)

(* Halts is backwards closed w.r.t. one step *)
Lemma Halts_backwards_closed :
  forall (M M' : tm 0),
    step M M' →
    Halts M' →
    Halts M.
Proof.
  intros M M' Hs Hh.
  destruct Hh as [V Hms Hn].
  eapply Halts_c.
  - eapply ms_step; eauto.
  - assumption.
Qed.

(* Reducible terms halt *)
Lemma reduce_halts :
  forall A {M : tm 0},
    Reduce A M → Halts M.
Proof.
  induction A; cbn in *; sfirstorder.
Qed.

(* Main lemma: Reduce is backwards closed w.r.t. one step *)
Lemma Reduce_backwards_closed :
  forall A (M M' : tm 0),
    step M M' →
    Reduce A M' →
    Reduce A M.
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
      intros N HN.
      (* Hclos gives reducibility for app M' N ; step-congruence S_App1
         and the IH on A2 give reducibility for app M N. *)
      eapply (IHA2 (app M N)).
      * hauto l: on .
      * exact (Hclos N HN) .
Qed.

(* ----------------------------------- *)
(* Reducible substitutions             *)
(* ----------------------------------- *)

Definition RedSub {n} (Δ : tenv n) : (fin n → tm 0) → Prop :=
  fun σ =>
    forall (x : fin n),
      let (ty, mult) := Δ x in
      Reduce ty (σ x).

Lemma RedSub_nil : RedSub emptyT (fun x => var_tm x).
Proof. sauto. Qed.

Lemma RedSub_extend :
  forall {n} {Δ : tenv n} {σ : fin n → tm 0} {T : ty} {N : tm 0},
    RedSub Δ σ →
    Reduce T N →
    RedSub (scons (T, One) Δ) (scons N σ).
Proof.
  intros n Δ σ T N H1 H2 x.
  unfold scons.
  destruct x as [x'|].
  - specialize (H1 x'). destruct (Δ x'). exact H1.
  - exact H2.
Qed.

(* If RedSub Δ σ and Δ = Δ₁ ⋈ Δ₂, then RedSub Δ₁ σ and RedSub Δ₂ σ *)
Lemma RedSub_split1 :
  forall {n} {Δ Δ1 Δ2 : tenv n} {σ : fin n → tm 0},
    RedSub Δ σ →
    join Δ1 Δ2 Δ →
    RedSub Δ1 σ.
Proof.
  intros n Δ Δ1 Δ2 σ HRed Hjoin x.
  (* RedSub Δ1 σ *)
  unfold RedSub in HRed.
  specialize (HRed x).
  destruct (Δ x) as [t m] eqn:E.
  destruct (Δ1 x) as [t1 m1] eqn:E1.
  (* Need to show t1 = t *)
  assert (Heq : t1 = t).
  { pose proof (join_types_match x Hjoin) as [H1 H2].
    rewrite E, E1 in H1. cbn in H1. symmetry. exact H1. }
  rewrite Heq. exact HRed.
Qed.

Corollary RedSub_split :
  forall {n} {Δ Δ1 Δ2 : tenv n} {σ : fin n → tm 0},
    RedSub Δ σ →
    join Δ1 Δ2 Δ →
    RedSub Δ1 σ ∧ RedSub Δ2 σ.
Proof.
  eauto using join_comm, RedSub_split1.
Qed.

Lemma lookup_redsub :
  forall {n} {Δ Δ' : tenv n} {x : fin n} {t t' : ty}
         {m m' : mult} (σ : fin n → tm 0),
    RedSub Δ σ →
    upd Δ x t t' m m' Δ' →
    Reduce t (σ x).
Proof.
  intros * HRed Hupd.
  unfold RedSub, upd in *.
  specialize (HRed x). specialize (Hupd x).
  destruct (fin_eq x x); [| congruence].
  destruct Hupd as [Heq _].
  destruct (Δ x) as [tx mx].
  inversion Heq. subst. assumption.
Qed.

(* ----------------------------------- *)
(* Weak normalization                  *)
(* ----------------------------------- *)

Lemma fund :
  forall {n} {Δ : tenv n} {M : tm n} {A : ty} (σ : fin n → tm 0),
    has_type Δ M A →
    RedSub Δ σ →
    Reduce A M[σ].
Proof.
  intros. induction H.
  - exact (lookup_redsub H0 H).
  - split.
    + apply Halts_lam.
    + intros.
      eapply (@Reduce_backwards_closed T1 ((app (lam T2 e1)[σ]) N) e1[N .: σ]).
      * asimpl. apply step_beta'. asimpl. reflexivity.
      * exact (IHhas_type _ (RedSub_extend H0 H1)).
  - destruct (RedSub_split H0 H2) as [HRed1' HRed2'].
    specialize (IHhas_type1 σ HRed1') as HRed1.
    destruct HRed1 as [_ Hfun].
    apply Hfun. exact (IHhas_type2 σ HRed2').
Qed.

Lemma weak_norm :
  forall {M : tm 0} {A : ty},
    has_type emptyT M A →
    Halts M.
Proof.
  intros. apply (reduce_halts A).
  rewrite <- (instId'_tm M).
  exact (fund H RedSub_nil).
Qed.