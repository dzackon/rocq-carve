(* ======================================================= *)
(* Weak normalization for linear-intuitionistic λ-calculus *)
(* ======================================================= *)

(* Imports *)
From Coq Require Import Lia Logic.FunctionalExtensionality
                        Program.Equality Logic.JMeq
                        Unicode.Utf8.
From Hammer Require Import Hammer.
From Autosubst Require Import ARS core fintype stlc_ext step_ext.
Require Import algebra_ext.
Import ScopedNotations.

(* General settings *)
Set Implicit Arguments.

(* -------------------------------------------- *)
(* Typing judgment                              *)
(* -------------------------------------------- *)

Inductive has_type {n} (Δ : tenv n) : tm n → ty → Prop :=

  | t_VarL :
      forall (Δ' : tenv n) (T : ty) (fn : fin n),
        upd Δ fn T T One Zero Δ' →
        @exh _ _ mult hal Δ' →
        has_type Δ (var_tm fn) T

  | t_VarI :
      forall (T : ty) (fn : fin n),
        Δ fn = (T, Omega) →
        @exh _ _ mult hal Δ →
        has_type Δ (var_tm fn) T

  | t_Unit :
        @exh _ _ mult hal Δ →
        has_type Δ unit Unit

  | t_ElimUnit :
      forall Δ1 Δ2 M N B,
        has_type Δ1 M Unit →
        has_type Δ2 N B →
        join Δ1 Δ2 Δ →
        has_type Δ (elimunit M N) B

  | t_Abs :
      forall (T1 T2 : ty) e1,
        has_type (scons (T2, One) Δ) e1 T1 →
        has_type Δ (lam T2 e1) (Fun T2 T1)

  | t_App :
      forall (Δ1 Δ2 : tenv n) (T1 T2 : ty) (e1 e2 : tm n),
        has_type Δ1 e1 (Fun T2 T1) →
        has_type Δ2 e2 T2 →
        join Δ1 Δ2 Δ →
        has_type Δ (Core.app e1 e2) T1

  | t_Bang :
      forall M A,
        has_type Δ M A →
        @exh _ _ mult hal Δ →
        has_type Δ (bang M) (Bang A)

  | t_LetBang :
      forall Δ1 Δ2 M N A B,
        has_type Δ1 M (Bang A) →
        has_type (scons (A, Omega) Δ2) N B →
        join Δ1 Δ2 Δ →
        has_type Δ (letbang M N) B.

Notation "Δ '|-' M ':' A" := (has_type Δ M A) (at level 40).

(* -------------------------------------------- *)
(* Multi-step reduction and halting             *)
(* -------------------------------------------- *)

Definition mstep {n} (s t : tm n) := star step s t.

Inductive Halts : tm 0 → Prop :=
| Halts_c :
    forall (M V : tm 0),
      mstep M V → value V → Halts M.

Lemma Halts_lam :
  forall T e, Halts (lam T e).
Proof.
  intros T e.
  apply Halts_c with (V := lam T e).
  - apply starR.
  - simpl. exact I.
Qed.

(* -------------------------------------------- *)
(* Logical predicate                            *)
(* -------------------------------------------- *)

(* Closure under multi-step reduction *)
Inductive closure {n} (R : tm n → Prop) : tm n → Prop :=
| CRed {M : tm n} : R M → closure R M
| CStep {M M' : tm n} : closure R M' → mstep M M' → closure R M.

(* Reducibility predicate, defined by structural recursion on the type *)
Fixpoint Reduce (A : ty) : tm 0 → Prop :=
  match A with
  | Unit => closure (fun M => M = unit) (* Halts *)
  | Fun A1 A2 =>
    fun M =>
    (* 1) the term itself halts *)
    Halts M ∧
    (* 2) closure under application to any reducible argument,
          along any context split *)
    (forall (N : tm 0),
      Reduce A1 N →
      Reduce A2 (Core.app M N))
  | Bang A =>
    closure (fun M => (exists M', M = bang M' ∧ Reduce A M'))
  end.

Notation "M ∈ A" := (Reduce A M) (at level 40).

(* -------------------------------------------- *)
(* Lemmas                                       *)
(* -------------------------------------------- *)

(* Halts is backwards closed under single-step evaluation *)
Lemma Halts_backwards_closed :
  forall (M M' : tm 0),
    step M M' →
    Halts M' →
    Halts M.
Proof.
  intros M M' Hs Hh.
  destruct Hh as [V Hms Hn].
  eapply Halts_c.
  - eapply starSE; eauto.
  - assumption.
Qed.

(* Halts is backwards closed under multi-step evaluation *)
Corollary Halts_backwards_closed_mstep :
  forall (M M' : tm 0),
    mstep M M' →
    Halts M' →
    Halts M.
Proof.
  induction 1; eauto using Halts_backwards_closed.
Qed.

(* Reduction is backwards closed under multi-step evaluation *)
Lemma Reduce_backwards_closed_mstep :
  forall A (M M' : tm 0),
    mstep M M' →
    Reduce A M' →
    Reduce A M.
Proof.
  induction A; intros; cbn in *; try eapply CStep; try eauto.
  - destruct H0 as [Hhalt Hclos]. split.
    * eapply Halts_backwards_closed_mstep; eauto.
    * intros N HN.
      eapply (IHA2 (app M N)).
      + hauto l: on .
      + assert (Hstep := mstep_app H (starR step N)).
        eapply IHA2.
        ** exact Hstep.
        ** exact (Hclos N HN). 
Qed.

(* Reducible terms halt *)
Lemma Reduce_halts :
  forall A {M : tm 0},
    Reduce A M → Halts M.
Proof.
  induction A; cbn in *; try sfirstorder; intros.
  - induction H.
    + sauto.
    + exact (Halts_backwards_closed_mstep H0 IHclosure).
  - induction H.
    + destruct H as [M' [Heq Hred]]; subst.
      specialize (IHA M' Hred). inversion IHA; subst.
      apply (Halts_c (mstep_bang H)). assumption.
    + exact (Halts_backwards_closed_mstep H0 IHclosure).
Qed.

(* -------------------------------------------- *)
(* Reducible substitutions             *)
(* -------------------------------------------- *)

Definition RedSub {n} (Δ : tenv n) : (fin n → tm 0) → Prop :=
  fun σ =>
    forall (x : fin n),
      let (ty, mult) := Δ x in
      Reduce ty (σ x).

(* RedSub ⋅ id *)
Lemma RedSub_nil : RedSub emptyT (fun x => var_tm x).
Proof. intros x. inversion x. Qed.

(* If RedSub Δ σ and M ∈ [A], then RedSub (Δ, A^α) (σ, M) for any α *)
Lemma RedSub_extend :
  forall {n} {Δ : tenv n} {σ : fin n → tm 0} {A : ty} {M : tm 0} (α : mult),
    RedSub Δ σ →
    Reduce A M →
    RedSub (scons (A, α) Δ) (scons M σ).
Proof.
  intros * H1 H2 x.
  unfold scons.
  destruct x as [x'|].
  - specialize (H1 x'). destruct (Δ x'). exact H1.
  - exact H2.
Qed.

(* If RedSub Δ σ and Δ = Δ₁ ⋈ Δ₂, then RedSub Δ₁ σ *)
Lemma RedSub_split1 :
  forall {n} {Δ Δ₁ Δ₂ : tenv n} {σ : fin n → tm 0},
    RedSub Δ σ →
    join Δ₁ Δ₂ Δ →
    RedSub Δ₁ σ.
Proof.
  intros n Δ Δ1 Δ2 σ HRed Hjoin x.
  unfold RedSub in HRed.
  specialize (HRed x).
  destruct (Δ x) as [t m] eqn:E.
  destruct (Δ1 x) as [t1 m1] eqn:E1.
  assert (Heq : t1 = t).
  { pose proof (join_types_match x Hjoin) as [H1 H2].
    rewrite E, E1 in H1. cbn in H1. symmetry. exact H1. }
  rewrite Heq. exact HRed.
Qed.

(* If RedSub Δ σ and Δ = Δ₁ ⋈ Δ₂, then RedSub Δ₁ σ and RedSub Δ₂ σ *)
Corollary RedSub_split :
  forall {n} {Δ Δ₁ Δ₂ : tenv n} {σ : fin n → tm 0},
    RedSub Δ σ →
    join Δ₁ Δ₂ Δ →
    RedSub Δ₁ σ ∧ RedSub Δ₂ σ.
Proof.
  eauto using join_comm, RedSub_split1.
Qed.

(* If RedSub Δ σ and x : t ∈ Δ, then σ(x) ∈ [t] *)
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

(* -------------------------------------------- *)
(* Weak normalization                  *)
(* -------------------------------------------- *)

(* Fundamental lemma: If Δ ⊢ M : A and RedSub Δ σ, then M[σ] ∈ [A] *)
Lemma fund :
  forall {n} {Δ : tenv n} {M : tm n} {A : ty} (σ : fin n → tm 0),
    has_type Δ M A →
    RedSub Δ σ →
    Reduce A M[σ].
Proof.
  intros. induction H.
  - exact (lookup_redsub H0 H).
  - rewrite lookup_upd in H. exact (lookup_redsub H0 H).
  - sauto.
  - destruct (RedSub_split H0 H2) as [Hσ1 Hσ2].
    specialize (IHhas_type1 σ Hσ1) as HRedM.
    inversion HRedM; asimpl.
    + rewrite H3. eapply Reduce_backwards_closed_mstep.
      * apply step_mstep, step_beta_unit.
      * exact (IHhas_type2 σ Hσ2).
    + induction H3; subst.
      * eapply Reduce_backwards_closed_mstep.
        apply (mstep_elimunit H4 (starR step _)).
        eapply Reduce_backwards_closed_mstep.
        apply step_mstep, step_beta_unit.
        exact (IHhas_type2 _ Hσ2).
      * exact (IHclosure (star_trans _ H4 H6)).
  - split.
    + apply Halts_lam.
    + intros. eapply Reduce_backwards_closed_mstep.
      2: exact (IHhas_type _ (RedSub_extend _ H0 H1)). 
      asimpl. apply step_mstep, step_beta_lam'. asimpl. reflexivity.
  - destruct (RedSub_split H0 H2) as [Hσ1' Hσ2'].
    destruct (IHhas_type1 σ Hσ1') as [_ Hfun].
    apply Hfun, IHhas_type2, Hσ2'.
  - apply CRed. exists M[σ].
    split; [reflexivity | exact (IHhas_type σ H0)].
  - asimpl. destruct (RedSub_split H0 H2) as [Hσ1 Hσ2].
    specialize (IHhas_type1 σ Hσ1) as HRed1.
    induction HRed1.
    + destruct H3 as [M' [Heq HRed1']]; subst.
      assert (Hσ2' := RedSub_extend Omega Hσ2 HRed1').
      eapply Reduce_backwards_closed_mstep.
      2: exact (IHhas_type2 _ Hσ2').
      apply step_mstep, step_beta_bang'. asimpl. reflexivity.
    + eapply Reduce_backwards_closed_mstep.
      apply (mstep_letbang H3 (starR step _)). exact IHHRed1.
Qed.

(* Theorem: If ⋅ ⊢ M : A, then M halts *)
Theorem weak_norm :
  forall {M : tm 0} {A : ty},
    has_type emptyT M A →
    Halts M.
Proof.
  intros. apply (Reduce_halts A).
  rewrite <- (instId'_tm M).
  exact (fund H RedSub_nil).
Qed.