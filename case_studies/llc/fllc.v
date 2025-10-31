(* ======================================================= *)
(* Weak normalization for linear λ-calculus                *)
(* ======================================================= *)

(* Imports *)
From Coq Require Import Lia Logic.FunctionalExtensionality Unicode.Utf8.
From Hammer Require Import Hammer.
From VST.msl Require Import sepalg functors.
From CARVe Require Import contexts.total_fun algebras.purely_linear.
From Autosubst Require Import ARS core fintype stlc step.
Require Import tenv typing.
Import ScopedNotations.

(* General settings *)
Set Implicit Arguments.

(* -------------------------------------------- *)
(* Multi-step reduction and halting             *)
(* -------------------------------------------- *)

(* Definition mstep{n} (s t : tm n) := star step s t. *)

Definition mstep {n} (s t : tm n) := star step s t.

Inductive Halts : tm 0 → Prop :=
| Halts_c :
    forall (M V : tm 0),
      mstep M V → value V → Halts M.

Lemma Halts_lam : forall T e,
  Halts (lam T e).
Proof.
  intros T e.
  apply Halts_c with (V := lam T e).
  - sfirstorder.
  - simpl. exact I.
Qed.

(* -------------------------------------------- *)
(* Logical predicate                            *)
(* -------------------------------------------- *)

(* by structural recursion on the type *)
Fixpoint Reduce (A : ty) (M : tm 0) : Prop :=
  match A with
  | Unit => Halts M
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

(* -------------------------------------------- *)
(* Lemmas                                       *)
(* -------------------------------------------- *)

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
  - eapply starSE; eauto.
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
    cbn in *.
    eapply Halts_backwards_closed; eauto.
  - (* A = ty_Arrow A1 A2 *)
    cbn in Hred. destruct Hred as [Hhalt Hclos].
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

(* -------------------------------------------- *)
(* Reducible substitutions                      *)
(* -------------------------------------------- *)

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
    RedSub (scons (T, one) Δ) (scons N σ).
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
  unfold RedSub in HRed.
  specialize (HRed x).
  destruct (Δ x) as [t m] eqn:E.
  destruct (Δ1 x) as [t1 m1] eqn:E1.
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
  forall {n} {Δ : tenv n} {x : fin n} {t : ty} {m : mult}
         (σ : fin n → tm 0),
    RedSub Δ σ ->
    @lookup_tfctx _ _ _ Δ x = (t, m) ->
    Reduce t (σ x).
Proof.
  intros * HRed Hlook.
  unfold RedSub in HRed.
  specialize (HRed x).
  unfold lookup_tfctx in *.
  now rewrite Hlook in HRed.
Qed.

(* -------------------------------------------- *)
(* Fundamental lemma                            *)
(* -------------------------------------------- *)

Lemma fund :
  forall {n} {Δ : tenv n} {M : tm n} {A : ty} (σ : fin n → tm 0),
    has_type Δ M A →
    RedSub Δ σ →
    Reduce A M[σ].
Proof.
  intros. induction H.
  - specialize (lookup_redsub H0 H). sfirstorder.
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

(* -------------------------------------------- *)
(* Weak normalization                           *)
(* -------------------------------------------- *)

Lemma weak_norm :
  forall {M : tm 0} {A : ty},
    has_type emptyT M A →
    Halts M.
Proof.
  intros. apply (reduce_halts A).
  rewrite <- (instId'_tm M).
  exact (fund H RedSub_nil).
Qed.