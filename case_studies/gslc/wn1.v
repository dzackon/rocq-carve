(* ======================================================= *)
(* Weak normalization for generic substructural λ-calculus *)
(* (first approach)                                        *)
(* ======================================================= *)

From Hammer Require Import Tactics.
From Autosubst Require Import ARS core fintype stlc step.
From VST Require Import sepalg.
From CARVe Require Import total_fun genv resalg.
Require Import gslc.
Import ScopedNotations.
Set Implicit Arguments.

Section WeakNorm.
Variable A : Type. (* Resource algebra elements *)
Variable JA : Join A.
Variable RA : Res_alg A.

(* -------------------------------------------- *)
(* Multi-step reduction and halting             *)
(* -------------------------------------------- *)

Definition mstep {n} (s t : tm n) := star step s t.

Inductive Halts : tm 0 -> Prop :=
| Halts_c :
    forall (M V : tm 0),
      mstep M V -> value V -> Halts M.

Lemma Halts_lam : forall T e,
  Halts (lam T e).
Proof. intros T e; apply Halts_c with (V := lam T e); hauto l: on. Qed.

(* -------------------------------------------- *)
(* Logical predicate                            *)
(* -------------------------------------------- *)

(* by structural recursion on the type *)
Fixpoint Reduce (T : ty) (M : tm 0) : Prop :=
  match T with
  | Unit => Halts M
  | Fun A1 A2 =>
      (* 1) the term itself halts *)
      Halts M /\
      (* 2) closure under application to any reducible argument,
            along any context split *)
      (forall (N : tm 0),
        Reduce A1 N ->
        Reduce A2 (app M N))
  end.

Notation "M ∈ T" := (Reduce T M) (at level 40).

(* -------------------------------------------- *)
(* Lemmas                                       *)
(* -------------------------------------------- *)

(* Halts is backwards closed w.r.t. one step *)
Lemma Halts_backwards_closed :
  forall (M M' : tm 0),
    step M M' ->
    Halts M' ->
    Halts M.
Proof.
intros ? ? ? Hh.
  destruct Hh as [V Hms Hn].
  eapply Halts_c.
  - eapply starSE; eauto.
  - assumption.
Qed.

(* Reducible terms halt *)
Lemma reduce_halts :
  forall T {M : tm 0},
    Reduce T M -> Halts M.
Proof. induction T; cbn in *; sfirstorder. Qed.

(* Main lemma: Reduce is backwards closed w.r.t. one step *)
Lemma Reduce_backwards_closed :
  forall T (M M' : tm 0),
    step M M' ->
    Reduce T M' ->
    Reduce T M.
Proof.
  (* structural induction on the type T, matching the fixpoint Reduce *)
  induction T as [| ? ? ? IHA2]; intros M M' Hs Hred.
  - (* T = ty_Unit *)
    eapply Halts_backwards_closed; eauto.
  - (* T = ty_Arrow T1 T2 *)
    destruct Hred as [Hhalt Hclos]. split.
    + (* Halts M *)
      eapply Halts_backwards_closed; eauto.
    + (* Closure: for any split and reducible arg, the application reduces *)
      intros N HN.
      (* Hclos gives reducibility for app M' N ; step-congruence S_App1
         and the IH on T2 give reducibility for app M N. *)
      eapply (IHA2 (app M N)).
      * sfirstorder.
      * auto.
Qed.

(* -------------------------------------------- *)
(* Reducible substitutions                      *)
(* -------------------------------------------- *)

Definition RedSub {n} (Δ : @tenv A n) : (fin n -> tm 0) -> Prop :=
  fun σ =>
    forall (x : fin n),
      let (ty, mult) := Δ x in
      Reduce ty (σ x).

Definition emptyT (default : A) := emptyG (Unit, default).

Lemma RedSub_nil {default : A} : RedSub (emptyT default) (fun x => var x).
Proof. hauto l: on. Qed.

Lemma RedSub_extend :
  forall {n} {Δ : tenv n} {σ : fin n -> tm 0} {T : ty} {N : tm 0},
    RedSub Δ σ ->
    Reduce T N ->
    forall a, RedSub (scons (T, a) Δ) (scons N σ).
Proof. intros * ? ? ? x. destruct x; sfirstorder. Qed.

(* If RedSub Δ σ and Δ = Δ₁ ⋈ Δ₂, then RedSub Δ₁ σ and RedSub Δ₂ σ *)
Lemma RedSub_split1 :
  forall {n} {Δ Δ1 Δ2 : tenv n} {σ : fin n -> tm 0},
    RedSub Δ σ ->
    join Δ1 Δ2 Δ ->
    RedSub Δ1 σ.
Proof.
  intros ? Δ Δ1 ? ? HRed Hj x. specialize (HRed x).
  destruct (Δ x) as [t ?] eqn:E1, (Δ1 x) as [t1 ?] eqn:E2.
  eapply merge_pointwise_fun with (x := x) in Hj as [H1 H2].
  assert (E : t1 = t) by (rewrite E1, E2 in H1; scongruence); rewrite E.
  assumption.
Qed.

Corollary RedSub_split {PA: Perm_alg A} :
  forall {n} {Δ Δ1 Δ2 : tenv n} {σ : fin n -> tm 0},
    RedSub Δ σ ->
    join Δ1 Δ2 Δ ->
    RedSub Δ1 σ /\ RedSub Δ2 σ.
Proof. eauto using join_comm, RedSub_split1. Qed.

Lemma lookup_redsub :
  forall {n} {Δ : tenv n} {x : fin n} {T : ty} {m : A} (σ : fin n -> tm 0),
    RedSub Δ σ ->
    lookup Δ x = (T, m) ->
    Reduce T (σ x).
Proof.
  intros * HRed Hlook. unfold RedSub, lookup in *. specialize (HRed x).
  now rewrite Hlook in HRed.
Qed.

(* -------------------------------------------- *)
(* Fundamental lemma                            *)
(* -------------------------------------------- *)

Variable PA : Perm_alg A.
Variable SA : Sep_alg A.

Lemma fundamental :
  forall {n} {M : tm n} {Δ : tenv n} {T : ty} {a : A} (σ : fin n -> tm 0),
    has_type Δ M (T, a) ->
    RedSub Δ σ ->
    Reduce T M[σ].
Proof.
  intros n M; induction M; intros; inversion H; subst.
  - cbn; eapply lookup_redsub; eassumption.
  - split.
    + apply Halts_lam.
    + intros.
      eapply (@Reduce_backwards_closed T1 _ M[N .: σ]).
      * asimpl. apply step_beta'. asimpl. reflexivity.
      * eapply IHM. 2: eapply RedSub_extend. all: eassumption.
  - destruct (RedSub_split H0 H7) as [HRed1' HRed2'].
    destruct (IHM1 _ _ _ σ H5 HRed1') as [_ Hfun].
    apply Hfun. eapply IHM2; eassumption.
Qed.

(* -------------------------------------------- *)
(* Weak normalization                           *)
(* -------------------------------------------- *)

Lemma weak_norm {default} :
  forall {M : tm 0} {T : ty} {a : A},
    has_type (emptyT default) M (T, a) ->
    Halts M.
Proof.
  intros. apply (reduce_halts T).
  assert (H' := fundamental H RedSub_nil); now asimpl in H'.
Qed.

End WeakNorm.