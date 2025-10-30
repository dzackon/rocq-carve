(* ============================================= *)
(* Weak normalization for linear λ-calculus      *)
(* (with reductions under binders)               *)
(* ============================================= *)

(* following K. Stark,
https://www.ps.uni-saarland.de/~kstark/thesis/website/Chapter9.wn.html *)

(* Library imports *)
From Coq Require Import Unicode.Utf8.
From Coq Require Import Lia.
From Hammer Require Import Hammer.
From Coq Require Import Logic.FunctionalExtensionality.

(* Local imports *)
From Autosubst Require Import ARS core fintype stlc step.
Import ScopedNotations.
Require Import tenv typing.
From VST.msl Require Import sepalg functors.
From CARVe Require Import contexts.total_fun algebras.purely_linear.

(* ------------------------------------- *)
(* Multi-step reduction and halting      *)
(* ------------------------------------- *)

Definition mstep {n} (s t : tm n) := star step s t.

(* DZ: can we just invoke `star_trans` directly? *)
Lemma mstep_trans :
  forall {n} {s1 s2 s3 : tm n},
    mstep s1 s2 → mstep s2 s3 → mstep s1 s3.
Proof.
  unfold mstep in *. eauto using star_trans.
Qed.

Inductive Halts {n} : tm n → Prop :=
| Halts_c :
  forall (M V : tm n),
    mstep M V → value V → Halts M.

(* ------------------------------------- *)
(* Logical predicate for open terms      *)
(* ------------------------------------- *)

(* E_ is the 'evaluation to a value satisfying L' predicate *)
Definition E_ {m} (L : tm m → Prop) (s : tm m) : Prop :=
  exists v, mstep s v ∧ L v.

(* L is the logical predicate indexed by types, now for tm m *)
Fixpoint L {m} (A : ty) : tm m → Prop :=
  match A with
  | Unit => fun s => exists v, mstep s v ∧ value v
  | Fun A1 A2 => fun e =>
      match e with
      | lam _ s =>
          forall k (xi : fin m → fin k) v,
            L A1 v →
            E_ (L A2) (subst_tm (scons v (xi >> var_tm)) s)
      | _ => False
      end
  end.

(* Reducibility for open terms is now E_ (L A)
Definition Reduce {m} (A : ty) (M : tm m) : Prop := E_ (L A) M. *)

(* ------------------------------------- *)
(* Key lemma: L is closed under renaming *)
(* ------------------------------------- *)

Lemma L_ren {m n} A (s : tm m) (xi : fin m → fin n) :
  L A s → L A (ren_tm xi s).
Proof.
  revert xi. induction A; intros xi.
  - (* Unit case *)
    intros (v & Hmstep & Hval).
    exists (ren_tm xi v).
    split.
    + substify. eapply mstep_inst. trivial.
    + destruct v; cbn in Hval; try contradiction; exact I.
  - (* Fun case *)
    intros.
    destruct s; try contradiction.
    intros k zeta v Hv.
    cbn in H.
    destruct (H k (xi >> zeta) v Hv) as (w & Hmstep & Hw).
    exists w. split; eauto. asimpl. eauto.
Qed.

(* ------------------------------------- *)
(* Semantic typing judgment              *)
(* ------------------------------------- *)

(* G says a substitution σ is good for context Δ: as RedSub but open *)
Definition G {m k} (Δ : tenv m) : (fin m → tm k) → Prop :=
  fun σ => forall (x : fin m), L (fst (Δ x)) (σ x).

(* Semantic typing: for all good substitutions, the term reduces *)
Definition has_ty_sem {m} (Δ : tenv m) (s : tm m) (A : ty) : Prop :=
  forall k (σ : fin m → tm k), G Δ σ → E_ (L A) s[σ].

(* ------------------------------------- *)
(* Helper lemmas                         *)
(* ------------------------------------- *)

Lemma val_inclusion {m} A (e : tm m) :
  L A e → E_ (L A) e.
Proof.
  sauto lq: on.
Qed.

(* G holds for the empty context and identity substitution *)
Lemma G_empty : G emptyT (fun x => var_tm x).
Proof.
  sauto.
Qed.

(* Remark: same proof as for RedSub *)
Lemma G_split1 :
  forall {n k} {Δ Δ1 Δ2 : tenv n} {σ : fin n → tm k},
    G Δ σ →
    join Δ1 Δ2 Δ →
    G Δ1 σ.
Proof.
  intros n k Δ Δ1 Δ2 σ HRed Hjoin x.
  unfold G in HRed.
  specialize (HRed x).
  destruct (Δ x) as [t m] eqn:E.
  destruct (Δ1 x) as [t1 m1] eqn:E1.
  assert (Heq : t1 = t).
  { pose proof (join_types_match x Hjoin) as [H1 H2].
    rewrite E, E1 in H1. cbn in H1. symmetry. exact H1. }
  rewrite Heq. exact HRed.
Qed.

Corollary G_split :
  forall {n k} {Δ Δ1 Δ2 : tenv n} {σ : fin n → tm k},
    G Δ σ →
    join Δ1 Δ2 Δ →
    G Δ1 σ ∧ G Δ2 σ.
Proof.
  eauto using G_split1, join_comm.
Qed.

(* Remark: same proof as for RedSub *)
Lemma lookup_G :
  forall {n k} {Δ  : tenv n} {x : fin n} {t  : ty}
         (σ : fin n → tm k),
    G Δ σ →
    (*     upd Δ x t t' m m' Δ' → *)
    fst ( Δ x) = t  -> 
    L t (σ x).
Proof.
  intros * HG Hupd.
  unfold G  in *. 
  sauto. (*
  specialize (HG x). (* specialize (Hupd x). *)
  destruct (fin_eq x x); [| congruence].
  destruct Hupd as [Heq _].
  destruct (Δ x) as [tx mx].
  inversion Heq. subst. assumption. *)
Qed.

(* ------------------------------------- *)
(* Main lemmas                           *)
(* ------------------------------------- *)

(* Reducible terms halt *)
Lemma EL_halts :
  forall A {M : tm 0},
    E_ (L A) M → Halts M.
Proof.
  intros A M [v [Hmv HLv]].
  destruct A.
  - destruct HLv as [w [Hvw Hvalw]].
  hfcrush use: mstep_trans.
  - destruct v; try contradiction.
    hauto l: on .
Qed.

(* Fundamental lemma: If Δ ⊢ M : A, then Δ ⊨ M : A *)
Lemma fundamental :
  forall {m} {Δ : tenv m} {M : tm m} {A : ty},
    has_type Δ M A → has_ty_sem Δ M A.
Proof.
  intros * HT.
  unfold has_ty_sem, E_.
  induction HT; intros * HG.

  - (* t_Var *)
    sauto lq:on use: val_inclusion, lookup_G. 
(*    apply (val_inclusion _ _ (lookup_G σ HG H)).*)

  - (* t_Abs *)
    apply val_inclusion. asimpl.
    intros k' xi v Hv.
    (* Need to extend G to work with v .: (σ >> ⟨xi⟩) *)
    assert (HG' : G (scons (T2, one) Δ) (scons v (σ >> ren_tm xi))).
    { unfold G. intros [x'|]; cbn.
      - specialize (HG x'). now apply L_ren.
      - exact Hv. }
    destruct (IHHT _ _ HG') as (v' & Hmstep & Hv').
    exists v'. repeat split; auto.
    assert (Hsub : ren_tm xi = subst_tm (xi >> @var_tm k')).
    { extensionality s. apply rinstInst'_tm. }
    rewrite Hsub in Hmstep; asimpl; assumption.

  - (* t_App *)
    destruct (G_split HG H) as (D1 & D2).
    (* Apply IHs to get values *)
    destruct (IHHT1 k σ D1) as (v1 & Hmstep1 & Hv1).
    destruct (IHHT2 k σ D2) as (v2 & Hmstep2 & Hv2).
    (* v1 must be a lambda *)
    destruct v1; try contradiction.
    (* Apply the lambda to v2 *)
    destruct (Hv1 k id v2 Hv2) as (v & Hmstep & Hv).
    exists v; split; eauto. asimpl.
    enough (star step (app (lam t v1) v2) v).
    + eapply star_trans.
      eapply mstep_app; eauto. assumption.
    + eapply star_trans.
      * eright. econstructor; eauto. constructor.
      * sfirstorder.
Qed.

(* ----------------------------------- *)
(* Weak normalization                  *)
(* ----------------------------------- *)

Lemma weak_norm :
  forall {M : tm 0} {A : ty},
    has_type emptyT M A →
    Halts M.
Proof.
  intros.
  assert (HLm := (fundamental H) 0 _ G_empty); asimpl in HLm.
  exact (EL_halts _ HLm).
Qed.
