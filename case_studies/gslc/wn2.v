(* ======================================================= *)
(* Weak normalization for generic substructural λ-calculus *)
(* (second approach)                                       *)
(* ======================================================= *)

(** Based on https://www.ps.uni-saarland.de/~kstark/thesis/website/Chapter9.wn.html *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From Hammer Require Import Tactics.
From Autosubst Require Import ARS core fintype stlc step.
From VST Require Import sepalg.
From CARVe Require Import total_fun genv resalg.
Require Import gslc.
Import ScopedNotations.

Section WeakNorm.
Variable A : Type. (* Resource algebra elements *)
Variable JA : Join A.
Variable RA : Res_alg A.

(* -------------------------------------------- *)
(* Multi-step reduction and halting             *)
(* -------------------------------------------- *)

Definition mstep {n} (s t : tm n) := star step s t.

Inductive Halts {n} : tm n -> Prop :=
| Halts_c :
  forall (M V : tm n),
    mstep M V -> value V -> Halts M.

(* -------------------------------------------- *)
(* Logical predicate for open terms             *)
(* -------------------------------------------- *)

(* E_ is the 'evaluation to a value satisfying L' predicate *)
Definition E_ {m} (L : tm m -> Prop) (s : tm m) : Prop :=
  exists v, mstep s v /\ L v.

(* L is the logical predicate indexed by types, now for tm m *)
Fixpoint L {m} (T : ty) : tm m -> Prop :=
  match T with
  | Unit => fun s => exists v, mstep s v /\ value v
  | Fun T1 T2 => fun e =>
      match e with
      | lam _ s =>
          forall k (xi : fin m -> fin k) v,
            L T1 v ->
            E_ (L T2) (subst_tm (scons v (xi >> var)) s)
      | _ => False
      end
  end.

(* -------------------------------------------- *)
(* Key lemma: L is closed under renaming        *)
(* -------------------------------------------- *)

Lemma L_ren {m n} T (s : tm m) (xi : fin m -> fin n) :
  L T s -> L T (ren_tm xi s).
Proof.
  revert xi. induction T; intros xi.
  - (* Unit case *)
    intros (v & Hmstep & Hval). exists (ren_tm xi v). split.
    + substify. eapply mstep_inst. trivial.
    + destruct v; cbn in Hval; try contradiction; exact I.
  - (* Fun case *)
    intros. destruct s; try contradiction.
    intros k zeta v Hv. cbn in H.
    destruct (H k (xi >> zeta) v Hv) as (w & ? & ?).
    exists w. split; eauto. asimpl. eauto.
Qed.

(* -------------------------------------------- *)
(* Semantic typing judgment                     *)
(* -------------------------------------------- *)

(* G: a substitution σ is good for context Δ (as RedSub but open) *)
Definition G {m k} (Δ : @tenv A m) : (fin m -> tm k) -> Prop :=
  fun σ => forall (x : fin m), L (fst (Δ x)) (σ x).

(* Semantic typing: for all good substitutions, the term reduces *)
Definition has_ty_sem {m} (Δ : tenv m) (s : tm m) (T : ty) : Prop :=
  forall k (σ : fin m -> tm k), G Δ σ -> E_ (L T) s[σ].

(* -------------------------------------------- *)
(* Helper lemmas                                *)
(* -------------------------------------------- *)

Lemma val_inclusion {m} T (e : tm m) :
  L T e -> E_ (L T) e.
Proof. sauto lq: on. Qed.

(* G holds for the empty context and identity substitution *)
Lemma G_empty {default : A} : G (emptyT default) (fun x => var x).
Proof. hauto l: on. Qed.

(* Remark: same proof as for RedSub *)
Lemma G_split1 :
  forall {n k} {Δ Δ1 Δ2 : tenv n} {σ : fin n -> tm k},
    G Δ σ ->
    join Δ1 Δ2 Δ ->
    G Δ1 σ.
Proof.
  intros ? ? Δ Δ1 ? ? HRed Hjoin x.
  unfold G in HRed. specialize (HRed x).
  destruct (Δ x) as [t ?] eqn:E, (Δ1 x) as [t1 ?] eqn:E1.
  assert (Heq : t1 = t).
  { eapply merge_pointwise_fun with (x := x) in Hjoin as [H1 ?].
    rewrite E, E1 in H1. cbn in H1. auto. }
  rewrite Heq. assumption.
Qed.

Corollary G_split {PA: Perm_alg A} :
  forall {n k} {Δ Δ1 Δ2 : tenv n} {σ : fin n -> tm k},
    G Δ σ ->
    join Δ1 Δ2 Δ ->
    G Δ1 σ /\ G Δ2 σ.
Proof. eauto using G_split1, join_comm. Qed.

(* -------------------------------------------- *)
(* Main lemmas                                  *)
(* -------------------------------------------- *)

(* Reducible terms halt *)
Lemma EL_halts :
  forall T {M : tm 0},
    E_ (L T) M -> Halts M.
Proof.
  intros T ? [v [? HLv]]. destruct T.
  - destruct HLv as [w [Hvw Hvalw]]. scrush use: star_trans.
  - destruct v; try contradiction. hauto l: on.
Qed.

(* -------------------------------------------- *)
(* Fundamental lemma                            *)
(* -------------------------------------------- *)

Variable PA : Perm_alg A.
Variable SA : Sep_alg A.

(* Fundamental lemma: If Δ ⊢ M : T, then Δ ⊨ M : T *)
Lemma fundamental :
  forall {n} {Δ : tenv n} {M : tm n} {T : ty} {a : A},
    has_type Δ M (T, a) ->
    has_ty_sem Δ M T.
Proof.
  intros * HT. unfold has_ty_sem, E_.
  dependent induction HT; intros * HG.

  - (* t_Var *)
    apply val_inclusion. specialize (HG fn); unfold lookup in H0; now rewrite H0 in HG.

  - (* t_Abs *)
    asimpl; apply val_inclusion.
    intros k' xi v Hv.
    (* Need to extend G to work with v .: (σ >> ⟨xi⟩) *)
    assert (HG' : G (scons (T2, a) Δ) (scons v (σ >> ren_tm xi))).
    { unfold G. intros [x'|]; cbn. specialize (HG x'). now apply L_ren. exact Hv. }
    destruct (IHHT _ _ _ eq_refl _ _ HG') as (v' & Hmstep & ?).
    exists v'. repeat split; auto.
    assert (Hsub : ren_tm xi = subst_tm (xi >> @var k')).
    { extensionality s; apply rinstInst'_tm. }
    rewrite Hsub in Hmstep; asimpl; assumption.

  - (* t_App *)
    destruct (G_split HG H) as (D1 & D2).
    (* Apply IHs to get values *)
    destruct (IHHT1 _ _ _ eq_refl k σ D1) as (v1 & ? & Hv1).
    destruct (IHHT2 _ _ _ eq_refl k σ D2) as (v2 & ? & Hv2).
    (* v1 must be a lambda *)
    destruct v1; try contradiction.
    (* Apply the lambda to v2 *)
    destruct (Hv1 k id v2 Hv2) as (v & ? & ?).
    exists v; split; eauto. asimpl.
    enough (star step (app (lam t v1) v2) v).
    + eapply star_trans. eapply mstep_app; eauto. assumption.
    + eapply star_trans.
      * eright. econstructor; eauto. constructor.
      * sfirstorder.
Qed.

(* -------------------------------------------- *)
(* Weak normalization                           *)
(* -------------------------------------------- *)

Lemma weak_norm {default} (M : tm 0) T a :
  has_type (emptyT default) M (T, a) ->
  Halts M.
Proof.
  intros.
  assert (HLm := (fundamental H) 0 _ G_empty); asimpl in HLm.
  exact (EL_halts _ HLm).
Qed.

End WeakNorm.