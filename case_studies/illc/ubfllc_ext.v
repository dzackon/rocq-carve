(* ======================================================= *)
(* Weak normalization for linear λ-calculus with !, Unit   *)
(* ======================================================= *)

(* Imports *)
From Coq Require Import Lia Logic.FunctionalExtensionality Program.Equality Logic.JMeq Unicode.Utf8.
From Hammer Require Import Hammer.
From VST.msl Require Import sepalg functors.
From CARVe Require Import contexts.total_fun algebras.dill.
From Autosubst Require Import ARS core fintype fintype_axioms  stlc_ext step_ext.
Require Import tenv_ext typing_ext.
Import ScopedNotations.

(* General settings *)
Set Implicit Arguments.

(* -------------------------------------------- *)
(* Multi-step reduction and halting             *)
(* -------------------------------------------- *)

Definition mstep {n} (s t : tm n) := star step s t.

Lemma mstep_trans :
  forall {n} {s1 s2 s3 : tm n},
    mstep s1 s2 → mstep s2 s3 → mstep s1 s3.
Proof.
  unfold mstep in *. eauto using star_trans.
Qed.

Inductive Halts : tm 0 → Prop :=
| Halts_c :
    forall (M V : tm 0),
      mstep M V → value V → Halts M.

(* -------------------------------------------- *)
(* Logical predicate for open terms             *)
(* -------------------------------------------- *)

(* Closure under single-step reduction *)
Inductive closure {n} (R : tm n → Prop) : tm n → Prop :=
| CRed {M : tm n} :
    R M → closure R M
| CStep {M M' : tm n} :
    closure R M' → mstep M M' → closure R M.

(* E_ is the 'evaluation to a value satisfying L' predicate *)
Definition E_ {m} (L : tm m → Prop) (s : tm m) : Prop :=
  exists v, mstep s v ∧ L v.

(* L is the logical predicate indexed by types, now for tm m *)
Fixpoint L {m} (A : ty) : tm m → Prop :=
  match A with
  | Unit =>
      closure (fun M => M = unit)
  | Fun A1 A2 => 
    fun e =>
      match e with
      | lam _ s =>
          forall k (xi : fin m → fin k) v,
            L A1 v →
            E_ (L A2) (subst_tm (scons v (xi >> var_tm)) s)
      | _ => False
      end
  | Bang A1 =>
      closure (fun e =>
        (exists e', e = bang e' ∧ E_ (L A1) e'))
  end.

(* -------------------------------------------- *)
(* Key lemma: L is closed under renaming        *)
(* -------------------------------------------- *)

Lemma closure_reaches_R :
  forall {n} (R : tm n → Prop) t,
    closure R t → exists t', mstep t t' ∧ R t'.
Proof.
  intros. induction H.
  - exists M. split. apply starR. exact H.
  - destruct IHclosure as (v & Hmv & HRv).
    exists v. split. apply (mstep_trans H0 Hmv). exact HRv.
Qed.

Lemma L_ren {m n} A (s : tm m) (xi : fin m → fin n) :
  L A s → L A (ren_tm xi s).
Proof.
  revert s xi. induction A; intros s xi.

  - (* Unit case *)
    simpl in *. intros H. induction H.
    + constructor. rewrite H. reflexivity.
    + eapply CStep.
      * apply IHclosure.
      * substify. eapply mstep_inst. exact H0.

  - (* Fun case *)
    intros.
    destruct s; try contradiction.
    intros k zeta v Hv.
    cbn in H.
    destruct (H k (xi >> zeta) v Hv) as (w & Hmstep & ?).
    exists w. split; auto.
    asimpl. exact Hmstep.

  - (* Bang case *)
    intros. destruct H as [? [e [? HE]] | ? ? Hcl Hstep]; subst.
    + apply CRed. exists (ren_tm xi e). split.
      * reflexivity.
      * destruct HE as (v & Hmv & HLv).
        exists (ren_tm xi v). split.
        -- substify. eapply mstep_inst. exact Hmv.
        -- apply IHA. exact HLv.
    + destruct (closure_reaches_R Hcl) as (_ & Hmt & e & -> & HE).
      eapply CStep with (bang (ren_tm xi e)).
      * apply CRed. exists (ren_tm xi e). split.
        -- reflexivity.
        -- destruct HE as (v & Hmv & HLv).
           exists (ren_tm xi v). split.
           ++ substify. eapply mstep_inst. exact Hmv.
           ++ apply IHA. exact HLv.
      * assert (Hstep' := @mstep_inst m n
                          (xi >> var_tm) _ _ (mstep_trans Hstep Hmt)).
        cbn in Hstep'. substify. exact Hstep'.
Qed.

(* -------------------------------------------- *)
(* Semantic typing judgment                     *)
(* -------------------------------------------- *)

(* G says a substitution σ is good for context Δ: as RedSub but open *)
Definition G {m k} (Δ : tenv m) : (fin m → tm k) → Prop :=
  fun σ => forall (x : fin m), L (fst (Δ x)) (σ x).

(* Semantic typing: for all good substitutions, the term reduces *)
Definition has_ty_sem {m} (Δ : tenv m) (s : tm m) (A : ty) : Prop :=
  forall k (σ : fin m → tm k), G Δ σ → E_ (L A) s[σ].

(* -------------------------------------------- *)
(* Helper lemmas                                *)
(* -------------------------------------------- *)

Lemma val_inclusion {m} A (e : tm m) :
  L A e → E_ (L A) e.
Proof.
  sauto lq: on.
Qed.

(* G holds for the empty context and identity substitution *)
Lemma G_empty : G emptyT (fun x => var_tm x).
Proof.
  intros x. destruct x.
Qed.

Lemma G_extend :
  forall {n k} {Δ : tenv n} {σ : fin n → tm k} {v : tm k} {T : ty} (m : mult),
    G Δ σ →
    L T v →
    G (scons (T, m) Δ) (scons v σ).
Proof.
  intros * HG HL x.
  destruct x; simpl.
  - exact (HG f).
  - exact HL.
Qed.

(* Remark: same proof as for RedSub *)
Lemma G_split1 :
  forall {n k} {Δ Δ1 Δ2 : tenv n} {σ : fin n → tm k},
    G Δ σ →
    join Δ1 Δ2 Δ →
    G Δ1 σ.
Proof.
  intros ? ? Δ Δ1 ? ? HRed Hjoin x.
  unfold G in HRed. specialize (HRed x).
  destruct (Δ x) as [t ?] eqn:E.
  destruct (Δ1 x) as [t1 ?] eqn:E1.
  assert (Heq : t1 = t).
  { pose proof (join_types_match x Hjoin) as [H1 ?].
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
  forall {n k} {Δ : tenv n} {x : fin n} {t : ty}
         {m : mult} (σ : fin n → tm k),
    G Δ σ →
    Δ x = (t, m) →
    L t (σ x).
Proof.
  intros * Hred Heq. unfold G in *.
  specialize (Hred x).
  rewrite Heq in Hred. exact Hred.
Qed.

(* -------------------------------------------- *)
(* Main lemmas                                  *)
(* -------------------------------------------- *)

(* Reducible terms halt *)
Lemma EL_halts :
  forall A {M : tm 0},
    E_ (L A) M → Halts M.
Proof.
  induction A; intros.

  - (* Unit case *)
    destruct H as (v & Hmv & HL).
    destruct (closure_reaches_R HL) as (v' & Hmv' & ->).
    exists unit.
    + eapply mstep_trans; eauto.
    + constructor.

  - (* Fun case *)
    destruct H as (v & Hmv & ?).
    destruct v; try contradiction.
    exists (lam t v).
    + exact Hmv.
    + constructor.

  - (* Bang case *)
    destruct H as (? & Hmv & HL).
    destruct (closure_reaches_R HL) as (? & Hmv' & ? & -> & w & Hmw & HLw).
    specialize (IHA w (val_inclusion A w HLw)).
    destruct IHA.
    exists (bang V).
    + apply (mstep_trans Hmv (mstep_trans Hmv'
            (mstep_trans (mstep_bang Hmw) (mstep_bang H)))).
    + eauto.
Qed.

(* Fundamental lemma: If Δ ⊢ M : A, then Δ ⊨ M : A *)
Lemma fundamental :
  forall {m} {Δ : tenv m} {M : tm m} {A : ty},
    has_type Δ M A → has_ty_sem Δ M A.
Proof.
  intros * HT.
  unfold has_ty_sem, E_.
  induction HT; intros * HG.

  - (* t_VarL *)
    apply (val_inclusion _ _ (lookup_G HG H)).

  - (* t_VarI *)
    exists (σ fn). split.
     + asimpl; apply starR.
     + specialize (HG fn). rewrite H in HG. exact HG.

  - (* t_Unit *)
    exists unit. split.
    + asimpl; apply starR.
    + eapply CRed. reflexivity.

  - (* t_ElimUnit *)
    destruct (G_split HG H) as (G1 & G2).
    destruct (IHHT1 _ _ G1) as (? & Hm1 & HL1).
    destruct (IHHT2 _ _ G2) as (v2 & Hm2 & HL2).
    exists v2. split.
    + eapply mstep_trans.
      * unfold L in HL1.
        destruct (closure_reaches_R HL1) as (_ & Hu & ->).
        apply (mstep_elimunit (mstep_trans Hm1 Hu) Hm2).
      * apply (step_mstep (step_beta_unit _)).
    + exact HL2.

  - (* t_Abs *)
    apply val_inclusion. cbn.
    intros k' xi v Hv.
    (* Need to extend G to work with v .: (σ >> ⟨xi⟩) *)
    assert (HG' : G (scons (T2, one) Δ) (scons v (σ >> ren_tm xi))).
    { unfold G. intros [x'|]; cbn.
      - specialize (HG x'). now apply L_ren.
      - exact Hv. }
    destruct (IHHT _ _ HG') as (v' & Hmstep & ?).
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
    destruct (Hv1 k id v2 Hv2) as (v & ? & ?).
    exists v; split; eauto. asimpl.
    enough (star step (app (lam t v1) v2) v).
    + eapply star_trans.
      eapply mstep_app; eauto. assumption.
    + eapply star_trans.
      * eright. econstructor; eauto. constructor.
      * sfirstorder.

  - (* t_Bang *)
    destruct (IHHT _ _ HG) as (v & Hm & HL). asimpl.
    exists (bang v). split.
    + exact (mstep_bang Hm).
    + apply CRed. exists v. split.
      * reflexivity.
      * apply val_inclusion. exact HL.

  - (* t_LetBang *)
    destruct (G_split HG H) as (G1 & G2).
    (* apply IHHT1 *)
    destruct (IHHT1 _ _ G1) as (v & Hm_v & ?).
    (* invoke closure property of L (Bang A) *)
    assert (HR : closure (fun e => exists e', e = bang e' ∧ E_ (L A) e') v)
      by sauto.
    destruct (closure_reaches_R HR)
      as (_ & Hm_v' & v' & -> & e & Hm_e & HL_e).
    (* extend G2, apply IHHT2 *)
    assert (G2' := G_extend omega G2 HL_e).
    destruct (IHHT2 _ _ G2') as (? & Hm_w & HL_w).  
    (* conclude case *)
    eexists. split. 
    + cbn.
      eapply mstep_trans.
      eapply (mstep_letbang
        (mstep_trans (mstep_trans Hm_v Hm_v') (mstep_bang Hm_e))
        (starR _ _)).
      assert (subst_eq :
      forall {n k} (N : tm (S n)) (σ : fin n → tm k) (e : tm k),
        N[scons e σ] = N[up_tm σ][scons e ids]).
      { intros. dependent induction N; fsimpl_fext; asimpl; try reflexivity. }
      eapply (starSE (step_beta_bang' (subst_eq _ _ N σ e)) Hm_w).
    + exact HL_w.
Qed.

(* -------------------------------------------- *)
(* Weak normalization                           *)
(* -------------------------------------------- *)

Lemma weak_norm :
  forall {M : tm 0} {A : ty},
    has_type emptyT M A →
    Halts M.
Proof.
  intros.
  assert (HLm := (fundamental H) 0 _ G_empty); asimpl in HLm.
  exact (EL_halts _ HLm).
Qed.