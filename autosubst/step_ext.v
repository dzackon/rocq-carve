(** ** Reduction and Values *)

Require Export Coq.Program.Equality.
From Autosubst Require Import ARS core fintype stlc_ext.
Set Implicit Arguments.
Unset Strict Implicit.

Ltac inv H := dependent destruction H.
#[global] Hint Constructors star : core.
Import ScopedNotations.

(** *** Single-step reduction *)
Inductive step {n} : tm n -> tm n -> Prop :=
  | step_beta_unit t :
      step (elimunit unit t) t
  | step_beta_lam A s t :
      step (app (lam A s) t) (s[t..])
  | step_beta_bang s t :
      step (letbang (bang s) t) (t[s..])
  | step_elimunitL s1 s2 t :
      step s1 s2 -> step (elimunit s1 t) (elimunit s2 t)
  | step_elimunitR s t1 t2 :
      step t1 t2 -> step (elimunit s t1) (elimunit s t2)
  | step_abs A b1 b2 :
      @step (S n) b1 b2 -> step (lam A b1) (lam A b2)
  | step_appL s1 s2 t :
      step s1 s2 -> step (app s1 t) (app s2 t)
  | step_appR s t1 t2 :
      step t1 t2 -> step (app s t1) (app s t2)
  | step_bang s1 s2 :
      step s1 s2 -> step (bang s1) (bang s2)
  | step_letbangL s1 s2 t :
      step s1 s2 -> step (letbang s1 t) (letbang s2 t)
  | step_letbangR s t1 t2 :
      step t1 t2 -> step (letbang s t1) (letbang s t2).

#[global] Hint Constructors step : core.

Lemma step_beta_lam' n A b (t t': tm n):
  t' = b[t..] -> step (app (lam A b) t) t'.
Proof. intros ->. now constructor. Qed.

Lemma step_beta_bang' n (s t' : tm n) (t : tm (S n)):
  t' = t[s..] -> step (letbang (bang s) t) t'.
Proof. intros ->. now constructor. Qed.

(** *** Multi-step reduction *)

Lemma step_mstep :
  forall {n} {s1 s2 : tm n},
    step s1 s2 -> star step s1 s2.
Proof. eauto. Qed.
  
Lemma mstep_elimunit n (s1 s2 t1 t2 : tm n) :
  star step s1 s2 -> star step t1 t2 -> star step (elimunit s1 t1) (elimunit s2 t2).
Proof with eauto. intros ms. induction 1. induction ms... auto... Qed.

Lemma mstep_lam n A (s t : tm (S n)) :
  star step s t -> star step (lam A s) (lam A t).
Proof. induction 1; eauto. Qed.

Lemma mstep_app n (s1 s2 : tm n) (t1 t2 : tm n) :
  star step s1 s2 -> star step t1 t2 -> star step (app s1 t1) (app s2 t2).
Proof with eauto.
  intros ms. induction 1. induction ms... auto...
Qed.

Lemma mstep_bang n (s t : tm n) :
  star step s t -> star step (bang s) (bang t).
Proof. induction 1; eauto. Qed.

Lemma mstep_letbang n (s1 s2 : tm n) (t1 t2 : tm (S n)) :
  star step s1 s2 -> star step t1 t2 -> star step (letbang s1 t1) (letbang s2 t2).
Proof. induction 1; induction 1; eauto. Qed.

(** *** Substitutivity *)

Lemma step_inst {m n} (f : fin m -> tm n) (s t : tm m) :
  step s t -> step (subst_tm f s) (subst_tm f t).
Proof.
  intros st. revert n f.
  induction st; intros; cbn.
  - auto. 
  - apply step_beta_lam'. now asimpl.
  - apply step_beta_bang'. now asimpl.
  - apply step_elimunitL, IHst.
  - apply step_elimunitR, IHst.
  - apply step_abs. eapply IHst.
  - apply step_appL, IHst.
  - apply step_appR, IHst.
  - apply step_bang, IHst.
  - apply step_letbangL, IHst.
  - apply step_letbangR, IHst.
Qed.

Lemma mstep_inst m n (f : fin m -> tm n) (s t : tm m) :
  star step s t -> star step (s[f]) (t[f]).
Proof. induction 1; eauto using step_inst. Qed.

Lemma mstep_subst m n (f g : fin m -> tm n) (s t : tm m) :
  star step s t -> (forall i, star step (f i) (g i)) ->
  star step (s[f]) (t[g]).
Proof with eauto.
  intros st fg.
  apply star_trans with (y := t[f]); [eauto using mstep_inst|].
  clear s st. revert n f g fg.
  induction t; eauto using mstep_elimunit, mstep_app, mstep_bang; intros; simpl.
  - apply mstep_lam, IHt. intros [i|]; [|constructor].
    + asimpl. cbn. unfold funcomp. substify. now apply mstep_inst.
  - apply mstep_letbang, IHt2. eauto. intros [i|]; [|constructor].
    + asimpl. unfold funcomp. substify. now apply mstep_inst.
Qed.

Lemma mstep_beta_lam n (s1 s2 : tm (S n)) (t1 t2 : tm n) :
  star step s1 s2 -> star step t1 t2 ->
  star step (s1 [t1..]) (s2 [t2..]).
Proof. intros st1 st2. apply mstep_subst; [assumption|]. now intros [|]. Qed.

Lemma step_naturality m n (M: tm m) (rho: fin m -> fin n) M' :
  step (M ⟨rho⟩) M' -> exists M'', step M M'' /\ M' = (M'' ⟨rho⟩).
Proof.
  intros H.
  dependent induction H.
  - (* step_beta_unit *)
    destruct M; try inversion x; subst.
    destruct M1; try discriminate.
    exists M2; auto.
  - (* step_beta_lam *)
    destruct M; try inversion x. subst.
    destruct M1; try inversion H0. subst.
    exists (M1[M2..]). split. eauto.
    asimpl. reflexivity.
  - (* step_beta_bang *)
    destruct M; try inversion x; subst.
    destruct M1; try inversion H0; subst.
    exists (M2[M1..]). split; asimpl; auto.
  - (* step_elimunitL *)
    destruct M; inversion x. subst.
    edestruct (IHstep _ M1) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
  - (* step_elimunitR *)
    destruct M; inversion x. subst.
    edestruct (IHstep _ M2) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
  - (* step_abs *)
    destruct M; inversion x. subst.
    edestruct (IHstep _ M) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
  - (* step_appL *)
    destruct M; inversion x. subst.
    edestruct (IHstep _ M1) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
  - (* step_appR *)
    destruct M; inversion x. subst.
    edestruct (IHstep _ M2) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
  - (* step_bang *)
    destruct M; try inversion x; subst.
    edestruct (IHstep _ M) as (?&?&?); [reflexivity|].
    eexists. rewrite H1. split; eauto.
  - (* step_letbangL *)
    destruct M; inversion x. subst.
    edestruct (IHstep _ M1) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
  - (* step_letbangR *)
    destruct M; inversion x. subst.
    edestruct (IHstep _ M2) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
Qed.

Fixpoint value {m} (e : tm m) : Prop :=
  match e with
  | unit => True
  | lam _ _ => True
  | bang t => value t
  | _ => False
  end.

Lemma value_anti {m n} (xi : fin m -> fin n) (s : tm m) :
  value (s⟨xi⟩) -> value s.
Proof. induction s; eauto. apply IHs. Qed.