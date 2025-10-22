(* ======================================================= *)
(* Weak normalization for DILL (with redns. under binders) *)
(* ======================================================= *)

(* Library imports *)
Require Import ARS core fintype stlc_ext step_ext algebra_ext.
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

(* ----------------------------------- *)
(* Multi-step reduction and halting    *)
(* ----------------------------------- *)

Definition mstep {n} (s t : tm n) := star step s t.

(* (* DZ: can we just invoke `star_trans` directly? *)
Lemma mstep_trans :
  forall {n} {s1 s2 s3 : tm n},
    mstep s1 s2 → mstep s2 s3 → mstep s1 s3.
Proof.
  unfold mstep in *. eauto using star_trans.
Qed. *)

Inductive Halts : tm 0 → Prop :=
| Halts_c :
  forall (M V : tm 0),
    mstep M V → value V → Halts M.

(* ------------------------------------- *)
(* Logical predicate for open terms      *)
(* ------------------------------------- *)

(* Closure under single-step reduction *)
Inductive closure {n} (R : tm n → Prop) : tm n → Prop :=
| CRed {M : tm n} : R M → closure R M
| CStep {M M' : tm n} : closure R M' → step M M' → closure R M.

(* E_ is the 'evaluation to a value satisfying L' predicate *)
Definition E_ {m} (L : tm m → Prop) (s : tm m) : Prop :=
  exists v, mstep s v ∧ L v.

(* L is the logical predicate indexed by types, now for tm m *)
Fixpoint L {m} (A : ty) : tm m → Prop :=
  match A with
  | Unit => fun s => exists v, mstep s v ∧ value v (* TODO *)
  | Fun A1 A2 => fun e =>
      match e with
      | lam _ s =>
          forall k (xi : fin m → fin k) v,
            L A1 v →
            E_ (L A2) (subst_tm (scons v (xi >> var_tm)) s)
      | _ => False
      end
  | Bang A1 =>
    closure (fun e => (exists e', e = bang e' ∧ E_ (L A1) e'))
  end.

(* ------------------------------------- *)
(* Key lemma: L is closed under renaming *)
(* ------------------------------------- *)

(* monotonicity of closure *)
(* Lemma closure_monotone {m} (R1 R2 : tm m -> Prop) s :
  (forall t, R1 t -> R2 t) ->
  closure R1 s ->
  closure R2 s.
Proof.
  intros HR Hcl. induction Hcl.
  - apply CRed. apply HR. assumption.
  - eapply CStep; eauto.
Qed. *)

(* monotonicity of closure under renaming *)
Lemma closure_monotone_ren {m n} (R1 : tm m -> Prop) (R2 : tm n -> Prop) (xi : fin m → fin n) s :
  (forall t, R1 t -> R2 t ⟨xi⟩) ->
  closure R1 s ->
  closure R2 s ⟨xi⟩.
Proof.
  intros HR Hcl. induction Hcl.
  - apply CRed. apply HR. assumption.
  - eapply CStep; eauto. substify. eapply step_inst. assumption.
Qed.

(* renaming property of closure *)
(* Lemma closure_ren {m n} (R : tm m → Prop) (xi : fin m → fin n) :
  forall s, closure R s →
    closure (fun t => exists s', t = ren_tm xi s' ∧ R s') (ren_tm xi s).
Proof.
  intros s H. induction H.
  - apply CRed. exists M. split; auto.
  - eapply CStep.
    + apply IHclosure.
    + substify. eapply step_inst. assumption.
Qed. *)

Lemma L_ren {m n} A (s : tm m) (xi : fin m → fin n) :
  L A s → L A (ren_tm xi s).
Proof.
  revert s xi. induction A(*  as [|A1 IHA1 A2 IHA2|A] *); intros s xi.
  - (* Base case *)
    intros (v & Hmstep & Hval).
    exists (ren_tm xi v).
    split.
    + substify. eapply mstep_inst. trivial.
    + destruct v; cbn in Hval; try contradiction; try exact I.
      admit.
  - (* Fun case *)
    intros.
    destruct s; try contradiction.
    intros k zeta v Hv.
    cbn in H.
    destruct (H k (xi >> zeta) v Hv) as (w & Hmstep & Hw).
    exists w. split; eauto. asimpl. eauto.
  - (* Bang case *)
    intros. destruct H as [e [e' [He' HE]] | e e' Hcl Hstep]; subst.
    + asimpl in IHA.
      admit.
    + simpl.
      eapply CStep.
      * (* assert (Hcl' := closure_ren xi Hcl); simpl in Hcl'. *)
        (* IHA *)
        admit.
      * substify. eapply step_inst. exact Hstep.
Admitted.

(* TODO *)