(* ======================================================= *)
(* Intrinsically typed _intutionistic_ case                *)
(* ======================================================= *)

From Coq Require Import Lia List Unicode.Utf8.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.
Import ListNotations.

Set Implicit Arguments.
Generalizable All Variables.

(* -------------------------------------------- *)
(* Basic definitions                            *)
(* -------------------------------------------- *)

Inductive ty : Type :=
| ty_Unit
| ty_Arrow : ty → ty → ty.

Definition tenv := list ty.

Inductive Var : tenv → ty → Type :=
| ZVAR : forall Δ t, Var (t :: Δ) t
| SVAR : forall Δ t t', Var Δ t → Var (t' :: Δ) t.

Inductive tm (Δ : tenv) : ty → Type :=
| var  : forall t, Var Δ t → tm Δ t
| ut   : tm Δ ty_Unit
| abs  : forall t1 t2, tm (t1 :: Δ) t2 → tm Δ (ty_Arrow t1 t2)
| app  : forall t1 t2, tm Δ (ty_Arrow t1 t2) → tm Δ t1 → tm Δ t2.

Arguments ZVAR {Δ t}.
Arguments SVAR {Δ t t'} _.

Notation "'U'" := ty_Unit .

(* -------------------------------------------- *)
(* Mutually defined intrinsically-typed         *)
(* environments and values                      *)
(* -------------------------------------------- *)

Inductive env : tenv → Type :=
| ENil  : env []
| ECons : forall Δ t, val t → env Δ → env (t :: Δ)
with val : ty → Type :=
| VUnit : val ty_Unit
| VClos : forall Δ t1 t2, tm (t1 :: Δ) t2 → env Δ → val (ty_Arrow t1 t2).

Arguments ECons {Δ t} _ _.
Arguments VClos  {Δ t1 t2} _ _.

(* -------------------------------------------- *)
(* Environment extension                        *)
(* -------------------------------------------- *)

Definition extend {Δ t} (v : val t) (ρ : env Δ) : env (t :: Δ) := ECons v ρ.
Notation "v .: ρ" := (extend v ρ) (at level 60, right associativity).

(* -------------------------------------------- *)
(* Relational lookup (typed de Bruijn indexing) *)
(* -------------------------------------------- *)

Inductive lookup : forall Δ t, env Δ → Var Δ t → val t → Prop :=
| LZ  : forall Δ t (v : val t) (ρ : env Δ),
    lookup (ECons v ρ) ZVAR v
| LS  : forall Δ t t' (v' : val t') (ρ : env Δ) (x : Var Δ t) (v : val t),
    lookup ρ x v →
    lookup (ECons v' ρ) (SVAR x) v.

(* Functionality of lookup *)
Lemma lookup_functional :
  forall Δ t (ρ : env Δ) (x : Var Δ t) v1 v2,
    lookup ρ x v1 → lookup ρ x v2 → v1 = v2.
Proof.
  intros Δ t ρ x v1 v2 H1; revert v2.
  induction H1; intros v2 H2; dependent destruction H2; subst; eauto.
Qed.

(* Totality of lookup *)
Lemma lookup_total :
  forall Δ t (ρ : env Δ) (x : Var Δ t),
    exists v, lookup ρ x v.
Proof.
  intros Δ t ρ x.
  induction x; dependent destruction ρ; sintuition.
Qed.

(* -------------------------------------------- *)
(* Big-step, call-by-value evaluation           *)
(* (using relational lookup)                    *)
(* -------------------------------------------- *)

Inductive eval : forall (Δ : tenv) t, env Δ → tm Δ t → val t → Prop :=
| Ev_Var :
    forall Δ t (ρ : env Δ) (x : Var Δ t) v,
      lookup ρ x v →
      eval ρ (var x) v
| Ev_Ut :
    forall Δ (ρ : env Δ),
      eval ρ (ut Δ) VUnit
| Ev_Abs :
    forall Δ t1 t2 (ρ : env Δ) (e : tm (t1 :: Δ) t2),
      eval ρ (abs e) (VClos e ρ)
| Ev_App :
    forall Δ t1 t2 (ρ : env Δ)
           (e1 : tm Δ (ty_Arrow t1 t2)) (e2 : tm Δ t1)
           (Δ0 : tenv) (e : tm (t1 :: Δ0) t2) (ρ0 : env Δ0)
           (varg : val t1) (vres : val t2),
      (* operator to closure *)
      eval ρ e1 (VClos e ρ0) →
      (* argument to value *)
      eval ρ e2 varg →
      (* body under captured env extended with argument *)
      eval (varg .: ρ0) e vres →
      eval ρ (app e1 e2) vres.

Arguments eval {Δ t} _ _ _.

(* -------------------------------------------- *)
(* Determinism of evaluation                    *)
(* -------------------------------------------- *)

Lemma eval_deterministic :
  forall Δ t (ρ : env Δ) (e : tm Δ t) v1 v2,
    eval ρ e v1 →
    eval ρ e v2 →
    v1 = v2.
Proof.
  intros Δ t ρ e v1 v2 He1.
  generalize dependent v2.
  (* Key: dependent induction on the FIRST derivation *)
  induction He1; intros v2 He2; dependent destruction He2; try trivial.
  - (* var *) eapply lookup_functional ; eauto.
  - (* app *)
    (* By IH on the operator, both closures are equal. *)
    specialize (IHHe1_1 _ He2_1).
    dependent destruction IHHe1_1; subst.
    (* Now equalize the argument results. *)
    specialize (IHHe1_2 _ He2_2). subst.
    (* Finally equalize the body results. *)
    eapply IHHe1_3; eauto.
Qed.

(* -------------------------------------------- *)
(* Logical relation                             *)
(* -------------------------------------------- *)

Fixpoint Reduce (t : ty) : val t → Prop :=
  match t with
  | ty_Unit => fun _ => True
  | ty_Arrow t1 t2 =>
      fun w =>
        exists Δ (e : tm (t1 :: Δ) t2) (ρ : env Δ),
          w = VClos e ρ /\
          (forall (a : val t1), @Reduce t1 a →
             exists (b : val t2), eval (a .: ρ) e b /\ @Reduce t2 b)
  end.

Notation "W ∈ T" := (Reduce T W) (at level 40).

Definition RedEnv (Δ : tenv) (ρ : env Δ) : Prop :=
  forall t (x : Var Δ t) v, lookup ρ x v → Reduce v.

Lemma RedEnvNil : RedEnv ENil.
Proof. hfcrush. Qed.

Lemma RedEnv_extend {Δ t} (ρ : env Δ) (w : val t) :
  RedEnv ρ → @Reduce t w → RedEnv (w .: ρ).
Proof.
  intros Hρ Ha t' x v Hlk; dependent destruction Hlk; eauto.
Qed.

(* -------------------------------------------- *)
(* Fundamental Lemma (logical relation)         *)
(* -------------------------------------------- *)

Theorem fundamental :
  forall Δ t (e : tm Δ t) (ρ : env Δ),
    RedEnv ρ →
    exists v, eval ρ e v /\ @Reduce t v.
Proof.
  intros Δ t e.
  (* no need of `dependent induction` *)
  induction e; intros ρ Hρ.
  - (* var *)
    destruct (lookup_total ρ v) as [w Hw].
    exists w. split.
    + constructor; exact Hw.
    + eapply Hρ; exact Hw.
  - (* ut *)
    exists VUnit. split; constructor.
  - (* abs *)
    exists (VClos e ρ). split.
    + constructor.
    + (* show Reduce (Arrow t1 t2) for the closure *)
      exists Δ, e, ρ. split; try reflexivity.
      intros a Ha.
      specialize (IHe (a .: ρ)).
      destruct (IHe (RedEnv_extend Hρ Ha)) as [b [He Hb]].
      exists b. split; assumption.
  - (* app *)
    destruct (IHe1 ρ Hρ) as [w1 [He1 Hw1]].
    destruct Hw1 as [Δ0 [e0 [ρ0 [-> Hclos]]]]. (* w1 = VClos e0 ρ0 *)
    destruct (IHe2 ρ Hρ) as [a [He2 Ha]].
    specialize (Hclos a Ha).
    destruct Hclos as [b [He3 Hb]].
    exists b. split.
    + econstructor; eauto.
    + exact Hb.
Qed.

(* -------------------------------------------- *)
(* Theorem                                      *)
(* -------------------------------------------- *)

(* Totality of evaluation: The evaluation of any (well-typed) term is well-defined *)
Corollary total:
  forall t (e : tm [] t),
    exists a, eval ENil e a.
Proof.
  intros.
  specialize (@fundamental nil t e ENil RedEnvNil).
  sfirstorder.
Qed.