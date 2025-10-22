(** Closure based presentation of the linear lambda calculus: encoding
based _intrinsically typed_. The op sem is
big step and  does not perform substitutions, hence no shifting 
is required nor any substitution lemma. 

We prove weak normalization.

*)

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Unicode.Utf8.
From Coq Require Import Lia.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.

Require Import VST.msl.functors.
Require Import VST.msl.sepalg.

From CARVe.contexts Require Import list.
From CARVe.algebras Require Import purely_linear.


Inductive ty : Type :=
| ty_Unit  : ty
| ty_Arrow : ty -> ty -> ty.

Definition tenv := lctx ty mult.

Inductive tm (Δ : tenv) : ty -> Type :=
| var   : forall t Δ' , upd Δ t t one zero Δ' -> exh hal Δ' -> tm Δ t
| ut : exh hal Δ -> tm Δ ty_Unit
| abs : forall t1 t2, tm ((t1,one) :: Δ) t2 -> tm Δ ( ty_Arrow  t1 t2)
| app   : forall t1 t2 Δ1 Δ2, tm Δ1 ( ty_Arrow  t1 t2) -> tm Δ2 t1 -> merge Δ1 Δ2 Δ -> tm Δ t2
.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -o T" := (ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (app x y) (in custom stlc at level 1, left associativity).
Notation "/\ y" :=
  (abs  y) (in custom stlc at level 90,
        y custom stlc at level 99,
        left associativity).

Notation "'Unit'" := ty_Unit (in custom stlc at level 0).
Notation "'unit'" := ut (in custom stlc at level 0).

Ltac inv H := dependent destruction H; subst; clear H; trivial.

(** values *)
Inductive env : tenv -> Type :=
| ENil  : env []
| ECons : forall Δ t m, val t -> env Δ -> env ((t,m) :: Δ)
with val : ty -> Type :=
| VUnit : val ty_Unit
| VClos : forall Δ t1 t2 , tm ((t1,one) :: Δ) t2 -> env Δ -> val (ty_Arrow t1 t2).

Arguments ECons {Δ t} _ _.
Arguments VClos  {Δ t1 t2} _ _.

(*
Lemma merge_ctxrel_pres1: forall Δ1 Δ2 Δ η,
    join Δ1 Δ2 Δ -> hasty_env η Δ -> hasty_env η Δ1.
Proof.
  intros.
  generalize dependent Δ1.
  generalize dependent Δ2.
  induction H0; fcrush.
Qed.
*)

Lemma merge_env_pres1: forall Δ1 Δ2 Δ ,
    join Δ1 Δ2 Δ -> env  Δ -> env Δ1.
Proof.
  intros.
  generalize dependent Δ1.
  generalize dependent Δ2.
  dependent induction X; intros.
  assert (Δ1 = []) by admit.
  - subst. constructor.
  - eapply IHX. Admitted.

(* ---- Environment extension - *)

Definition extend {Δ : tenv} {t : ty} (v : val t) m (ρ : env Δ) : env ((t,m) :: Δ) := 
  ECons m  v ρ.
Notation "v .: ρ" := (extend v ρ) (at level 60, right associativity).

(** STOP HERE
Inductive lookup_venv {Δ : tenv} {t : ty} :  val t -> env Δ -> Prop :=
| vlook_t : forall  W (η : env Δ)  (m : mult), lookup_venv  W (@ECons _ _ m W  η).
| vlook_n : forall  W η W', lookup_venv  W η -> lookup_venv  W ( W' :: η).



Inductive lookup : forall Δ t, env Δ -> Var Δ t -> val t -> Prop :=
| LZ  : forall Δ t (v : val t) (ρ : env Δ),
    lookup  (ECons v ρ) ZVAR v.
| LS  : forall Δ t t' (v' : val t') (ρ : env Δ) (x : Var Δ t) (v : val t),
    lookup ρ x v ->
    lookup  (ECons v' ρ) (SVAR x) v.
(* ---- Big-step, call-by-value evaluation (using relational lookup) ---- *)
Inductive eval : forall (Δ : tenv) t, env Δ -> tm Δ t -> val t -> Prop :=

| Ev_Var :
    forall Δ t (ρ : env Δ) (x : Var Δ t) v,
      lookup  ρ x v ->
      eval  ρ (var x) v 
| Ev_Ut :
    forall Δ (ρ : env Δ),
      eval  ρ (ut Δ) VUnit
| Ev_Abs :
    forall Δ t1 t2 (ρ : env Δ) (e : tm (t1 :: Δ) t2),
      eval   ρ (abs e) (VClos e ρ)
| Ev_App :
    forall Δ t1 t2 (ρ : env Δ)
           (e1 : tm Δ (ty_Arrow t1 t2)) (e2 : tm Δ t1)
           (Δ0 : tenv) (e : tm (t1 :: Δ0) t2) (ρ0 : env Δ0)
           (varg : val t1) (vres : val t2),
      (* operator to closure *)
      eval ρ e1 (VClos  e ρ0) ->
      (* argument to value *)
      eval ρ e2 varg ->
      (* body under captured env extended with argument *)
      eval (varg .: ρ0) e vres ->
      eval  ρ (app e1 e2) vres.
      
(* ---- Determinism of evaluation ---- *)

Lemma eval_deterministic :
  forall Δ t (ρ : env Δ) (e : tm Δ t) v1 v2,
    eval ρ e v1 ->
    eval  ρ e v2 ->
    v1 = v2.
Proof.
  intros Δ t ρ e v1 v2 He1.
  generalize dependent v2.
  (* Key: dependent induction on the FIRST derivation *)
   induction He1; intros v2 He2; dependent destruction He2; try trivial.
  - (* var *)
    eapply lookup_functional ; eauto.
  - (* app *)
   (* hauto lq: on rew: off dep: on *)
    (* By IH on the operator, both closures are equal. *)
    specialize (IHHe1_1 _ He2_1).
    dependent destruction IHHe1_1; subst.
    (* Now equalize the argument results. *)
    specialize (IHHe1_2 _ He2_2). subst.
    (* Finally equalize the body results. *)
    eapply IHHe1_3; eauto.
    Restart.
      intros Δ t ρ e v1 v2 He1.
  generalize dependent v2.
  induction He1; intros v2 He2; dependent destruction He2;  
  hauto lq: on dep:on use: lookup_functional .
Qed.      
      
    
Notation "η '|-' e '>>' w" := (eval η e w) (at level 40).
(** typing values and env *)

(* % Preservation of context relation under merge:
% If η ~ Δ and Δ₁ ⋈ Δ₂ = Δ, then η ~ Δ₁ (and Δ₂ by commutativity)*)
Lemma merge_ctxrel_pres1: forall Δ1 Δ2 Δ η,
    join Δ1 Δ2 Δ -> hasty_env η Δ -> hasty_env η Δ1.
Proof.
  intros.
  generalize dependent Δ1.
  generalize dependent Δ2.
  induction H0; fcrush.
Qed.

Lemma merge_ctxrel_pres2: forall Δ1 Δ2 Δ η, join Δ1 Δ2 Δ -> hasty_env η Δ -> hasty_env η Δ2.
Proof.
  intros.
  apply join_comm in H.
  eapply merge_ctxrel_pres1; eassumption.
Qed.

(** Evaluation of terms*)

(** W ∈ₙ η
lookup_venv +nat -val + venv
*)

Inductive lookup_venv : nat -> val -> env -> Prop :=
| vlook_t : forall  W η, lookup_venv 0 W (W :: η)
| vlook_n : forall n W η W', lookup_venv n W η -> lookup_venv (S n) W ( W' :: η).


Inductive eval: env -> tm -> val -> Prop:=
| eval_unit: forall e: env, eval e <{unit}> unit
| eval_var:  forall n W η, lookup_venv n W η → eval η (var n) W
| eval_abs: forall  e  t1, eval e <{/\ t1}> (closure e <{/\ t1}>)
| eval_app: forall  e e' t1 t2 t3 v v',
    eval e t2 (closure e' <{/\ t1}>) ->
    eval e t3 v' ->
    eval ( v' :: e' ) t1 v -> 
    eval e <{t2 t3}> v.
    
Notation "η '|-' e '>>' w" := (eval η e w) (at level 40).

 (** LR *)
 
 (** Semantic types: because of stratification we define the logical 
 predicate as a Prop total function over types. Note: no 
 "real" linearity involved. 
 *)

Fixpoint Reduce (T: ty)(w: val) : Prop :=
  (match T with
   | ty_Unit  => True
   | ty_Arrow T1 T2 => 
     (match w with
      | closure η <{/\ t1}>  
      => (forall a, Reduce T1 a  ->  exists b,  
        eval (a :: η) t1 b /\  Reduce T2 b)
      | _ => False
      end)
  end).

Notation "W ∈ T" := (Reduce T W) (at level 40).

(** Semantic typing for environments*)

Inductive REG: tenv -> env -> Prop :=
| REGn: REG nil nil
|REGc1 Δ η W A m   : REG Δ η -> Reduce  A W 
 -> REG ( (A,m ) :: Δ) (W :: η).

Notation "  Δ '~~' η" := (REG  Δ η) (at level 40).


(*Semantic typing for terms *)  

Definition Valid (Δ :tenv) (t : tm)  (T : ty) : Prop :=
forall η, REG Δ η -> exists a, eval η t a /\ Reduce T a.
Notation "Gamma '|=' t ':' T" := (Valid Gamma t T) (at level 40).

Hint Unfold Valid : core.

Lemma REG_preservation1: forall Δ1 Δ2 Δ ,
    join Δ1 Δ2 Δ ->  forall η, Δ ~~ η  ->  Δ1 ~~ η .
  intros  Δ1 Δ2 Δ H.
  induction H; intros.
  - inv H; constructor.
  - inv H1.
 destruct x.
  constructor.
  now eapply IHlist_join.
  (* the following is not pretty to look at, but it works*)
  inv H0; sauto.
  Restart. (* blind automation*)
    intros  Δ1 Δ2 Δ H.
  induction H; sauto.
  Qed.
  
Lemma REG_preservation2: forall Δ1 Δ2 Δ η,
    join Δ1 Δ2 Δ ->  Δ ~~ η  ->  Δ2 ~~ η .  
    intros.
  apply join_comm in H.
  eapply REG_preservation1; eassumption.
  Qed.

Lemma REG_lookup: forall Δ η, Δ ~~ η -> forall Δ' n m m' T, updn Δ n T T m m' Δ' ->  exists W, lookup_venv n W η  /\ W ∈ T.
Proof.
  intros Δ η RR.
  induction RR.
  - (* both of these cases are impossible *)
    sauto.
  - intros Δ' n ?m ?m' T U. dependent destruction U; sauto lq: on .
  (*
    -- exists W. sfirstorder.
    -- destruct (IHRR _ _ _ _ _ U) as [x _].
       hauto. *)
Qed.

(** Well-typed terms are semantically typed*)

Lemma fundamental: forall Δ t T, has_type Δ t T -> Valid Δ t T.
Proof.
unfold Valid.
intros Δ t A H. induction H; intros η  Rel.

(** Case UNIT*)
-  eexists. split; econstructor.
  (* hauto l:on.*) 
 (** Case var*)
-  eapply REG_lookup in Rel.
destruct Rel. 2:eassumption.
exists x. split.
   + constructor . firstorder. 
   + tauto.
(*case ABS + inductive hyp*) 
-  exists (closure η <{/\ t1}>).
   split.
   -- eauto using eval.
   -- simpl. intros. specialize (  IHhas_type (cons a η)).
      assert ((cons (T2,one) Δ) ~~ (cons a η)) by eauto using REG.
      firstorder.
(* sauto q:on.*)

(* this is a trick to duplicate hypothesis*)
-  assert (Rel':= Rel). assert (H1' := H1). 
assert (join Δ1 Δ2 Δ ->  Δ ~~ η  ->  Δ1 ~~ η) 
by sfirstorder use: REG_preservation1. 
apply  H2 in H1'. clear H2.
apply  (REG_preservation2 Δ1 Δ2 Δ η)in H1.
apply IHhas_type1 in H1'. clear IHhas_type1.
apply IHhas_type2 in H1. clear IHhas_type2.

2:assumption. 2:assumption.
sintuition.
destruct a; try tauto.
-- destruct t; try tauto.
apply (H4 a0) in H5. sintuition.
exists b; eauto using eval.
Qed.
*)
