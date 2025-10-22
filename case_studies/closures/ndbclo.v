(** Closure based presentation of the linear lambda calculus: encoding
based on standard DB notation -- not well scoped. The op sem is
big step and  does not perform substitutions, hence no shifting 
is required nor any substitution lemma. 

We prove subject reduction and weak normalization.

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
| Ty_Unit  : ty
| Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
| var   : nat -> tm
| app   : tm -> tm -> tm
| abs   : tm -> tm
| ut    : tm.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -o T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (app x y) (in custom stlc at level 1, left associativity).
Notation "/\ y" :=
  (abs  y) (in custom stlc at level 90,
        y custom stlc at level 99,
        left associativity).

Notation "'Unit'" := Ty_Unit (in custom stlc at level 0).
Notation "'unit'" := ut (in custom stlc at level 0).

Ltac inv H := inversion H; subst; clear H; trivial.

(** list based contexts*)

Definition tenv := lctx ty mult.

Inductive has_type: tenv -> tm -> ty -> Prop :=
| t_Unit: forall (Δ  :tenv), exh hal Δ -> has_type Δ <{unit}> Ty_Unit
| t_Var: forall (Δ Δ': tenv) (T : ty) (n : nat),
    updn Δ n T T one zero Δ' -> exh hal Δ' -> has_type Δ (var n) T
| t_Abs: forall Δ (T1 T2: ty)  t1,
    has_type ((T2,one):: Δ) t1 T1 ->
    has_type Δ <{/\ t1}> (Ty_Arrow T2 T1)
| t_App: forall (Δ Δ1 Δ2 :tenv) (T1 T2 : ty) t1 t2 ,
    has_type Δ1 t1 (Ty_Arrow T2 T1) ->
    has_type Δ2 t2 T2 -> join Δ1 Δ2 Δ
    -> has_type Δ <{t1 t2}> T1.

Notation "Δ '|-' t ':' T" := (has_type Δ t T) (at level 40).                                                                                                   
(** values *)

Inductive val : Type :=
| unit: val
| closure: list val -> tm -> val.

Definition env := list val.

(** typing values and env *)

Inductive hasty_env: env -> tenv -> Prop:=
| type_empty: hasty_env nil nil
| type_cons: forall e  Δ v T m, 
    hasty_env e Δ -> 
    has_ty v T ->
    hasty_env (v ::  e)((T,m) :: Δ )   
with has_ty: val -> ty -> Prop:=
| type_unit: has_ty unit Ty_Unit
| type_closure: forall e Δ T  t1, 
    has_type Δ <{/\ t1}> T ->
    hasty_env e Δ-> 
    has_ty (closure e <{/\ t1}>) T.

Notation "  t ':' T" := (has_ty t T) (at level 40).
Notation "  η '~' Δ" := (hasty_env η Δ) (at level 40).


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

(** Determine a value's type by performing a look-up in the linear context:
If η ~ Δ, A¹ ∈ₙ Δ, and W ∈ₙ η, then W : A

rec lookup_hasty : [ ⊢ hasty_env η Δ] → [ ⊢ upd Δ n _ _ A _ 𝟙 _ _] → [ ⊢ lookup_venv n W η]
→ [ ⊢ hasty W A]*)

(* generalized to any m m', not just 1 to 0*)
Lemma lookup_hasty: forall η n W  ,
    lookup_venv n W η -> forall Δ Δ' m m' A , hasty_env η Δ 
    ->  updn Δ n A A  m m' Δ' ->  has_ty W A.
Proof.
  intros η n W Hlookup.
  induction Hlookup; intros Δ Δ' m m' A Hhasty Hupd.
  - (* Case: vlook_t *)
    inv Hhasty.
    inv Hupd. 
    (* The value `W` is at the head of the environment and matches the type `A`. *)     
  - (* Case: vlook_n *)
    inv  Hhasty.
    inv Hupd.
    + (* Recursive case: look up in the tail of the environment. *)
      eapply IHHlookup with (Δ := Δ0); eauto.
Qed.

(** Subject reduction*)
Theorem consistency: forall η M W Δ T,
     eval η M W -> hasty_env η Δ -> has_type Δ M T -> has_ty W T.
Proof.
   intros.
   generalize dependent Δ.
   generalize dependent T.
   induction H; intros.
   (* unit *)
   - sauto lq: on.
   - (* var*)
     inv H1. 
     eapply lookup_hasty  in H0; eauto. 
   - sauto lq: on.
   (*app*)
   - rename e into η.
     inv H3.
     specialize (merge_ctxrel_pres1 _ _ _ _ H10 H2). intro.
     specialize (merge_ctxrel_pres2 _ _ _ _ H10 H2). intro.
     specialize(IHeval2 T2 Δ2 H4 H8).
     specialize(IHeval1 (Ty_Arrow T2 T) Δ1 H3 H6).
     inv IHeval1. 
     inv H9. 
     specialize(IHeval3 T ((T2, one) :: Δ0)).
     apply IHeval3; eauto.
     constructor; eauto.
   Qed. (* to be fixed *)
 
 (** LR *)
 
 (** Semantic Types: because of stratification we define the logical 
 predicate as a Prop total function over types. Note: no 
 "real" linearity involved. 
 *)

Fixpoint Reduce (T: ty)(w: val) : Prop :=
  (match T with
   | Ty_Unit  => True
   | Ty_Arrow T1 T2 => 
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

(** Totality of evaluation: the evaluation of any (well-typed) term is well-defined*)
Corollary total: forall t T, has_type [] t T -> 
  exists a, eval [] t a.
Proof.
intros. apply fundamental in H. unfold Valid in H. destruct (H  nil); sfirstorder.
(* hauto use: fundamental unfold: Valid. *)
Qed.

(** comments: linearity shows up in the fundamental lemma, barely: 

- var: just need to look up values in Δ ~~ η
- app: here we need  that the extension of the predicate to contexts is 
preserved under merge/join: join Δ1 Δ2 Δ  -> Δ ~~ η  ->  Δ1 ~~ η /\ Δ2 ~~ η to fire the IH
 
 This lemma  follows by the definition of join, *no* algebraic property needed

*)
