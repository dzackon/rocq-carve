(* ======================================================= *)
(* Adjoint natural deduction calculus                      *)
(* ======================================================= *)

From Autosubst Require Import ARS fintype adjnd.
From VST Require Import sepalg.
From CARVe Require Import total_fun genv adjoint.
Import ScopedNotations.

Section AdjointND.
Variable A : Type.
Variable JA : Join A.
Variable MS : ModeStructure A.

(* Contexts *)

Definition tenv := @genv (@ty A) A.

Definition ctx_has_prop {n} (Δ : tenv n) (P : struct_prop) : Prop :=
  ctx_forall (fun m => P ∈ σ m) Δ.
Notation "P ∈ᶜ Δ" := (ctx_has_prop Δ P) (at level 70).

Definition ctx_ge {n} (Δ : tenv n) (k : A) : Prop :=
  ctx_forall (fun m => m ⩾ k) Δ.
Notation "Δ ⩾ᶜ k" := (ctx_ge Δ k) (at level 70).

(* Typing judgment *)

Inductive has_type {SA : Sep_alg A} {n} (Δ : tenv n) : tm n -> (ty * A) -> Prop :=

| ht_hyp {x T m} :
  Δ ⩾ᶜ m -> (* for independence to hold *)
  nonzero m -> (* to ensure 0-moded propositions unprovable *)
  lookup Δ x = (T, m) ->
  W ∈ᶜ upd Δ x (T, core m) -> (* equiv.: exh (upd Δ x (T, core m)) *)
  has_type Δ (var x) (T, m)

| ht_lolli_I {e T1 T2 m} :
  has_type ((T1, m) .: Δ) e (T2, m) ->
  has_type Δ (lam T1 e) (T1 ⊸ T2, m)

| ht_lolli_E {Δ1 Δ2 e1 e2 T1 T2 m} :
  has_type Δ1 e1 (T1 ⊸ T2, m) ->
  has_type Δ2 e2 (T1, m) ->
  join Δ1 Δ2 Δ ->
  has_type Δ (app e1 e2) (T2, m)

| ht_up_I {e T m k} :
  Δ ⩾ᶜ m -> m ⩾ k -> (* for independence to hold *) (* m ⩾ k implicit on paper *)
  nonzero m -> (* to ensure 0-moded propositions unprovable *)
  has_type Δ e (T, k) ->
  has_type Δ (lift k m e) (ty_up k m T, m)

| ht_up_E {Δ1 Δ2 e T m k} :
  Δ1 ⩾ᶜ k -> (* for independence to hold *)
  Δ2 ⩾ᶜ m -> m ⩾ k -> (* m ⩾ k implicit on paper *)
  nonzero k -> (* to ensure 0-moded propositions unprovable *)
  W ∈ᶜ Δ1 -> (* equiv.: exh Δ1 *)
  has_type Δ2 e (ty_up k m T, m) ->
  join Δ1 Δ2 Δ ->
  has_type Δ (unlift k m e) (T, k)

| ht_down_I {Δ1 Δ2 e T m k} :
  Δ1 ⩾ᶜ k -> (* for independence to hold *) (* m? *)
  Δ2 ⩾ᶜ m -> m ⩾ k -> (* m ⩾ k implicit on paper *)
  nonzero k -> (* to ensure 0-moded propositions unprovable *)
  W ∈ᶜ Δ1 -> (* equiv.: exh Δ1 *)
  has_type Δ2 e (T, m) ->
  join Δ1 Δ2 Δ ->
  has_type Δ (drop m k e) (ty_down m k T, k)

| ht_down_E {Δ1 Δ2 s e T C m k r} :
  Δ1 ⩾ᶜ k -> k ⩾ r ->
  m ⩾ k -> (* m ⩾ k implicit on paper *)
  has_type Δ1 s (ty_down m k T, k) ->
  has_type ((T, m) .: Δ2) e (C, r) ->
  join Δ1 Δ2 Δ ->
  has_type Δ (letdrop m s e) (C, r).

(* Dynamics *)

(** Single-step reduction *)

Inductive step {n} : @tm A n -> tm n -> Prop :=
(* β-rules *)
| step_beta_lolli T e e' : step (app (lam T e) e') e[e'..]
| step_beta_up e m k : step (unlift m k (lift m k e)) e
| step_beta_down e e' m k : step (letdrop m (drop m k e) e') e'[e..]
(* congruence rules *)
| step_abs T e e' : step e e' -> step (lam T e) (lam T e')
| step_app_l e1 e1' e2 : step e1 e1' -> step (app e1 e2) (app e1' e2)
| step_app_r e1 e2 e2' : step e2 e2' -> step (app e1 e2) (app e1 e2')
| step_lift m k e e' : step e e' -> step (lift m k e) (lift m k e')
| step_unlift m k e e' : step e e' -> step (unlift m k e) (unlift m k e')
| step_drop m k e e' : step e e' -> step (drop m k e) (drop m k e')
| step_letdrop_s m s s' e : step s s' -> step (letdrop m s e) (letdrop m s' e)
| step_letdrop_e m s e e' : step e e' ->  step (letdrop m s e) (letdrop m s e').

Fixpoint value {n} (e : @tm A n) : Prop :=
  match e with
  | lam _ _ => True
  | lift _ _ _ => True
  | drop _ _ e' => value e'
  | _ => False
  end.

End AdjointND.

Global Arguments tenv {A}.
Global Arguments has_type {A JA MS SA n}.
Global Arguments step {A n}.
Global Arguments value {A n}.
Global Arguments ctx_ge {A JA MS n}.
Global Arguments ctx_has_prop {A JA MS n}.
Global Notation "Δ '⊢' e ':' p" := (has_type Δ e p) (at level 40).
Global Notation "P ∈ᶜ Δ" := (ctx_has_prop Δ P) (at level 70).
Global Notation "Δ ⩾ᶜ k" := (ctx_ge Δ k) (at level 70).