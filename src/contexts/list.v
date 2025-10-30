(**
  We reuse the VST/MSL functor and separation algebra machinery to
  encode CARVe. The aim is to show that our contexts of resources and
  use annotations, modelled by

    list (R * A),

  inherit the algebraic structure of A. To do so, we show that

    list (R * -)

  is a functor from (permission, resource, separation, etc.) algebras to
  (permission, resource, separation, etc.) algebras. Contexts then get for
  free properties like commutativity, associativity, cancellativity, etc.
**)

From Coq Require Import List.
Import List.ListNotations.

Require Import Coq.Program.Equality.

Require Import VST.msl.sepalg.
Require Import VST.msl.functors.
Require Import VST.msl.sepalg_functors.
Require Import VST.msl.sepalg_generators.

Import CovariantFunctor.
Import CovariantFunctorLemmas.
Import CovariantFunctorGenerator.

From Hammer Require Import Tactics.

Section ListCtx.

  Variable R : Type. (* Resources *)
  Variable A : Type. (* Resource Algebra *)
  Variable JA : Join A.
  Variable CA : Canc_alg A.
  Variable PA : Perm_alg A.
  Variable SA : Sep_alg A.

  (* Functor from permission algebras A to contexts of resources of
    type R, i.e., to list (R * A). *)
  Definition lctx : Type := list (R * A).

  #[global] Instance Join_lctx : Join lctx :=
    Join_list _ (Join_prod _ (Join_equiv _) _ JA).

  #[global] Instance Perm_alg_lctx : Perm_alg lctx.
  Proof.
    sauto use: Perm_list, Perm_prod, Perm_equiv.
  Qed.

  #[global] Instance Canc_alg_lctx : Canc_alg lctx.
  Proof.
    intros; apply Canc_list, Canc_prod; [ apply Canc_equiv | auto ].
  Qed.

  #[global] Instance Sep_alg_lctx : Sep_alg lctx.
  Proof.
    intros; apply Sep_list, Sep_prod; sauto.
  Qed.

End ListCtx.

(**
  As a sanity check, we give an inductive characterization of lctx,
  and show that it has the same action on the join relation. We should
  not directly use this definition in any future developments, but
  instead should use JoinFunctor_lctx applied to the resource algebra we are
  annotating contexts with.
**)

Inductive merge {R A: Type} {join: Join A} : Join (lctx R A) :=
| mg_n : merge [] [] []
| mg_c r {Δ₁ Δ₂ Δ α₁ α₂ α} :
    join α₁ α₂ α ->
    merge Δ₁ Δ₂ Δ ->
    merge ((r, α₁) :: Δ₁) ((r, α₂) :: Δ₂) ((r, α) :: Δ).

Proposition merge_is_JoinFunctor_lctx
  {A R: Type} {JA: Join A} {L1 L2 L3 : list (R * A)}:
    merge L1 L2 L3 <-> join L1 L2 L3.
Proof.
  split; intro H; induction H; sauto.
Qed.

(* Property merge_comm'
  {R A : Type} {JA : Join A} {PA : Perm_alg A} {SA : Sep_alg A} {Δ₁ Δ₂ Δ : lctx R A} :
    merge Δ₁ Δ₂ Δ -> merge Δ₂ Δ₁ Δ.
Proof.
  intros. 
  apply merge_is_JoinFunctor_lctx.
  eapply (@join_comm (lctx R A)).
  eapply (Perm_alg_lctx R A); assumption.
  apply merge_is_JoinFunctor_lctx; assumption.
Qed. *)

(* get 'for free'? *)
Property merge_comm
  {R A : Type} {join: Join A} {Δ₁ Δ₂ Δ : lctx R A} :
    merge Δ₁ Δ₂ Δ -> merge Δ₂ Δ₁ Δ.
Admitted.

(* get 'for free'? *)
Property merge_assoc
  {R A : Type} {join: Join A} {Δ₁ Δ₂ Δ₃ Δ₁₂ Δ : lctx R A} :
    merge Δ₁ Δ₂ Δ₁₂ -> merge Δ₁₂ Δ₃ Δ ->
      exists (Δ₂₃ : lctx R A),
        merge Δ₂ Δ₃ Δ₂₃ /\ merge Δ₁ Δ₂₃ Δ.
Admitted.

Corollary merge_assoc2
  {R A : Type} {join: Join A} {Δ₁ Δ₂ Δ₃ Δ₁₂ Δ : lctx R A} :
    merge Δ₁ Δ₂ Δ₁₂ -> merge Δ₁₂ Δ₃ Δ ->
      exists (Δ₁₃ : lctx R A),
        merge Δ₁ Δ₃ Δ₁₃ /\ merge Δ₁₃ Δ₂ Δ.
Proof.
  intros μ1 μ2.
  destruct (merge_assoc (merge_comm μ1) μ2) as [Δ₁₃ [μ3 μ4]].
  exists Δ₁₃. split; [ | apply merge_comm]; assumption.
Qed.

Inductive exh {R A: Type} (hal : A -> Prop) : lctx R A -> Prop :=
| exh_n : exh hal []
| exh_c : forall {Δ : lctx R A} (X : R) {α : A},
    exh hal Δ -> hal α -> exh hal ((X, α) :: Δ).

(* Not sure that we need lctx_exh, but as an experiment, we can write
exh as a functional program. *)
Definition lctx_exh {R A : Type} (hal : A -> Prop) : lctx R A -> Prop :=
  fold_right (fun ra p => and (hal (snd ra)) p) True.

Lemma exh_lctx_exh :
  forall R A hal (ctx : lctx R A),
    exh hal ctx <-> lctx_exh hal ctx.
Proof.
  intros; split; intro; simpl in ctx.
  + induction H; sfirstorder.
  + induction ctx; hauto.
Qed.

Lemma exh_id  :
  forall {A R} {join : Join A} {hal : A -> Prop} {Δ₁ Δ₂ Δ : lctx R A},
    merge Δ₁ Δ₂ Δ ->
    exh hal Δ₁ ->
    (forall a b c : A, join a b c -> hal a -> b = c) ->
    Δ₂ = Δ.
Proof.
  intros. induction H; sauto.
Qed.

Inductive updn {R A : Type} :
  lctx R A -> nat -> R -> R -> A -> A -> lctx R A -> Prop :=
| updn_t : forall (Δ : lctx R A) (X X' : R) (α α' : A),
    updn ((X, α) :: Δ) 0 X X' α α' ((X', α') :: Δ)
| updn_n : forall (Δ Δ' : lctx R A) (n : nat) (X X' Y : R) (α α' β : A),
    updn Δ n X X' α α' Δ' ->
    updn ((Y, β) :: Δ) (S n) X X' α α' ((Y, β) :: Δ').

(* w/o index *)
Inductive upd {R A : Type}:
  lctx R A -> R -> R -> A -> A -> lctx R A -> Prop :=
| upd_t : forall (Δ : lctx R A) (X X' : R) (α α' : A),
    upd ((X, α) :: Δ) X X' α α' ((X', α') :: Δ)
| upd_n : forall (Δ Δ' : lctx R A) (X X' Y : R) (α α' β : A),
    upd Δ X X' α α' Δ' ->
    upd ((Y, β) :: Δ) X X' α α' ((Y, β) :: Δ').

Property upd_exh_inv
  {R A : Type} {hal : A -> Prop} {t s s' : R} {Δ Δ' α α'} :
    upd ((t, α) :: Δ) s s' α α' Δ' ->
    exh hal Δ' ->
    ~ hal α -> hal α' ->
    (s = t) /\ (Δ' = (s', α') :: Δ).
Proof.
  sauto.
Qed.