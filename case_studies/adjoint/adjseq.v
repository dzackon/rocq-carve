(* ======================================================= *)
(* Adjoint sequent calculus                                *)
(* ======================================================= *)

From Stdlib Require Import Arith.PeanoNat List Sorting.Permutation.
From VST Require Import sepalg.
From CARVe Require Import list adjoint.
Set Implicit Arguments.

Section AdjointSeq.
Variable A : Type.
Variable JA : Join A.
Variable PA : Perm_alg A.
Variable SA : Sep_alg A.
Variable MS : ModeStructure A.

(* Types *)

Inductive ty : Type :=
| ty_atom : nat -> ty
| ty_tensor : ty -> ty -> ty
| ty_lolli : ty -> ty -> ty
| ty_one : ty
| ty_zero : ty
| ty_true : ty
| ty_with : ty -> ty -> ty
| ty_plus : ty -> ty -> ty
| ty_up : A -> A -> ty -> ty
| ty_down : A -> A -> ty -> ty.

(* Notations for readability *)
Notation "'𝟙'" := ty_one (at level 0).
Notation "'𝟘'" := ty_zero (at level 0).
Notation "'⊤'" := ty_true (at level 0).
Notation "A ⊗ B" := (ty_tensor A B) (at level 40).
Notation "A ⊸ B" := (ty_lolli A B) (at level 51, right associativity).
Notation "A & B" := (ty_with A B) (at level 42).
Notation "A ⊕ B" := (ty_plus A B) (at level 43).
Notation "'↑[' m ',' k ']' A" := (ty_up m k A) (at level 30).
Notation "'↓[' m ',' k ']' A" := (ty_down m k A) (at level 30).

(* Contexts *)

Definition ctx := @lctx ty A.

Definition ctx_has_prop (Δ : ctx) (p : struct_prop) : Prop :=
  forall n x, lookup Δ n = Some x -> p ∈ σ (snd x).
Notation "p ∈ᶜ Δ" := (ctx_has_prop Δ p) (at level 70).

Definition ctx_ge (Δ : ctx) (k : A) : Prop :=
  forall n x, lookup Δ n = Some x -> snd x ⩾ k.
Notation "Δ ⩾ᶜ k" := (ctx_ge Δ k) (at level 70).

(* x appears in Δ at n, and Δ' is either the result of 'using' it or, if C ∈ σ m, leaving it as is *)
(* Remark 1: if σ m = {W, C} and hence (core m) = m, then `consume` and `retain` are equivalent *)
(* Remark 2: We keep this relational, since it is non-deterministic *)
Inductive opt_use : ctx -> nat -> (ty * A) -> ctx -> Prop :=
| consume {Δ Δ' A m n} : upd_rel Δ n (A, m) (A, core m) Δ' -> opt_use Δ n (A, m) Δ'
| retain {Δ x n} : lookup Δ n = Some x -> C ∈ σ (snd x) -> opt_use Δ n x Δ.

(* Typing judgment *)

(* Remark: we include `nonzero` conditions in each left rule to enforce that zero-moded
  assumptions cannot be used. *)
(* Remark: Some additional assumptions added to enforce independence (indicated by †) *)
Inductive has_type : ctx -> (ty * A) -> Prop :=
| ht_id {Δ A m n} :
  Δ ⩾ᶜ m -> (* † *)
  nonzero m ->
  lookup Δ n = Some (A, m) ->
  W ∈ᶜ (upd Δ n (A, core m)) ->
  has_type Δ (A, m)

| ht_lolli_R {Δ m A B} :
  has_type ((A, m) :: Δ) (B, m) ->
  has_type Δ (A ⊸ B, m)

| ht_lolli_L {Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₁₂' Δ₂₃ Δ₂₃' Δ n m k A₁ A₂ B} :
  Δ₁ ⩾ᶜ m -> Δ₂ ⩾ᶜ m -> C ∈ᶜ Δ₂ ->
  nonzero m ->
  opt_use Δ₁₂ n (A₁ ⊸ A₂, m) Δ₁₂' ->
  opt_use Δ₂₃ n (A₁ ⊸ A₂, m) Δ₂₃' ->
  has_type Δ₁₂' (A₁, m) ->
  has_type ((A₂, m) :: Δ₂₃') (B, k) ->
  join Δ₁ Δ₂ Δ₁₂ -> join Δ₂ Δ₃ Δ₂₃ ->
  join Δ₁₂ Δ₃ Δ -> (* obtain `join Δ₁ Δ₂₃ Δ` from associativity *)
  has_type Δ (B, k)

| ht_tensor_R {Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₂₃ Δ m A B} :
  C ∈ᶜ Δ₂ ->
  has_type Δ₁₂ (A, m) ->
  has_type Δ₂₃ (B, m) ->
  join Δ₁ Δ₂ Δ₁₂ -> join Δ₂ Δ₃ Δ₂₃ -> join Δ₁₂ Δ₃ Δ -> (* ditto *)
  has_type Δ (A ⊗ B, m)

| ht_tensor_L {Δ Δ' n m k A₁ A₂ B} :
  nonzero m ->
  opt_use Δ n (A₁ ⊗ A₂, m) Δ' ->
  has_type ((A₂, m) :: ((A₁, m) :: Δ')) (B, k) ->
  has_type Δ (B, k)

| ht_plus_R1 {Δ m A B} :
  has_type Δ (A, m) ->
  has_type Δ (A ⊕ B, m)

| ht_plus_R2 {Δ m A B} :
  has_type Δ (B, m) ->
  has_type Δ (A ⊕ B, m)

| ht_plus_L {Δ Δ' n m k A₁ A₂ B} :
  nonzero m ->
  opt_use Δ n (A₁ ⊕ A₂, m) Δ' ->
  has_type ((A₁, m) :: Δ') (B, k) ->
  has_type ((A₂, m) :: Δ') (B, k) ->
  has_type Δ (B, k)

| ht_with_R {Δ m A B} :
  has_type Δ (A, m) ->
  has_type Δ (B, m) ->
  has_type Δ (A & B, m)

| ht_with_L1 {Δ Δ' n m k A₁ A₂ B} :
  nonzero m ->
  opt_use Δ n (A₁ & A₂, m) Δ' ->
  has_type ((A₁, m) :: Δ') (B, k) ->
  has_type Δ (B, k)

| ht_with_L2 {Δ Δ' n m k A₁ A₂ B} :
  nonzero m ->
  opt_use Δ n (A₁ & A₂, m) Δ' ->
  has_type ((A₂, m) :: Δ') (B, k) ->
  has_type Δ (B, k)

| ht_one_R {Δ m} :
  Δ ⩾ᶜ m -> (* † *)
  W ∈ᶜ Δ ->
  has_type Δ (ty_one, m)

| ht_one_L {Δ Δ' n m k B} :
  m ⩾ k -> (* † *)
  nonzero m ->
  opt_use Δ n (ty_one, m) Δ' ->
  has_type Δ' (B, m) ->
  has_type Δ (B, k)

| ht_zero_L {Δ m k B} :
  Δ ⩾ᶜ k -> (* † *)
  nonzero m ->
  In (ty_zero, m) Δ ->
  has_type Δ (B, k)

| ht_true_R Δ k :
  Δ ⩾ᶜ k -> (* † *)
  has_type Δ (ty_true, k)

| ht_down_R {Δ₁ Δ₂ Δ m k A} :
  m ⩾ k ->
  Δ₁ ⩾ᶜ m -> W ∈ᶜ Δ₂ ->
  Δ₂ ⩾ᶜ k -> (* † *)
  has_type Δ₁ (A, m) ->
  join Δ₁ Δ₂ Δ ->
  has_type Δ (ty_down m k A, k)

| ht_down_L {Δ Δ' n m k l A B} :
  m ⩾ k -> k ⩾ l -> (* † *)
  nonzero m ->
  opt_use Δ n (ty_down m k A, k) Δ' ->
  has_type ((A, m) :: Δ') (B, l) ->
  has_type Δ (B, l)

| ht_up_R {Δ m k A} :
  k ⩾ m ->
  Δ ⩾ᶜ m -> (* † *)
  has_type Δ (A, k) ->
  has_type Δ (ty_up k m A, m)

| ht_up_L {Δ Δ' n m k l A B} :
  k ⩾ m -> m ⩾ l -> (* † *)
  nonzero k ->
  opt_use Δ n (ty_up k m A, m) Δ' ->
  has_type ((A, k) :: Δ') (B, l) ->
  has_type Δ (B, l).

End AdjointSeq.