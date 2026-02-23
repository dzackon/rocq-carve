(* ======================================================= *)
(* Let elimination for a general substructural λ-calculus  *)
(* ======================================================= *)

From Autosubst Require Import fintype stlc_let.
From VST Require Import sepalg.
From CARVe Require Import total_fun genv resalg.

Section GenLetElim.
Variable A : Type.
Variable JA : Join A.
Variable PA : Perm_alg A.
Variable SA : Sep_alg A.
Variable RA : Res_alg A.

(* Contexts and extended typing judgment *)

Definition tenv n := @genv ty A n.

Inductive has_type {n} (Δ : tenv n) : tm n -> ty * A -> Prop :=

| t_Var :
    forall (T : ty) (fn : fin n) (m : A),
      nonzero m ->
      lookup Δ fn = (T, m) ->
      ctx_forall hasW (upd Δ fn (T, core m)) ->
      (hasC m -> ctx_forall hasC Δ) ->
      has_type Δ (var fn) (T, m)

| t_Abs :
    forall (T1 T2 : ty) (e1 : tm (S n)) (m : A),
      has_type (scons (T2, m) Δ) e1 (T1, m) ->
      has_type Δ (lam T2 e1) (Fun T2 T1, m)

| t_App :
    forall (Δ1 Δ2 : tenv n) (T1 T2 : ty) (e1 e2 : tm n) (m : A),
      has_type Δ1 e1 (Fun T2 T1, m) ->
      has_type Δ2 e2 (T2, m) ->
      join Δ1 Δ2 Δ ->
      (hasC m -> ctx_forall hasC Δ2) ->
      has_type Δ (app e1 e2) (T1, m)

| t_Let :
    forall (Δ1 Δ2 : tenv n) (T1 T2 : ty) (e1 : tm n) (e2 : tm (S n)) (m : A),
      has_type Δ1 e1 (T1, m) ->
      has_type (scons (T1, m) Δ2) e2 (T2, m) ->
      join Δ1 Δ2 Δ ->
      (hasC m -> ctx_forall hasC Δ1) ->
      has_type Δ (letin T1 e1 e2) (T2, m).

(* Let-elimination *)

Fixpoint let_elim {n} (e : tm n) : tm n :=
  match e with
  | var x         => var x
  | lam T e1      => lam T (let_elim e1)
  | app e1 e2     => app (let_elim e1) (let_elim e2)
  | letin T e1 e2 => app (lam T (let_elim e2)) (let_elim e1)
  end.

Theorem let_elim_preserves_typing {n} (Δ : tenv n) (e : tm n) (T : ty) (a : A) :
  has_type Δ e (T, a) <->
  has_type Δ (let_elim e) (T, a).
Proof.
  split.
  - induction 1; repeat (econstructor; eauto).
  - revert T; induction e; intros ? Hty; inversion Hty.
    4: inversion H3. all: econstructor; eauto.
Qed.

End GenLetElim.