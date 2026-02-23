(* Types and terms for λ-calculus with 'let' constructor *)

From Autosubst Require Import fintype.

Inductive ty : Type :=
  | Unit : ty
  | Fun : ty -> ty -> ty.

Inductive tm (n : nat) : Type :=
  | var : fin n -> tm n
  | app : tm n -> tm n -> tm n
  | lam : ty -> tm (S n) -> tm n
  | letin : ty -> tm n -> tm (S n) -> tm n.

Arguments var {n}.
Arguments app {n}.
Arguments lam {n}.
Arguments letin {n}.