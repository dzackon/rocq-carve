(** This file contains an algebra for structural contexts, where the
algebra is given by the trivial monoid on unit. *)

From Coq Require Import Unicode.Utf8.

Require Import VST.msl.sepalg.
Require Import VST.msl.sepalg_generators.

Definition mult : Type := unit.

  Variant hal : mult → Prop :=
  | halo : hal tt.

  Instance Join_mult : Join mult := Join_unit.
  Instance Canc_mult : Canc_alg mult := Canc_unit.
  Instance Perm_mult : Perm_alg mult := Perm_unit.
  Instance Sep_mult : Sep_alg mult.
  exists (fun _ => tt); auto with *.

Defined.