(** Purely structural resource algebra
    Represents unrestricted/structural resources using the trivial monoid on unit *)

From VST Require Import sepalg sepalg_generators.
From Hammer Require Import Tactics.
From CARVe Require Import resalg.

(** The only multiplicity: unit (omega/unrestricted) *)
Definition mult : Type := unit.

(** `mult` is a separation algebra *)

#[global] Instance Join_mult : Join mult := Join_unit.
#[global] Instance Canc_mult : Canc_alg mult := Canc_unit.
#[global] Instance Perm_mult : Perm_alg mult := Perm_unit.
#[global] Instance Disj_mult : Disj_alg mult := Disj_unit.

#[global] Instance Sep_mult : Sep_alg mult.
Proof. exists (fun _ => tt); auto with *. Defined.

#[global] Instance Flat_mult : Flat_alg mult.
Proof. constructor. intros []. reflexivity. Defined.

(** Resource algebra instance *)

Local Obligation Tactic := sauto.
#[global] Program Instance StructuralRes_alg : Res_alg mult :=
  { hasW := fun _ => True;
    hasC := fun _ => True; }.

#[global] Instance StructuralIdRes_alg : IdRes_alg mult.
Proof. constructor; intros ? ? ? ? ?; sauto lq: on rew: off. Defined.