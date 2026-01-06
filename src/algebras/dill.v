From Hammer Require Import Hammer.
From VST.msl Require Import sepalg sepalg_generators.
From CARVe.algebras Require Import linear structural.

Definition mult : Type := linear.mult + structural.mult.

(* Handy definitions *)
Definition zero  : mult := inl linear.zero.
Definition one   : mult := inl linear.one.
Definition omega : mult := inr tt.

Instance Join_mult : Join mult :=
  Join_sum _ linear.Join_mult _ structural.Join_mult.

(* The following definition and lemma are an inductive
characterization of the join that MSL generates. They exists solely to
reassure the reader that the framework does the right thing, and they
are not meant to be used in proof developments. *)

Inductive mult_op : mult -> mult -> mult -> Prop:=
| m_00 : mult_op zero zero zero
| m_10 : mult_op one zero one
| m_01 : mult_op zero one one
| m_ωω : mult_op omega omega omega.

Lemma join_is_mult_op : forall (x y z : mult),
    join x y z <-> mult_op x y z.
Proof. sauto. Qed.

Instance mult_Perm_alg : Perm_alg mult :=
  Perm_sum _ _ _ _ linear.Perm_alg_mult structural.Perm_mult.

Instance mult_Sep_alg : Sep_alg mult :=
  Sep_sum _ _ _ _ _ _ linear.mult_Sep_alg structural.Sep_mult.

Variant hal : mult -> Prop :=
  | halz : hal zero
  | halo : hal omega.

Definition hal_core : mult -> Prop := fun m => m = (core m).

Lemma hal_is_core : forall x, hal x <-> hal_core x.
Proof. sauto. Qed.