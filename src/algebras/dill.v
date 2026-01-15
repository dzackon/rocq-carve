From Hammer Require Import Hammer.
From Coq.Logic Require Import FunctionalExtensionality PropExtensionality.
From VST.msl Require Import sepalg sepalg_generators.
From CARVe.algebras Require Import linear structural.

Definition mult : Type := linear.mult + structural.mult.

(* Handy definitions *)
Definition zero  : mult := inl linear.zero.
Definition one   : mult := inl linear.one.
Definition omega : mult := inr tt.

Instance Join_mult : Join mult :=
  Join_sum _ linear.Join_mult _ structural.Join_mult.

Variant hal : mult -> Prop :=
  | halz : hal zero
  | halo : hal omega.

Property hal_is_identity : hal = identity.
Proof.
  extensionality x; apply propositional_extensionality; split; intro H.
  - inversion H; intros ? ? ?; sauto.
  - destruct x as [lx | sx].
    + destruct lx.
      * constructor.
      * assert (H' : join one zero one) by constructor; discriminate (H _ _ H').
    + destruct sx; constructor.
Qed.

Definition hal_core : mult -> Prop := fun m => m = core m.

Property hal_is_core : hal = hal_core.
Proof. extensionality x; apply propositional_extensionality; sauto. Qed.

Property join_hal {x y z : mult} :
  join x y z -> hal z -> x = z.
Proof. intros; destruct H0; destruct x, y; inversion H; sauto. Qed.

(* Useful characterization property *)
Property join_cases {x y z : mult} :
  join x y z ->
  match z with
  | inl linear.zero => x = zero /\ y = zero
  | inl linear.one => (x = one /\ y = zero) \/ (x = zero /\ y = one)
  | inr tt => x = omega /\ y = omega
  end.
Proof. destruct x, y, z; sauto. Qed.

(* The following definition and lemma are an inductive
characterization of the join that MSL generates. These exists solely to
reassure the reader that the framework does the 'right thing'; they
are not meant to be used in proof developments. *)

Inductive mult_op : mult -> mult -> mult -> Prop:=
| m_00 : mult_op zero zero zero
| m_10 : mult_op one zero one
| m_01 : mult_op zero one one
| m_ωω : mult_op omega omega omega.

Property join_is_mult_op : forall (x y z : mult),
  join x y z <-> mult_op x y z.
Proof. sauto. Qed.

(* Proving mult is a separation algebra *)

Instance mult_Perm_alg : Perm_alg mult :=
  Perm_sum _ _ _ _ linear.Perm_alg_mult structural.Perm_mult.

Instance mult_Sep_alg : Sep_alg mult :=
  Sep_sum _ _ _ _ _ _ linear.mult_Sep_alg structural.Sep_mult.

Instance mult_Flat_alg : Flat_alg mult.
Proof. constructor; intros. rewrite join_is_mult_op in H; destruct H; constructor. Defined.