(* * DILL Resource Algebra
    Combines linear and structural resources *)

From Stdlib.Logic Require Import Classical_Prop FunctionalExtensionality PropExtensionality.
From Hammer Require Import Tactics.
From VST Require Import sepalg sepalg_generators.
From CARVe Require Import resalg linear structural.

Definition mult : Type := linear.mult + structural.mult.

(** Handy definitions *)
Definition zero  : mult := inl linear.zero.
Definition one   : mult := inl linear.one.
Definition omega : mult := inr tt.

#[global] Instance Join_mult : Join mult :=
  Join_sum _ linear.Join_mult _ structural.Join_mult.

(** Harmless elements: zero and omega *)
Inductive hal : mult -> Prop :=
  | halz : hal zero
  | halo : hal omega.

Property hal_is_identity : hal = identity.
Proof.
  extensionality x; apply propositional_extensionality; split; intro H.
  - inversion H; intros ? ? ?; sauto q: on.
  - destruct x as [lx | sx].
    + destruct lx.
      * constructor.
      * assert (H' : join one zero one) by constructor; discriminate (H _ _ H').
    + destruct sx; constructor.
Qed.

(* The following definition and lemma are an inductive
characterization of the join that MSL generates. These exists solely to
reassure the reader that the framework does the 'right thing'; they
are not meant to be used in proof developments. *)

Inductive mult_op : mult -> mult -> mult -> Prop:=
| m_00 : mult_op zero zero zero
| m_10 : mult_op one zero one
| m_01 : mult_op zero one one
| m_ωω : mult_op omega omega omega.

Property join_is_mult_op : forall {x y z : mult},
  join x y z <-> mult_op x y z.
Proof. sauto. Qed.

(* Useful characterization property *)
Property join_cases {x y z : mult} :
  join x y z ->
  match z with
  | inl linear.zero => x = zero /\ y = zero
  | inl linear.one => (x = one /\ y = zero) \/ (x = zero /\ y = one)
  | inr tt => x = omega /\ y = omega
  end.
Proof. destruct x, y, z; sauto q: on. Qed.

(** Separation algebra structure *)

#[global] Instance mult_Perm_alg : Perm_alg mult :=
  Perm_sum _ _ _ _ linear.Perm_alg_mult structural.Perm_mult.

#[global] Instance mult_Sep_alg : Sep_alg mult.
Proof. unfold mult. typeclasses eauto. Defined.

#[global] Instance mult_Canc_alg : Canc_alg mult.
Proof. unfold mult. typeclasses eauto. Defined.

#[global] Instance mult_Flat_alg : Flat_alg mult.
Proof. constructor; intros. rewrite join_is_mult_op in H; destruct H; constructor. Defined.

(** Resource algebra structure *)

#[global] Program Instance ILLRes_alg : Res_alg mult :=
  { hasW := hal;
    hasC := hal; }.
Next Obligation. destruct a as [[] | []]. 2: specialize (H zero one). all: ecrush. Defined.
Next Obligation. sauto q: on. Defined.
Next Obligation. sauto q: on. Defined.
Next Obligation.
  inversion H.
  - exists a1, a2.
    destruct a12 as [[] | []], a1 as [[] | []], a2 as [[] | []], a as [[] | []];
    try inversion H0; try inversion H1; sfirstorder.
  - exists omega, omega. hauto l: on dep: on.
Defined.
Next Obligation. inversion H0; inversion H1; destruct a as [[] | []]; qblast. Defined.
Next Obligation.
  inversion H as [b H1].
  destruct a1 as [[] | []], b as [[] | []], a as [[] | []]; try reflexivity; try inversion H1.
  apply not_and_or in H0; destruct H0. 2: exfalso; apply H0; exists one. all: sauto lq: on rew: off.
Defined.

#[global] Instance ILLIdRes_alg : IdRes_alg mult.
Proof. constructor. intros. now rewrite <- hal_is_identity. Qed.