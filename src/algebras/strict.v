(** Relevant (strict) resource algebra *)

From Hammer Require Import Tactics.
From VST Require Import sepalg.
From CARVe Require Import resalg.

Local Obligation Tactic := try sauto.

Inductive mult : Type :=
| zero : mult
| one  : mult.

(** Join operation *)
Inductive mult_op : mult -> mult -> mult -> Prop :=
| m_00 : mult_op zero zero zero
| m_10 : mult_op one zero one
| m_01 : mult_op zero one one
| m_11 : mult_op one one one.
Notation "a • b == c" := (mult_op a b c) (at level 50, left associativity).

#[global] Instance Join_mult : Join mult := mult_op.

(** Algebraic structure *)

Property mult_op_comm : forall a b c,
  mult_op a b c -> mult_op b a c.
Proof. intros; inversion H; constructor. Qed.

Property mult_op_assoc' : forall a b c d e,
  mult_op a b d -> mult_op d c e ->
  {f : mult & mult_op b c f /\ mult_op a f e}.
Proof.
  intros a b c d e ? ?; destruct a, b, c, d, e;
    try match goal with
      | [ H : mult_op zero one zero |- _ ] => assert (~ mult_op zero one zero); [ unfold not; intro X; inversion X; auto | intuition]
      | [ H : mult_op one zero zero |- _ ] => assert (~ mult_op one zero zero); [ unfold not; intro X; inversion X; auto | intuition]
      | [ H : mult_op zero zero one |- _ ] => assert (~ mult_op zero zero one); [ unfold not; intro X; inversion X; auto | intuition]
      | [ H : mult_op one one zero |- _ ] => assert (~ mult_op one one zero); [ unfold not; intro X; inversion X; auto | intuition]
      | [ |- {f : mult & mult_op zero zero f /\ mult_op zero f zero } ] => eexists; exact (conj m_00 m_00)
      | [ |- {f : mult & mult_op zero zero f /\ mult_op one f one } ] => eexists; exact (conj m_00 m_10)
      | [ |- {f : mult & mult_op zero one f /\ mult_op zero f one } ] => eexists; exact (conj m_01 m_01)
      | [ |- {f : mult & mult_op one zero f /\ mult_op zero f one } ] => eexists; exact (conj m_10 m_01)
      | [ |- {f : mult & mult_op zero one f /\ mult_op one f one } ] => eexists; exact (conj m_01 m_11)
      | [ |- {f : mult & mult_op one zero f /\ mult_op one f one } ] => eexists; exact (conj m_10 m_11)
      | [ |- {f : mult & mult_op one one f /\ mult_op one f one } ] => eexists; exact (conj m_11 m_11)
      | [ |- {f : mult & mult_op one one f /\ mult_op zero f one } ] => eexists; exact (conj m_11 m_01)
      end.
Qed.

#[global] Program Instance Perm_alg_mult : Perm_alg mult :=
  { join_assoc := mult_op_assoc'; join_comm := mult_op_comm }.

#[global] Program Instance mult_Sep_alg : Sep_alg mult :=
  { core := fun m => match m with zero => zero | one => zero end }.

#[global] Program Instance mult_Flat_alg : Flat_alg mult.

(** Resource algebra structure *)

#[global] Program Instance LinearRes_alg : Res_alg mult :=
  { hasW := fun m => m = zero; (* i.e., hal *)
    hasC := fun _ => True; }.
Next Obligation. destruct a. reflexivity. intro H; discriminate (H zero one m_10). Qed.

#[global] Instance LinearIdRes_alg : IdRes_alg mult.
Proof. constructor; intros ? ? ? ? ?; sauto q: on. Defined. 