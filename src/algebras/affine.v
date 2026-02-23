(** Affine Resource Algebra *)

From Hammer Require Import Tactics.
From VST Require Import sepalg.
From CARVe Require Import resalg.

Local Obligation Tactic := try sauto.

(** The multiplicities: zero (used) and one (available at most once) *)
Inductive mult : Type :=
| zero : mult
| one  : mult.

(** Join operation *)
Inductive mult_op : mult -> mult -> mult -> Prop :=
| m_00 : mult_op zero zero zero
| m_10 : mult_op one zero one
| m_01 : mult_op zero one one.

#[global] Instance Join_mult : Join mult := mult_op.

(** Harmless elements (both zero and one) *)
Definition hal : mult -> Prop := fun _ => True.

(** Permission algebra structure *)

Lemma mult_op_comm : forall a b c,
  mult_op a b c -> mult_op b a c.
Proof. intros; inversion H; constructor. Qed.

Lemma mult_op_assoc' : forall a b c d e,
  mult_op a b d -> mult_op d c e ->
  {f : mult & mult_op b c f /\ mult_op a f e}.
Proof.
  intros a b c d e ? ?; destruct a, b, c, d, e;
    try match goal with
      | [ H : mult_op zero one zero |- _ ] => assert (~ mult_op zero one zero); [ unfold not; intro X; inversion X; auto | intuition]
      | [ H : mult_op one zero zero |- _ ] => assert (~ mult_op one zero zero); [ unfold not; intro X; inversion X; auto | intuition]
      | [ H : mult_op zero zero one |- _ ] => assert (~ mult_op zero zero one); [ unfold not; intro X; inversion X; auto | intuition]
      | [ H : mult_op one one zero |- _ ] => assert (~ mult_op one one zero); [ unfold not; intro X; inversion X; auto | intuition]
      | [ H : mult_op one one one |- _ ] => assert (~ mult_op one one one); [ unfold not; intro X; inversion X; auto | intuition]
      | [ |- {f : mult & mult_op zero zero f /\ mult_op zero f zero } ] => eexists; exact (conj m_00 m_00)
      | [ |- {f : mult & mult_op zero zero f /\ mult_op one f one } ] => eexists; exact (conj m_00 m_10)
      | [ |- {f : mult & mult_op zero one f /\ mult_op zero f one } ] => eexists; exact (conj m_01 m_01)
      | [ |- {f : mult & mult_op one zero f /\ mult_op zero f one } ] => eexists; exact (conj m_10 m_01)
      end.
Qed.

#[global] Program Instance Perm_alg_mult : Perm_alg mult :=
  { join_assoc := mult_op_assoc'; join_comm := mult_op_comm }.

(** Separation algebra structure *)

#[global] Program Instance mult_Sep_alg : Sep_alg mult :=
  { core := fun m => match m with zero => zero | one => zero end }.

#[global] Instance mult_Canc_alg : Canc_alg mult.
Proof. unfold Canc_alg. sauto q: on. Qed.

#[global] Program Instance mult_Flat_alg : Flat_alg mult.

(** Resource algebra instance *)

#[global] Program Instance AffineRes_alg : Res_alg mult :=
  { hasW := fun _ => True; (* i.e., hal *)
    hasC := fun m => m = zero; }.

(** Remark: does NOT satisfy IdentityRes_alg condition *)