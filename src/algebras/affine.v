From Coq Require Import List Program.Equality Unicode.Utf8.
From Hammer Require Import Tactics.
From VST.msl Require Import sepalg.

Inductive mult : Type :=
| zero : mult  (* used *)
| one  : mult. (* available at most once *)

Inductive mult_op : mult -> mult -> mult -> Prop :=
| m_00 : mult_op zero zero zero
| m_10 : mult_op one zero one
| m_01 : mult_op zero one one.

Notation "c == a • b" := (mult_op a b c) (at level 50, left associativity).

Instance Join_mult : Join mult := mult_op.

Variant hal : mult → Prop :=
| halz : hal zero
| halo : hal one.

Lemma mult_eq_dec : forall (X Y : mult), {X = Y} + {X <> Y}.
Proof. decide equality. Qed.

(* Monoidal properties *)
(* Remark: `mult_hal_unit` does not hold, since not all harmless elements are unit *)

Lemma mult_unit : forall a, exists u, mult_op u a a.
Proof. intros. destruct a; hauto l: on . Qed.

Lemma mult_op_comm : forall (a b c : mult), mult_op a b c -> mult_op b a c.
Proof. sauto lq: on. Qed.

Lemma mult_func : forall α₁ α₂ α α', mult_op α₁ α₂ α → mult_op α₁ α₂ α' → α = α'.
Proof. sauto lq: on. Qed.

Lemma mult_canc : forall α₁ α₂ α α₂', mult_op α₁ α₂ α → mult_op α₁ α₂' α → α₂ = α₂'.
Proof. sauto lq: on. Qed.

Instance mult_Canc_alg : @Canc_alg mult mult_op.
Proof. unfold Canc_alg. sauto lq: on. Qed.

Lemma mult_op_assoc : forall a b c d e,
  mult_op a b d -> mult_op d c e ->
  exists f, mult_op b c f /\ mult_op a f e.
Proof. intros * H1 H2; inversion H1; subst; inversion H2; eauto using mult_op. Qed.

Lemma join_positivity : forall a a' b b', mult_op a a' b -> mult_op b b' a -> a=b.
Proof. sauto lq: on . Qed.

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

Instance Perm_alg_mult : Perm_alg mult :=
  @mkPerm mult Join_mult
    mult_func        (* join_eq *)
    mult_op_assoc'   (* join_assoc *)
    mult_op_comm     (* join_comm *)
    join_positivity. (* join_positivity *)

(* Proving mult is a separation algebra *)

Lemma mult_unit_sep : exists u, forall a, mult_op u a a.
Proof. exists zero. intros. destruct a; hauto l: on . Qed.

Lemma mult_unit_sep_unique : exists ! u, forall a, mult_op u a a.
Proof. sauto lq: on use: mult_canc. Qed.

Definition mult_op_sub (a c : mult) : Prop := exists b, mult_op a b c.
Notation "a ⊑ c" := (mult_op_sub a c) (at level 70, no associativity).

Definition mcore (m : mult) : mult :=
  match m with
  | zero => zero
  | one => zero
  end.

Lemma mcore_unit: forall t, unit_for (mcore t) t.
Proof. intros [|]; constructor. Qed.

Lemma join_mcore_sub: forall (a b c : mult), mult_op a b c -> mult_op_sub (mcore a) (mcore c).
Proof. sauto lq: on . Qed.

Lemma mcore_idem : forall a, mcore (mcore a) = mcore a.
Proof. intros [|]; reflexivity. Qed.

Instance mult_Sep_alg : Sep_alg mult :=
  { core := mcore;
    core_unit := mcore_unit;
    join_core_sub := join_mcore_sub;
    core_idem := mcore_idem }.