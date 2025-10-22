From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Unicode.Utf8.
From Coq Require Import Lia.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.

Require Import VST.msl.sepalg.
Require Import VST.msl.functors.
Require Import VST.msl.sepalg_functors.
Require Import VST.msl.sepalg_generators.

Import CovariantFunctor.
Import CovariantFunctorLemmas.
Import CovariantFunctorGenerator.

Inductive mult : Type :=
| zero : mult (* used *)
| one : mult. (* available linearly *)

Inductive mult_op : mult -> mult -> mult -> Prop:=
| m_00 : mult_op zero zero zero
| m_10 : mult_op one zero one
| m_01 : mult_op zero one one.

Notation "c == a • b" := (mult_op a b c) (at level 50, left associativity).

Instance Join_mult : Join mult := mult_op.

Variant hal : mult → Prop :=
| halz : hal zero.

(*
Lemma mult_eq_dec : forall (X Y : mult), {X = Y} + {X <> Y}.
Proof.
  decide equality.
Qed.
*)

(* Monoidal properties*)
Lemma mult_unit : forall a, exists u, mult_op u a a.
Proof.
  intros. destruct a; hauto l: on .
Qed.

Lemma mult_hal_unit : forall {a b c : mult}, mult_op a b c -> hal a -> b = c.
Proof.
  sauto.
Qed.

(* Property mult_hal_unit2 : forall a, hal a -> forall b, mult_op a b b.
Proof. sauto. Qed. *)

Lemma mult_op_comm: forall (a b c : mult), mult_op a b c -> mult_op b a c.
Proof.
  sauto lq: on.
  (* intros. destruct a; destruct b; reflexivity. *)
Qed.

Lemma mult_func : forall α₁ α₂ α α', mult_op α₁ α₂ α → mult_op α₁ α₂ α' → α = α'.
  sauto lq: on.
Qed.

Lemma mult_canc : forall α₁ α₂ α α₂', mult_op α₁ α₂ α → mult_op α₁ α₂' α → α₂ = α₂'.
  sauto lq: on.
Qed.

Instance mult_Canc_alg : @Canc_alg mult mult_op.
  unfold Canc_alg.
  sauto lq: on.
Qed.

Lemma mult_op_assoc: forall a b c d e,
  mult_op a b d -> mult_op d c e ->
  exists f, mult_op b c f /\ mult_op a f e.
Proof.
  intros a b c d e H1 H2.
  inversion H1; subst; inversion H2; subst; eauto using mult_op.
Qed.

Lemma join_positivity: forall a a' b b', mult_op a a' b -> mult_op b b' a -> a = b.
Proof.
  sauto lq: on .
Qed.

Lemma mult_op_assoc' : forall a b c d e,
  mult_op a b d -> mult_op d c e ->
  {f : mult & mult_op b c f /\ mult_op a f e}.
Proof.
  intros a b c d e H1 H2;
  destruct a, b, c, d, e;
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

(*
Class Perm_alg (t: Type) {J: Join t} : Type :=
  mkPerm   {
   join_eq: forall {x y z z'}, join x y z -> join x y z' -> z = z';
   join_assoc: forall {a b c d e}, join a b d -> join d c e ->
                    {f : t & join b c f /\ join a f e};
   join_comm: forall {a b c}, join a b c -> join b a c;
   join_positivity: forall {a a' b b'}, join a a' b -> join b b' a -> a=b
}.
*)

Instance Perm_alg_mult : Perm_alg mult :=
  @mkPerm mult Join_mult
    mult_func        (* join_eq *)
    mult_op_assoc'   (* join_assoc *)
    mult_op_comm     (* join_comm *)
    join_positivity. (* join_positivity *)

(* Proving mult is a Sep Algebra, not that
we need it*)

(* unit property for sep alg, see Dockins*)
Lemma mult_unit_sep: exists u, forall a, mult_op u a a.
Proof.
  exists zero. intros. destruct a; hauto l: on .
Qed.

Lemma mult_unit_sep_unique: exists ! u, forall a, mult_op u a a.
Proof.
  sauto lq: on use: mult_canc.
Qed.

Definition mult_op_sub (a c : mult) : Prop :=
    exists b, mult_op a b c.
Notation "a ⊑ c" := (mult_op_sub a c) (at level 70, no associativity).

Definition mcore (m : mult) : mult :=
  match m with
  | zero => zero
  | one => zero
  end.

Lemma mcore_unit: forall t, unit_for (mcore t) t.
Proof.
  intros [|]; constructor.
  (* sauto l: on.*)
Qed.

Lemma join_mcore_sub: forall (a b c : mult), mult_op a b c -> mult_op_sub (mcore a) (mcore c).
Proof.
  sauto lq: on .
Qed.

Lemma mcore_idem : forall a, mcore (mcore a) = mcore a.
Proof.
  intros [|];reflexivity.
Qed.

(*
  Class Sep_alg A {J: Join A} : Type :=
    {
      core: A -> A;
      core_unit: forall t, unit_for (core t) t;
      (* weaker core axioms *)
      join_core_sub: forall {a b c}, join a b c -> join_sub (core a) (core c);
      core_idem : forall a, core (core a) = core a
    }.
*)

Instance mult_Sep_alg : Sep_alg mult :=
  {
    core := mcore;
    core_unit := mcore_unit;
    join_core_sub := join_mcore_sub;
    core_idem := mcore_idem
  }.