(* ================================================== *)
(* Contexts for dual linear-intuitionistic calculus  *)
(* ================================================= *)

(* Library imports *)
Require Import ARS core fintype stlc_ext.
Import ScopedNotations.
From Coq Require Import Unicode.Utf8.
From Coq Require Import Lia.
From Hammer Require Import Hammer.

(* General settings *)
Set Implicit Arguments.

(* ----------------------------------- *)
(* Decidable equality                  *)
(* ----------------------------------- *)

Class EqDec (A : Type) : Type :=
  { eq_dec : forall x y : A, {x = y} + {x <> y} }.

Lemma fin_eq {n} (x y : fin n) : {x = y} + {x <> y}.
Proof.
  induction n; [destruct x | decide equality].
Qed.

(* ----------------------------------- *)
(* Contexts as total maps              *)
(* ----------------------------------- *)

Section TotalFunCtx.
  Variable D : Type. (* Function domain *)
  Variable R : Type. (* Resources *)
  Variable A : Type. (* Resource algebra *)

  Definition tfctx : Type := D → R * A.

  Definition exh (hal : A → Prop) : tfctx → Prop :=
    fun C => forall r, hal (snd (C r)).

  (* Definition empty_tfctx default : tfctx := fun _ => default. *)

  Definition lookup_tfctx : tfctx → D → R * A :=
    fun C x => C x.

  Definition update_tfctx `{EqDec D} : tfctx → D → R → A → tfctx :=
    fun C x r a x' =>
      if eq_dec x x' then (r, a) else C x'.
End TotalFunCtx.

(* -------------------------------------- *)
(* Linear-intuitionistic resource algebra *)
(* -------------------------------------- *)

Inductive mult : Type :=
| Zero  : mult  (* used *)
| One   : mult  (* available linearly *)
| Omega : mult. (* available unrestrictedly *)

Inductive mult_op : mult → mult → mult → Prop :=
| m_00 : mult_op Zero  Zero  Zero
| m_10 : mult_op One   Zero  One
| m_01 : mult_op Zero  One   One
| m_ωω : mult_op Omega Omega Omega.

Variant hal : mult → Prop :=
| halz : hal Zero
| halo : hal Omega.

Notation "a • b == c" := (mult_op a b c) (at level 50, left associativity).

(* ----------------------------------- *)
(* Typing environments                 *)
(* ----------------------------------- *)

Definition tenv n := tfctx (fin n) ty mult.

Definition femptyT (T : ty) : tenv 0 := fun _ => (T, Zero).

(* Remark: equality constraints required to avoid shadowing *)
Definition join {n} (Δ1 Δ2 Δ : tenv n) : Prop :=
  forall x,
    let (t1, m1) := Δ1 x in
    let (t2, m2) := Δ2 x in
    let (t,  m ) := Δ  x in
    t1 = t ∧ t2 = t ∧ mult_op m1 m2 m.

Definition upd {n} (Δ : tenv n) (x : fin n)
  (ty_old ty_new : ty) (m_old m_new : mult) (Δ' : tenv n) : Prop :=
  forall y : fin n,
    if fin_eq x y then
      Δ y = (ty_old, m_old) ∧ Δ' y = (ty_new, m_new)
    else
      Δ y = Δ' y.

(* ----------------------------------- *)
(* Context properties                  *)
(* ----------------------------------- *)

Lemma lookup_upd :
  forall {n} {Δ : tenv n} {x t m},
    Δ x = (t, m) <->
    upd Δ x t t m m Δ.
Proof.
  intros n Δ x t m. split.
  - intros H y.
    destruct (fin_eq x y); subst; auto.
  - intros Hupd. sauto using (Hupd x).
Qed.

(* If Δ₁ ⋈ Δ₂ = Δ, then Δ₂ ⋈ Δ₁ = Δ *)
(* DZ: should get 'for free' from separation algebra *)
Lemma join_comm :
  forall {n} (Δ1 Δ2 Δ : tenv n),
    join Δ1 Δ2 Δ → join Δ2 Δ1 Δ.
Proof.
  intros n Δ1 Δ2 Δ Hjoin x.
  unfold join in *.
  specialize (Hjoin x).
  destruct (Δ1 x) as [t1 m1].
  destruct (Δ2 x) as [t2 m2].
  destruct (Δ x) as [t m].
  destruct Hjoin as [Heq1 [Heq2 Hmult]].
  repeat split; try assumption.
  inversion Hmult; constructor.
Qed.

(* If Δ₁ ⋈ Δ₂ = Δ, then types must match at each input x *)
Lemma join_types_match :
  forall {n} {Δ Δ1 Δ2 : tenv n} (x : fin n),
    join Δ1 Δ2 Δ →
    fst (Δ x) = fst (Δ1 x) ∧ fst (Δ x) = fst (Δ2 x).
Proof.
  intros n Δ Δ1 Δ2 x Hjoin.
  unfold join in Hjoin.
  specialize (Hjoin x).
  destruct (Δ1 x) as [t1 m1].
  destruct (Δ2 x) as [t2 m2].
  destruct (Δ x) as [t m].
  (* From the definition of join, t = t1 and t = t2 *)
  cbn. split; sfirstorder.
Qed.

Definition emptyT := femptyT Unit.

(* ----------------------------------- *)
(* Notation                            *)
(* ----------------------------------- *)

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -o T" := (Fun S T) (in custom stlc at level 50, right associativity).
Notation "x ^ y" := (Core.app x y) (in custom stlc at level 1, left associativity).
Notation "/\ T e" := (lam T e)
                     (in custom stlc at level 90,
                      e custom stlc at level 99, left associativity).