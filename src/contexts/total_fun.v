Require Import VST.msl.sepalg.
Require Import VST.msl.functors.
Require Import VST.msl.sepalg_functors.
Require Import VST.msl.sepalg_generators.

Import CovariantFunctor.
Import CovariantFunctorLemmas.
Import CovariantFunctorGenerator.

From Hammer Require Import Tactics.

(* Decidable equality *)
Class EqDec (A : Type) : Type :=
  {
    eq_dec : forall x y : A, {x = y} + {x <> y}
  }.

Section TotalFunCtx.
  Variable D: Type. (* Function domain *)
  Variable R: Type. (* Resources *)
  Variable A: Type. (* Resource Algebra *)
  Variable JA: Join A.
  Variable CA: Canc_alg A.
  Variable PA: Perm_alg A.
  Variable SA: Sep_alg A.
  #[global] Generalizable All Variables.

  Definition tfctx : Type := (D -> R * A).

  #[global] Instance Join_tfctx : Join tfctx :=
    Join_fun _ _ (Join_prod _ (Join_equiv _) _ JA).

  #[global] Instance Perm_alg_tfctx : Perm_alg tfctx.
  Proof.
    sauto use: Perm_fun, Perm_prod, Perm_equiv.
  Defined.
  #[global] Instance Canc_alg_tfctx : Canc_alg tfctx :=
    Canc_fun _ _ _ (Canc_prod _ (Join_equiv _) _ JA).
  #[global] Instance Sep_alg_tfctx : Sep_alg tfctx.
  Proof.
    sauto use: Sep_fun, Perm_fun, Sep_prod, Perm_prod, Sep_equiv, Perm_equiv.
  Defined.

  Definition exh (hal: A -> Prop): tfctx -> Prop :=
    fun C => forall r, hal (snd (C r)).

  Definition empty_tfctx default : tfctx := fun _ => default.

  Definition lookup_tfctx : tfctx -> D -> R * A :=
    fun C x => C x.

  Definition update_tfctx `{EqDec D} : tfctx -> D -> R -> A -> tfctx :=
    fun C x r a x' => if eq_dec x x' then (r, a) else C x'.
End TotalFunCtx.