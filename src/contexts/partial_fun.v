From Hammer Require Import Tactics.
From VST.msl Require Import sepalg sepalg_generators.
From CARVe Require Import optalg.

(* Decidable equality *)
Class EqDec (A : Type) : Type :=
  { eq_dec : forall x y : A, {x = y} + {x <> y} }.

Section FunCtx.
  Variable R: Type.
  Variable A: Type. (* Resource algebra *)
  Variable JA: Join A.
  Variable CA: Canc_alg A.
  Variable PA: Perm_alg A.
  Variable SA: Sep_alg A.

  Definition fctx : Type := (R -> option A).

  #[global] Instance Join_fctx : Join fctx :=
    Join_fun _ _ (Join_opt _ JA).

  (* The following is only included to provide intuition on the fairly
  opaque definition. It is not meant to be used in any developments. *)
  Proposition _explicit_Join_fctx :
    forall C1 C2 C3,
      join C1 C2 C3 <-> (forall x,
                          match C1 x, C2 x, C3 x with
                          | Some a, Some b, Some c => JA a b c
                          | None, None, None => True
                          | _, _, _ => False
                          end).
  Proof. reflexivity. Qed.

  #[global] Instance Perm_alg_fctx : Perm_alg fctx.
  Proof. hauto use: Perm_fun, Perm_opt. Defined.
  #[global] Instance Canc_alg_fctx : Canc_alg fctx.
  Proof. hauto use: Canc_fun, Canc_opt. Defined.
  #[global] Instance Sep_alg_fctx : Sep_alg fctx.
  Proof. hauto use: Sep_fun, Sep_opt, Perm_opt. Defined.

  Definition exh (hal: A -> Prop): fctx -> Prop :=
    fun C => forall r, match C r with
               | Some a => hal a
               | None => False
               end.

  Definition empty_fctx : fctx := fun _ => None.

  Definition lookup_fctx : fctx -> R -> option A :=
    fun C x => C x.

  Definition update_fctx `{EqDec R} : fctx -> R -> A -> fctx :=
    fun C r a r' => if eq_dec r r' then Some a else C r'.

  Definition is_defined : fctx -> R -> Prop :=
    fun C r => C r <> None.

End FunCtx.