Require Import VST.msl.sepalg.

From CARVe.contexts Require Import partial_fun.
From CARVe.algebras Require Import purely_linear.

Inductive dom : Type :=
| A : dom
| B : dom.

Instance dom_eqdec : EqDec dom.
Proof.
  constructor; decide equality.
Defined.

Definition myctx := fctx dom mult.

Notation "[ a ]" := (Some a).
Notation "⊥" := None.

Example ctx0 : myctx :=
  fun r => match r with
        | A => [zero]
        | B => ⊥
        end.

Example ctx1 : myctx :=
  fun r => match r with
        | A => [one]
        | B => ⊥
        end.

Example ajoin : join ctx0 ctx1 ctx1.
Proof.
  intro. destruct x; constructor.
Qed.

(* Notation from Software Foundations section on partial maps. *)
Notation "x '↦' v ';' m" := (update_fctx _ _ m x v)
                            (at level 100, v at next level, right associativity).
Notation "x '↦' v" := (update_fctx _ _ (empty_fctx _ _) x v)
                      (at level 100).

(* I would like to figure out how to make dom/mult implicit *)
Example ctx0' : myctx := A ↦ zero.
Example ctx1' : myctx := A ↦ one.
Example ajoin' : join ctx0' ctx1' ctx1'.
Proof.
  intro; destruct x; constructor.
Qed.