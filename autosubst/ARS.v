(** ** Tactics *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Stdlib Require Import Program.Equality.

Declare Scope prop_scope.
Delimit Scope prop_scope with PROP.
Open Scope prop_scope.

Ltac inv H := inversion H; subst; clear H.

Ltac not_in_context P :=
  match goal with
    |[_ : P |- _] => fail 1
    | _ => idtac
  end.

Ltac extend H :=
let A := type of H in not_in_context A; generalize H; intro.

Definition Rel  (T : Type) := T -> T -> Prop.

(** Union of two relations *)
Inductive Or {X} (R R': X -> X -> Prop) : X -> X -> Prop :=
| Inl x y : R x y -> Or R R' x y
| Inr x y : R' x y -> Or R R' x y.

#[global] Hint Constructors Or : core.

(** ** Reflexive, Transitive closure *)

Section Definitions.

Variables (T : Type) (e : Rel T).
Implicit Types (R S : T -> T -> Prop).

Inductive star (x : T) : T -> Prop :=
| starR : star x x
| starSE y z : e x y -> star y z -> star x z.

Hint Constructors star : core.
#[local] Hint Resolve starR : core.

Lemma star1 x y : e x y -> star x y.
Proof. intros. eapply starSE; eauto. Qed.

Lemma star_trans y x z : star x y -> star y z -> star x z.
Proof.
  intros H H'. revert x H.
  induction H' as [|x y z H1 H2 IH]; intros; eauto. eapply IH. induction H; eauto.
Qed.

End Definitions.
#[global] Hint Constructors star : core.

Arguments star_trans {T e} y {x z} A B.

Lemma star_img T1 T2 (f : T1 -> T2) (e1 : Rel T1) e2 :
  (forall x y, e1 x y -> star e2 (f x) (f y)) ->
  (forall x y, star e1 x y -> star e2 (f x) (f y)).
Proof.
  intros ? x y H. induction H; eauto.
  eapply star_trans with (y  := f y); eauto.
Qed.

Lemma star_hom T1 T2 (f : T1 -> T2) (e1 : Rel T1) (e2 : Rel T2) :
  (forall x y, e1 x y -> e2 (f x) (f y)) ->
  (forall x y, star e1 x y -> star e2 (f x) (f y)).
Proof. intros. induction H0; eauto. Qed.