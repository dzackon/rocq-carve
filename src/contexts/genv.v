(* ======================================================= *)
(* Contexts as total functions with finite type as domain  *)
(* ======================================================= *)

From Stdlib Require Import Logic.FunctionalExtensionality Program.Basics.
From Hammer Require Import Tactics.
From VST Require Import eq_dec sepalg.
From CARVe Require Import resalg total_fun.
From Autosubst Require Import core fintype.
Import ScopedNotations.
Set Implicit Arguments.

Section GenTEnv.
Variable R : Type. (* Resource type *)
Variable A : Type. (* Resource algebra elements *)
Variable JA : Join A.

(* An EqDec instance for fin n *)
#[global] Program Instance EqDec_fin (n : nat) : EqDec (fin n) := fin_eq.

(* -------------------------------------------- *)
(* Definitions                                  *)
(* -------------------------------------------- *)

Definition genv n := @fctx (fin n) R A.
Definition emptyG (default : R * A) := empty_fctx (fin 0) _ _ default.
Definition genv_head {n} (Γ : genv (S n)) : R * A := Γ None.
Definition genv_tail {n} (Γ : genv (S n)) : genv n := fun i => Γ (Some i).
Definition core_genv {SA: Sep_alg A} {n} := (@core_fctx (fin n) R A JA SA).

(* -------------------------------------------- *)
(* Basic properties of contexts                 *)
(* -------------------------------------------- *)

Property genv_eta {n} (Γ : genv (S n)) :
  Γ = scons (Γ None) (genv_tail Γ).
Proof. extensionality x; destruct x; reflexivity. Qed.

Property genv_tail_cons {n} (x : R * A) (Γ : genv n) :
  genv_tail (x .: Γ) = Γ.
Proof. reflexivity. Qed.

(* -------------------------------------------- *)
(* Properties of `ctx_forall`                   *)
(* -------------------------------------------- *)

Property ctx_forall_genv {n} P {Γ : genv (S n)} :
  ctx_forall P Γ <-> ctx_forall P (genv_tail Γ) /\ P (snd (Γ None)).
Proof.
  split.
  - intros H; split; [intro i; exact (H (Some i))|exact (H None)].
  - intros [Htail Hhd] x; destruct x; [apply Htail|exact Hhd].
Qed.

Corollary ctx_forall_cons {n} P {Γ : genv n} {p} :
  ctx_forall P (p .: Γ) <-> ctx_forall P Γ /\ P (snd p).
Proof. apply ctx_forall_genv. Qed.

(* -------------------------------------------- *)
(* Properties of update                         *)
(* -------------------------------------------- *)

Lemma upd_cons {n} (Γ : genv n) (fn : fin (S n)) (x y : R * A) :
  upd (x .: Γ) fn y =
  (match fn with None => y | Some _ => x end) .: (match fn with None => Γ | Some i => upd Γ i y end).
Proof. extensionality z; unfold upd; destruct (eq_dec fn z); sauto lq: on rew: off. Qed.

(* -------------------------------------------- *)
(* Properties of context merge                  *)
(* -------------------------------------------- *)

Property join_emptyG {default} {Γ1 Γ2} :
  join Γ1 Γ2 (emptyG default) -> Γ1 = emptyG default /\ Γ2 = emptyG default.
Proof. split; apply functional_extensionality; intro x; contradiction. Qed.

Property join_cons_inv {n} {Γ₁ Γ₂ Γ : genv (S n)} :
  join Γ₁ Γ₂ Γ ->
  fst (Γ₁ None) = (fst (Γ None)) /\
  fst (Γ₂ None) = (fst (Γ None)) /\
  join (snd (Γ₁ None)) (snd (Γ₂ None)) (snd (Γ None)) /\
  join (genv_tail Γ₁) (genv_tail Γ₂) (genv_tail Γ).
Proof. intros; sauto using merge_pointwise_fun. Qed.

(* A convenient property (could merge with `join_cons_inv`?) *)
Property join_cons {n} {Γ₁ Γ₂ Γ : genv n} {a₁ a₂ a} :
  join Γ₁ Γ₂ Γ ->
  join a₁ a₂ a ->
  forall r, join ((r, a₁) .: Γ₁) ((r, a₂) .: Γ₂) ((r, a) .: Γ).
Proof.
  intros; eapply merge_pointwise_fun; destruct x.
  1: specialize (H f). all: sfirstorder.
Qed.

(* --------------------------------------------- *)
(* Properties of permutations, context morphisms *)
(* --------------------------------------------- *)

(* Interaction with generic lifting operation for renamings *)
Instance up_bijection {n} (b : @bijection (fin n)) : bijection :=
{|
  ren_fun := up_ren ren_fun;
  ren_inv := up_ren ren_inv;
  ren_left_inv := fun x =>
    match x with
    | None => eq_refl
    | Some i => f_equal Some (ren_left_inv i)
    end;
  ren_right_inv := fun x =>
    match x with
    | None => eq_refl
    | Some i => f_equal Some (ren_right_inv i)
    end;
|}.

Property up_ren_cons_genv {n} (xi : fin n -> fin n) (Γ : genv (S n)) :
  ren_fctx (up_ren xi) Γ = (Γ None) .: (ren_fctx xi (genv_tail Γ)).
Proof. extensionality z; destruct z; auto. Qed.

Corollary up_ren_cons {n} (xi : fin n -> fin n) (Γ : genv n) (x : R * A) :
  ren_fctx (up_ren xi) (x .: Γ) = x .: (ren_fctx xi Γ).
Proof. auto using up_ren_cons_genv. Qed.

(* Swapping two arbitrary elements of a context is a valid permutation *)

Definition swap_indices {n} (i j : fin n) : fin n -> fin n :=
  fun x =>
    if fin_eq i x then j
    else if fin_eq j x then i
    else x.

Property swap_indices_involutive {n} (i j : fin n) :
  forall x : fin n, swap_indices i j (swap_indices i j x) = x.
Proof.
  intros x; unfold swap_indices.
  destruct (fin_eq i x); destruct (fin_eq j x); hauto q: on.
Qed.

Property ren_swap_eq_update_swap {n} (Γ : genv n) (i j : fin n) :
  ren_fctx (swap_indices i j) Γ = upd (upd Γ i (Γ j)) j (Γ i).
Proof.
  unfold ren_fctx, swap_indices. extensionality x.
  destruct (fin_eq i x) as [->|Hi], (fin_eq j x) as [->|Hj];
  [ destruct (Γ x); now rewrite lookup_update_hit
  | destruct (Γ x), (Γ j) | destruct (Γ x), (Γ i) | destruct (Γ i), (Γ j) ];
  unfold upd; hauto q: on.
Qed.

(* Swapping the topmost elements of a context is a valid permutation *)

Definition swap_top {n} : fin (S (S n)) -> fin (S (S n)) :=
  shift var_zero .: (var_zero .: shift >> shift).

Property swap_top_involutive {n} :
  funcomp (@swap_top n) swap_top = id.
Proof. extensionality x; destruct x as [[|]|]; reflexivity. Qed.

Property swap_top_cons {n} (Γ : genv n) (x y : R * A) :
  ren_fctx swap_top (x .: (y .: Γ)) = y .: (x .: Γ).
Proof. extensionality z; destruct z as [[|]|]; reflexivity. Qed.

Instance bijection_swap_top {n} : bijection :=
  {|
    ren_fun       := @swap_top n;
    ren_inv       := @swap_top n;
    ren_left_inv  := equal_f swap_top_involutive;
    ren_right_inv := equal_f swap_top_involutive;
  |}.

End GenTEnv.

Global Arguments genv_head {R A n} _.
Global Arguments genv_tail {R A n} _.
Global Arguments join_cons {R A JA n _ _ _ _ _ _}.
Global Arguments ctx_forall_cons {R A n}.
Global Arguments core_genv {R A JA SA n} _.

Global Notation "'hasCᶜ' Δ" := (ctx_forall hasC Δ) (at level 40).
Global Notation "'hasWᶜ' Δ" := (ctx_forall hasW Δ) (at level 40).