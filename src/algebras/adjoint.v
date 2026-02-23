(**
  Generic multiplicity structure for adjoint logic
**)

From Stdlib Require Import Logic.Classical Program.Equality RelationClasses.
From Hammer Require Import Tactics.
From VST Require Import sepalg.
From CARVe Require Import resalg.

Local Obligation Tactic := try sauto.

(* ----------------------------------------- *)
(* Mode structure                            *)
(* ----------------------------------------- *)

(* Structural properties *)
Inductive struct_prop := W | C.

(* 'Set' of structural properties *)
Record struct_set := { has_W : bool; has_C : bool }.

(* Check if a structural property is in a set *)
Definition has_prop (μ : struct_set) (p : struct_prop) : Prop :=
  match p with
  | W => has_W μ = true
  | C => has_C μ = true
  end.
Notation "p ∈ μ" := (has_prop μ p) (at level 70).

(* Generic mode structure *)
Class ModeStructure (A : Type) {JA : Join A} := {

  (* Main definitions *)
  σ : A -> struct_set;
  unr m := W ∈ σ m /\ C ∈ σ m;
  zero m := unr m /\ exists m', unit_for m m' /\ ~ unr m';
  nonzero a := ~ zero a;

  (* Preorder on modes *)
  (* Remark: For simplicity, we define `mode_ge` as exactly property inclusion, but it could be made more general
    (at the expense of useful properties like `core_ge`):
    mode_ge : mode -> mode -> Prop;
    mode_ge_preorder : PreOrder mode_ge;
    mode_ge_subset : forall m k p, mode_ge m k -> p ∈ σ k -> p ∈ σ m; *)
  mode_ge : A -> A -> Prop := fun m k => forall p, p ∈ σ k -> p ∈ σ m;

  (* Properties of W, C *)
  has_prop_join_closed : forall {m1 m2 m} p, join m1 m2 m -> (p ∈ σ m <-> p ∈ σ m1 /\ p ∈ σ m2);
  hasW_identity {a} :
    identity a -> W ∈ σ a;
  hasC_idem {a} : join a a a -> C ∈ σ a;
  hasC_join_distrib {c a1 a2 a12 a} :
    C ∈ σ c ->
    join a1 a2 a12 -> join a12 c a ->
    exists a1' a2',
      join a1 c a1' /\ join a2 c a2' /\ join a1' a2' a;

  (* 'Zero-like' elements *)
  zero_join_collapse {a1 a2 a} :
    join a1 a2 a -> zero a1 -> zero a2 -> a1 = a;
  nonzero_split {a1 a} :
    join_sub a1 a -> nonzero a1 -> a1 = a;
}.

#[global] Program Instance AdjointRes_alg {A} {JA: Join A} {MS: ModeStructure A} : Res_alg A :=
  { hasW := fun m => W ∈ σ m;
    hasC := fun m => C ∈ σ m;
    hasW_identity := fun _ => hasW_identity;
    hasW_join_closed := fun _ _ _ Hj Hw1 Hw2 => ((proj2 (has_prop_join_closed W Hj)) (conj Hw1 Hw2));
    hasC_idem := fun _ => hasC_idem;
    hasC_join_distrib := fun _ _ _ _ _ => hasC_join_distrib;
    zero_join_collapse := fun _ _ _ => zero_join_collapse;
    nonzero_split := fun _ _ => nonzero_split;
  }.
Notation "m ⩾ k" := (mode_ge m k) (at level 70).

(* ----------------------------------------- *)
(* Properties of `mode_ge`                   *)
(* ----------------------------------------- *)

(* `mode_ge` forms a preorder *)

Lemma mode_ge_refl `{ModeStructure} : forall m, m ⩾ m.
Proof. intros m p Hp. exact Hp. Qed.

Lemma mode_ge_trans `{ModeStructure} : forall m k l, m ⩾ k -> k ⩾ l -> m ⩾ l.
Proof. intros m k l Hmk Hkl p Hp. apply Hmk, Hkl, Hp. Qed.

(* More properties of `mode_ge` *)

Property core_ge' {A} {JA: Join A} {SA: Sep_alg A} {MA: ModeStructure A} :
  forall m k : A, mode_ge (core m) m.
Proof. intros m ? ? ?; now apply (has_prop_join_closed _ (core_unit m)). Qed.

Property core_ge {A} {JA: Join A} {PA: Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A} {RA: Res_alg A} {MA: ModeStructure A} :
  forall m k, mode_ge (core m) k.
Proof.
  intros ? ? p ?; destruct p.
  eapply (@hasW_core _ _ _ _ _ AdjointRes_alg). eapply (@hasC_core _ _ _ AdjointRes_alg).
Qed.

Property mode_ge_join `{ModeStructure} {m1 m2 m} :
  join m1 m2 m ->
  forall k, (mode_ge m k <-> mode_ge m1 k /\ mode_ge m2 k).
Proof. intros * Hjoin; split; [intros ?; split|intros [? ?]]; intros p ?; eapply (has_prop_join_closed p Hjoin); auto. Qed.

(* ----------------------------------------- *)
(* Concrete instance:                        *)
(* Intuitionistic-linear-affine-strict logic *)
(* ----------------------------------------- *)

Module AdjointLogic.

  Inductive mult :=
  | zero   (* irrelevant *)
  | oneL   (* linear     *)
  | oneA   (* affine     *)
  | oneS   (* strict     *)
  | omega. (* structural *)

  Definition σ_mult (m : mult) : struct_set :=
    match m with
    | zero  => {| has_W := true  ; has_C := true  |} (* {W,C} *)
    | oneL  => {| has_W := false ; has_C := false |} (* { }   *)
    | oneA  => {| has_W := true  ; has_C := false |} (* {W}   *)
    | oneS  => {| has_W := false ; has_C := true  |} (* {C}   *)
    | omega => {| has_W := true  ; has_C := true  |} (* {W,C} *)
    end.

  Inductive mult_op : mult -> mult -> mult -> Prop :=
  | mult_zero_zero : mult_op zero zero zero
  | mult_zero_oneL : mult_op zero oneL oneL
  | mult_oneL_zero : mult_op oneL zero oneL
  | mult_zero_oneA : mult_op zero oneA oneA
  | mult_oneA_zero : mult_op oneA zero oneA
  | mult_zero_oneS : mult_op zero oneS oneS
  | mult_oneS_zero : mult_op oneS zero oneS
  | mult_oneS_oneS : mult_op oneS oneS oneS
  | mult_omega_omega : mult_op omega omega omega.
  Notation "a • b == c" := (mult_op a b c) (at level 50, left associativity).

  Property mult_op_comm : forall a b c, mult_op a b c -> mult_op b a c.
  Proof. sauto lq: on rew: off. Qed.

  Property mult_op_assoc : forall a b c d e,
    mult_op a b d -> mult_op d c e ->
    exists f, mult_op b c f /\ mult_op a f e.
  Proof. intros * H1 H2; inversion H1; subst; inversion H2; eauto using mult_op. Qed.

  Ltac impossible_mult_op H :=
    match H with
    | mult_zero_zero => idtac
    | mult_zero_oneL => idtac
    | mult_oneL_zero => idtac
    | mult_zero_oneA => idtac
    | mult_oneA_zero => idtac
    | mult_oneS_zero => idtac
    | mult_zero_oneS => idtac
    | mult_omega_omega => idtac
    | _ => exfalso; inversion H
    end.

  Ltac solve_mult_assoc :=
    match goal with
      | [ |- {f : mult & mult_op zero zero f /\ mult_op zero f zero } ] => eexists; exact (conj mult_zero_zero mult_zero_zero)
      | [ |- {f : mult & mult_op zero zero f /\ mult_op oneL f oneL } ] => eexists; exact (conj mult_zero_zero mult_oneL_zero)
      | [ |- {f : mult & mult_op zero zero f /\ mult_op oneA f oneA } ] => eexists; exact (conj mult_zero_zero mult_oneA_zero)
      | [ |- {f : mult & mult_op zero oneL f /\ mult_op zero f oneL } ] => eexists; exact (conj mult_zero_oneL mult_zero_oneL)
      | [ |- {f : mult & mult_op zero oneA f /\ mult_op zero f oneA } ] => eexists; exact (conj mult_zero_oneA mult_zero_oneA)
      | [ |- {f : mult & mult_op zero zero f /\ mult_op oneS f oneS } ] => eexists; exact (conj mult_zero_zero mult_oneS_zero)
      | [ |- {f : mult & mult_op zero oneS f /\ mult_op zero f oneS } ] => eexists; exact (conj mult_zero_oneS mult_zero_oneS)
      | [ |- {f : mult & mult_op zero oneS f /\ mult_op oneS f oneS } ] => eexists; exact (conj mult_zero_oneS mult_oneS_oneS)
      | [ |- {f : mult & mult_op oneL zero f /\ mult_op zero f oneL } ] => eexists; exact (conj mult_oneL_zero mult_zero_oneL)
      | [ |- {f : mult & mult_op oneA zero f /\ mult_op zero f oneA } ] => eexists; exact (conj mult_oneA_zero mult_zero_oneA)
      | [ |- {f : mult & mult_op oneS zero f /\ mult_op oneS f oneS } ] => eexists; exact (conj mult_oneS_zero mult_oneS_zero)
      | [ |- {f : mult & mult_op oneS zero f /\ mult_op zero f oneS } ] => eexists; exact (conj mult_oneS_zero mult_zero_oneS)
      | [ |- {f : mult & mult_op oneS zero f /\ mult_op oneS f oneS } ] => eexists; exact (conj mult_oneS_zero mult_oneS_oneS)
      | [ |- {f : mult & mult_op oneS oneS f /\ mult_op oneS f oneS } ] => eexists; exact (conj mult_oneS_oneS mult_oneS_zero)
      | [ |- {f : mult & mult_op oneS oneS f /\ mult_op zero f oneS } ] => eexists; exact (conj mult_oneS_oneS mult_zero_oneS)
      | [ |- {f : mult & mult_op oneS oneS f /\ mult_op oneS f oneS } ] => eexists; exact (conj mult_oneS_oneS mult_oneS_oneS)
      | [ |- {f : mult & mult_op omega omega f /\ mult_op omega f omega } ] => eexists; exact (conj mult_omega_omega mult_omega_omega)
    end.

  Property mult_op_assoc' : forall a b c d e,
    mult_op a b d -> mult_op d c e ->
    {f : mult & mult_op b c f /\ mult_op a f e}.
  Proof.
    intros a b c d e H1 H2; destruct a, b, c, d, e;
    try solve_mult_assoc; try impossible_mult_op H1; try impossible_mult_op H2.
  Qed.

  Instance Join_mult : Join mult := mult_op.

  Program Instance Perm_alg_mult : Perm_alg mult :=
    { join_assoc := mult_op_assoc'; join_comm := mult_op_comm }.
  Next Obligation. intros * H1 H2. destruct x, y, z, z'; try inversion H1; try inversion H2; reflexivity. Defined.

  Program Instance Sep_alg_mult : Sep_alg mult :=
    {core := fun m => match m with | zero | oneL | oneA | oneS => zero
                                   | omega => omega end; }.

  Program Instance Flat_alg_mult : Flat_alg mult.

  Program Instance ModeStructure_mult : @ModeStructure mult Join_mult := { σ := σ_mult; }.
  Next Obligation. destruct 1; sauto lq: on rew: off. Defined.
  Next Obligation.
    intros; destruct a.
    2: specialize (H zero oneL). 4: specialize (H zero oneS). all: qauto l: on.
  Defined.
  Next Obligation. destruct 3; sauto. Defined.

  Program Instance Res_alg_mult : @Res_alg mult Join_mult :=
    @AdjointRes_alg mult Join_mult ModeStructure_mult.

End AdjointLogic.

(* ----------------------------------------- *)
(* Concrete instance: Linear logic           *)
(* ----------------------------------------- *)

From CARVe Require Import linear.

Module LinearLogic.

  Definition σ_mult (m : mult) : struct_set :=
    match m with
    | zero => {| has_W := true  ; has_C := true  |} (* {W,C} *)
    | one  => {| has_W := false ; has_C := false |} (* { }   *)
    end.

  Program Instance LinearModeStructure : @ModeStructure mult Join_mult := { σ := σ_mult; }.
  Next Obligation. destruct 1; sauto lq: on rew: off. Defined.
  Next Obligation. intros; destruct a. 2: specialize (H zero one). all: sauto lq: on. Defined.

End LinearLogic.