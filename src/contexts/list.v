(**
  We reuse the VST/MSL functor and separation algebra machinery to
  encode CARVe. The aim is to show that our contexts of resources and
  use annotations, modelled by

    list (R * A),

  inherit the algebraic structure of A. To do so, we show that

    list (R * -)

  is a functor from (permission, separation, etc.) algebras to (permission,
  separation, etc.) algebras. Contexts then get for free properties like
  commutativity, associativity, cancellativity, etc.
**)

From Stdlib Require Import List Program.Equality Sorting.Permutation.
From Hammer Require Import Tactics.
From VST Require Import sepalg sepalg_generators.
Import List.ListNotations.

Section ListCtx.
Variable R: Type. (* Resources *)
Variable A: Type. (* Resource algebra *)
Variable JA: Join A.
Variable CA: Canc_alg A.
Variable PA: Perm_alg A.
Variable SA: Sep_alg A.

(*-------------------------------------- *)
(* Basic definitions and properties      *)
(*-------------------------------------- *)

(* Functor from permission algebras A to contexts of resources of
  type R, i.e., to list (R * A). *)
Definition lctx : Type := list (R * A).

(* Algebraic structure *)

#[global] Instance Join_lctx : Join lctx :=
  Join_list _ (Join_prod _ (Join_equiv _) _ JA).

#[global] Instance Perm_alg_lctx : Perm_alg lctx.
Proof. sauto use: Perm_list, Perm_prod, Perm_equiv. Qed.

#[global] Instance Canc_alg_lctx : Canc_alg lctx.
Proof. intros; apply Canc_list, Canc_prod; [ apply Canc_equiv | auto ]. Qed.

#[global] Instance Sep_alg_lctx : Sep_alg lctx.
Proof. intros; apply Sep_list, Sep_prod; sauto. Qed.

(* `ctx_forall` predicate *)

Definition ctx_forall (P : A -> Prop) : lctx -> Prop :=
  fold_right (fun ra p => and (P (snd ra)) p) True.

(* Exhaustedness as an inductive predicate *)
Inductive ctx_forall_ind (P : A -> Prop) : lctx -> Prop :=
| ctx_forall_ind_n : ctx_forall_ind P []
| ctx_forall_ind_c {l a} :
  forall r, ctx_forall_ind P l -> P a -> ctx_forall_ind P ((r, a) :: l).

(* Equivalence of functional and inductive definitions *)
Lemma ctx_forall_ind_iff P l :
  ctx_forall_ind P l <-> ctx_forall P l.
Proof.
  split.
  - induction 1; simpl; auto.
  - induction l as [|[? ?] ? ?]; intros H; constructor; destruct H; auto.
Qed.

(* Lookup / update *)

Definition lookup (l : lctx) (n : nat) : option (R * A) := nth_error l n.

Definition has_entry (l : lctx) (x : R * A) : Prop := In x l.

Fixpoint upd (l : lctx) (n : nat) (x : R * A) : lctx :=
  match n, l with
  | _, [] => []
  | 0, _ :: tl => x :: tl
  | S n', hd :: tl => hd :: upd tl n' x
  end.

(* Update as a relation *)
Inductive upd_rel : lctx -> nat -> R * A -> R * A -> lctx -> Prop :=
| updrel_t : forall (l : lctx) x y,
  upd_rel (x :: l) 0 x y (y :: l)
| updrel_n {l l' n x x' y} :
  upd_rel l n x x' l' ->
  upd_rel (y :: l) (S n) x x' (y :: l').

(* Index-free update relation *)
Definition upd_rel_ex (l : lctx) (x y : R * A) (l' : lctx) : Prop :=
  exists n, upd_rel l n x y l'.

(* Properties of lookup *)

Lemma lookup_has_entry {l x} :
  (exists n, lookup l n = Some x) <-> has_entry l x.
Proof. hauto lq: on rew: off use: nth_error_In, In_nth_error. Qed.

Lemma lookup_cons {Δ n p} q :
  lookup Δ n = Some p <-> lookup (q :: Δ) (S n) = Some p.
Proof. sfirstorder. Qed.

Ltac impossible_lookup_nil :=
  match goal with
  | H : lookup [] _ = Some _ |- _ => assert (H' := nth_error_In _ _ H); inversion H'
  end.

(* Properties of update *)

Lemma upd_nil n x :
  upd [] n x = [].
Proof. induction n; auto. Qed.

Lemma upd_cons l n x y :
  upd (x :: l) n y =
  (match n with 0 => y | S _ => x end) :: (match n with 0 => l | S n' => upd l n' y end).
Proof. destruct n; constructor. Qed.

Lemma upd_id {l n x} :
  lookup l n = Some x -> upd l n x = l.
Proof. revert n; induction l; hauto lq: on rew: off. Qed.

Lemma upd_none {l n} :
  lookup l n = None ->
  forall x, upd l n x = l.
Proof. revert n; induction l; hauto q: on. Qed.

Lemma upd_overwrite l n x y :
  upd (upd l n x) n y = upd l n y.
Proof. revert n; induction l; hauto q: on. Qed.

Lemma upd_comm {l n m x y} :
  n <> m ->
  upd (upd l n x) m y = upd (upd l m y) n x.
Proof.
  revert l n m x y.
  induction l as [|? ? IH]; intros n m ? ? ?.
  - rewrite !upd_nil; reflexivity.
  - destruct n, m; simpl; f_equal; [contradiction|apply IH; congruence].
Qed.

Lemma lookup_upd_eq :
  forall {l n y} x,
    lookup l n = Some y ->
    lookup (upd l n x) n = Some x.
Proof.
  induction l; intros n x y Hlk; destruct n; try discriminate.
  - inversion Hlk; reflexivity.
  - eapply IHl; exact Hlk.
Qed.

Lemma lookup_upd_neq {n m} :
  n <> m ->
  forall l y, lookup (upd l m y) n = lookup l n.
Proof. intros Hneq l. revert n m Hneq. induction l as [| ? ? ?]; intros; [|destruct n, m]; hauto q: on. Qed.

(* Properties of relational update *)

(* `upd_rel` corresponds to lookup and update *)
Lemma upd_rel_iff_fun {l l' n x y} :
  upd_rel l n x y l' <->
  lookup l n = Some x /\ upd l n y = l'.
Proof. split; [intro H; induction H|revert n x y l'; induction l]; sauto. Qed.

Lemma lookup_upd_rel_neq {n m} :
  n <> m ->
  forall {l l' x y}, upd_rel l m x y l' -> lookup l' n = lookup l n.
Proof. intros; hauto lq: on use: upd_rel_iff_fun, lookup_upd_neq. Qed.

Lemma upd_rel_refl {l l' n x} :
  upd_rel l n x x l' -> l = l'.
Proof. intros H; dependent induction H. 2: f_equal; eapply IHupd_rel. all: eauto. Qed.

(* Context merge *)

(* A useful characterization of non-trivial joins *)
Lemma destruct_join :
  forall {X Y Z : lctx} {A z},
    join X Y ((A, z) :: Z) ->
    exists x y X' Y',
      X = ((A, x) :: X') /\ Y = ((A, y) :: Y') /\ join x y z /\ join X' Y' Z.
Proof. intros; inversion H; sauto. Qed.

Property merge_lookup {l1 l2 l3 n r a} :
    lookup l3 n = Some (r, a) ->
    join l1 l2 l3 ->
    exists a1 a2,
      join a1 a2 a /\
      lookup l1 n = Some (r, a1) /\
      lookup l2 n = Some (r, a2).
Proof.
  intros Hlk Hm. revert n Hlk; induction Hm; intros ? Hlk.
  - impossible_lookup_nil.
  - destruct n.
  + inversion Hlk; inversion H; exists (snd x), (snd y); repeat split; sauto.
  + eapply IHHm in Hlk; destruct Hlk; eexists; repeat split; eauto.
Qed.

Corollary merge_has_entry {l1 l2 l3 r a} :
    has_entry l3 (r, a) ->
    join l1 l2 l3 ->
    exists a1 a2,
      join a1 a2 a /\
      has_entry l1 (r, a1) /\
      has_entry l2 (r, a2).
Proof.
  intros Hin Hj.
  destruct ((proj2 lookup_has_entry) Hin) as [? Hlk], (merge_lookup Hlk Hj) as (? & ? & ? & ? & ?).
  repeat eexists; try (apply (proj1 lookup_has_entry); eexists); eassumption.
Qed.

Property merge_lookup_forward_l {l1 l2 l3 n r a1} :
    lookup l1 n = Some (r, a1) ->
    join l1 l2 l3 ->
    exists a2 a,
      join a1 a2 a /\
      lookup l2 n = Some (r, a2) /\
      lookup l3 n = Some (r, a).
Proof.
  intros Hlk Hm; revert n Hlk; induction Hm; intros ? Hlk.
  - impossible_lookup_nil.
  - destruct n.
  + inversion Hlk; subst; inversion H. exists (snd y), (snd z).
    repeat split; simpl in *; sauto.
  + eapply IHHm in Hlk; destruct Hlk; eexists; repeat split; eauto.
Qed.

Corollary merge_has_entry_forward_l {l1 l2 l3 r a1} :
    has_entry l1 (r, a1) ->
    join l1 l2 l3 ->
    exists a2 a,
      join a1 a2 a /\
      has_entry l2 (r, a2) /\
      has_entry l3 (r, a).
Proof.
  intros Hin Hj.
  destruct ((proj2 lookup_has_entry) Hin) as [? Hlk], (merge_lookup_forward_l Hlk Hj) as (? & ? & ? & ? & ?).
  repeat eexists; try (apply (proj1 lookup_has_entry); eexists); eassumption.
Qed.

Property merge_lookup_forward_r {l1 l2 l3 n r a2} :
    lookup l2 n = Some (r, a2) ->
    join l1 l2 l3 ->
    exists a1 a,
      join a1 a2 a /\
      lookup l1 n = Some (r, a1) /\
      lookup l3 n = Some (r, a).
Proof. hauto l: on use: merge_lookup_forward_l, join_comm. Qed.

Corollary merge_has_entry_forward_r {l1 l2 l3 r a2} :
    has_entry l2 (r, a2) ->
    join l1 l2 l3 ->
    exists a1 a,
      join a1 a2 a /\
      has_entry l1 (r, a1) /\
      has_entry l3 (r, a).
Proof. hauto l: on use: merge_has_entry_forward_l, join_comm. Qed.

Lemma merge_lookup_none {l1 l2 l3 n} :
  join l1 l2 l3 ->
  (lookup l1 n = None <-> lookup l2 n = None) /\
  (lookup l2 n = None <-> lookup l3 n = None).
Proof.
  intros Hj; repeat split.
  - intro H1.
    destruct (lookup l2 n) as [[r a2]|] eqn:H2; auto.
    destruct (merge_lookup_forward_r H2 Hj) as (? & ? & _ & H1' & _).
    rewrite H1 in H1'; discriminate.
  - intro H2.
    destruct (lookup l1 n) as [[r a1]|] eqn:H1; auto.
    destruct (merge_lookup_forward_l H1 Hj) as (? & ? & _ & H2' & _).
    rewrite H2 in H2'; discriminate.
  - intro H2.
    destruct (lookup l3 n) as [[r a]|] eqn:H3; auto.
    destruct (merge_lookup H3 Hj) as (? & ? & _ & _ & H2').
    rewrite H2 in H2'; discriminate.
  - intro H3.
    destruct (lookup l2 n) as [[r a2]|] eqn:H2; auto.
    destruct (merge_lookup_forward_r H2 Hj) as (? & ? & _ & _ & H3').
    rewrite H3 in H3'; discriminate.
Qed.

(* If harmless elements are identity for resource join,
  then exhausted contexts are identity for context join *)
Lemma ctx_forall_id {P l1 l2 l} :
  join l1 l2 l ->
  ctx_forall P l1 ->
  (forall a b c : A, join a b c -> P a -> b = c) ->
  l2 = l.
Proof. intros. induction H; sauto. Qed.

Lemma merge_exh {P l1 l2 l3} :
  (forall a1 a2 a, join a1 a2 a -> P a -> P a1 /\ P a2) ->
  join l1 l2 l3 ->
  ctx_forall P l3 ->
  ctx_forall P l1 /\ ctx_forall P l2.
Proof.
  intros HP Hj Hexh; revert HP Hexh; induction Hj; intros HP Hexh.
  - split; constructor.
  - sauto.
Qed.

Lemma merge_upd {l1 l2 l3 a a1 a2} n r :
  join l1 l2 l3 ->
  join a1 a2 a ->
  join (upd l1 n (r, a1))
       (upd l2 n (r, a2))
       (upd l3 n (r, a)).
Proof.
  intros * Hj Ha; revert n; induction Hj; intros n.
  - hauto l: on.
  - destruct n; [hauto l: on|constructor; [exact H|apply IHHj]].
Qed.

(**
  As a sanity check, we give an inductive characterization of lctx,
  and show that it has the same action on the join relation. We should
  not directly use this definition in any future developments, but
  instead should use JoinFunctor_lctx applied to the resource algebra we are
  annotating contexts with.
**)

Inductive merge_ind : Join lctx :=
| mg_n : merge_ind [] [] []
| mg_c r {l1 l2 l a1 a2 a} :
    join a1 a2 a ->
    merge_ind l1 l2 l ->
    merge_ind ((r, a1) :: l1) ((r, a2) :: l2) ((r, a) :: l).

Proposition merge_is_JoinFunctor_lctx {l1 l2 l3 : lctx}:
  merge_ind l1 l2 l3 <-> join l1 l2 l3.
Proof. split; intro H; induction H; sauto. Qed.

(*-------------------------------------- *)
(* Permutations                          *)
(*-------------------------------------- *)

Lemma lookup_perm {l l' n x} :
  Permutation l l' ->
  lookup l n = Some x ->
  exists n', lookup l' n' = Some x.
Proof.
  intros Hperm Hlk. revert n x Hlk.
  induction Hperm; intros * Hlk.
  - eauto.
  - destruct n.
    + inversion Hlk; exists 0; reflexivity.
    + apply IHHperm in Hlk as [n' ?]; exists (S n'); assumption.
  - destruct n as [|[|n']].
    + inversion Hlk; exists 1; reflexivity.
    + inversion Hlk; exists 0; reflexivity.
    + exists (S (S n')); assumption.
  - apply IHHperm1 in Hlk as [? H1]; apply IHHperm2 in H1 as [n' ?].
    exists n'; assumption.
Qed.

Property perm_join l1 l2 l l' :
  Permutation l l' ->
  join l1 l2 l ->
  exists l1' l2',
    Permutation l1 l1' /\
    Permutation l2 l2' /\
    join l1' l2' l'.
Proof.
  intros Hp Hj; revert l1 l2 Hj; induction Hp; intros.
  - (* perm_nil *)
    inversion Hj; subst; eauto.
  - (* perm_skip *)
    inversion Hj as [| x1 x2 ? ? ? ? ? Hj'].
    destruct (IHHp _ _ Hj') as (l1' & l2' & ? & ? & ?).
    repeat eexists; econstructor; eauto.
  - (* perm_swap *)
    inversion Hj as [| x1 x2 ? ? ? ? ? [| y1 y2 ? l1' l2' ? ? ?]].
    exists (y1 :: x1 :: l1'), (y2 :: x2 :: l2').
    repeat split; constructor; sauto lq: on rew: off.
  - (* perm_trans *)
    destruct (IHHp1 _ _ Hj) as (? & ? & ? & ? & Hj').
    destruct (IHHp2 _ _ Hj') as (? & ? & ? & ? & ?).
    repeat eexists; try eapply Permutation_trans; eauto.
Qed.

Lemma perm_upd {l l' n x} y :
  Permutation l l' ->
  lookup l n = x ->
  exists m,
    lookup l' m = x /\
    Permutation (upd l n y) (upd l' m y).
Proof.
  intros Hp; revert n x; induction Hp; intros n ? Hlk.
  - (* perm_nil *)
    destruct x.
    + impossible_lookup_nil.
    + exists n; eauto.
  - (* perm_skip *)
    destruct n; simpl in Hlk.
    + inversion Hlk; exists 0; simpl; auto.
    + specialize (IHHp _ _ Hlk) as (m & Hm & Hp'); exists (S m); simpl; auto.
  - (* perm_swap *)
    destruct n as [|[|n']]; simpl in Hlk; inversion Hlk.
    + exists 1; split; constructor.
    + exists 0; split; constructor.
    + exists (S (S n')); split; auto; constructor.
  - (* perm_trans *)
    specialize (IHHp1 _ _ Hlk) as (m & Hm & Hp1').
    specialize (IHHp2 _ _ Hm) as (k & Hk & Hp2').
    exists k; split; auto. eapply perm_trans; eauto.
Qed.

Corollary perm_upd_rel {l1 l1' l2 n x y} :
  Permutation l1 l2 ->
  upd_rel l1 n x y l1' ->
  exists m l2',
    upd_rel l2 m x y l2' /\
    Permutation l1' l2'.
Proof.
  intros HP Hur. apply upd_rel_iff_fun in Hur as [Hlk Heq].
  destruct (perm_upd y HP Hlk) as (m & ? & ?).
  exists m, (upd l2 m y). sfirstorder use: upd_rel_iff_fun, Heq.
Qed.

Lemma perm_exh {P l l'} :
  Permutation l l' ->
  ctx_forall P l ->
  ctx_forall P l'.
Proof. intros. induction H; sfirstorder. Qed.

End ListCtx.

Global Arguments lctx {R A}.
Global Arguments lookup {R A} _ _.
Global Arguments has_entry {R A} _ _.
Global Arguments upd {R A} _ _.
Global Arguments upd_rel {R A} _ _.
Global Arguments ctx_forall {R A}.
Global Arguments lookup_cons {R A JA PA SA}.
Global Arguments destruct_join {R A JA PA SA X Y Z A z}.

(*-------------------------------------- *)
(* Resource-algebraic properties         *)
(*-------------------------------------- *)

From CARVe Require Import resalg.

Section ResAlg.
Variable R: Type. (* Resources *)
Variable A: Type. (* Resource algebra *)
Variable JA: Join A.
Variable RA: Res_alg A.

(* Exhaustedness as a functional program *)
Definition exh : (@lctx R A) -> Prop := ctx_forall hasW.

End ResAlg.

Global Arguments exh {R A JA RA}.