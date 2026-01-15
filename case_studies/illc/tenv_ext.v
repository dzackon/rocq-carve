(* ======================================================= *)
(* Common type environments abbreviations for extended LLC *)
(* ======================================================= *)

(* Imports *)
From Coq Require Import Logic.FunctionalExtensionality Program.Basics Unicode.Utf8.
From Hammer Require Import Hammer.
From VST.msl Require Import sepalg.
From CARVe Require Import contexts.total_fun algebras.dill.
From Autosubst Require Import fintype stlc_ext.
Import ScopedNotations.

(* -------------------------------------------- *)
(* Definitions                                  *)
(* -------------------------------------------- *)

(* An EqDec instance for fin n *)
#[global] Program Instance EqDec_fin (n : nat) : EqDec (fin n) :=
  {| eq_dec := @fin_eq n |}.

Definition tenv n := tfctx (fin n) ty mult.
Definition emptyT := empty_tfctx (fin 0) _ _ (Unit, zero).
Definition tenv_head {n} (Δ : tenv (S n)) : ty * mult := Δ None.
Definition tenv_tail {n} (Δ : tenv (S n)) : tenv n := fun i => Δ (Some i).

#[global] Arguments lookup {D R A} _ _.
#[global] Arguments exh {D R A} _ _.
#[global] Arguments upd {D R A H} _ _ _ _.
#[global] Arguments ren_tfctx {D R A}.
#[global] Arguments BijectiveRenaming {D}.
#[global] Arguments merge_ren {D R A JA}.

(* -------------------------------------------- *)
(* Basic properties of contexts                 *)
(* -------------------------------------------- *)

Property tenv_eta {n} (Δ : tenv (S n)) :
  Δ = scons (Δ None) (tenv_tail Δ).
Proof. extensionality x; destruct x; reflexivity. Qed.

Property tenv_tail_cons {n} (x : ty * mult) (Δ : tenv n) :
  tenv_tail (scons x Δ) = Δ.
Proof. reflexivity. Qed.

Property tenv_eq_cons {n} {Δ Δ' : tenv n} :
  Δ = Δ' -> forall x, scons x Δ = scons x Δ'.
Proof. intros; subst; reflexivity. Qed.

(* -------------------------------------------- *)
(* Properties of context merge                  *)
(* -------------------------------------------- *)

(* If Δ₁ ⋈ Δ₂ = ⋅, then Δ₁ = Δ₂ = ⋅ *)
Property join_emptyT {Δ1 Δ2} :
  join Δ1 Δ2 emptyT → Δ1 = emptyT ∧ Δ2 = emptyT.
Proof. split; apply functional_extensionality; intro x; contradiction. Qed.

(* If Δ₁ ⋈ Δ₂ = Δ and exh(Δ₁), then Δ₂ = Δ *)
Property join_id {n} {Δ Δ₁ Δ₂ : tenv n} :
  join Δ₁ Δ₂ Δ → exh hal Δ₁ → Δ₂ = Δ.
Proof.
  intros. apply functional_extensionality; intro x.
  specialize (H x). specialize (H0 x).
  destruct (Δ₁ x), (Δ₂ x), (Δ x). sauto.
Qed.

Property id_join {n} {Δ : tenv n} : exh hal Δ → join Δ Δ Δ.
Proof. intros; intro x; split; [|destruct (H x)]; sauto. Qed.

Property merge_cons {n} {Δ₁ Δ₂ Δ : tenv n} {m1 m2 m : mult} :
  join Δ₁ Δ₂ Δ /\ join m1 m2 m <->
  forall T, join (scons (T, m1) Δ₁) (scons (T, m2) Δ₂) (scons (T, m)  Δ).
Proof.
  split.
  - intros [H ?] ? x; destruct x; simpl; [apply H|split; sauto].
  - intros H; split.
    + intro x; exact (H (fst (Δ x)) (Some x)).
    + specialize (H Unit None); sauto.
Qed.

Property join_cons_inv {n} {Δ₁ Δ₂ Δ : tenv (S n)} :
  join Δ₁ Δ₂ Δ →
  fst (Δ₁ None) = (fst (Δ None)) ∧
  fst (Δ₂ None) = (fst (Δ None)) ∧
  join (snd (Δ₁ None)) (snd (Δ₂ None)) (snd (Δ None)) ∧
  join (tenv_tail Δ₁) (tenv_tail Δ₂) (tenv_tail Δ).
Proof. intros * H. destruct (H None). repeat split; try specialize (H (Some x)); sauto. Qed.

(* -------------------------------------------- *)
(* Properties of update                         *)
(* -------------------------------------------- *)

(* Updating (Δ, (T1, m1)) at index ↑fn to is equivalent to updating Δ at fn and
  extending the resulting context with (T1, m1). *)
Property upd_some {n} (Δ : tenv n) (fn : fin n) (x y : ty * mult) :
  upd (scons x Δ) (Some fn) y = scons x (upd Δ fn y).
Proof. extensionality z; unfold upd; destruct (eq_dec (Some fn : fin (S n)) z); sauto. Qed.

Lemma upd_none {n} (Δ : tenv n) (x y : ty * mult) :
  upd (scons x Δ) None y = scons y Δ.
Proof. extensionality z; unfold upd; destruct (eq_dec (None : fin (S n)) z); sauto. Qed.

(* -------------------------------------------- *)
(* Properties of exhaustedness                  *)
(* -------------------------------------------- *)

(** Zero out every multiplicity in a tenv, i.e. get unit for Δ **)
Definition core_tenv {n} := (core_tfctx (fin n) ty mult _ _ ).

Property core_tenv_exh {n} (Δ : tenv n) : exh hal (core_tenv Δ).
Proof. unfold core_tenv; sauto using core_tfctx_exh. Qed.

Property core_tenv_unit {n} (Δ : tenv n) : join (core_tenv Δ) Δ Δ.
Proof. sauto use: core_tfctx_unit, mult_Perm_alg. Qed.

Property exh_cons {n} {Δ : tenv n} {x : ty * mult} :
  exh hal Δ ∧ hal (snd x) ↔ exh hal (scons x Δ).
Proof. split; [intros [H ?]|intros H].
  - intro z. destruct z as [z'|]; asimpl; [apply (H z')|assumption].
  - split; [intro r; specialize (H (Some r))| specialize (H None)]; auto.
Qed.

(* -------------------------------------------- *)
(* Properties of permutations                   *)
(* -------------------------------------------- *)

Property br_up_tm_inj {n} (b : BijectiveRenaming) :
  ∀ x y : fin (S n),
    up_ren ren_fun x = up_ren ren_fun y → x = y.
Proof. intros; destruct x, y; [apply f_equal, ren_inj; now injection H| | |]; sauto. Qed.

Instance up_BijectiveRenaming {n} (b : @BijectiveRenaming (fin n)) : BijectiveRenaming :=
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
  ren_inj := fun x y H => br_up_tm_inj b x y H;
  ren_surj := fun y =>
    match y with
    | None => ex_intro _ var_zero eq_refl
    | Some j =>
        let (i, Hi) := ren_surj j in
        ex_intro _ (Some i) (f_equal Some Hi)
    end
|}.

(* -------------------------------------------- *)
(* Context morphisms                            *)
(* -------------------------------------------- *)

Property tenv_tail_ren {n} (ξ : fin n → fin n) (Δ : tenv (S n)) :
  ren_tfctx ξ (tenv_tail Δ) = tenv_tail (ren_tfctx (up_ren ξ) Δ).
Proof. reflexivity. Qed.

Property up_ren_cons {n} (ξ : fin n → fin n) (Δ : tenv n) (x : ty * mult) :
  ren_tfctx (up_ren ξ) (scons x Δ) = scons x (ren_tfctx ξ Δ).
Proof. extensionality z; destruct z; auto. Qed.

(* Swapping two arbitrary elements of a context is a valid permutation *)

Definition swap_indices {n} (i j : fin n) : fin n → fin n :=
  fun x =>
    if fin_eq i x then j
    else if fin_eq j x then i
    else x.

Property swap_indices_involutive {n} (i j : fin n) :
  ∀ x : fin n, swap_indices i j (swap_indices i j x) = x.
Proof.
  intros x; unfold swap_indices.
  destruct (fin_eq i x); destruct (fin_eq j x); sauto.
Qed.

Definition swap_tenv_fun {n} (Δ : tenv n) (i j : fin n) : tenv n :=
  let 'xi := Δ i in
  let 'xj := Δ j in
  upd (upd Δ i xj) j xi.

Property ren_swap_eq_update_swap {n} (Δ : tenv n) (i j : fin n) :
  ren_tfctx (swap_indices i j) Δ = swap_tenv_fun Δ i j.
Proof.
  unfold swap_tenv_fun, ren_tfctx, swap_indices.
  extensionality x.
  destruct (fin_eq i x) as [->|Hi];
  destruct (fin_eq j x) as [->|Hj];
  [ destruct (Δ x); now rewrite lookup_update_hit
  | destruct (Δ x), (Δ j) | destruct (Δ x), (Δ i)
  | destruct (Δ i), (Δ j) ];
  unfold upd; sauto.
Qed.

(* Swapping the topmost elements of a context is a valid permutation *)

Definition swap_top {n} : fin (S (S n)) → fin (S (S n)) :=
shift var_zero .: (var_zero .: shift >> shift).

Property swap_top_shift {n} :
  shift >> @swap_top n = up_ren shift.
Proof. reflexivity. Qed.

Property swap_top_involutive {n} :
  compose (@swap_top n) swap_top = id.
Proof. unfold compose, id. extensionality x; destruct x as [[|]|]; reflexivity. Qed.

Property swap_top_cons {n} (Δ : tenv n) (x y : ty * mult) :
  ren_tfctx swap_top (x .: (y .: Δ)) = y .: (x .: Δ).
Proof. extensionality z; destruct z as [[|]|]; reflexivity. Qed.

Instance BijectiveRenaming_swap_top {n} : BijectiveRenaming :=
{|
  ren_fun       := @swap_top n;
  ren_inv       := @swap_top n;
  ren_left_inv  := equal_f swap_top_involutive;
  ren_right_inv := equal_f swap_top_involutive;
  ren_inj := fun x y H =>
    eq_trans (eq_sym ((equal_f swap_top_involutive) x))
             (eq_trans (f_equal swap_top H) ((equal_f swap_top_involutive) y));
  ren_surj := fun x => ex_intro _ (swap_top x) ((equal_f swap_top_involutive) x)
|}.

(* -------------------------------------------- *)
(* Join families                                *)
(* -------------------------------------------- *)

(* Intuition: l is a function mapping each index x : fin n to a context Δₓ, and
  l(0) ⋈ l(1) ⋈ ... ⋈ l(n - 1) = Δ *)

Fixpoint join_family {n k} (l : fin n → tenv k) (Δ : tenv k) : Prop :=
  match n return (fin n → tenv k) → tenv k → Prop with
  | 0 => λ _ Δ, exh hal Δ
  | S n' =>
      λ l Δ,
        ∃ Δ' : tenv k,
          join_family (λ i, l (Some i)) Δ' ∧
          join (l None) Δ' Δ
  end l Δ.

(* Extending a join family (harmless element) *)
Property join_family_scons_head {n k} {l : fin n → tenv k} {Δ : tenv k} (h : ty * mult) :
  join_family l Δ →
  hal (snd h) →
  join_family (λ i, scons h (l i)) (scons h Δ).
Proof.
  revert Δ. induction n; intros Δ Hjf Hh.
  - simpl in *; intro r; destruct r; sauto.
  - destruct Hjf as [Δ' [Hjf' J]].
    econstructor; split.
    + exact (IHn (λ i, l (Some i)) Δ' Hjf' Hh).
    + intro; sauto unfold: scons.
Qed.

(* Extending a join family (arbitrary element) *)
(* TODO: extend to omegas *)
(* Property join_family_scons_head_one {n k}
  (l : fin n → tenv k) (Δ : tenv k) (h : ty * mult) :
  join_family l Δ →
  join_family
    (λ i : fin (S n),
       match i with
       | None   => scons h (λ x, (fst (Δ x), zero))
       | Some j => scons (fst h, zero) (l j)
       end)
    (scons h Δ).
Admitted. *)

(* If all contexts in a join family are exhausted, then so is the result *)
Property join_family_all_exh {n k} (l : fin n → tenv k) (Δ : tenv k) :
  join_family l Δ →
  (∀ fn, exh hal (l fn)) →
  exh hal Δ.
Proof.
  revert l Δ. induction n as [|n' IH]; intros l ? Hjf Hexh.
  - assumption.
  - destruct Hjf as [Δ' [Hjf' Hjoin]].
    destruct (join_id Hjoin (Hexh None)); sauto use: (IH (λ i, l (Some i)) Δ' Hjf').
Qed.

(* If all but one context in a join family are exhausted,
   then that one context equals the result *)

Property join_family_exh_single {n k} (l : fin n → tenv k) (Δ' : tenv k) (fn : fin n) :
  join_family l Δ' →
  (∀ x, x ≠ fn → exh hal (l x)) →
  l fn = Δ'.
Proof.
  revert l Δ' fn.
  induction n as [|n' IH]; intros l Δ' fn Jfam Hexh.
  - contradiction fn.
  - destruct Jfam as [Δ'' [Jfam' Hjoin]].
    destruct fn as [fn'|] eqn:EE.
    + assert (Hneq1 : None ≠ Some fn') by sauto.
      destruct (join_id Hjoin (Hexh None Hneq1)).
      apply (IH (λ i, l (Some i)) Δ'' fn' Jfam').
      intros x Hneq2; eapply (Hexh (Some x)); sauto.
    + eapply join_id; eauto.
      eapply join_family_all_exh; sauto.
Qed.

(* -------------------------------------------- *)
(* var_family (singleton join family)           *)
(* -------------------------------------------- *)

(* var_family maps x to the context Δ with only the entry for x
   given multiplicity snd(Δ x), and zero at other positions *)

Definition var_family {n} (Δ : tenv n) : fin n → tenv n :=
  λ i j, let '(A, m) := Δ j in
         if eq_dec i j then (A, m) else (A, core m).

(* Basic properties of var_family *)

Property var_family_match {n} (Δ : tenv n) (i : fin n) :
  var_family Δ i i = Δ i.
Proof. unfold var_family; destruct (fin_eq i i); sauto. Qed.

Property var_family_zero {n} (Δ : tenv n) (i j : fin n) :
  i ≠ j → var_family Δ i j = (fst (Δ j), core (snd (Δ j))).
Proof. intros; unfold var_family; destruct (fin_eq i j); sauto. Qed.

Property var_family_exh {n} (Δ : tenv n) (x : fin n) :
  snd (Δ x) = zero → exh hal (var_family Δ x).
Proof.
  unfold var_family, exh; intros. destruct (Δ r) eqn:E.
  destruct (eq_dec x r); [subst; rewrite E in H|]; sauto.
Qed.

(* The var_family construction forms a valid join family *)
(* Property var_family_is_join_family {n} (Δ : tenv n) :
  join_family (var_family Δ) Δ.
Proof.
  intros; induction n as [|n' IH].
  - intro; contradiction.
  - exists (scons (fst (Δ None), zero) (tenv_tail Δ)); split.
    + assert (var_family_Some :
        ∀ n (Δ : tenv (S n)) (i j : fin n),
          var_family Δ (Some i) (Some j) = var_family (tenv_tail Δ) i j).
      { intros; unfold tenv_tail, var_family.
        destruct (eq_dec i j); destruct (eq_dec (Some i : fin (S n)) (Some j)); sauto. }
      (* assert (var_family_tail_scons :
        ∀ n (Δ : tenv (S n)),
          (λ i, var_family Δ (Some i)) =
          (λ i, (fst (Δ None), zero) .: var_family (tenv_tail Δ) i)).
      { intros; extensionality i; extensionality j.
        destruct j; [rewrite var_family_Some | rewrite var_family_zero]; sauto. }
      rewrite var_family_tail_scons.
      exact (join_family_scons_head (fst _, _) (IH _) halz). *)
      admit.
    + (* assert (∀ m, join m zero m) as Hjoin by (destruct m; constructor).
      intro x; destruct x; [rewrite var_family_zero | rewrite var_family_match]; sauto. *)
      admit.
Admitted. *)