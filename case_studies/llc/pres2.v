(* ======================================================= *)
(* Typing, context morphism lemmas, and preservation       *)
(* (contexts as total maps)                                *)
(* ======================================================= *)

(* Library imports *)
From Coq Require Import List Logic.JMeq Logic.FunctionalExtensionality Unicode.Utf8.
From Hammer Require Import Hammer.

(* Local imports *)
From VST.msl Require Import sepalg functors.
From CARVe Require Import contexts.total_fun algebras.linear.
From Autosubst Require Import core fintype stlc step.
Require Import tenv typing.
Import ScopedNotations.

(* ------------------------------------- *)
(* Context renaming lemma                *)
(* ------------------------------------- *)

(** Admissibility of exchange *)
Lemma typing_ren {n} {Δ : tenv n} {M : tm n} {T : ty} (b : BijectiveRenaming) :
  has_type Δ M T →
  has_type (ren_tfctx ren_fun Δ) (ren_tm ren_inv M) T.
Proof.
  intros Htyp. revert b.
  induction Htyp; intros; cbn.
  - econstructor.
    + unfold lookup, ren_tfctx; now rewrite ren_right_inv.
    + rewrite <- bij_ren_tfctx_upd. now apply tfctx_exh_ren.
  - eapply t_Abs.
    specialize (IHHtyp (up_BijectiveRenaming b)).
    rewrite <- up_ren_cons; apply IHHtyp.
  - eapply t_App; [apply IHHtyp1|apply IHHtyp2|now apply merge_ren].
Qed.

Corollary weakening_top {n} :
  ∀ {Δ : tenv n} {M : tm n} {T : ty} (T' : ty),
    has_type Δ M T →
    has_type (scons (T', zero) Δ) (ren_tm shift M) T.
Proof.
  intros * Htyp. induction Htyp.
  - eapply t_Var; [now asimpl|].
    unfold shift; rewrite upd_some; eapply (proj1 exh_cons); sauto.
  - cbn; econstructor.
    rewrite <- swap_top_shift, <- renRen_tm, <- swap_top_cons.
    now apply (typing_ren BijectiveRenaming_swap_top).
  - eapply t_App; eauto; intros []; sauto.
Qed.

(* ------------------------------------- *)
(* Join families                         *)
(* ------------------------------------- *)

(* Splitting join family s.t. typing conditions are preserved *)

Lemma join_family_split {k n} {l : fin n → tenv k} (σ : fin n → tm k)
                        {Δ Δ1 Δ2 : tenv n} {Δ' : tenv k} :
  join_family l Δ' →
  join Δ1 Δ2 Δ →
  (∀ x, (snd (Δ x) = one  → has_type (l x) (σ x) (fst (Δ x))) ∧
        (snd (Δ x) = zero → exh hal (l x))) →
  ∃ (l1 l2 : fin n → tenv k) (Δ1' Δ2' : tenv k),
    join Δ1' Δ2' Δ' ∧
    join_family l1 Δ1' ∧ join_family l2 Δ2' ∧
    (∀ x, join (l1 x) (l2 x) (l x)) ∧
    (∀ x, (snd (Δ1 x) = one  → has_type (l1 x) (σ x) (fst (Δ1 x))) ∧
          (snd (Δ1 x) = zero → exh hal (l1 x))) ∧
    (∀ x, (snd (Δ2 x) = one  → has_type (l2 x) (σ x) (fst (Δ2 x))) ∧
          (snd (Δ2 x) = zero → exh hal (l2 x))).
Proof.
  revert k l σ Δ Δ1 Δ2 Δ'.
  induction n as [| n IH]; intros ? l σ Δ Δ1 Δ2 Δ' Hjf J Hty.

  - (* Base case: n = 0 *)
    exists l, l, Δ', Δ'.
    repeat split; try contradiction; try assumption.
    sauto use: (Hjf x).

  - (* Inductive case: n = S n' *)
    destruct Hjf as [Δt [Htail Jl0]].
    destruct (join_cons_inv J) as (_ & _ & _ & Jtail). 

    (* IH on the tail *)
    assert (Hih : ∀ x,
      (snd (Δ (Some x)) = one  → has_type (l (Some x)) (σ (Some x)) (fst (Δ (Some x)))) ∧
      (snd (Δ (Some x)) = zero → exh hal (l (Some x)))) by sauto.
    destruct (IH k (λ i, l (Some i)) (λ i, σ (Some i)) _ _ _ _ Htail Jtail Hih)
      as (l1' & l2' & Δt1 & Δt2 & Jt & ? & ? & ? & ? & ?).

    (* Helper: multiplicity characterization *)
    assert (neq_one : ∀ m, m ≠ one ↔ m = zero) by (intro; split; destruct m; sauto).

    (* Use join associativity to decompose contexts *)
    destruct (join_assoc (join_comm Jt) (join_comm Jl0)) as [Δt1_0 [J1b ?]].
    destruct (join_assoc Jt (join_comm Jl0)) as [Δt2_0 [J1a ?]].

    (* Define contexts and families based on head multiplicities *)
    exists
      (λ x, match x with
        | None => if mult_eq_dec (snd (Δ1 None)) one then l None else zero_tenv (l None)
        | Some y => l1' y end),
      (λ x, match x with
        | None => if mult_eq_dec (snd (Δ2 None)) one then l None else zero_tenv (l None)
        | Some y => l2' y end),
      (if mult_eq_dec (snd (Δ1 None)) one then Δt1_0 else Δt1),
      (if mult_eq_dec (snd (Δ2 None)) one then Δt2_0 else Δt2).

    (* Case analysis on head multiplicities *)
    destruct (merge_pointwise_fun _ _ _ _ J (None : fin (S n)) ) as (Heq01 & Heq02 & Jhead);
    destruct (mult_eq_dec (snd (Δ1 None)) one) as [Heq3|Hneq1];
    destruct (mult_eq_dec (snd (Δ2 None)) one) as [Heq4|Hneq2].

    (* Case: both heads are one (impossible) *)
    + rewrite Heq3, Heq4 in Jhead; inversion Jhead.

    (* Case: Δ1 head is one, Δ2 head is zero *)
    + split; [now apply join_comm|].
      split; [exists Δt1; auto using join_comm|].
      split; [exists Δt2; auto;
        destruct (join_assoc (zero_tenv_unit (l None)) (join_comm J1a)) as [? [Jz' ?]];
        now rewrite <- (join_id Jz' (zero_tenv_exh _)) in Jz'|].
      split; [destruct x; auto using zero_tenv_unit|].
      split; [destruct x; sauto|split; sauto use: zero_tenv_exh].

    (* Case: Δ1 head is zero, Δ2 head is one *)
    + split; [assumption|].
      split; [exists Δt1; auto;
        destruct (join_assoc (zero_tenv_unit (l None)) (join_comm J1b)) as [? [Jz' ?]];
        now rewrite <- (join_id Jz' (zero_tenv_exh _)) in Jz'|].
      split; [exists Δt2; auto|].
      split; [sauto use: zero_tenv_unit, join_comm|].
      split; [sauto use: zero_tenv_exh|].
      split; [destruct x;
        [sauto | intros ?; rewrite Heq4 in Jhead; inversion Jhead;
        assert (Hty' := proj1 (Hty None) (eq_sym H7));
        now rewrite Heq02 in Hty']|].
      intro Heq; destruct x;
        [sauto | assert (Heq4' := proj2 (neq_one _) Heq);
        rewrite <- Heq4 in Heq4'; now destruct Heq4'].

    (* Case: both heads are zero *)
    + apply neq_one in Hneq1, Hneq2. rewrite Hneq1, Hneq2 in Jhead;
      assert (Hexh := (proj2 (Hty None)) (eq_sym (mult_hal_unit Jhead halz)));
      remember (join_id (join_comm J1a) Hexh); remember (join_id (join_comm J1b) Hexh);
      rewrite <- (proj1 (exh_zero_tenv _) Hexh).
      split; [|split; [|split; [|split]]]; sauto use: id_join, join_comm.
Qed.

Lemma var_family_has_type {n} (Δ : tenv n) (x : fin n) :
  snd (Δ x) = one →
  has_type (var_family Δ x) (var_tm x) (fst (Δ x)).
Proof.
  intros. econstructor; unfold var_family, lookup. 
  destruct (eq_dec x x); [|contradiction].
  - destruct (Δ x); sauto.
  - unfold exh, upd; intro y. sauto use: (eq_dec x y).
Qed.

(* ------------------------------------- *)
(* Typing instantiation lemma            *)
(* ------------------------------------- *)

(* Substitution preserves typing *)

Lemma typing_inst
  {n k} {Δ : tenv n} (Δ' : tenv k) (σ : fin n → tm k) (l : fin n → tenv k) {e T} :
  join_family l Δ' →
  (∀ x, (snd (Δ x) = one  → has_type (l x) (σ x) (fst (Δ x))) ∧
        (snd (Δ x) = zero → exh hal (l x))) →
  has_type Δ e T →
  has_type Δ' e[σ] T.
Proof.
  intros Jfam Hσ Htyp.
  revert k Δ' σ l Jfam Hσ.
  induction Htyp as [* ? Hexh|?|?]; intros k Δ' σ l Jfam Hσ.

  - assert (Htyp_fn: has_type (l fn) (σ fn) T).
    { unfold lookup in H. specialize (Hσ fn); rewrite H in Hσ; sauto. }
    assert (Hl_fn_eq: l fn = Δ').
    { eapply join_family_exh_single; [assumption|].
      intros x ?.
      unfold upd in Hexh; specialize (Hexh x).
      destruct (eq_dec fn x); [|apply (proj2 (Hσ x))]; sauto. }
    rewrite <- Hl_fn_eq; assumption.

  - asimpl; constructor; eapply IHHtyp.
    + apply (join_family_scons_head_one _ _ _ Jfam).
    + intro x; destruct x as [x'|].
      * split; intro Heq.
        -- specialize ((proj1 (Hσ x')) Heq) as Heq'. apply (weakening_top T2 Heq').
        -- eapply (proj1 exh_cons); split; [now apply (proj2 (Hσ x'))|sauto].
      * split; [intro; econstructor; [sauto|]|sauto].
        remember (fun x => (fst (Δ' x), zero)) as Δupd.
        assert (Hexh : exh hal Δupd) by sauto.
        assert (Hexh' : exh hal ((T2, zero) .: Δupd)) by (sauto use: exh_cons, halz).
        now rewrite <- (upd_none _ (T2, one) _) in Hexh'.

  - asimpl.
    destruct (join_family_split σ Jfam H Hσ)
      as (? & ? & ? & ? & Jt & Jfam1 & Jfam2 & _ & Hσ1 & Hσ2).
    specialize (IHHtyp1 _ _ σ _ Jfam1 Hσ1).
    specialize (IHHtyp2 _ _ σ _ Jfam2 Hσ2).
    eapply t_App; eassumption.
Qed.

(* ------------------------------------- *)
(* Theorem                               *)
(* ------------------------------------- *)

(** Preservation *)

Lemma preservation {n} (Δ : tenv n) (M : tm n) T :
  has_type Δ M T →
  ∀ M', step M M' → has_type Δ M' T.
Proof.
  induction 1 as [? | * ? IHA | * H1 ? ? ? ?];
  intros M' Hstep; inversion Hstep; try (eapply t_App; eauto).
  - econstructor. now apply IHA.
  - subst; inversion H1; subst.
    set (l := λ x : fin (S n),
      match x with
      | None   => Δ2
      | Some y => var_family Δ1 y
      end).
    eapply (typing_inst _ _ l); try eassumption; repeat split.
    + exists Δ1; sauto using var_family_is_join_family.
    + destruct x; cbn; auto using var_family_has_type.
    + destruct x; cbn; [apply var_family_exh | sauto].
Qed.