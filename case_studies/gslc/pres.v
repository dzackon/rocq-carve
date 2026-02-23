(* ======================================================= *)
(* Type preservation for generic substructural λ-calculus  *)
(* ======================================================= *)

From Stdlib.Logic Require Import FunctionalExtensionality.
From Hammer Require Import Tactics.
From Autosubst Require Import core fintype stlc step.
From VST Require Import sepalg.
From CARVe Require Import total_fun genv resalg.
Require Import gslc.
Import ScopedNotations.

Section TPres.
Variable A : Type.
Variable JA : Join A.
Variable PA : Perm_alg A.
Variable SA : Sep_alg A.
Variable CA : Canc_alg A.
Variable RA : Res_alg A.

(* ------------------------------------- *)
(* Structural properties                 *)
(* ------------------------------------- *)

(** Properties of consequent multiplicity *)
Lemma typing_hasW {n} {Δ : tenv n} {M : tm n} {p : ty * A} :
  has_type Δ M p ->
  hasW_if Δ (snd p).
Proof. revert p; induction M; intros * Htyp Hc; inversion Htyp.
  - sfirstorder.
  - qauto l: on use: ctx_forall_cons.
  - qauto l: on use: ctx_forall_join, @hasW_join_closed.
Qed.

Lemma typing_hasC {n} {Δ : tenv n} {M : tm n} {p : ty * A} :
  has_type Δ M p ->
  hasC_if Δ (snd p).
Proof. revert p; induction M; intros * Htyp Hc; inversion Htyp.
  - sfirstorder.
  - qauto l: on use: ctx_forall_cons.
  - qauto l: on use: ctx_forall_join, @hasC_join_closed.
Qed.

Lemma typing_nonzero {n} {Δ : tenv n} {M : tm n} {p : ty * A} :
  has_type Δ M p -> nonzero (snd p).
Proof. revert p; induction M; intros * Htyp; inversion Htyp; hauto q: on. Qed.

(** Admissibility of exchange *)

Lemma typing_ren {n} {Δ : tenv n} {M : tm n} {p : ty * A} (b : bijection) :
  has_type Δ M p ->
  has_type (ren_fctx ren_fun Δ) (ren_tm ren_inv M) p.
Proof.
  intros Htyp. revert b. induction Htyp; intros; cbn.
  - econstructor.
    + eassumption.
    + unfold lookup, ren_fctx in *. rewrite ren_right_inv; eassumption.
    + rewrite <- bij_ren_fctx_upd. now apply ctx_forall_ren.
    + sfirstorder use: ctx_forall_ren.
    + sfirstorder use: ctx_forall_ren.
  - eapply t_Abs.
    specialize (IHHtyp (up_bijection b)). rewrite <- up_ren_cons; apply IHHtyp.
  - eapply t_App. apply IHHtyp1. apply IHHtyp2. now apply merge_ren.
Qed.

Corollary typing_ren_sym {n} {Δ : tenv n} {M : tm n} {p : ty * A} (b : bijection) :
  has_type Δ M p ->
  has_type (ren_fctx ren_inv Δ) (ren_tm ren_fun M) p.
Proof. intros Hty. apply (typing_ren (@bijection_sym _ b) Hty). Qed.

(* Remark: We have two different weakening principles, which are
  not interderivable.
  The first comes from the algebraic structure: Weakening here
  amounts to updating the availability of existing assumptions.
  This second increases the size of the context by adding a new
  entry at the front.
*)

Lemma weakening_join {n} {Δ₁ Δ₂ Δ : tenv n} {e p} :
  has_type Δ₁ e p ->
  hasWᶜ Δ₂ ->
  hasC_if Δ₂ (snd p) ->
  join Δ₁ Δ₂ Δ ->
  has_type Δ e p.
Proof.
  intro Hty; revert Δ₂ Δ. induction Hty; intros ?Δ₂ ?Δ Hexh Hc J.
  - (* ht_hyp *)
    econstructor.
    + eassumption.
    + unfold lookup in *; specialize (J fn); rewrite H0 in J.
      assert (Heq := nonzero_split (join_join_sub (proj2 J)) H).
      destruct (Δ0 fn); inversion J; f_equal; sfirstorder.
    + eapply ctx_forall_join. eapply @hasW_join_closed.
      eapply merge_upd. exact J. apply core_duplicable.
      assumption.
      apply ctx_forall_upd. assumption. specialize (H1 fn); now rewrite lookup_update_hit in H1.
    + intro; eapply ctx_forall_join; eauto using hasW_join_closed.
    + intro; eapply ctx_forall_join; eauto using hasC_join_closed.
  - (* ht_lolli_I *)
    destruct (nonzero_core_or_unr (typing_nonzero Hty)) as [Jm|Hu].
    + econstructor; eapply IHHty.
      3: eapply (join_cons J); eapply join_comm, core_unit.
      apply ctx_forall_cons; eauto using zero_hasW.
      intro; apply ctx_forall_cons; eauto using zero_hasC.
    + econstructor; eapply IHHty.
      3: eapply (join_cons J); eapply join_comm, hasC_idem', Hu.
      eapply ctx_forall_cons; split; [assumption|apply Hu].
      intro; apply ctx_forall_cons; eauto.
  - (* ht_lolli_E *)
    destruct (join_assoc H J) as [? [? ?]].
    econstructor. 2: eapply IHHty2. all: eauto.
Qed.

(** Admissibility of weakening of W- and C-satisfying assumptions *)

Lemma weakening_top {n} {Δ : tenv n} {M : tm n} {p q : ty * A} :
  has_type Δ M p ->
  hasW (snd q) ->
  hasC (snd q) ->
  has_type (scons q Δ) (ren_tm shift M) p.
Proof.
  revert Δ p q. induction M; intros Δ p q Htyp Hw Hc; inversion Htyp.
  - eapply t_Var; try eassumption; subst p.
    unfold shift; rewrite (upd_cons _ _); apply ctx_forall_cons; auto.
    1-2: intro; apply ctx_forall_cons; auto.
  - econstructor; rewrite <- swap_top_cons. specialize (IHM _ _ _ H2 Hw).
    eapply typing_ren with (b := bijection_swap_top) in IHM; now asimpl in IHM.
  - cbn; subst. eapply t_App.
    + apply IHM1. eassumption. eassumption. apply Hc.
    + apply IHM2. eassumption. eassumption. apply Hc.
    + destruct q; eapply join_cons; eauto using hasC_idem'.
Qed.

(** Admissibility of strengthening of used assumptions *)
(** Remark: If we try to prove `strengthening_top` directly by induction on
    `has_type (scons q Δ) M T`, Rocq expects equalities between
    permuted contexts in the `t_Abs` case. Making permutation explicit
    in the hypothesis avoids this. *)

Lemma strengthening {n} {Δ : tenv n} {Δ' : tenv (S n)} {M : tm (S n)} {p q : ty * A}
                    (b : bijection) :
    has_type Δ' M p ->
    ren_fctx ren_inv Δ' = (q .: Δ) ->
    zero (snd q) ->
    exists M', has_type Δ M' p /\ (M = ren_tm ren_inv (ren_tm shift M')).
Proof.
  intros Htyp. revert b Δ q.
  dependent induction M; inversion Htyp; intros b Δ q Hrn Hz; subst.
  - (* t_Var *)
    assert (Hrn' := equal_f Hrn (ren_fun f)).
    unfold lookup in H1; unfold ren_fctx in Hrn'. rewrite ren_left_inv, H1 in Hrn'.
    destruct (ren_fun f) as [x'|] eqn:Eq1; cbn in Hrn'.
    + eexists; split.
      * eapply t_Var.
        -- eassumption.
        -- unfold lookup; rewrite Hrn'; reflexivity.
        -- apply ctx_forall_ren with (π := ren_inv) in H2.
          now rewrite (bij_ren_fctx_upd_sym _ _ _), Hrn, Eq1, (upd_cons _ _), ctx_forall_cons in H2.
        -- intro; qauto l: on use: ctx_forall_ren, ctx_forall_cons.
        -- intro; qauto l: on use: ctx_forall_ren, ctx_forall_cons.
      * cbn; unfold shift; now rewrite <- Eq1, ren_left_inv.
    + inversion Hrn'; subst. contradiction.
  - (* t_Abs *)
    remember (bijection_trans (up_bijection b) (bijection_swap_top)) as b'.
    assert (Heq1 : @ren_inv _ b' = funcomp (up_ren (@ren_inv _ b)) swap_top) by sfirstorder.
    assert (P' := f_equal (ren_fctx swap_top) (up_ren_cons ren_inv Δ' (t, m))).
    rewrite Hrn, swap_top_cons, ren_fctx_trans, <- Heq1 in P'.
    destruct (IHM _ _ _ _ _ _ _ _ eq_refl JMeq_refl _ H2 b' _ _ P' Hz) as (? & H' & ->).
    eexists; split.
    + apply t_Abs, H'.
    + rewrite Heq1. unfold swap_top; asimpl. reflexivity.
  - (* t_App *)
    eapply merge_ren with (π := ren_inv) in H4; rewrite Hrn in H4.
    destruct (join_cons_inv H4) as (Eq1 & Eq2 & Jhd & Jtl).
    assert (Heq1 := genv_eta (ren_fctx ren_inv Δ1)); rewrite (surjective_pairing _), Eq1 in Heq1.
    assert (Heq2 := genv_eta (ren_fctx ren_inv Δ2)); rewrite (surjective_pairing _), Eq2 in Heq2.
    assert (Hz1 := zero_sub (join_join_sub Jhd) Hz).
    assert (Hz2 := zero_sub (join_join_sub' Jhd) Hz).
    destruct (IHM1 _ _ _ _ _ _ _ _ eq_refl JMeq_refl _ H1 b _ _ Heq1 Hz1) as (? & ? & ->).
    destruct (IHM2 _ _ _ _ _ _ _ _ eq_refl JMeq_refl _ H2 b _ _ Heq2 Hz2) as (? & ? & ->).
    eexists; split.
    + eapply t_App; eauto.
    + reflexivity.
Qed.

Corollary strengthening_top {n} :
  forall {Δ : tenv n} {M : tm (S n)} {p q : ty * A},
    has_type (scons q Δ) M p ->
    zero (snd q) ->
    exists M', has_type Δ M' p /\ (M = ren_tm shift M').
Proof.
  intros * H Hz.
  destruct (strengthening (bijection_id _) H eq_refl Hz) as (? & ? & Heq).
  asimpl in Heq; eauto.
Qed.

(* -------------------------------------- *)
(* Substitution lemma                     *)
(* -------------------------------------- *)

(** The same issue as in `strengthening` occurs if we try to prove
    `subst_lemma_top` directly; hence the general `subst_lemma`. *)

Lemma subst_lemma {n} {Δ₁' : tenv (S n)} {Δ₁ Δ₂ Δ : tenv n} {e1 e2 p q}
                  (b : bijection) :
    has_type Δ₁' e1 p ->
    has_type Δ₂ e2 q ->
    join Δ₁ Δ₂ Δ ->
    ren_fctx ren_inv Δ₁' = (q .: Δ₁) ->
    hasW_if Δ₂ (snd q) -> (* i.e. m satisfies weakening *)
    hasC_if Δ₂ (snd q) -> (* i.e. m satisfies contraction *)
    has_type Δ (ren_tm ren_fun e1)[e2..] p.
Proof.
  revert Δ₁' Δ₁ Δ₂ Δ b e2 p q;
  dependent induction e1; intros * Hty1 Hty2 Hj Hrn Hw Hc; inversion Hty1.
  - (* t_Var *)
    assert (Hmap := bij_ren_lookup _ _ _ Δ₁' f); unfold lookup in H1; rewrite H1 in Hmap.
    apply ctx_forall_ren with (π := ren_inv) in H2; rewrite bij_ren_fctx_upd_sym, Hrn in H2.
    rewrite Hrn in Hmap.
    destruct (ren_fun f) as [x'|] eqn:E1.
    + substify; asimpl; rewrite E1; simpl. econstructor.
      * eassumption.
      * destruct (Hj x') as [Hj1 Hj2]. inversion Hj1. simpl in Hmap; rewrite Hmap in *.
        assert (Heq := nonzero_split (join_join_sub Hj2) H0). unfold lookup; destruct (Δ x'). scongruence.
      * rewrite (upd_cons _ _), ctx_forall_cons in H2; destruct H2 as [? Hwq].
        eapply ctx_forall_join. eapply @hasW_join_closed.
        eapply merge_upd. eassumption. apply core_duplicable.
        assumption. eapply ctx_forall_upd. apply (Hw Hwq). apply hasW_core.
      * intro Hwm. specialize (H3 Hwm); apply ctx_forall_ren with (π := ren_inv) in H3; rewrite Hrn in H3;
        apply ctx_forall_cons in H3; destruct H3 as [Hc1 Hcq].
        eapply ctx_forall_join. eapply @hasW_join_closed. 1-2: eassumption. apply (Hw Hcq).
      * intro Hcm. specialize (H4 Hcm); apply ctx_forall_ren with (π := ren_inv) in H4; rewrite Hrn in H4;
        apply ctx_forall_cons in H4; destruct H4 as [Hc1 Hcq].
        eapply ctx_forall_join. eapply @hasC_join_closed. 1-4: eassumption. apply (Hc Hcq).
    + rewrite (upd_cons _ _) in H2; apply ctx_forall_cons in H2; destruct H2 as [Hw2 ?].
      simpl in Hmap. substify; asimpl; rewrite E1; simpl.
      eapply weakening_join. 1-2: subst; eassumption. 2: now apply join_comm.
      intro Hcm; specialize (H4 Hcm); apply ctx_forall_ren with (π := ren_inv) in H4; rewrite Hrn in H4.
      now apply ctx_forall_cons in H4.
  - (* t_Abs *)
    remember (bijection_trans (up_bijection b) (bijection_swap_top)) as b'.
    assert (Heq1 : @ren_inv _ b' = funcomp (up_ren (@ren_inv _ b)) swap_top) by sfirstorder.
    assert (Heq2 : @ren_fun _ b' = funcomp swap_top (up_ren (@ren_fun _ b))) by sfirstorder.
    assert (P' := f_equal (ren_fctx swap_top) (up_ren_cons ren_inv Δ₁' (t, m))).
    rewrite Hrn, swap_top_cons, ren_fctx_trans, <- Heq1 in P'.
    destruct (nonzero_core_or_unr (typing_nonzero Hty1)) as [Hnz|Hnz]; subst p.
    1: assert (J' : join ((t, m) .: Δ₁) ((t, core m) .: Δ₂) ((t, m) .: Δ))
        by (eapply (join_cons Hj); apply join_comm, core_unit);
      assert (Hw2 : hasW (snd q) -> hasWᶜ ((t, core m) .: Δ₂))
        by (intro; apply ctx_forall_cons; eauto using hasW_core);
      assert (Hc2 : hasC (snd q) -> hasCᶜ ((t, core m) .: Δ₂))
        by (intro; apply ctx_forall_cons; eauto using hasC_core);
     eapply @weakening_top with (q := (t, core m)) in Hty2.
    4: assert (J' : join ((t, m) .: Δ₁) ((t, m) .: Δ₂) ((t, m) .: Δ))
        by (eapply (join_cons Hj); hauto q: on use: hasC_idem');
      assert (Hw2 : hasW (snd q) -> hasWᶜ ((t, m) .: Δ₂))
        by (intro; apply ctx_forall_cons; sfirstorder use: hasW_core);
      assert (Hc2 : hasC (snd q) -> hasCᶜ ((t, m) .: Δ₂))
        by (intro; apply ctx_forall_cons; sfirstorder use: hasC_core);
      eapply @weakening_top with (q := (t, m)) in Hty2.
    1, 4: specialize (IHe1 _ _ _ _ _ _ _ eq_refl JMeq_refl _ _ _ _ b' _ _ _ H2 Hty2 J' P' Hw2 Hc2);
      refine (typing_conversion (t_Abs IHe1) _); asimpl;
      repeat f_equal; rewrite Heq2; unfold swap_top; extensionality z; destruct z; asimpl; eauto.
    all: sfirstorder use: Hnz.
  - (* t_App *)
    apply merge_ren with (π := ren_inv) in H4; rewrite Hrn in H4.
    destruct (join_cons_inv H4) as (? & ? & Jhd & Jtl);
    rewrite genv_tail_cons in Jtl.
    pose proof (typing_ren_sym b H1) as Hty1a.
    pose proof (typing_ren_sym b H2) as Hty1b.
    assert (Heq1 : ren_fctx ren_inv Δ1 =
      ((fst q, snd (ren_fctx ren_inv Δ1 None)) .: genv_tail (ren_fctx ren_inv Δ1)))
      by (rewrite (genv_eta _), (surjective_pairing _); f_equal; f_equal; assumption).
    assert (Heq2 : ren_fctx ren_inv Δ2 =
      ((fst q, snd (ren_fctx ren_inv Δ2 None)) .: genv_tail (ren_fctx ren_inv Δ2)))
      by (rewrite (genv_eta _), (surjective_pairing _); f_equal; f_equal; assumption).
    destruct (join_canonical_decomp Jhd) as [[E1 E2] | [[E1 Z2] | [Z1 E2]]];
    try rewrite E1 in *; try rewrite E2 in *.
    + destruct (join_assoc (join_comm Jtl) Hj) as [? [J1 J2]];
      destruct (join_assoc Jtl Hj) as [? [J1' J2']].
      destruct q; econstructor.
      * apply (IHe1_1 _ _ _ _ _ _ _ eq_refl JMeq_refl _ _ _ _ _ _ _ _ H1 Hty2 J1 Heq1 Hw Hc).
      * apply (IHe1_2 _ _ _ _ _ _ _ eq_refl JMeq_refl _ _ _ _ _ _ _ _ H2 Hty2 J1' Heq2 Hw Hc).
      * eapply ctx_join_contract; eauto. now apply Hc, hasC_idem.
    + destruct (join_assoc (join_comm Jtl) Hj) as [? [J1 J2]].
      rewrite Heq2 in Hty1b; destruct (strengthening_top Hty1b Z2) as (? & Hty1b' & Heq3).
      cbn; simpl in Heq3; rewrite Heq3. econstructor.
      3: eapply (join_comm J2).
      * destruct q; eapply (IHe1_1 _ _ _ _ _ _ _ eq_refl JMeq_refl _ _ _ _ _ _ _ _ H1 Hty2 J1 Heq1 Hw Hc).
      * asimpl; eapply Hty1b'.
    + destruct (join_assoc Jtl Hj) as [? [J1 J2]].
      rewrite Heq1 in Hty1a; destruct (strengthening_top Hty1a Z1) as (? & Hty1a' & Heq3).
      cbn; simpl in Heq3; rewrite Heq3. econstructor.
      2: destruct q; eapply (IHe1_2 _ _ _ _ _ _ _ eq_refl JMeq_refl _ _ _ _ _ _ _ _ H2 Hty2 J1 Heq2 Hw Hc).
      2: eassumption.
      asimpl; eapply Hty1a'.
Admitted.

Corollary subst_lemma_top {n} :
  forall {Δ₁ Δ₂ Δ : tenv n} {e1 e2 p q},
    has_type (q .: Δ₁) e1 p ->
    has_type Δ₂ e2 q ->
    join Δ₁ Δ₂ Δ ->
    hasW_if Δ₂ (snd q) ->
    hasC_if Δ₂ (snd q) ->
    has_type Δ e1[e2..] p.
Proof.
  intros * H1 H2 J Hexh Hc.
  assert (H' := subst_lemma (bijection_id _) H1 H2 J eq_refl Hexh Hc).
  now rewrite rinstId'_tm in H'.
Qed.

(* ------------------------------------- *)
(* Theorem                               *)
(* ------------------------------------- *)

(** Preservation *)

Lemma preservation {n} (Δ : tenv n) (M : tm n) T m :
  has_type Δ M (T, m) ->
  forall M', step M M' -> has_type Δ M' (T, m).
Proof.
  induction 1; intros ? Hstep; dependent destruction Hstep; try (econstructor; eauto).
  - inversion H. eauto using subst_lemma_top, typing_hasW, typing_hasC.
Qed.

End TPres.