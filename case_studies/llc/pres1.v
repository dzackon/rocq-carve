(* ======================================================= *)
(* Typing, context morphism lemmas, and preservation       *)
(* (contexts as total maps)                                *)
(* ======================================================= *)

(* Library imports *)
From Coq Require Import List Logic.JMeq Logic.FunctionalExtensionality Program.Basics Unicode.Utf8.
From Hammer Require Import Hammer.

(* Local imports *)
From VST.msl Require Import sepalg functors.
From CARVe Require Import contexts.total_fun algebras.linear.
From Autosubst Require Import core fintype stlc step.
Require Import tenv typing.
Import ScopedNotations.

(* ------------------------------------- *)
(* Structural properties                 *)
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

Corollary typing_ren_sym {n} {Δ : tenv n} {M : tm n} {T : ty} (b : BijectiveRenaming) :
  has_type Δ M T →
  has_type (ren_tfctx ren_inv Δ) (ren_tm ren_fun M) T.
Proof. intros Hty. apply (typing_ren (@BijectiveRenaming_sym _ b) Hty). Qed.

Corollary exchange_top_two {n} :
  ∀ {Δ : tenv n} {M : tm (S (S n))} {T : ty} {x y : ty * mult},
    has_type (x .: (y .: Δ)) M T →
    has_type (y .: (x .: Δ)) (ren_tm swap_top M) T.
Proof. intros * Hty. rewrite <- swap_top_cons; apply (typing_ren BijectiveRenaming_swap_top Hty). Qed.

(** Admissibility of weakening of used assumptions *)

Lemma weakening_top {n} :
  ∀ {Δ : tenv n} {M : tm n} {T : ty} (T' : ty),
    has_type Δ M T →
    has_type (scons (T', zero) Δ) (ren_tm shift M) T.
Proof.
  intros * Htyp. induction Htyp.
  - eapply t_Var; [now asimpl|unfold shift; rewrite upd_some; eapply (proj1 exh_cons); sauto].
  - apply t_Abs.
    assert (Heq : ∀ {n} {M : tm (S n)},
      ren_tm (shift >> swap_top) M = ren_tm (var_zero .: shift >> shift) M) by sauto.
    assert (IHHtyp' := exchange_top_two IHHtyp); now asimpl in IHHtyp'.
  - eapply t_App; eauto; intros []; sauto.
Qed.

(** Admissibility of strengthening of used assumptions *)
(** Remark: If we try to prove `strengthening_top` directly by induction on
    `has_type (scons (T', zero) Δ) M T`, Rocq expects equalities between
    permuted contexts in the `t_Abs` case. Making permutation explicit
    in the hypothesis avoids this. *)

Lemma strengthening {n} :
  ∀ {Δ : tenv n} {Δ' : tenv (S n)} {M : tm (S n)} {T T' : ty}
    (b : BijectiveRenaming),
    has_type Δ' M T →
    ren_tfctx ren_inv Δ' = ((T', zero) .: Δ) →
    ∃ M', has_type Δ M' T ∧ (M = ren_tm ren_inv (ren_tm shift M')).
Proof.
  intros * H P. revert b Δ T' P.
  dependent induction H; intros.
  - (* t_Var *)
    assert (P' := equal_f P (ren_fun fn)).
    unfold lookup in H; unfold ren_tfctx in P'; rewrite ren_left_inv, H in P'.
    destruct (ren_fun fn) as [x'|] eqn:Eq1; cbn in P'; try discriminate.
    eexists; split.
    + eapply t_Var.
      -- unfold lookup; rewrite P'; reflexivity.
      -- apply tfctx_exh_ren with (π := ren_inv) in H0.
        now rewrite (bij_ren_tfctx_upd_sym _ _ _), P, Eq1, upd_some, <- exh_cons in H0.
    + cbn; unfold shift; now rewrite <- Eq1, ren_left_inv.
  - (* t_Abs *)
    remember (BijectiveRenaming_trans (up_BijectiveRenaming b) (BijectiveRenaming_swap_top)) as b'.
    assert (Heq1 : @ren_inv _ b' = compose (up_ren (@ren_inv _ b)) swap_top) by sauto.
    assert (P' := f_equal (ren_tfctx swap_top) (up_ren_cons ren_inv Δ' (T2, one))).
    rewrite P, swap_top_cons, ren_tfctx_trans, <- Heq1 in P'.
    destruct (IHhas_type _ _ _ eq_refl JMeq_refl JMeq_refl b' _ _ P') as (? & H' & ->).
    eexists; split.
    + apply t_Abs, H'.
    + assert (Heq2 : ∀ {n} (σ : fin (S n) → fin (S n)),
       (shift >> (swap_top >> (var_zero .: σ >> shift))) =
       (var_zero .: shift >> (σ >> shift)))
       by (intros; extensionality y; destruct y; cbn; reflexivity).
      rewrite Heq1; unfold compose; asimpl; rewrite Heq2; reflexivity.
  - (* t_App *)
    assert (J1 := merge_ren _ _ _ (@ren_inv _ b) H1); rewrite P in J1.
    destruct (join_cons_inv J1) as (Eq1 & Eq2 & Jhd & Jtl).
    rewrite tenv_tail_cons in Jtl. inversion Jhd.
    assert (Heq1 := tenv_eta (ren_tfctx ren_inv Δ1)); rewrite (surjective_pairing _), Eq1 in Heq1.
    assert (Heq2 := tenv_eta (ren_tfctx ren_inv Δ2)); rewrite (surjective_pairing _), Eq2 in Heq2.
    simpl in *; rewrite <- H3, <- H4 in *.
    destruct (IHhas_type1 _ _ _ eq_refl JMeq_refl JMeq_refl b _ _ Heq1) as (? & ? & ->).
    destruct (IHhas_type2 _ _ _ eq_refl JMeq_refl JMeq_refl b _ _ Heq2) as (? & ? & ->).
    eexists; split.
    + eapply t_App; eassumption.
    + now asimpl. 
Qed.

Corollary strengthening_top {n} :
  ∀ {Δ : tenv n} {M : tm (S n)} {T T' : ty},
    has_type (scons (T', zero) Δ) M T →
    ∃ M', has_type Δ M' T ∧ (M = ren_tm shift M').
Proof.
  intros * H.
  destruct (strengthening (BijectiveRenaming_id _) H eq_refl) as (? & ? & Heq).
  asimpl in Heq; eauto.
Qed.

(* -------------------------------------- *)
(* Substitution lemma                     *)
(* -------------------------------------- *)

(** The same issue as in `strengthening` occurs if we try to prove
    `lin_subst_top` directly; hence the general `lin_subst`. *)

Lemma lin_subst {n} {Δ₁' : tenv (S n)} {Δ₁ Δ₂ Δ : tenv n} {e1 e2 T1 T2}
                (b : BijectiveRenaming) :
    has_type Δ₁' e1 T1 →
    has_type Δ₂ e2 T2 →
    join Δ₁ Δ₂ Δ →
    ren_tfctx ren_inv Δ₁' = ((T2, one) .: Δ₁) →
    has_type Δ (ren_tm ren_fun e1)[e2..] T1.
Proof.
  intros H1 H2 J P; revert Δ₁ Δ₂ Δ b e2 T2 P H2 J.
  dependent induction H1; intros ? ? ? ? ? ? P H2 J.
  - (* t_Var *)
    assert (Hmap := bij_ren_lookup _ _ _ Δ₁' fn); unfold lookup in H; rewrite H in Hmap.
    assert (E := @tfctx_exh_ren _ _ _ ren_inv _ _ H0); rewrite bij_ren_tfctx_upd_sym, P in E.
    rewrite P in Hmap.
    destruct (ren_fun fn) as [x'|] eqn:Heq1.
    + rewrite upd_some in E; destruct ((proj2 exh_cons) E) as [? Hhal]; inversion Hhal.
    + simpl in Hmap; inversion Hmap; subst.
      assert (E2 : exh hal Δ₁)
        by (intro r; specialize (E (Some r)); rewrite upd_none in E; now simpl in E).
      rewrite <- (join_id J E2).
      assert (Heq2 : (ren_fun >> (e2 .: var_tm)) fn = e2) by (unfold scons, funcomp; now rewrite Heq1).
      asimpl; now rewrite Heq2.
  - (* t_Abs *)
    assert (J' : join ((T2, one) .: Δ₁) ((T2, zero) .: Δ₂) ((T2, one) .: Δ))
      by (intro x; sauto).
    remember (BijectiveRenaming_trans (up_BijectiveRenaming b) (BijectiveRenaming_swap_top)) as b'.
    assert (Heq1 : @ren_inv _ b' = compose (up_ren (@ren_inv _ b)) swap_top) by sauto.
    assert (Heq2 : @ren_fun _ b' = compose swap_top (up_ren (@ren_fun _ b))) by sauto.
    assert (P' := f_equal (ren_tfctx swap_top) (up_ren_cons ren_inv Δ₁' (T2, one))).
    rewrite P, swap_top_cons, ren_tfctx_trans, <- Heq1 in P'.
    apply (weakening_top T2) in H2.
    assert (H1' := IHhas_type _ _ _ eq_refl JMeq_refl JMeq_refl _ _ _ b' _ _ P' H2 J').
    rewrite Heq2 in H1'; unfold compose in H1'; asimpl in H1'; unfold shift in *.
    assert (Heq3 :
      ∀ {n} (σ : fin (S n) → fin (S n)) (f : fin (S n) → tm (S n)) {e},
        Some >> (swap_top >> (e .: f)) = e .: Some >> f)
      by (intros; extensionality y; sauto).
    assert (Heq4 :
      ∀ {n} (σ : fin (S n) → fin (S n)) (f : fin (S n) → tm (S n)) {e},
        (swap_top >> (e .: f)) var_zero .: σ >> (shift >> (swap_top >> (e .: f))) =
        f var_zero .: σ >> (e .: shift >> f))
      by sauto.
    rewrite Heq4 in H1'; unfold shift in H1'.
    now apply t_Abs in H1'.
  - (* t_App *)
    assert (J1 := merge_ren _ _ _ (@ren_inv _ b) H); rewrite P in J1.
    destruct (join_cons_inv J1) as (? & ? & Jhd & Jtl).
    rewrite tenv_tail_cons in Jtl. (* inversion Jhd. *)
    pose proof (typing_ren_sym b H1_) as Hty1.
    pose proof (typing_ren_sym b H1_0) as Hty2.
    assert (Heq1 : ren_tfctx ren_inv Δ1 =
      ((T0, snd (ren_tfctx ren_inv Δ1 None)) .: tenv_tail (ren_tfctx ren_inv Δ1)))
      by sauto use: tenv_eta, surjective_pairing.
    assert (Heq2 : ren_tfctx ren_inv Δ2 =
      ((T0, snd (ren_tfctx ren_inv Δ2 None)) .: tenv_tail (ren_tfctx ren_inv Δ2)))
      by sauto use: tenv_eta, surjective_pairing.
    simpl in *; inversion Jhd; rewrite <- H4, <- H5 in *.
    + destruct (join_assoc (join_comm Jtl) J) as [? [J0 J2]].
      rewrite Heq2 in Hty2; destruct (strengthening_top Hty2) as (? & Hty2' & ->).
      specialize (IHhas_type1 _ _ _ eq_refl JMeq_refl JMeq_refl _ _ _ _ _ _ Heq1 H2 J0).
      assert (Hty := t_App IHhas_type1 Hty2' (join_comm J2)).
      now asimpl in Hty.
    + destruct (join_assoc Jtl J) as [? [J0 J2]].
      rewrite Heq1 in Hty1; destruct (strengthening_top Hty1) as (? & Hty1' & ->).
      specialize (IHhas_type2 _ _ _ eq_refl JMeq_refl JMeq_refl _ _ _ _ _ _ Heq2 H2 J0).
      assert (Hty := t_App Hty1' IHhas_type2 J2).
      now asimpl in Hty.
Qed.

Corollary lin_subst_top {n} :
  ∀ {Δ₁ Δ₂ Δ : tenv n} {e1 e2 T1 T2},
    has_type ((T2, one) .: Δ₁) e1 T1 →
    has_type Δ₂ e2 T2 →
    join Δ₁ Δ₂ Δ →
    has_type Δ e1[e2..] T1.
Proof.
  intros * H1 H2 J.
  assert (H' := lin_subst (BijectiveRenaming_id _) H1 H2 J eq_refl).
  now rewrite rinstId'_tm in H'.
Qed.

(* ------------------------------------- *)
(* Theorem                               *)
(* ------------------------------------- *)

(** Preservation *)

Lemma preservation {n} (Δ : tenv n) (M : tm n) T :
  has_type Δ M T →
  ∀ M', step M M' → has_type Δ M' T.
Proof.
  induction 1; intros ? Hstep; inv Hstep; try (econstructor; eauto).
  - sauto using lin_subst_top.
Qed.