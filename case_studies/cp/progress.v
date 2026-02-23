(* ======================================================= *)
(* Progress for (a fragment of) CP                         *)
(* ======================================================= *)

From Stdlib Require Import List Program.Equality Sets.Permut Sorting.Permutation.
From Hammer Require Import Tactics.
From VST Require Import sepalg.
From CARVe Require Import list linear.
Require Import cp.

(* Useful tactics *)

(* If we are updating a list with at least one or two elements,
   then the result also has at least one or two elements. *)
Ltac refine_upd :=
  try repeat match goal with
  | [ H : upd (_ :: _) _ _ _ _ ?Δ |- _ ] =>
      let E := fresh "E" in
      match Δ with
      | _ :: _ => fail 1
      | _ => assert (exists x xs, Δ = x :: xs) as E; [ destruct H; hauto | destruct E as [? [? ?]]; subst ]
      end
  | [ H : upd (_ :: _ :: _) _ _ _ _ ?Δ |- _ ] =>
      let E := fresh "E" in
      match Δ with
      | _ :: _ :: _ => fail 1
      | _ => assert (exists x y xs, Δ = x :: y :: xs) as E; [ destruct H; hauto | destruct E as [? [? [? ?]]]; subst ]
      end
  end.

(* Generates hypotheses by reassociating known joins.
 Useful in proof search. *)
Ltac join_reassoc :=
  match goal with
  | [ H1 : join ?A ?B ?C, H2 : join ?C ?D ?E |- _] =>
      destruct (join_assoc H1 H2) as [?G [?J1 ?J2]];
      destruct (join_assoc (join_comm H1) H2) as [?G [?J ?J]]
  | [ H1 : join ?A ?B ?C, H2 : join ?D ?C ?E |- _] =>
      destruct (join_assoc H1 (join_comm H2)) as [?G [?J1 ?J2]];
      destruct (join_assoc (join_comm H1) (join_comm H2)) as [?G [?J ?J]]
  end.

Ltac join_tails :=
  match goal with
  | [ H : join (_ :: ?G1) (_ :: ?G2) (_ :: ?G3) |- _] =>
      assert (join G1 G2 G3) by (clear - H; sauto)
  end.

(* Tactics to make using red_cong easier *)
Ltac applyl_cong H :=
  match type of H with
  | ?P ≡ ?Q =>
      match goal with
      | [ |- reduction P ?R ] =>
          let X := fresh "X" in
          enough (reduction Q R) as X;
          [ apply (@red_cong P Q R R H X cong_refl) | ]
      end
  end.

Ltac applyr_cong H :=
  match type of H with
  | ?Q ≡ ?R =>
      match goal with
      | [ |- reduction ?P R ] =>
          let X := fresh "X" in
          enough (reduction P Q) as X;
          [ apply (@red_cong P P Q R cong_refl X H) | ]
      end
  end.

(* Structural properties  *)

(** Exchange *)
Theorem perm_has_type :
  forall {Γ Γ' : ctx},
    Permutation Γ Γ' ->
    forall {P}, has_type P Γ -> has_type P Γ'.
Proof.
  intros * P ? H. revert Γ' P.
  induction H; intros ? ?P.
  - destruct (perm_upd_rel _ _ P H) as (? & ? & ? & ?).
    eapply has_close. eassumption. eapply (perm_exh _ _ _ _ _ ); eassumption.
  - destruct (perm_upd_rel _ _ P0 H) as (? & ? & ? & P1).
    specialize (IHhas_type _ P1); hauto use: has_wait.
  - destruct (perm_join _ _ _ _ _ _ _ P H) as (? & ? & P3 & P4 & H').
    apply (has_cut H' (IHhas_type1 _ (perm_skip (A, one) P3))
                      (IHhas_type2 _ (perm_skip (dual A, one) P4))).
Qed.

(** Weakening *)
Theorem weak_has_type :
  forall {P Γ},
    has_type P Γ ->
    forall {A α}, hal α -> has_type P ((A, α) :: Γ).
Proof.
  intros * H. induction H.
  - intros; refine (@has_close ((A, α) :: G) ((A, α) :: G') (S n) _ _); sauto l: on.
  - intros; refine (@has_wait ((A, α) :: G) ((A, α) :: G') (S n) _ _ _); hauto.
  - intros.
    assert (has_type P1 ((A, one) :: (A0, α) :: G1)) as ?TP1;
      [ sfirstorder use: perm_has_type, perm_swap | ].
    assert (has_type P2 ((dual A, one) :: (A0, α) :: G2)) as ?TP2;
      [ sfirstorder use: perm_has_type, perm_swap | ].
    assert (join ((A0, α) :: G1) ((A0, α) :: G2) ((A0, α) :: G)) as ?J;
      [ sauto | ].
    apply (@has_cut _ _ _ A P1 P2 J TP1 TP2).
Qed.

(* Progress  *)

(* The following lemma is useful for ruling out impossible cases. *)
(* Remark: special case of `upd_exh_inv` in list.v *)
Lemma upd_exh {n A B} {G G' : ctx} :
  upd_rel ((A, one) :: G) n (B, one) (B, zero) G' ->
  exh G' ->
  A = B /\ exh G.
Proof. intros U E; dependent induction U; sauto q: on. Qed.

Theorem progress (P Q : process) (G : ctx) :
  has_type (cut P Q) G -> exists R, reduction (cut P Q) R.
Proof.
  intros HT. sdepinvert HT.
  dependent induction P;
  dependent induction Q;
  dependent induction A;
  simpl in *;

  try match goal with
  | [ H : has_type close ((⊥, one) :: _) |- _ ] =>
      (* impossible case *)
      inversion H; hauto use: upd_exh
  | [ |- exists R : process, reduction (cut close (wait ?Q)) R ] =>
      (* genuine reduction *)
      exists Q; apply beta_one_bot
  | [ |- exists R : process, reduction (cut (wait ?Q) close) R ] =>
      exists Q; apply (red_cong cut_comm beta_one_bot cong_refl)
  | [ |- exists R : process, reduction (cut (cut ?P1 ?P2) (wait ?Q)) R] =>
      exists (wait (cut Q (cut P1 P2)));
      applyl_cong (@cut_comm (cut P1 P2) (wait Q));
      apply kappa_cut_wait
  | [ H : has_type (wait ?P) ((𝟙, one) :: _) |- _ ] =>
      (* impossible case *)
      inversion H; hauto l: on use: upd_exh
  | [ |- exists R : process, reduction (cut (cut _ _) (cut _ _)) R] =>
      repeat match goal with
             | [ H : has_type (cut _ _) _ |- _ ] => sdepinvert H
             end;
      match goal with
      | [ IH :
          forall (Q : process) (G G1 G2 : ctx) (A : ty),
            join G1 G2 G -> has_type ?P1 ((A, one) :: G1) ->
            has_type Q ((dual A, one) :: G2) ->
            exists R : process, reduction (cut ?P1 Q) R,
          TP1 : has_type ?P1 ((?A, one) :: ?G1),
          TP2 : has_type ?P2 ((dual ?A, one) :: ?G2),
          J : join ?G1 ?G2 _ |- _ ] =>
          destruct (IH P2 _ _ _ A J TP1 TP2) as [?R ?Red];
          clear - Red; sauto lq: on
      end
  end.
  
  - (* |- exists R : process, reduction (cut close (cut Q1 Q2)) R *)
    match goal with
    | [ H : has_type (cut _ _) ((⊥, one) :: _) |- _ ] => sdepinvert H
    end;
    match goal with
    | [ H : join _ _ (_ :: _) |- _] => destruct (destruct_join H0) as [? [? [? [? [? [? [? ?]]]]]]]; subst
    end;
    match goal with
    | [ H : join _ _ one |- _] => inversion H; subst
    end;
    match goal with
    | [ Hw : has_type ?Qi ((?Ai, ?ai) :: (⊥, one) :: ?Di),
          Hother : has_type ?Qo (_ :: (⊥, zero) :: ?Dj),
          Hc : has_type close (_ :: ?G1) |- _] =>
        let HQ := fresh "H" in
        let T  := fresh "H" in
        let HC := fresh "H" in
        assert (has_type Qi ((⊥, one) :: (Ai, ai) :: Di)) as HQ
          by (qauto use: perm_has_type, perm_swap);
        assert (has_type close ((Ai, zero) :: (𝟙, one) :: G1)) as T
          by (apply weak_has_type; [ auto | constructor ]);
        assert (has_type close ((𝟙, one) :: (Ai, zero) :: G1)) as HC
          by (qauto use: perm_has_type, perm_swap);
        clear T; join_tails; join_reassoc; join_reassoc;
        match goal with
        | [ _ : join G1 Di ?G |- _ ] =>
            assert (join ((Ai, zero) :: G1) ((Ai, one) :: Di) ((Ai, one) :: G)) by hauto
        | [ _ : join Di G1 ?G |- _ ] =>
            assert (join ((Ai, zero) :: G1) ((Ai, one) :: Di) ((Ai, one) :: G)) by (apply join_comm; hauto)
        end;
        assert (exists R, reduction (cut close Qi) R) as ER by strivial;
        destruct ER as [?R ?Red];
        exists (cut R Qo);
        idtac
    end.
    (* help sauto along later, because it is *slow* *)
    sauto.
    sauto.

  - (* |- exists R : process, reduction (cut close (cut Q1 Q2)) R *)
    match goal with
    | [ H : has_type (cut _ _) ((𝟙, one) :: _) |- _ ] => sdepinvert H
    end;
    match goal with
    | [ H : join _ _ (_ :: _) |- _] => destruct (destruct_join H0) as [? [? [? [? [? [? [? ?]]]]]]]; subst
    end;
    match goal with
    | [ H : join _ _ one |- _] => inversion H; subst
    end.
    + match goal with
       | [ Hw : has_type ?Qi ((?Ai, ?ai) :: (𝟙, one) :: ?Di),
            Hother : has_type ?Qo (_ :: (𝟙, zero) :: ?Dj),
            Hc : has_type (wait ?Q) (_ :: ?G1) |- _] =>
          let HQ := fresh "H" in
          let T  := fresh "H" in
          let HC := fresh "H" in
          assert (has_type Qi ((𝟙, one) :: (Ai, ai) :: Di)) as HQ
            by (qauto use: perm_has_type, perm_swap);
          assert (has_type (wait Q) ((Ai, zero) :: (⊥, one) :: G1)) as T
            by (apply weak_has_type; [ auto | constructor ]);
          assert (has_type (wait Q) ((⊥, one) :: (Ai, zero) :: G1)) as HC
            by (qauto use: perm_has_type, perm_swap);
          clear T; join_tails; join_reassoc; join_reassoc;
          match goal with
          | [ _ : join G1 Di ?G |- _ ] =>
              assert (join ((Ai, zero) :: G1) ((Ai, one) :: Di) ((Ai, one) :: G)) by hauto;
              assert (join ((Ai, one) :: G1) ((Ai, zero) :: Di) ((Ai, one) :: G)) by (apply join_comm; hauto);
              assert (join ((Ai, zero) :: Di) ((Ai, one) :: G1) ((Ai, one) :: G)) by hauto;
              assert (join ((Ai, one) :: Di) ((Ai, zero) :: D1) ((Ai, one) :: G)) by (apply join_comm; hauto)
          | [ H : join Di G1 ?G |- _ ] =>
              assert (join ((Ai, zero) :: G1) ((Ai, one) :: Di) ((Ai, one) :: G)) by (apply join_comm; hauto);
              assert (join ((Ai, one) :: G1) ((Ai, zero) :: Di) ((Ai, one) :: G)) by (apply join_comm; hauto);
              assert (join ((Ai, zero) :: Di) ((Ai, one) :: G1) ((Ai, one) :: G)) by (apply join_comm; hauto);
              assert (join ((Ai, one) :: Di) ((Ai, zero) :: G1) ((Ai, one) :: G)) by (apply join_comm; hauto)
          end
       end;
       assert (exists R, reduction (cut (wait P) Q1) R); hauto l: on.
    + assert (exists R, reduction (cut (wait P) Q2) R); hauto l: on.

  - (* |- exists R : process, reduction (cut (cut P1 P2) close) R *)
    repeat match goal with
           | [ H : has_type (cut _ _) _ |- _ ] => sdepinvert H
           end;
    match goal with
    | [ IHP1 :
        forall (Q : process) (G G1 G2 : ctx) (A : ty),
          join G1 G2 G -> has_type ?P1 ((A, one) :: G1) ->
          has_type Q ((dual A, one) :: G2) ->
          exists R : process, reduction (cut ?P1 Q) R,
        TP1 : has_type ?P1 ((?A, one) :: ?G1),
        TP2 : has_type ?P2 ((dual ?A, one) :: ?G2),
        J : join ?G1 ?G2 _ |- _ ] =>
        destruct (IHP1 P2 _ _ _ A J TP1 TP2) as [?R ?Red];
        clear - Red; sauto lq: on rew: off
    end.
Qed.