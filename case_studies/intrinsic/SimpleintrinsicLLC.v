(* ============================================ *)
(* Weak normalization, no redn. under binders.  *)
(* ============================================ *)

(* Related work: doi.org/10.1145/3372885.3373818 *)

(* Library imports *)
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Unicode.Utf8.
From Coq Require Import Lia.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.

(* Separation logic imports *)
Require Import VST.msl.functors.
Require Import VST.msl.sepalg.

(* CARVe imports *)
From CARVe.contexts Require Import list.
From CARVe.algebras Require Import purely_linear.

(* General settings *)
Set Implicit Arguments.

(* Tactics *)
Ltac inv H := dependent destruction H; subst; clear H; trivial.

(* ----------------------------------- *)
(* Types and intrinsically-typed terms *)
(* ----------------------------------- *)

Inductive ty : Type :=
| ty_Unit  : ty
| ty_Arrow : ty → ty → ty.

Definition tenv := lctx ty mult.

(* TODO: add other constructors and generalize algebra? *)
Inductive tm (Δ : tenv) : ty → Type :=
| var  : forall {t Δ'}, upd Δ t t one zero Δ' → exh hal Δ' → tm Δ t
| ut   : exh hal Δ → tm Δ ty_Unit
| llam : forall {t1 t2}, tm ((t1, one) :: Δ) t2 → tm Δ (ty_Arrow t1 t2)
| lapp : forall {t1 t2 Δ₁ Δ₂},
    tm Δ₁ (ty_Arrow t1 t2) →
    tm Δ₂ t1 →
    merge Δ₁ Δ₂ Δ →
    tm Δ t2.

(* Notation *)

Declare Custom Entry stlc.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -o T" := (ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x ^ y" := (lapp x y) (in custom stlc at level 1, left associativity).
Notation "/\ y" := (llam y) (in custom stlc at level 90,
                             y custom stlc at level 99,
                             left associativity).

Notation "'Unit'" := ty_Unit (in custom stlc at level 0).
Notation "'unit'" := ut (in custom stlc at level 0).

(* ----------------------------------- *)
(* Structural properties               *)
(* ----------------------------------- *)

(* Exchange at the top level of the context (as relation) *)

Parameter tm_exch_top :
  forall {Δ A₁ A₂ α₁ α₂ B},
    tm ((A₁, α₁) :: (A₂, α₂) :: Δ) B →
    tm ((A₂, α₂) :: (A₁, α₁) :: Δ) B →
    Prop.

(* TODO *)
Lemma tm_exch_top_total :
  forall {Δ A₁ A₂ α₁ α₂ B} (M : tm ((A₁, α₁) :: (A₂, α₂) :: Δ) B),
    exists M', tm_exch_top M M'.
Admitted.

(* Alternatively, not as relation: *)

(* TODO *)
Lemma tm_exch_top' :
  forall {Δ A₁ A₂ α₁ α₂ B},
    tm ((A₁, α₁) :: (A₂, α₂) :: Δ) B →
    tm ((A₂, α₂) :: (A₁, α₁) :: Δ) B.
Admitted.

(* Weakening / strengthening of terms (as relations) *)

Inductive tm_weak : forall {Δ B α},
  tm Δ B → forall (A : ty), hal α → tm ((A, α) :: Δ) B → Prop :=

  | tmweak_lvar :
    forall {Δ Δ' A B α}
           (u  : upd Δ B B one zero Δ')
           (u' : upd ((A, α) :: Δ) B B one zero ((A, α) :: Δ'))
           (e  : exh hal Δ')
           (e' : exh hal ((A, α) :: Δ'))
           (h  : hal α),
      tm_weak (var u e) h (var u' e')

  | tmweak_ut :
    forall {Δ A α}
           (e  : exh hal Δ)
           (e' : exh hal ((A, α) :: Δ))
           (h  : hal α),
      tm_weak (ut e) h (ut e')

  | tmweak_llam :
    forall {Δ A B1 B2 α}
           (M   : tm ((B1, one) :: Δ) B2)
           (M'  : tm (((A, α) :: (B1, one) :: Δ)) B2)
           (M'' : tm ((B1, one) :: ((A, α) :: Δ)) B2)
           (h  : hal α),
      tm_weak M h M' →
      tm_exch_top M' M'' →
      tm_weak (llam M) h (llam M'')

  | tmwk_lapp :
    forall {Δ₁ Δ₂ Δ A B1 B2 α}
           (M : tm Δ₁ (ty_Arrow B1 B2))
           (M' : tm ((A, α) :: Δ₁) (ty_Arrow B1 B2))
           (N  : tm Δ₂ B1)
           (N' : tm ((A, α) :: Δ₂) B1)
           (μ  : merge Δ₁ Δ₂ Δ)
           (μ' : merge ((A, α) :: Δ₁) ((A, α) :: Δ₂) ((A, α) :: Δ))
           (h  : hal α),
      tm_weak M h M' →
      tm_weak N h N' →
      tm_weak (lapp M N μ) h (lapp M' N' μ').

Inductive tm_str : forall {Δ A B},
  tm ((A, zero) :: Δ) B → tm Δ B → Prop :=

  | tmstr_lvar :
    forall {Δ Δ' A B}
           (u  : upd ((A, zero) :: Δ) B B one zero ((A, zero) :: Δ'))
           (u' : upd Δ B B one zero Δ')
           (e  : exh hal ((A, zero) :: Δ'))
           (e' : exh hal Δ'),
      tm_str (var u e) (var u' e')

  | tmst_ut :
    forall {Δ A}
           (e  : exh hal ((A, zero) :: Δ))
           (e' : exh hal Δ),
      tm_str (ut e) (ut e')

  | tmstr_llam :
    forall {Δ A B1 B2}
           (M   : tm ((B1, one) :: ((A, zero) :: Δ)) B2)
           (M'  : tm (((A, zero) :: (B1, one) :: Δ)) B2)
           (M'' : tm ((B1, one) :: Δ) B2),
      tm_exch_top M M' →
      tm_str M' M'' →
      tm_str (llam M) (llam M'')

| tmstr_lapp :
    forall {Δ₁ Δ₂ Δ A B1 B2}
           (M  : tm ((A, zero) :: Δ₁) (ty_Arrow B1 B2))
           (M' : tm Δ₁ (ty_Arrow B1 B2))
           (N  : tm ((A, zero) :: Δ₂) B1)
           (N' : tm Δ₂ B1)
           (μ  : merge ((A, zero) :: Δ₁) ((A, zero) :: Δ₂) ((A, zero) :: Δ))
           (μ' : merge Δ₁ Δ₂ Δ),
      tm_str M M' →
      tm_str N N' →
      tm_str (lapp M N μ) (lapp M' N' μ').

(* TODO *)
Lemma tm_weak_total :
  forall {Δ B α} (M : tm Δ B) (A : ty) (h : hal α),
    exists M', @tm_weak _ _  _  M A h M'.
Admitted.

(* TODO: finish remaining cases *)
Lemma tm_str_total :
  forall {Δ A B} (M : tm ((A, zero) :: Δ) B),
    exists M', tm_str M M'.
Proof.
  intros. dependent induction M.
  - (* Case: M = var u e *)
    dependent destruction u.
    dependent destruction e.
    exists (var u e). apply tmstr_lvar.
  - (* Case: M = ut *)
    dependent destruction e.
    exists (ut e). apply tmst_ut.
  - (* Case: M = llam M1 *)
    specialize (IHM Δ t1).
    admit.
  - (* Case: M = lapp M1 M2 μ1 *)
    admit.
Admitted.

(* Alternatively, not as relation: *)

Lemma tm_weak' : forall {Δ B α},
  tm Δ B → forall (A : ty), hal α → tm ((A, α) :: Δ) B.
Proof.
  intros Δ B α Ht.
  dependent induction Ht; intros.
  - eapply var. econstructor; eauto. hauto l: on.
  - sauto lq: on .
  - econstructor 3. apply tm_exch_top'. sfirstorder.
  - econstructor 4. eapply (IHHt1 A H). eapply (IHHt2 A H).
    constructor; sauto lq: on . 
Qed.

Lemma tm_str' : forall {Δ A B},
  tm ((A, zero) :: Δ) B → tm Δ B.
Proof.
  intros Δ A B Ht.
  dependent induction Ht.
  - assert (exists Δ'', Δ' = ((A, zero) :: Δ'') /\ upd Δ t t one zero Δ'' /\ exh hal Δ'') as E by sauto.
    (* should be immediate: unpack E, then apply (var u' e'). *)
    admit.
  - assert (exh hal Δ) as e' by sauto.
    apply (ut e').
  - eapply llam. apply tm_exch_top' in Ht.
    specialize (IHHt ((t1, one) :: Δ) t1). apply IHHt.
    (* stuck here because of exchange, ~= *)
    admit.
  - assert (exists Δ₁' Δ₂', (Δ₁ = (A, zero) :: Δ₁') /\ (Δ₂ = (A, zero) :: Δ₂') /\ merge Δ₁' Δ₂' Δ) as E by sauto.
    (* will run into issues with ~= *)
    admit.
Admitted.

(* ----------------------------------- *)
(* Linear substitution                 *)
(* ----------------------------------- *)

Inductive lsubst :
  forall {A B Δ₁ Δ₂ Δ},
    tm ((A, one) :: Δ₁) B → tm Δ₂ A → merge Δ₁ Δ₂ Δ → tm Δ B → Prop :=

  | lsubst_lvar :
      forall {Δ' Δ A}
             (u : upd ((A, one) :: Δ') A A one zero ((A, zero) :: Δ'))
             (e : exh hal ((A, zero) :: Δ'))
             (N : tm Δ A)
             (μ : merge Δ' Δ Δ),
        lsubst (var u e) N μ N

  (* Remark: no case for unit since no term (ut e) : tm ((A, one) :: Δ₁) B exists*)

  | lsubst_llam :
      forall {Δ₁ Δ₂ Δ A B₁ B₂}
             (M   : tm ((B₁, one) :: ((A, one) :: Δ₁)) B₂)
             (M'  : tm ((A, one) :: ((B₁, one) :: Δ₁)) B₂)
             (M'' : tm ((B₁, one) :: Δ) B₂)
             (N   : tm Δ₂ A)
             (N'  : tm ((B₁, zero) :: Δ₂) A)
             (μ   : merge Δ₁ Δ₂ Δ),
        tm_exch_top M M' →
        tm_weak N halz N' → (* not taking B₁ as explicit argument? *)
        lsubst M' N' (mg_c B₁ m_10 μ) M'' →
        lsubst (llam M) N μ (llam M'')

  (* Case 1: A¹ is 'sent to the left' *)
  | lsubst_lapp1 :
      forall {A B₁ B₂ Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₁₃ Δ}
             (M₁  : tm ((A, one) :: Δ₁) (ty_Arrow B₁ B₂))
             (M₁' : tm Δ₁₃ (ty_Arrow B₁ B₂))
             (M₂  : tm ((A, zero) :: Δ₂) B₁)
             (M₂' : tm Δ₂ B₁)
             (N   : tm Δ₃ A)
             (μ1  : merge ((A, one) :: Δ₁) ((A, zero) :: Δ₂) ((A, one) :: Δ₁₂))
             (μ2  : merge Δ₁₂ Δ₃ Δ)
             (μ3  : merge Δ₁ Δ₃ Δ₁₃)
             (μ4  : merge Δ₁₃ Δ₂ Δ),
        lsubst M₁ N μ3 M₁' →
        tm_str M₂ M₂' →
        lsubst (lapp M₁ M₂ μ1) N μ2 (lapp M₁' M₂' μ4)

  (* Case 2: A¹ is 'sent to the right' *)
  | lsubst_lapp2 :
      forall {A B₁ B₂ Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₂₃ Δ}
             (M₁  : tm ((A, zero) :: Δ₁) (ty_Arrow B₁ B₂))
             (M₁' : tm Δ₁ (ty_Arrow B₁ B₂))
             (M₂  : tm ((A, one) :: Δ₂) B₁)
             (M₂' : tm Δ₂₃ B₁)
             (N   : tm Δ₃ A)
             (μ1  : merge ((A, zero) :: Δ₁) ((A, one) :: Δ₂) ((A, one) :: Δ₁₂))
             (μ2  : merge Δ₁₂ Δ₃ Δ)
             (μ3  : merge Δ₂ Δ₃ Δ₂₃)
             (μ4  : merge Δ₁ Δ₂₃ Δ),
        tm_str M₁ M₁' →
        lsubst M₂ N μ3 M₂' →
        lsubst (lapp M₁ M₂ μ1) N μ2 (lapp M₁' M₂' μ4).

(* TODO: figure out applying IH in llam case *)
Lemma lsubst_total :
  forall {A B Δ₁ Δ₂ Δ}
         (M : tm ((A, one) :: Δ₁) B)
         (N : tm Δ₂ A)
         (μ : merge Δ₁ Δ₂ Δ),
    exists M', lsubst M N μ M'.
Proof.
  intros A B Δ₁ Δ₂ Δ M N μ. revert Δ₂ Δ N μ.
  dependent induction M.
  - (* Case: M = var u e *)
    intros Δ₂ Δ N μ.
    assert (nhalo : ¬ hal one) by sauto.
    destruct (upd_exh_inv u e nhalo halz) as [E1 E2]; subst.
    inversion e as [| Δ₁' t' a' e'].
    assert (E := exh_id μ e' (fun a b c => mult_hal_unit)); subst.
    exists N. apply lsubst_lvar.
  - (* Case: M = ut (impossible by linearity) *)
    inversion e. sauto.
  - (* Case: M = llam M1 *)
    intros Δ₂ Δ N μ.
    destruct (tm_exch_top_total M) as [M' e].
    destruct (tm_weak_total N t1 halz) as [N' w].
    assert (μ_ext := mg_c t1 m_10 μ).
    specialize (IHM A ((t1, one) :: Δ₁) M').
    (* stuck here because of exchange, ~= *)
    (* destruct (IHM A ((t1, one) :: Δ₁) M' JMeq_refl JMeq_refl
              ((A, zero) :: Δ₂) ((A, one) :: Δ) N' (mg_c t1 m_10 μ)) as [M'' l]. *)
    (* ... *)
    admit.
  - (* Case: M = lapp M1 M2 μ1 *)
    intros Δ3 Δ N μ.
    inversion m as [| A' Δ1 Δ2 Δ12 α₁ α₂ α j μ1]; subst.
    dependent induction j.
    + (* Subcase: (α₁,α₂) = (1,0) *)
      destruct (merge_assoc2 μ1 μ) as [Δ13 [μ3 μ4]].
      destruct (tm_str_total M2) as [M2' s].
      destruct (IHM1 A Δ1 M1 JMeq_refl JMeq_refl Δ3 Δ13 N μ3) as [M1' l].
      exists (lapp M1' M2' μ4).
      apply lsubst_lapp1 with (μ3 := μ3); assumption.
    + (* Subcase: (α₁,α₂) = (0,1) *)
      destruct (merge_assoc μ1 μ) as [Δ23 [μ3 μ4]].
      destruct (tm_str_total M1) as [M1' s].
      destruct (IHM2 A Δ2 M2 JMeq_refl JMeq_refl Δ3 Δ23 N μ3) as [M2' l].
      exists (lapp M1' M2' μ4).
      apply lsubst_lapp2 with (μ3 := μ3); assumption.
Admitted.

(* ----------------------------------- *)
(* Operational semantics               *)
(* ----------------------------------- *)

Inductive step : forall Δ A, tm Δ A → tm Δ A → Prop :=

  | S_Beta_App :
      forall {Δ Δ₁ Δ₂ : tenv} {A B : ty}
             (M  : tm ((A, one) :: Δ₁) B)
             (N  : tm Δ₂ A)
             (μ  : merge Δ₁ Δ₂ Δ)
             (M' : tm Δ B),
        lsubst M N μ M' →
        step (lapp (llam M) N μ) M'

  | S_App1 :
      forall {Δ Δ₁ Δ₂ : tenv} {A B : ty}
             (M M' : tm Δ₁ (ty_Arrow A B))
             (N    : tm Δ₂ A)
             (μ    : merge Δ₁ Δ₂ Δ),
        step M M' →
        step (lapp M N μ) (lapp M' N μ).

(* Multi-step relation *)

Inductive mstep : forall Δ A, tm Δ A → tm Δ A → Prop :=
  | ms_refl :
      forall Δ A (M : tm Δ A), mstep M M
  | ms_step :
      forall Δ A (M N P : tm Δ A),
        step M N →
        mstep N P →
        mstep M P.

(* ----------------------------------- *)
(* Values                              *)
(* ----------------------------------- *)

Definition value {A} (e : tm [] A) : Prop :=
  match e with
  | llam  _
  | ut _ => True
  | _ => False
  end.

Lemma value_arrow_llam :
  forall A B (e : tm [] (ty_Arrow A B)),
    value e → exists M, e = llam M.
Proof.
  intros A B e. dependent destruction e; sfirstorder.
Qed.

(* ----------------------------------- *)
(* Progress                            *)
(* ----------------------------------- *)

(*
(* to put in the algebra *)
Lemma merge_nil_nil :
  forall (Δ₁ Δ₂ : tenv) (H: merge Δ₁ Δ₂ []), Δ₁ = [] ∧ Δ₂ = [].
  intros. now inv H.
Qed.

Lemma progress (A : ty) (M : tm [] A) :
  value M ∨ exists (M' : tm [] A), step M M'.
Proof.
  dependent induction M; intros.
  - (* var *) inv u.
  - (* unit *) sfirstorder.
  - (* lam *) sfirstorder.
  - (* app *)
    right.
    assert (m0 := m).
    dependent destruction m0.
    destruct (IHM1 M1 JMeq_refl JMeq_refl).
    destruct (IHM2 M2 JMeq_refl JMeq_refl).
    + (* M1 is a value *)
      destruct (value_arrow_llam M1 H) as [Mb ->].
      destruct (lsubst_total Mb M2 m) as [Mb' Hβ].
      exists Mb'. constructor; exact Hβ.
    + sauto lq: on.
    + sauto lq: on.
Qed.
*)

(* ----------------------------------- *)
(* Logical predicate                   *)
(* ----------------------------------- *)

Inductive Halts : forall A, tm [] A → Prop :=
  | Halts_c :
      forall A (M V : tm [] A),
        mstep M V → value V → Halts M.

(* by structural recursion on the type *)
Fixpoint Reduce (A : ty) (M : tm [] A) : Prop :=
  match A as A0 return tm [] A0 → Prop with
  | ty_Unit =>
      fun M0 => Halts M0
  | ty_Arrow A1 A2 =>
      fun M0 =>
        (* 1) the term itself halts *)
        Halts M0 ∧
        (* 2) closure under application to any reducible argument,
              along any context split *)
        forall (N : tm [] A1),
          Reduce N →
          Reduce (lapp M0 N mg_n)
  end M.

Notation "M ∈ A" := (Reduce A M) (at level 40).

(* ----------------------------------- *)
(* Lemmas                              *)
(* ----------------------------------- *)

(* Halts is backwards closed w.r.t. one step *)

Lemma Halts_backwards_closed :
  forall A (M M' : tm [] A),
    step M M' →
    Halts M' →
    Halts M.
Proof.
  intros A M M' Hs Hh.
  destruct Hh as [V Hms Hn]. (* Halts_c *)
  eapply Halts_c.
  - (* mstep from M to V: one step, then the chain from Hms *)
    eapply ms_step; eauto.
  - exact H0.
Qed.

(* Reducible terms halt *)

Lemma reduce_halts :
  forall A (M : tm [] A),
    Reduce M → Halts M.
Proof.
  induction A; cbn in *; sfirstorder.
Qed.

(* Main lemma: Reduce is backwards closed w.r.t. one step *)

Lemma Reduce_backwards_closed :
  forall A (M M' : tm [] A),
    step M M' →
    Reduce M' →
    Reduce M.
Proof.
  (* structural induction on the type A, matching the Fixpoint Reduce *)
  induction A as [| A1 IHA1 A2 IHA2]; intros M M' Hs Hred.
  - (* A = ty_Unit *)
    cbn in *. (* Reduce ty_Unit M' = Halts M' *)
    eapply Halts_backwards_closed; eauto.
  - (* A = ty_Arrow A1 A2 *)
    cbn in Hred. destruct Hred as [Hhalt Hclos]. (* Halts M' ∧ closure *)
    split.
    + (* Halts M *)
      eapply Halts_backwards_closed; eauto.
    + (* Closure: for any split and reducible arg, the application reduces *)
      intros N HN.
      (* Hclos gives reducibility for lapp M' N μ; step-congruence S_App1
         and the IH on A2 give reducibility for lapp M N μ. *)
      specialize (Hclos N HN) as Happ'.
      eapply (IHA2 (lapp M N mg_n)).
        * hauto l: on .
        * exact Happ'.
Qed.

(* here are monsters *)