(** ** Typing, Context Morphism Lemmas, Preservation and progress:
context as functions
 *)

Require Import core fintype stlc step.
(*From Chapter9 Require Export reduction.*)
Import ScopedNotations.

From Hammer Require Import Tactics.
(** Context as total functions *)
Definition ctx n := fin n -> ty.

(** Typing predicate *)
Inductive has_type {n} (Gamma : ctx n) : tm n -> ty -> Prop :=
| ty_var_tm (x : fin n) :
    has_type Gamma (var_tm x) (Gamma x)
| ty_abs (S1 S2 : ty) (M : tm (S n)) :
    @has_type (S n) (S1 .: Gamma) M S2 ->
    has_type Gamma (lam S1 M) (Fun S1 S2)
| ty_app (T S : ty) (M N : tm n) :
    has_type Gamma M (Fun T S) ->
    has_type Gamma N T ->
    has_type Gamma (app M N) S.
Notation "Gamma |- M : T" := (has_type Gamma M T) (at level 20, M at level 99).


(** Context renaming *)
Definition ltc {k k'} (Gamma: ctx k) (Delta: ctx k') rho := forall x, Delta (rho x) = Gamma x.

(** Context renaming lemma *)
Lemma typing_ren n k (Gamma: ctx n) (Delta: ctx k) (rho: fin n -> fin k) (M: tm n) T :
  ltc Gamma Delta rho  -> Gamma |- M : T ->  Delta |- (M⟨rho⟩) : T.
Proof.
  intros C H. revert k Delta rho C. induction H; intros; cbn; eauto.
  - unfold ltc in C. rewrite <- C. constructor.
  - constructor. apply IHhas_type. asimpl. unfold ltc. auto_case.
  - econstructor; eauto.
Qed.

Lemma typing_inst n k (Gamma: ctx n) (Delta: ctx k) (sigma: fin n -> tm k) (M: tm n) T :
  (forall x, Delta |- sigma x : Gamma x) -> Gamma |- M : T ->  Delta |- (M[sigma]) : T.
Proof.
  intros C H. revert k Delta sigma C. induction H; intros; asimpl; eauto.
  - constructor. apply IHhas_type. auto_case.
    + eapply typing_ren; eauto. intros. unfold ltc. now asimpl.
    + constructor.
  - econstructor; eauto.
Qed.

Lemma preservation k (Gamma: ctx k) M T :
  Gamma |- M : T -> forall M', step M M' -> Gamma |- M' : T.
Proof.
  induction 1 as [k Gamma x | k Gamma T S M A IHA | k Gamma T S M N A IHA B IHB]; intros M' H; cbn.
  - inv H.
  - inv H. econstructor. now apply IHA.
  - inv H.
    + inv A. eapply typing_inst; try eassumption.
      auto_case. constructor.
    + eapply ty_app; eauto.
    + eapply ty_app; eauto.
Qed.

Print null.

Lemma canonical_forms_fun : forall  (M : tm 0) T1 T2,
  has_type null M (Fun T1  T2) ->
  value M ->
  exists N U, M = (lam U N).
Proof.
sauto lq: on .
Qed.    


Lemma progress0   (M : tm 0)  : forall T,
  has_type null M  T -> value M \/ exists (M' : tm 0), step M M'.  
  Proof.
    dependent induction M; intros. 
    - (* var *)
      sfirstorder.
  - (* app *)
    right.
    inversion H; clear H; subst.
         specialize (IHM1 M1 eq_refl JMeq_refl (Fun T0 T)). 
      destruct (IHM1  H2).
      + (* t1 is a value *)
        apply canonical_forms_fun in H2; [|assumption].
        destruct H2 as [x [t H2]]; subst.
         specialize (IHM2 M2 eq_refl JMeq_refl T0). 
        destruct (IHM2  H4).
        * (* ... and t2 is a value *) eauto.
        * (* ... and t2 can step *) destruct H0 as [t' H0]. eauto.
      + (* t1 can step *)
        destruct H as [t' H]. eauto.
  - (*lam *) sfirstorder. 
Qed.

      
