(** ** Typing, Context Morphism Lemmas,  Preservation and progress *)
(** version with ctx as vectors*)

Require Import core fintype stlc step.
(*From Chapter9 Require Export reduction.*)
Import ScopedNotations.
Require Import Arith.

From Hammer Require Import Tactics.

(* Length-indexed polymorphic lists *)
Inductive vlist (A : Type) : nat -> Type :=
| vnil : vlist A 0
| vcons : A -> forall n, vlist A n -> vlist A (S n).

Arguments vnil {A}.
Arguments vcons {A} _ {n} _.

(** A context *)
Definition ctx n := vlist ty n.

Inductive VLookup {A : Type} : forall {n}, vlist A n -> fin n -> A -> Prop :=
| VLookup_here : forall n (x : A) (xs : vlist A n),
    VLookup (vcons x xs) None x
| VLookup_there : forall n (x y : A) (xs : vlist A n) (i : fin n),
    VLookup xs i y ->
    VLookup (vcons x xs) (Some i) y.

Notation "Gamma ( x ) = T" := (VLookup Gamma x T) (at level 20, x at next level).

(* Lookup in a context with fin indices *)
(* Update relation with fin indices *)
Inductive VUpdate {A : Type} : forall {n}, vlist A n -> fin n -> A -> vlist A n -> Prop :=
| VUpdate_here : forall n (x y : A) (xs : vlist A n),
    VUpdate (vcons x xs) None y (vcons y xs)
| VUpdate_there : forall n (x : A) (xs xs' : vlist A n) (i : fin n) (y : A),
    VUpdate xs i y xs' ->
    VUpdate (vcons x xs) (Some i) y (vcons x xs').


(** Typing predicate *)
Inductive has_type {n} (Gamma : ctx n) : tm n -> ty -> Prop :=
| ty_var_tm (x : fin n) T :
    VLookup Gamma x T ->
    has_type Gamma (var_tm x) T 
| ty_abs (S1 S2 : ty) (M : tm (S n)) :
    @has_type (S n) (vcons S1 Gamma) M S2 ->
    has_type Gamma (lam S1 M) (Fun S1 S2)
| ty_app (T S : ty) (M N : tm n) :
    has_type Gamma M (Fun T S) ->
    has_type Gamma N T ->
    has_type Gamma (app M N) S.
Notation "Gamma |- M : T" := (has_type Gamma M T) (at level 20, M at level 99).


(** Context renaming 
Definition ltc {k k'} (Gamma: ctx k) (Delta: ctx k') rho := forall x, Delta (rho x) = Gamma x.
*)
Definition ltc {k k'} (Gamma: ctx k) (Delta: ctx k') (rho: fin k -> fin k') := 
  forall (x : fin k) T, VLookup Gamma x T -> VLookup Delta (rho x) T.
(** Context renaming lemma *)
Lemma typing_ren n k (Gamma: ctx n) (Delta: ctx k) (rho: fin n -> fin k) (M: tm n) T :
  ltc Gamma Delta rho  -> Gamma |- M : T ->  Delta |- (M⟨rho⟩) : T.
Proof.
  intros C H. revert k Delta rho C. induction H; intros; cbn; eauto.
  - unfold ltc in C.  apply ty_var_tm. now apply C.  
  - constructor. apply IHhas_type. asimpl. unfold ltc. auto_case.
  -- intros. unfold funcomp, shift.
  inv H0. apply VLookup_there. now apply C.
  -- intros. sauto lq: on dep: on.
  - econstructor; eauto.
Qed.
(*
Lemma ltc_shift n (Delta : ctx n) T :
 ltc Delta (vcons T Delta) (fun x => Some x).
Proof.
 intros x T' H.
 apply VLookup_there.
 exact H.
Qed.
*)
Lemma typing_inst n k (Gamma: ctx n) (Delta: ctx k) (sigma: fin n -> tm k) (M: tm n) T :
 (forall x T, VLookup Gamma x T -> Delta |- sigma x : T) -> 
 Gamma |- M : T -> Delta |- (M[sigma]) : T.
 Proof.
  intros C H. revert k Delta sigma C. induction H; intros; asimpl; eauto.
  - constructor. apply IHhas_type. auto_case.
    + intros.  
    apply typing_ren with (Gamma := Delta) . 
     2: apply C; inv H0; assumption .
     unfold ltc. intros. 
     hauto l: on .
     
    + sauto lq: on dep: on.  (*eapply typing_ren; eauto. intros. unfold ltc. now asimpl.
     + constructor.*)
  - econstructor; eauto.
Qed.

Lemma preservation k (Gamma: ctx k) M T :
  Gamma |- M : T -> forall M', step M M' -> Gamma |- M' : T.
Proof.
  induction 1 as [k Gamma x | k Gamma T S M A IHA | k Gamma T S M N A IHA B IHB]; intros M' H'; cbn.
  - inv H'.
  - inv H'. econstructor. now apply IHA.
  - inv H'.
    + inv A. eapply typing_inst; try eassumption.
      auto_case. constructor. now inv H.
      ++ sauto lq: on dep: on .
      
          + eapply ty_app; eauto.
    + eapply ty_app; eauto.
Qed.


(** progress *)

Lemma canonical_forms_fun : forall (M : tm 0) T1 T2,
  has_type vnil M (Fun T1  T2) ->
  value M ->
  exists N U, M = (lam U N).
Proof.
sauto lq: on .
Qed.    


Lemma progress0   (M : tm 0)  : forall T,
  has_type vnil M  T -> value M \/ exists (M' : tm 0), step M M'.  
  Proof.
    dependent induction M; intros. 
  - (* var *)
    inv H.  inv H.
  - (* app *)
    right.
    inversion H; clear H; subst.
    (* inversion H6; clear H6; subst. *)
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
