(* ======================================================= *)
(* Contexts as total functions                             *)
(* ======================================================= *)

From Stdlib.Logic Require Import FunctionalExtensionality.
From Hammer Require Import Tactics.
From Autosubst Require Import core.
From VST Require Import eq_dec sepalg sepalg_generators.

Section TotalFunCtx.
Variable D: Type. (* Function domain *)
Variable R: Type. (* Resources *)
Variable A: Type. (* Resource algebra *)
Variable JA: Join A.
#[global] Generalizable All Variables.

(* ------------------------------------- *)
(* Basic definitions and properties      *)
(* ------------------------------------- *)

Definition fctx : Type := (D -> R * A).

(* Apply functions pointwise to elements of a context. *)
Definition map (f : R -> R) (g : A -> A) (C : fctx) : fctx :=
  fun x => let (T, m) := C x in (f T, g m).

Definition ren_fctx (π : D -> D) (C : fctx) : fctx := fun x => C (π x).
Hint Transparent ren_fctx : core.

Definition ctx_forall (P : A -> Prop) : fctx -> Prop :=
  fun C => forall x, P (snd (C x)).
Hint Transparent ctx_forall : core.

Definition empty_fctx default : fctx := fun _ => default.

Definition lookup : fctx -> D -> R * A := fun C x => C x.
Hint Transparent lookup : core.

Definition upd `{EqDec D} : fctx -> D -> (R * A) -> fctx :=
  fun C x ra x' => if eq_dec x x' then ra else C x'.
Hint Transparent upd : core.

(* Generic relational update — no EqDec required *)
Definition upd_rel (C : fctx) (x : D) (ra : R * A) (C' : fctx) : Prop :=
  forall x',
    (x' = x -> C' x' = ra) /\
    (x' <> x -> C' x' = C x').

#[global] Instance Join_fctx : Join fctx :=
  Join_fun _ _ (Join_prod _ (Join_equiv _) _ JA).

(** Properties of update **)

Lemma ctx_forall_upd `{EqDec D} {C : fctx} {P m} :
  ctx_forall P C -> P m -> forall x A, ctx_forall P (upd C x (A, m)).
Proof. intros ? ? x ? y. unfold upd. destruct (eq_dec x y); auto. Qed.

(* Updating the same index twice is the same as the last update. *)
Property upd_overwrite `{EqDec D} (C : fctx) (x : D) (ra1 ra2 : R * A) :
  upd (upd C x ra1) x ra2 = upd C x ra2.
Proof.
  intros; apply functional_extensionality; intro y.
  unfold upd. destruct (eq_dec x y); reflexivity.
Qed.

(* Commutativity of update *)
Property upd_comm `{EqDec D} {C x y ra1 ra2} :
  x <> y ->
  upd (upd C x ra1) y ra2 = upd (upd C y ra2) x ra1.
Proof.
  intros * Hneq; apply functional_extensionality; intro z.
  unfold upd. destruct (eq_dec x z) as [->|?], (eq_dec y z) as [->|?]; try reflexivity.
  exfalso; now apply Hneq.
Qed.

(** Properties of relational update **)

(* The functional update satisfies the relational spec *)
Property upd_rel_self `{EqDec D} (C : fctx) (x : D) (ra : R * A) :
  upd_rel C x ra (upd C x ra).
Proof.
  intros x'. split.
  - intros ->. unfold upd. destruct (eq_dec x x) as [_|contra]; [reflexivity|contradiction].
  - intros Hneq. unfold upd. destruct (eq_dec x x') as [Heq|_]; [congruence|reflexivity].
Qed.

(* Relational ↔ functional equivalence (requires EqDec + functional extensionality) *)
Property upd_rel_iff_fun `{EqDec D} :
  forall (C : fctx) (x : D) (ra : R * A) (C' : fctx),
    upd_rel C x ra C' <-> C' = upd C x ra.
Proof.
  intros C x ra C'. split.
  - intros Hrel. apply functional_extensionality; intro x'.
    destruct (eq_dec x x') as [->|Hneq].
    + specialize (Hrel x') as [Hit _]. hauto unfold: upd.
    + specialize (Hrel x') as [_ Hmiss]. hauto unfold: upd.
  - intros ->. apply upd_rel_self.
Qed.

Property lookup_update_hit `{EqDec D} (C : fctx) (x : D) (ra : R * A) :
  (upd C x ra) x = ra.
Proof. intros. unfold upd. destruct (eq_dec x x) as [_|contra]; [reflexivity|contradiction]. Qed.

Property lookup_update_miss `{EqDec D} (C : fctx) {x y} (ra : R * A) :
  x <> y -> (upd C x ra) y = C y.
Proof. intros. unfold upd. destruct (eq_dec x y) as [Heq|_]; [congruence|reflexivity]. Qed.

(* Same lookup facts stated via the relational view (no EqDec needed) *)

Property upd_rel_hit {C x ra C'} :
  upd_rel C x ra C' -> C' x = ra.
Proof. intros Hrel. specialize (Hrel x) as [Hit _]. now apply Hit. Qed.

Property upd_rel_miss {C x y ra C'} :
  upd_rel C x ra C' -> x <> y -> C' y = C y.
Proof. intros Hrel ?. specialize (Hrel y) as [_ Hmiss]. now apply Hmiss. Qed.

(* ------------------------------------- *)
(* Renamings and permutations            *)
(* ------------------------------------- *)

(** Renaming **)

Property ren_fctx_id (C : fctx) :
  ren_fctx id C = C.
Proof. reflexivity. Qed.

Property ren_fctx_trans (π1 π2 : D -> D) (C : fctx) :
  ren_fctx π1 (ren_fctx π2 C) = ren_fctx (funcomp π2 π1) C.
Proof. reflexivity. Qed.

Property ctx_forall_ren (π : D -> D) {C : fctx} {P} :
  ctx_forall P C -> ctx_forall P (ren_fctx π C).
Proof. intros Hfor ?; apply Hfor. Qed.

Property merge_ren {C1 C2 C : fctx} (π : D -> D) :
  join C1 C2 C -> join (ren_fctx π C1) (ren_fctx π C2) (ren_fctx π C).
Proof. intros J; split; apply J. Qed.

(* Bijective renamings *)

Class bijection (D : Type) :=
{ ren_fun       : D -> D;
  ren_inv       : D -> D;
  ren_left_inv  : forall x, ren_inv (ren_fun x) = x;
  ren_right_inv : forall x, ren_fun (ren_inv x) = x }.

Lemma ren_inv_compose `{bijection D} :
  funcomp ren_inv ren_fun = id /\ funcomp ren_fun ren_inv = id.
Proof. split; extensionality x; eauto using ren_left_inv, ren_right_inv. Qed.

(* Injectivity and surjectivity follow from the inverse laws *)
Lemma ren_inj `{bijection D} :
  forall x y, ren_fun x = ren_fun y -> x = y.
Proof. intros. rewrite <- (ren_left_inv x), <- (ren_left_inv y). now rewrite H0. Qed.

Lemma ren_surj `{bijection D} :
  forall y, exists x, ren_fun x = y.
Proof. intros y. exists (ren_inv y). apply ren_right_inv. Qed.

Instance bijection_id : bijection D :=
{| ren_fun       := id;
   ren_inv       := id;
   ren_left_inv  := fun _ => eq_refl;
   ren_right_inv := fun _ => eq_refl |}.

Instance bijection_sym `{bijection D} : bijection D :=
{| ren_fun       := ren_inv;
   ren_inv       := ren_fun;
   ren_left_inv  := ren_right_inv;
   ren_right_inv := ren_left_inv |}.

Program Instance bijection_trans {D : Type}
        (b1 : bijection D) (b2 : bijection D) : bijection D :=
{|
  ren_fun := fun x => @ren_fun D b2 ( @ren_fun D b1 x);
  ren_inv := fun x => @ren_inv D b1 ( @ren_inv D b2 x);
  ren_left_inv := fun x =>
    eq_trans (f_equal ( @ren_inv D b1) ( @ren_left_inv D b2 ( @ren_fun D b1 x)))
             ( @ren_left_inv D b1 x);
  ren_right_inv := fun x =>
    eq_trans (f_equal ( @ren_fun D b2) ( @ren_right_inv D b1 ( @ren_inv D b2 x)))
             ( @ren_right_inv D b2 x) |}.

Property bij_ren_inj `{bijection D} :
  forall (C1 C2 : fctx),
    ren_fctx ren_fun C1 = ren_fctx ren_fun C2 -> C1 = C2.
Proof.
  intros C1 C2 E1.
  pose proof (f_equal (ren_fctx ren_inv) E1) as E2.
   now repeat rewrite ren_fctx_trans, (proj2 ren_inv_compose) in E2.
Qed.

Property bij_ren_lookup `{bijection D} :
  forall (C : fctx) (x : D),
    (ren_fctx ren_inv C) (ren_fun x) = C x.
Proof. intros. unfold ren_fctx. rewrite ren_left_inv. reflexivity. Qed.

Property bij_ren_fctx_upd `{EqDec D} `{bijection D} :
  forall (C : fctx) (x : D) (ra : R * A),
    ren_fctx ren_fun (upd C x ra) = upd (ren_fctx ren_fun C) (ren_inv x) ra.
Proof.
  intros; extensionality y; unfold upd, ren_fctx.
  destruct (eq_dec (ren_inv x) y).
  1: assert (ren_fun y = x) by (hauto lq: on rew: off use: ren_right_inv).
  2: assert (ren_fun y <> x) by (scongruence use: ren_left_inv).
  all: destruct (eq_dec x (ren_fun y)); scongruence.
Qed.

Corollary bij_ren_fctx_upd_sym `{EqDec D} `{bijection D} :
  forall (C : fctx) (x : D) (ra : R * A),
    ren_fctx ren_inv (upd C x ra) = upd (ren_fctx ren_inv C) (ren_fun x) ra .
Proof. exact (@bij_ren_fctx_upd _ (@bijection_sym H0)). Qed.

(** Context merge **)

Property merge_upd `{EqDec D} {C1 C2 C : fctx} (x : D) (r : R) {a1 a2 a : A} :
  join C1 C2 C ->
  join a1 a2 a ->
  join (upd C1 x (r, a1)) (upd C2 x (r, a2)) (upd C x (r, a)).
Proof.
  intros HjoinC HjoinA y; unfold upd; specialize (HjoinC y).
  destruct (eq_dec x y); [split|]; eauto.
Qed.

Property merge_pointwise_fun {C C1 C2 : fctx} :
  join C1 C2 C <->
  forall x : D,
    fst (C x) = fst (C1 x) /\
    fst (C x) = fst (C2 x) /\
    join (snd (C1 x)) (snd (C2 x)) (snd (C x)).
Proof.
  split.
  - intros Hjoin x; specialize (Hjoin x).
    destruct (C1 x), (C2 x), (C x).
    inversion Hjoin. inversion H. rewrite H1, H2. tauto.
  - intros Hpoint x; destruct (Hpoint x) as (? & ? & ?).
    destruct (C1 x), (C2 x), (C x).
    simpl in *; subst; constructor; eauto.
Qed.

Lemma ctx_forall_join {C1 C2 C : fctx} P :
  (forall m1 m2 m, join m1 m2 m -> P m1 -> P m2 -> P m) ->
  join C1 C2 C ->
  ctx_forall P C1 -> ctx_forall P C2 -> ctx_forall P C.
Proof. intros Hm Hjoin ? ? x; destruct (Hjoin x) as [? J2]; now eapply (Hm _ _ _ J2). Qed.

Lemma ctx_forall_join' {C1 C2 C : fctx} P :
  (forall m1 m2 m, join m1 m2 m -> P m -> P m1 /\ P m2) ->
  join C1 C2 C ->
  ctx_forall P C -> ctx_forall P C1 /\ ctx_forall P C2.
Proof. intros; split; intro x; apply (H _ _ _ (proj2 (H0 x)) (H1 x)). Qed.

(* ------------------------------------- *)
(* Algebraic structure                   *)
(* ------------------------------------- *)

Variable CA: Canc_alg A.
Variable PA: Perm_alg A.
Variable SA: Sep_alg A.

#[global] Instance Perm_alg_fctx : Perm_alg fctx.
Proof. sauto use: Perm_fun, Perm_prod, Perm_equiv. Defined.

#[global] Instance Canc_alg_fctx : Canc_alg fctx :=
  Canc_fun _ _ _ (Canc_prod _ (Join_equiv _) _ JA).

#[global] Instance Sep_alg_fctx : Sep_alg fctx.
Proof. sauto use: Sep_fun, Perm_fun, Sep_prod, Perm_prod, Sep_equiv, Perm_equiv. Defined.

(** Properties of `core` **)

(* Lift `core` to context-level predicate **)
Definition core_fctx := (map id core).

(* `core_fctx` corresponds to core from Sep_alg instance *)
Property core_iff_core_fctx :
  core_fctx = @core fctx _ _.
Proof. extensionality C; extensionality x. unfold core_fctx, core, Sep_alg_fctx, map; hauto q: on. Qed.

Property core_fctx_unit (C : fctx) :
  join (core_fctx C) C C.
Proof. rewrite core_iff_core_fctx; apply core_unit. Qed.

Property ctx_forall_core (P : A -> Prop) (C : fctx) :
  (forall x, P (core (snd (C x)))) -> ctx_forall P (core_fctx C).
Proof. intros H x; unfold core_fctx, map; specialize (H x); qauto l: on. Qed.

End TotalFunCtx.

Global Arguments lookup {D R A} _ _.
Global Arguments upd {D R A H} _ _ _ _.
Global Arguments ren_fctx {D R A}.
Global Arguments ctx_forall {D R A}.
Global Arguments bijection {D}.

(* ------------------------------------- *)
(* Resource-algebraic properties         *)
(* ------------------------------------- *)

From CARVe Require Import resalg.

Section ResAlg.
Variable D: Type. (* Function domain *)
Variable R: Type. (* Resources *)
Variable A: Type. (* Resource algebra *)
Variable JA: Join A.
Variable RA: Res_alg A.
#[global] Arguments fctx {D R A}.
#[global] Arguments core_fctx {D R A JA SA} _.

Definition exh : (@fctx D R A) -> Prop := ctx_forall hasW.
Hint Transparent exh : core.

Property core_genv_exh {PA: Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A} (C : fctx) :
  exh (core_fctx C).
Proof. apply ctx_forall_core; auto using hasW_core. Qed.

(* If C1 ⋈ C2 = C and exh(C1), then C2 = C *)
Property join_id {IA: IdRes_alg A} {C C1 C2 : fctx} :
  join C1 C2 C -> exh C1 -> C2 = C.
Proof.
  intros. apply functional_extensionality; intro x.
  specialize (H x); specialize (H0 x).
  destruct (C1 x) as [? a1], (C2 x) as [? a2], (C x) as [? a].
  inversion H as [J1 J2]. inversion J1. qauto l: on use: hasW_identity2.
Qed.

Property ctx_join_contract {PA: Perm_alg A} {C1 C2 C1' C2' C12 C C' : @fctx D R A} :
  ctx_forall hasC C' ->
  join C1 C' C1' -> join C2 C' C2' ->
  join C1 C2 C12 -> join C12 C' C ->
  join C1' C2' C.
Proof.
  intros HC J1 J2 J12 J x.
  specialize (J1 x); specialize (J2 x); specialize (J12 x); specialize (J x).
  constructor.
  - sfirstorder.
  - specialize (HC x). scrush use: hasC_join_distrib'.
Qed.

Property id_join {PA: Perm_alg A} {SA: Sep_alg A} {IA: IdRes_alg A} {C : @fctx D R A} :
  exh C -> join C C C.
Proof.
  intros Hexh x. specialize (Hexh x).
  destruct (C x) as [r a]. split; [constructor|]; try reflexivity.
  apply hasW_identity2 in Hexh. apply identity_unit. assumption. econstructor; now eapply identity_self_join.
Qed.

End ResAlg.

Global Arguments exh {D R A JA RA}.
Global Arguments join_id {D R A JA RA IA C C1 C2}.