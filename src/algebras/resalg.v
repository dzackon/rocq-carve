(** Generic resource algebra *)

From Stdlib Require Import Logic.Classical.
From VST Require Import sepalg.

Class Res_alg (A : Type) {JA : Join A} := {

  (* Primitive definitions *)
  hasW : A -> Prop;
  hasC : A -> Prop;
  unr a := hasW a /\ hasC a;
  zero a := unr a /\ exists a', unit_for a a' /\ ~ unr a';
  nonzero a := ~ zero a;

  (* Properties of elements satisfying weakening *)
  hasW_identity {a} :
    identity a -> hasW a;
  hasW_join_closed {a1 a2 a} :
    join a1 a2 a -> hasW a1 -> hasW a2 -> hasW a;

  (* Properties of elements satisfying contraction *)
  hasC_idem {a} : join a a a -> hasC a;
  hasC_join_distrib {c a1 a2 a12 a} :
    hasC c ->
    join a1 a2 a12 -> join a12 c a ->
    exists a1' a2',
      join a1 c a1' /\ join a2 c a2' /\ join a1' a2' a;

  (* Properties of 'zero-like' elements *)
  zero_join_collapse {a1 a2 a} :
    join a1 a2 a -> zero a1 -> zero a2 -> a1 = a;
  nonzero_split {a1 a} :
    join_sub a1 a -> nonzero a1 -> a1 = a;
}.
Hint Transparent unr : core.
Hint Transparent zero : core.
Hint Transparent nonzero : core.
Global Arguments zero {A JA Res_alg}.

(* ----------------------------------------- *)
(* Properties of `resalg`                    *)
(* ----------------------------------------- *)

(** Derived properties of `hasW` *)

Property hasW_core {A} {JA: Join A} {PA: Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A} {RA: Res_alg A} :
  forall a, hasW (core a).
Proof. intro. apply hasW_identity, core_identity. Qed.

Property zero_hasW `{Res_alg} {a} :
  zero a -> hasW a.
Proof. unfold zero, unr; tauto. Qed.

(** Derived properties of `hasC` *)

Property hasC_core {A} {JA: Join A} {SA: Sep_alg A} {RA: Res_alg A} :
  forall a, hasC (core a).
Proof. intro. apply hasC_idem, core_duplicable. Qed.

Property hasC_identity {A} {JA: Join A} {PA: Perm_alg A} {SA: Sep_alg A} {RA: Res_alg A} {a} :
  identity a -> hasC a.
Proof. eauto using identity_self_join, hasC_idem. Qed.

Property hasC_idem' {A} {JA: Join A} {PA: Perm_alg A} {SA: Sep_alg A} {RA: Res_alg A} {a} :
  hasC a -> join a a a.
Proof.
  intros Hc.
  destruct (hasC_join_distrib Hc (core_duplicable a) (core_unit a)) as (? & ? & J1 & J2 & ?).
  now destruct (join_eq J2 (core_unit a)); destruct (join_eq J1 (core_unit x0)).
Qed.

Property zero_hasC `{Res_alg} {a} :
  zero a -> hasC a.
Proof. unfold zero, unr; tauto. Qed.

Property hasC_join_distrib' {A} {JA: Join A} {PA: Perm_alg A} {RA: Res_alg A} {a1 a2 a1' a2' a12 a c} :
  hasC c ->
  join a1 c a1' -> join a2 c a2' ->
  join a1 a2 a12 -> join a12 c a ->
  join a1' a2' a.
Proof.
  intros Hc H1c H2c H12 H12c.
  destruct (hasC_join_distrib Hc H12 H12c) as (? & ? & H1c' & H2c' & ?).
  now rewrite (join_eq H1c H1c'), (join_eq H2c H2c').
Qed.

Property hasC_join_closed {A} {JA: Join A} {PA: Perm_alg A} {SA: Sep_alg A} {RA: Res_alg A} {a1 a2 a} :
  join a1 a2 a -> hasC a1 -> hasC a2 -> hasC a.
Proof.
  intros Hj Hc1 Hc2.
  destruct (hasC_join_distrib Hc2 (hasC_idem' Hc1) Hj) as (? & ? & Hj1 & Hj2 & Hj').
  destruct (join_eq Hj Hj1), (join_eq Hj Hj2). exact (hasC_idem Hj').
Qed.

(** Derived properties of zero / nonzero elements *)
(* Remark: almost certainly don't need all of these *)

Property zero_idem {A} {JA: Join A} {PA: Perm_alg A} {SA: Sep_alg A} {RA: Res_alg A} {m} :
  zero m -> join m m m.
Proof. eauto using zero_hasC, hasC_idem'. Qed.

Property join_decomp `{Res_alg} {a1 a} :
  join_sub a1 a -> zero a1 \/ a1 = a.
Proof. intro; eapply imply_and_or2. apply NNPP. eauto using imply_to_or, nonzero_split. Qed.

(* zero multiplicities cannot 'spawn' nonzero ones *)
Property zero_sub `{Res_alg} {a1 a2} :
  join_sub a1 a2 -> zero a2 -> zero a1.
Proof. intros Hj Hz. destruct (join_decomp Hj); subst; assumption. Qed.

Property join_canonical_decomp {A} {JA: Join A} {PA: Perm_alg A} {RA: Res_alg A} {a1 a2 a} :
  join a1 a2 a ->
  (a1 = a /\ a2 = a) \/
  (a1 = a /\ zero a2) \/
  (zero a1 /\ a2 = a).
Proof.
  intros J. destruct (join_decomp (join_join_sub J)); destruct (join_decomp (join_join_sub (join_comm J)));
  eauto using zero_join_collapse.
Qed.

Property canonical_join {A} {JA: Join A} {SA: Sep_alg A} {RA: Res_alg A} {a} :
  nonzero a -> zero (core a) \/ join a a a.
Proof.
  intro. eapply imply_and_or2. apply NNPP. apply imply_to_or. intro Hzero.
  apply core_self_join, (eq_sym (nonzero_split (join_join_sub (core_unit a)) Hzero)).
Qed.

Property nonzero_core_or_unr {A} {JA: Join A} {PA: Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A} {RA: Res_alg A} {a} :
  nonzero a -> zero (core a) \/ unr a.
Proof.
  intro. eapply imply_and_or2. apply NNPP. apply imply_to_or. intro Hzero.
  rewrite (eq_sym (nonzero_split (join_join_sub (core_unit a)) Hzero)).
  split; auto using hasW_core, hasC_core.
Qed.

Property nonzero_char `{Res_alg} {a} :
  nonzero a -> ~ hasW a \/ ~ hasC a \/ (forall a', unit_for a a' -> unr a').
Proof.
  intros Hus. unfold nonzero, zero, unr in *.
  apply not_and_or in Hus; destruct Hus as [Hunr | Hexists].
  - apply not_and_or in Hunr; destruct Hunr; eauto.
  - right; right. intros a' ?.
    pose proof (not_ex_all_not _ _ Hexists a') as Hforall; apply not_and_or in Hforall.
    destruct Hforall as [Hnu | ?]; [exfalso; apply Hnu; assumption|tauto].
Qed.

(* ----------------------------------------- *)
(* `IdRes_alg` class                         *)
(* ----------------------------------------- *)

(** Refined class: harmless => identity (e.g. linear, but not affine) *)

Class IdRes_alg (A : Type) `{Res_alg} :=
  { hasW_identity2 : forall {a}, hasW a -> identity a }.

Property join_hasW {A : Type} {JA: Join A} {PA: Perm_alg A} {SA: Sep_alg A}
                   {CA: Canc_alg A} {RA: Res_alg A} {IA: IdRes_alg A} {a1 a} :
  join_sub a1 a -> hasW a -> a1 = a.
Proof.
  intros [? H1] ?. apply join_comm in H1.
  eapply join_unit1_e. eapply split_identity.
  2: eapply hasW_identity2. all: eassumption.
Qed.