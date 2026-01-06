From Coq Require Import Logic.FunctionalExtensionality Program.Basics.
From Hammer Require Import Hammer.
From VST.msl Require Import sepalg sepalg_generators.

(* Decidable equality *)
Class EqDec (A : Type) : Type :=
  { eq_dec : forall x y : A, {x = y} + {x <> y} }.

Section TotalFunCtx.
  Variable D: Type. (* Function domain *)
  Variable R: Type. (* Resources *)
  Variable A: Type. (* Resource algebra *)
  Variable JA: Join A.
  Variable CA: Canc_alg A.
  Variable PA: Perm_alg A.
  Variable SA: Sep_alg A.

  #[global] Generalizable All Variables.

  Definition tfctx : Type := (D -> R * A).

  (* ---------------- Algebraic structure ---------------- *)

  #[global] Instance Join_tfctx : Join tfctx :=
    Join_fun _ _ (Join_prod _ (Join_equiv _) _ JA).

  #[global] Instance Perm_alg_tfctx : Perm_alg tfctx.
  Proof. sauto use: Perm_fun, Perm_prod, Perm_equiv. Defined.
  
  #[global] Instance Canc_alg_tfctx : Canc_alg tfctx :=
    Canc_fun _ _ _ (Canc_prod _ (Join_equiv _) _ JA).
  
  #[global] Instance Sep_alg_tfctx : Sep_alg tfctx.
  Proof. sauto use: Sep_fun, Perm_fun, Sep_prod, Perm_prod, Sep_equiv, Perm_equiv. Defined.

  (* ---------------- Exhaustedness ---------------- *)

  Definition exh (hal: A -> Prop): tfctx -> Prop :=
    fun C => forall r, hal (snd (C r)).

  Definition empty_tfctx default : tfctx := fun _ => default.
  
  (* ---------------- Lookup / update ---------------- *)

  Definition lookup : tfctx -> D -> R * A :=
    fun C x => C x.

  Definition upd `{EqDec D} : tfctx -> D -> (R * A) -> tfctx :=
    fun C x ra x' => if eq_dec x x' then ra else C x'.

  (* Generic relational update — no EqDec required *)
  Definition upd_rel (C : tfctx) (x : D) (ra : R * A) (C' : tfctx) : Prop :=
    forall x',
      (x' = x -> C' x' = ra) /\
      (x' <> x -> C' x' = C x').

  (* ---------------- Eta properties ---------------- *)

  Property tfctx_eta (C : tfctx) :
    (fun i => C i) = C.
  Proof. auto using functional_extensionality. Qed.

  (* ---------------- Properties of update ---------------- *)

  (* Updating the same index twice is the same as the last update. *)
  Property upd_overwrite `{EqDec D} (C : tfctx) (x : D) (ra1 ra2 : R * A) :
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

  (* ---------------- Properties of relational update ---------------- *)

  (* The functional update satisfies the relational spec *)
  Property upd_rel_self `{EqDec D} (C : tfctx) (x : D) (ra : R * A) :
    upd_rel C x ra (upd C x ra).
  Proof.
    intros x'. split.
    - intros ->. unfold upd. destruct (eq_dec x x) as [_|contra]; [reflexivity|contradiction].
    - intros Hneq. unfold upd. destruct (eq_dec x x') as [Heq|_]; [congruence|reflexivity].
  Qed.

  (* Relational ↔ functional equivalence (requires EqDec + functional extensionality) *)
  Property upd_rel_iff_fun `{EqDec D} :
    forall (C : tfctx) (x : D) (ra : R * A) (C' : tfctx),
      upd_rel C x ra C' <-> C' = upd C x ra.
  Proof.
    intros C x ra C'. split.
    - intros Hrel. apply functional_extensionality; intro x'.
      destruct (eq_dec x x') as [->|Hneq].
      + specialize (Hrel x') as [Hit _]. hauto unfold: upd.
      + specialize (Hrel x') as [_ Hmiss]. hauto unfold: upd.
    - intros ->. apply upd_rel_self.
  Qed.

  Property lookup_update_hit `{EqDec D} (C : tfctx) (x : D) (ra : R * A) :
    (upd C x ra) x = ra.
  Proof. intros. unfold upd. destruct (eq_dec x x) as [_|contra]; [reflexivity|contradiction]. Qed.

  Property lookup_update_miss `{EqDec D} (C : tfctx) {x y} (ra : R * A) :
    x <> y -> (upd C x ra) y = C y.
  Proof. intros. unfold upd. destruct (eq_dec x y) as [Heq|_]; [congruence|reflexivity]. Qed.

  (* Same lookup facts stated via the relational view (no EqDec needed) *)
  Property upd_rel_hit {C x ra C'} :
    upd_rel C x ra C' -> C' x = ra.
  Proof. intros Hrel. specialize (Hrel x) as [Hit _]. now apply Hit. Qed.

  Property upd_rel_miss {C x y ra C'} :
    upd_rel C x ra C' -> x <> y -> C' y = C y.
  Proof. intros Hrel ?. specialize (Hrel y) as [_ Hmiss]. now apply Hmiss. Qed.

  (* ---------------- Renaming ---------------- *)

  Definition ren_tfctx (π : D -> D) (Δ : tfctx) : tfctx := fun x => Δ (π x).

  Property ren_tfctx_id (Δ : tfctx) :
    ren_tfctx id Δ = Δ.
  Proof. reflexivity. Qed.

  Property ren_tfctx_trans (π₁ π₂ : D -> D) (Δ : tfctx) :
    ren_tfctx π₁ (ren_tfctx π₂ Δ) = ren_tfctx (compose π₂ π₁) Δ.
  Proof. reflexivity. Qed.

  Property tfctx_exh_ren (π : D -> D) {C : tfctx} {hal : A -> Prop} :
    exh hal C -> exh hal (ren_tfctx π C).
  Proof. intros Hexh x. unfold ren_tfctx. apply Hexh. Qed.

  Property merge_ren {C1 C2 C : tfctx} (π : D -> D) :
    join C1 C2 C -> join (ren_tfctx π C1) (ren_tfctx π C2) (ren_tfctx π C).
  Proof. intros J; unfold ren_tfctx; split; apply J. Qed.
  
  (* ---------------- Permutations ---------------- *)

  Class BijectiveRenaming (D : Type) :=
  { ren_fun       : D -> D;
    ren_inv       : D -> D;
    ren_left_inv  : forall x, ren_inv (ren_fun x) = x;
    ren_right_inv : forall x, ren_fun (ren_inv x) = x;
    ren_inj  : forall x y, ren_fun x = ren_fun y -> x = y;
    ren_surj : forall y, exists x, ren_fun x = y }.

  Instance BijectiveRenaming_id : BijectiveRenaming D :=
  {| ren_fun       := id;
     ren_inv       := id;
     ren_left_inv  := fun _ => eq_refl;
     ren_right_inv := fun _ => eq_refl;
     ren_inj  := fun _ _ H => H;
     ren_surj := fun y => ex_intro _ y eq_refl |}.

  Instance BijectiveRenaming_sym `{BijectiveRenaming D} : BijectiveRenaming D :=
  {| ren_fun       := ren_inv;
     ren_inv       := ren_fun;
     ren_left_inv  := ren_right_inv;
     ren_right_inv := ren_left_inv;
     ren_inj  := fun x y H => eq_trans (eq_trans (eq_sym (ren_right_inv x)) (f_equal ren_fun H)) (ren_right_inv y);
     ren_surj := fun y => ex_intro _ (ren_fun y) (ren_left_inv y) |}.

  Program Instance BijectiveRenaming_trans {D : Type}
          (b1 : BijectiveRenaming D) (b2 : BijectiveRenaming D) : BijectiveRenaming D :=
  {|
    ren_fun := fun x => @ren_fun D b2 ( @ren_fun D b1 x);
    ren_inv := fun x => @ren_inv D b1 ( @ren_inv D b2 x);
    ren_left_inv := fun x =>
      eq_trans (f_equal ( @ren_inv D b1) ( @ren_left_inv D b2 ( @ren_fun D b1 x)))
               ( @ren_left_inv D b1 x);
    ren_right_inv := fun x =>
      eq_trans (f_equal ( @ren_fun D b2) ( @ren_right_inv D b1 ( @ren_inv D b2 x)))
               ( @ren_right_inv D b2 x);
    ren_inj := fun _ _ H => @ren_inj D b1 _ _ ( @ren_inj D b2 _ _ H);
    ren_surj := fun y =>
      let '(ex_intro _ y' Hy') := @ren_surj D b2 y in
      let '(ex_intro _ x Hx) := @ren_surj D b1 y' in
      ex_intro _ x (eq_trans (f_equal ( @ren_fun D b2) Hx) Hy')
  |}.

  Property bij_ren_lookup `{BijectiveRenaming D} :
    forall (Δ : tfctx) (x : D),
      (ren_tfctx ren_inv Δ) (ren_fun x) = Δ x.
  Proof. intros. unfold ren_tfctx. rewrite ren_left_inv. reflexivity. Qed.

  Property bij_ren_tfctx_upd `{EqDec D} `{BijectiveRenaming D} :
    forall (C : tfctx) (x : D) (ra : R * A),
      ren_tfctx ren_fun (upd C x ra) = upd (ren_tfctx ren_fun C) (ren_inv x) ra.
  Proof.
    intros; extensionality y; unfold upd, ren_tfctx.
    destruct (eq_dec (ren_inv x) y).
    1: assert (ren_fun y = x) by (sauto use: ren_right_inv).
    2: assert (ren_fun y <> x) by (sauto use: ren_left_inv).
    all: destruct (eq_dec x (ren_fun y)); sauto.
  Qed.

  Corollary bij_ren_tfctx_upd_sym `{EqDec D} `{BijectiveRenaming D} :
    forall (C : tfctx) (x : D) (ra : R * A),
      ren_tfctx ren_inv (upd C x ra) = upd (ren_tfctx ren_inv C) (ren_fun x) ra .
  Proof. exact (@bij_ren_tfctx_upd _ (@BijectiveRenaming_sym H0)). Qed.
  
  (* ---------------- Context merge ---------------- *)

  Property merge_upd `{EqDec D} {C1 C2 C : tfctx} (x : D) (r : R) {a1 a2 a : A} :
    join C1 C2 C ->
    join a1 a2 a ->
    join (upd C1 x (r, a1)) (upd C2 x (r, a2)) (upd C x (r, a)).
  Proof.
    intros HjoinC HjoinA y; unfold upd; specialize (HjoinC y).
    destruct (eq_dec x y); [split|]; eauto.
  Qed.
    
  Property merge_pointwise_fun {Δ Δ1 Δ2 : tfctx} :
    join Δ1 Δ2 Δ ->
    forall (x : D),
      fst (Δ x) = fst (Δ1 x) /\
      fst (Δ x) = fst (Δ2 x) /\
      join (snd (Δ1 x)) (snd (Δ2 x)) (snd (Δ x)).
  Proof.
    intros Hjoin x; specialize (Hjoin x).
    destruct (Δ1 x) as [t1 m1], (Δ2 x) as [t2 m2], (Δ x) as [t m].
    inversion Hjoin. inversion H. rewrite H1, H2. tauto.
  Qed.

End TotalFunCtx.