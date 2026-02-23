(* Adjoint natural deduction calculus types and terms (generated mostly by Autosubst) *)

From Stdlib Require Import FunctionalExtensionality Relation_Definitions.
From Autosubst Require Import core fintype.

Section AdjointLC.
Variable A : Type.

Inductive ty : Type :=
  | ty_lolli : ty -> ty -> ty
  | ty_up : A -> A -> ty -> ty
  | ty_down : A -> A -> ty -> ty.

Lemma congr_ty_lolli {s0 s1 t0 t1 : ty} (H1 : s0 = t0) (H2 : s1 = t1) : ty_lolli s0 s1 = ty_lolli t0 t1 .
Proof. congruence. Qed.

Lemma congr_ty_up {s0 s1 : A} {s2 : ty} {t0 t1 : A} {t2 : ty} (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : ty_up s0 s1 s2 = ty_up t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_ty_down {s0 s1 : A} {s2 : ty} {t0 t1 : A} {t2 : ty} (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : ty_down s0 s1 s2 = ty_down t0 t1 t2 .
Proof. congruence. Qed.

Inductive tm (n : nat) : Type :=
  | var : fin n -> tm n
  | lam : ty -> tm (S n) -> tm n
  | app : tm n -> tm n -> tm n
  | lift : A -> A -> tm n -> tm n
  | unlift : A -> A -> tm n -> tm n
  | drop : A -> A -> tm n -> tm n
  | letdrop : A -> tm n -> tm (S n) -> tm n.

Lemma congr_lam {m : nat} {s0 : ty} {s1 : tm (S m)} {t0 : ty} {t1 : tm (S m)} (H1 : s0 = t0) (H2 : s1 = t1) : lam m s0 s1 = lam m t0 t1 .
Proof. congruence. Qed.

Lemma congr_app {m : nat} {s0 s1 : tm m} {t0 : tm m} {t1 : tm m} (H1 : s0 = t0) (H2 : s1 = t1) : app m s0 s1 = app m t0 t1 .
Proof. congruence. Qed.

Lemma congr_lift {m : nat} {s0 s1 : A} {s2 : tm m} {t0 t1 : A} {t2 : tm m} (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : lift m s0 s1 s2 = lift m t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_unlift {m : nat} {s0 s1 : A} {s2 : tm m} {t0 t1 : A} {t2 : tm m} (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : unlift m s0 s1 s2 = unlift m t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_drop {m : nat} {s0 s1 : A} {s2 : tm m} {t0 t1 : A} {t2 : tm m} (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : drop m s0 s1 s2 = drop m t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_letdrop {m : nat} {s0 : A} {s1 : tm m} {s2 : tm (S m)} {t0 : A} {t1 : tm m} {t2 : tm (S m)} (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : letdrop m s0 s1 s2 = letdrop m t0 t1 t2 .
Proof. congruence. Qed.

Definition upRen_tm_tm {m n : nat} (xi : fin m -> fin n) : fin (S m) -> fin (S n) :=
  (up_ren) xi.

Fixpoint ren_tm {m n : nat} (xi : fin m -> fin n) (s : tm m) : tm n :=
    match s return tm n with
    | var _ s => (var n) (xi s)
    (* | unit _  => unit n *)
    | lam _ s0 s1 => lam n s0 ((ren_tm (upRen_tm_tm xi)) s1)
    | app _ s0 s1 => app n ((ren_tm xi) s0) ((ren_tm xi) s1)
    | lift _ s0 s1 s2 => lift n s0 s1 ((ren_tm xi) s2)
    | unlift _ s0 s1 s2 => unlift n s0 s1 ((ren_tm xi) s2)
    | drop _ s0 s1 s2 => drop n s0 s1 ((ren_tm xi) s2)
    | letdrop _ s0 s1 s2 => letdrop n s0 ((ren_tm xi) s1) ((ren_tm (upRen_tm_tm xi)) s2)
    end.

Definition up_tm_tm {m n : nat} (sigma : fin m -> tm n) : fin (S m) -> tm (S n) :=
  scons ((var (S n)) (var_zero)) (funcomp (ren_tm shift) sigma).

Fixpoint subst_tm {m n : nat} (sigma : fin m -> tm n) (s : tm m) : tm n :=
    match s return tm n with
    | var _ s => sigma s
    (* | unit _  => unit n *)
    | lam _ s0 s1 => lam n s0 ((subst_tm (up_tm_tm sigma)) s1)
    | app _ s0 s1 => app n ((subst_tm sigma) s0) ((subst_tm sigma) s1)
    | lift _ s0 s1 s2 => lift n s0 s1 ((subst_tm sigma) s2)
    | unlift _ s0 s1 s2 => unlift n s0 s1 ((subst_tm sigma) s2)
    | drop _ s0 s1 s2 => drop n s0 s1 ((subst_tm sigma) s2)
    | letdrop _ s0 s1 s2 => letdrop n s0 ((subst_tm sigma) s1) ((subst_tm (up_tm_tm sigma)) s2)
    end.

Definition upId_tm_tm {m : nat} (sigma : fin m -> tm m) (Eq : forall x, sigma x = (var m) x) : forall x, (up_tm_tm sigma) x = (var (S m)) x :=
  fun n => match n with
  | Some fin_n => ap (ren_tm shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_tm {m : nat} (sigma : fin m -> tm m) (Eqtm : forall x, sigma x = (var m) x) (s : tm m) : subst_tm sigma s = s :=
    match s return subst_tm sigma s = s with
    | var _ s => Eqtm s
    | lam _ s0 s1 => congr_lam (eq_refl s0) ((idSubst_tm (up_tm_tm sigma) (upId_tm_tm _ Eqtm)) s1)
    | app _ s0 s1 => congr_app ((idSubst_tm sigma Eqtm) s0) ((idSubst_tm sigma Eqtm) s1)
    | lift _ s0 s1 s2 => congr_lift (eq_refl s0) (eq_refl s1) ((idSubst_tm sigma Eqtm) s2)
    | unlift _ s0 s1 s2 => congr_unlift (eq_refl s0) (eq_refl s1) ((idSubst_tm sigma Eqtm) s2)
    | drop _ s0 s1 s2 => congr_drop (eq_refl s0) (eq_refl s1) ((idSubst_tm sigma Eqtm) s2)
    | letdrop _ s0 s1 s2 => congr_letdrop (eq_refl s0) ((idSubst_tm sigma Eqtm) s1) ((idSubst_tm (up_tm_tm sigma) (upId_tm_tm _ Eqtm)) s2)
    end.

Definition upExtRen_tm_tm {m n : nat} (xi zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_tm xi) x = (upRen_tm_tm zeta) x :=
  fun n => match n with
  | Some fin_n => ap shift (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_tm {m n : nat} (xi zeta : fin m -> fin n) (Eqtm : forall x, xi x = zeta x) (s : tm m) : ren_tm xi s = ren_tm zeta s :=
    match s return ren_tm xi s = ren_tm zeta s with
    | var _ s => ap (var n) (Eqtm s)
    | lam _ s0 s1 => congr_lam (eq_refl s0) ((extRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upExtRen_tm_tm _ _ Eqtm)) s1)
    | app _ s0 s1 => congr_app ((extRen_tm xi zeta Eqtm) s0) ((extRen_tm xi zeta Eqtm) s1)
    | lift _ s0 s1 s2 => congr_lift (eq_refl s0) (eq_refl s1) ((extRen_tm xi zeta Eqtm) s2)
    | unlift _ s0 s1 s2 => congr_unlift (eq_refl s0) (eq_refl s1) ((extRen_tm xi zeta Eqtm) s2)
    | drop _ s0 s1 s2 => congr_drop (eq_refl s0) (eq_refl s1) ((extRen_tm xi zeta Eqtm) s2)
    | letdrop _ s0 s1 s2 => congr_letdrop (eq_refl s0) ((extRen_tm xi zeta Eqtm) s1) ((extRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upExtRen_tm_tm _ _ Eqtm)) s2)
    end.

Definition upExt_tm_tm {m n : nat} (sigma tau : fin m -> tm n) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_tm sigma) x = (up_tm_tm tau) x :=
  fun n => match n with
  | Some fin_n => ap (ren_tm shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_tm {m n : nat} (sigma tau : fin m -> tm n) (Eqtm : forall x, sigma x = tau x) (s : tm m) : subst_tm sigma s = subst_tm tau s :=
    match s return subst_tm sigma s = subst_tm tau s with
    | var _ s => Eqtm s
    | lam _ s0 s1 => congr_lam (eq_refl s0) ((ext_tm (up_tm_tm sigma) (up_tm_tm tau) (upExt_tm_tm _ _ Eqtm)) s1)
    | app _ s0 s1 => congr_app ((ext_tm sigma tau Eqtm) s0) ((ext_tm sigma tau Eqtm) s1)
    | lift _ s0 s1 s2 => congr_lift (eq_refl s0) (eq_refl s1) ((ext_tm sigma tau Eqtm) s2)
    | unlift _ s0 s1 s2 => congr_unlift (eq_refl s0) (eq_refl s1) ((ext_tm sigma tau Eqtm) s2)
    | drop _ s0 s1 s2 => congr_drop (eq_refl s0) (eq_refl s1) ((ext_tm sigma tau Eqtm) s2)
    | letdrop _ s0 s1 s2 => congr_letdrop (eq_refl s0) ((ext_tm sigma tau Eqtm) s1) ((ext_tm (up_tm_tm sigma) (up_tm_tm tau) (upExt_tm_tm _ _ Eqtm)) s2)
    end.

Definition up_ren_ren_tm_tm {k l m : nat} (xi : fin k -> fin l) (tau : fin l -> fin m) (theta : fin k -> fin m) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (upRen_tm_tm tau) (upRen_tm_tm xi)) x = (upRen_tm_tm theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_tm {k l m : nat} (xi : fin m -> fin k) (zeta : fin k -> fin l) (rho : fin m -> fin l) (Eqtm : forall x, (funcomp zeta xi) x = rho x) (s : tm m) : ren_tm zeta (ren_tm xi s) = ren_tm rho s :=
    match s return ren_tm zeta (ren_tm xi s) = ren_tm rho s with
    | var _ s => ap (var l) (Eqtm s)
    | lam _ s0 s1 => congr_lam (eq_refl s0) ((compRenRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upRen_tm_tm rho) (up_ren_ren _ _ _ Eqtm)) s1)
    | app _ s0 s1 => congr_app ((compRenRen_tm xi zeta rho Eqtm) s0) ((compRenRen_tm xi zeta rho Eqtm) s1)
    | lift _ s0 s1 s2 => congr_lift (eq_refl s0) (eq_refl s1) ((compRenRen_tm xi zeta rho Eqtm) s2)
    | unlift _ s0 s1 s2 => congr_unlift (eq_refl s0) (eq_refl s1) ((compRenRen_tm xi zeta rho Eqtm) s2)
    | drop _ s0 s1 s2 => congr_drop (eq_refl s0) (eq_refl s1) ((compRenRen_tm xi zeta rho Eqtm) s2)
    | letdrop _ s0 s1 s2 => congr_letdrop (eq_refl s0) ((compRenRen_tm xi zeta rho Eqtm) s1) ((compRenRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upRen_tm_tm rho) (up_ren_ren _ _ _ Eqtm)) s2)
    end.

Definition up_ren_subst_tm_tm {k l m : nat} (xi : fin k -> fin l) (tau : fin l -> tm m) (theta : fin k -> tm m) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (up_tm_tm tau) (upRen_tm_tm xi)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => ap (ren_tm shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_tm {k l m : nat} (xi : fin m -> fin k) (tau : fin k -> tm l) (theta : fin m -> tm l) (Eqtm : forall x, (funcomp tau xi) x = theta x) (s : tm m) : subst_tm tau (ren_tm xi s) = subst_tm theta s :=
    match s return subst_tm tau (ren_tm xi s) = subst_tm theta s with
    | var _ s => Eqtm s
    | lam _ s0 s1 => congr_lam (eq_refl s0) ((compRenSubst_tm (upRen_tm_tm xi) (up_tm_tm tau) (up_tm_tm theta) (up_ren_subst_tm_tm _ _ _ Eqtm)) s1)
    | app _ s0 s1 => congr_app ((compRenSubst_tm xi tau theta Eqtm) s0) ((compRenSubst_tm xi tau theta Eqtm) s1)
    | lift _ s0 s1 s2 => congr_lift (eq_refl s0) (eq_refl s1) ((compRenSubst_tm xi tau theta Eqtm) s2)
    | unlift _ s0 s1 s2 => congr_unlift (eq_refl s0) (eq_refl s1) ((compRenSubst_tm xi tau theta Eqtm) s2)
    | drop _ s0 s1 s2 => congr_drop (eq_refl s0) (eq_refl s1) ((compRenSubst_tm xi tau theta Eqtm) s2)
    | letdrop _ s0 s1 s2 => congr_letdrop (eq_refl s0) ((compRenSubst_tm xi tau theta Eqtm) s1) ((compRenSubst_tm (upRen_tm_tm xi) (up_tm_tm tau) (up_tm_tm theta) (up_ren_subst_tm_tm _ _ _ Eqtm)) s2)
    end.

Definition up_subst_ren_tm_tm {k l m : nat} (sigma : fin k -> tm l) (zeta : fin l -> fin m) (theta : fin k -> tm m) (Eq : forall x, (funcomp (ren_tm zeta) sigma) x = theta x) : forall x, (funcomp (ren_tm (upRen_tm_tm zeta)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => eq_trans (compRenRen_tm shift (upRen_tm_tm zeta) (funcomp shift zeta) (fun x => eq_refl) (sigma fin_n)) (eq_trans ((eq_sym) (compRenRen_tm zeta shift (funcomp shift zeta) (fun x => eq_refl) (sigma fin_n))) (ap (ren_tm shift) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_tm {k l m : nat} (sigma : fin m -> tm k) (zeta : fin k -> fin l) (theta : fin m -> tm l) (Eqtm : forall x, (funcomp (ren_tm zeta) sigma) x = theta x) (s : tm m) : ren_tm zeta (subst_tm sigma s) = subst_tm theta s :=
    match s return ren_tm zeta (subst_tm sigma s) = subst_tm theta s with
    | var _ s => Eqtm s
    | lam _ s0 s1 => congr_lam (eq_refl s0) ((compSubstRen_tm (up_tm_tm sigma) (upRen_tm_tm zeta) (up_tm_tm theta) (up_subst_ren_tm_tm _ _ _ Eqtm)) s1)
    | app _ s0 s1 => congr_app ((compSubstRen_tm sigma zeta theta Eqtm) s0) ((compSubstRen_tm sigma zeta theta Eqtm) s1)
    | lift _ s0 s1 s2 => congr_lift (eq_refl s0) (eq_refl s1) ((compSubstRen_tm sigma zeta theta Eqtm) s2)
    | unlift _ s0 s1 s2 => congr_unlift (eq_refl s0) (eq_refl s1) ((compSubstRen_tm sigma zeta theta Eqtm) s2)
    | drop _ s0 s1 s2 => congr_drop (eq_refl s0) (eq_refl s1) ((compSubstRen_tm sigma zeta theta Eqtm) s2)
    | letdrop _ s0 s1 s2 => congr_letdrop (eq_refl s0) ((compSubstRen_tm sigma zeta theta Eqtm) s1) ((compSubstRen_tm (up_tm_tm sigma) (upRen_tm_tm zeta) (up_tm_tm theta) (up_subst_ren_tm_tm _ _ _ Eqtm)) s2)
    end.

Definition up_subst_subst_tm_tm {k l m : nat} (sigma : fin k -> tm l) (tau : fin l -> tm m) (theta : fin k -> tm m) (Eq : forall x, (funcomp (subst_tm tau) sigma) x = theta x) : forall x, (funcomp (subst_tm (up_tm_tm tau)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => eq_trans (compRenSubst_tm shift (up_tm_tm tau) (funcomp (up_tm_tm tau) shift) (fun x => eq_refl) (sigma fin_n)) (eq_trans ((eq_sym) (compSubstRen_tm tau shift (funcomp (ren_tm shift) tau) (fun x => eq_refl) (sigma fin_n))) (ap (ren_tm shift) (Eq fin_n)))
  | None => eq_refl
  end.

Fixpoint compSubstSubst_tm {k l m : nat} (sigma : fin m -> tm k) (tau : fin k -> tm l) (theta : fin m -> tm l) (Eqtm : forall x, (funcomp (subst_tm tau) sigma) x = theta x) (s : tm m) : subst_tm tau (subst_tm sigma s) = subst_tm theta s :=
    match s return subst_tm tau (subst_tm sigma s) = subst_tm theta s with
    | var _ s => Eqtm s
    | lam _ s0 s1 => congr_lam (eq_refl s0) ((compSubstSubst_tm (up_tm_tm sigma) (up_tm_tm tau) (up_tm_tm theta) (up_subst_subst_tm_tm _ _ _ Eqtm)) s1)
    | app _ s0 s1 => congr_app ((compSubstSubst_tm sigma tau theta Eqtm) s0) ((compSubstSubst_tm sigma tau theta Eqtm) s1)
    | lift _ s0 s1 s2 => congr_lift (eq_refl s0) (eq_refl s1) ((compSubstSubst_tm sigma tau theta Eqtm) s2)
    | unlift _ s0 s1 s2 => congr_unlift (eq_refl s0) (eq_refl s1) ((compSubstSubst_tm sigma tau theta Eqtm) s2)
    | drop _ s0 s1 s2 => congr_drop (eq_refl s0) (eq_refl s1) ((compSubstSubst_tm sigma tau theta Eqtm) s2)
    | letdrop _ s0 s1 s2 => congr_letdrop (eq_refl s0) ((compSubstSubst_tm sigma tau theta Eqtm) s1) ((compSubstSubst_tm (up_tm_tm sigma) (up_tm_tm tau) (up_tm_tm theta) (up_subst_subst_tm_tm _ _ _ Eqtm)) s2)
    end.

Definition rinstInst_up_tm_tm {m n : nat} (xi : fin m -> fin n) (sigma : fin m -> tm n) (Eq : forall x, (funcomp (var n) xi) x = sigma x) : forall x, (funcomp (var (S n)) (upRen_tm_tm xi)) x = (up_tm_tm sigma) x :=
  fun n => match n with
  | Some fin_n => ap (ren_tm shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_tm {m n : nat} (xi : fin m -> fin n) (sigma : fin m -> tm n) (Eqtm : forall x, (funcomp (var n) xi) x = sigma x) (s : tm m) : ren_tm xi s = subst_tm sigma s :=
    match s return ren_tm xi s = subst_tm sigma s with
    | var _ s => Eqtm s
    | lam _ s0 s1 => congr_lam (eq_refl s0) ((rinst_inst_tm (upRen_tm_tm xi) (up_tm_tm sigma) (rinstInst_up_tm_tm _ _ Eqtm)) s1)
    | app _ s0 s1 => congr_app ((rinst_inst_tm xi sigma Eqtm) s0) ((rinst_inst_tm xi sigma Eqtm) s1)
    | lift _ s0 s1 s2 => congr_lift (eq_refl s0) (eq_refl s1) ((rinst_inst_tm xi sigma Eqtm) s2)
    | unlift _ s0 s1 s2 => congr_unlift (eq_refl s0) (eq_refl s1) ((rinst_inst_tm xi sigma Eqtm) s2)
    | drop _ s0 s1 s2 => congr_drop (eq_refl s0) (eq_refl s1) ((rinst_inst_tm xi sigma Eqtm) s2)
    | letdrop _ s0 s1 s2 => congr_letdrop (eq_refl s0) ((rinst_inst_tm xi sigma Eqtm) s1) ((rinst_inst_tm (upRen_tm_tm xi) (up_tm_tm sigma) (rinstInst_up_tm_tm _ _ Eqtm)) s2)
    end.

Lemma rinstInst_tm {m n : nat} (xi : fin m -> fin n) : ren_tm xi = subst_tm (funcomp (var n) xi) .
Proof. exact ((functional_extensionality _ _ ) (fun x => rinst_inst_tm xi _ (fun n => eq_refl) x)). Qed.

Lemma instId_tm {m : nat} : subst_tm (var m) = id .
Proof. exact ((functional_extensionality _ _ ) (fun x => idSubst_tm (var m) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_tm {m : nat} : @ren_tm m m (id) = id .
Proof. exact (eq_trans (rinstInst_tm ((id) _)) instId_tm). Qed.

Lemma varL_tm {m n : nat} (sigma : fin m -> tm n) : funcomp (subst_tm sigma) (var m) = sigma .
Proof. exact ((functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_tm {m n : nat} (xi : fin m -> fin n) : funcomp (ren_tm xi) (var m) = funcomp (var n) xi .
Proof. exact ((functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_tm {k l m : nat} (sigma : fin m -> tm k) (tau : fin k -> tm l) (s : tm m) : subst_tm tau (subst_tm sigma s) = subst_tm (funcomp (subst_tm tau) sigma) s .
Proof. exact (compSubstSubst_tm sigma tau _ (fun n => eq_refl) s). Qed.

Lemma compComp'_tm {k l m : nat} (sigma : fin m -> tm k) (tau : fin k -> tm l) : funcomp (subst_tm tau) (subst_tm sigma) = subst_tm (funcomp (subst_tm tau) sigma) .
Proof. exact ((functional_extensionality _ _ ) (fun n => compComp_tm sigma tau n)). Qed.

Lemma compRen_tm {k l m : nat} (sigma : fin m -> tm k) (zeta : fin k -> fin l) (s : tm m) : ren_tm zeta (subst_tm sigma s) = subst_tm (funcomp (ren_tm zeta) sigma) s .
Proof. exact (compSubstRen_tm sigma zeta _ (fun n => eq_refl) s). Qed.

Lemma compRen'_tm {k l m : nat} (sigma : fin m -> tm k) (zeta : fin k -> fin l) : funcomp (ren_tm zeta) (subst_tm sigma) = subst_tm (funcomp (ren_tm zeta) sigma) .
Proof. exact ((functional_extensionality _ _ ) (fun n => compRen_tm sigma zeta n)). Qed.

Lemma renComp_tm {k l m : nat} (xi : fin m -> fin k) (tau : fin k -> tm l) (s : tm m) : subst_tm tau (ren_tm xi s) = subst_tm (funcomp tau xi) s .
Proof. exact (compRenSubst_tm xi tau _ (fun n => eq_refl) s). Qed.

Lemma renComp'_tm {k l m : nat} (xi : fin m -> fin k) (tau : fin k -> tm l) : funcomp (subst_tm tau) (ren_tm xi) = subst_tm (funcomp tau xi) .
Proof. exact ((functional_extensionality _ _ ) (fun n => renComp_tm xi tau n)). Qed.

Lemma renRen_tm {k l m : nat} (xi : fin m -> fin k) (zeta : fin k -> fin l) (s : tm m) : ren_tm zeta (ren_tm xi s) = ren_tm (funcomp zeta xi) s .
Proof. exact (compRenRen_tm xi zeta _ (fun n => eq_refl) s). Qed.

Lemma renRen'_tm {k l m : nat} (xi : fin m -> fin k) (zeta : fin k -> fin l) : funcomp (ren_tm zeta) (ren_tm xi) = ren_tm (funcomp zeta xi) .
Proof. exact ((functional_extensionality _ _ ) (fun n => renRen_tm xi zeta n)). Qed.

Global Instance Subst_tm {m n : nat} : Subst1 (fin m -> tm n) (tm m) (tm n) := @subst_tm m n .
Global Instance Ren_tm {m n : nat} : Ren1 (fin m -> fin n) (tm m) (tm n) := @ren_tm m n .
Global Instance VarInstance_tm {m : nat} : Var (fin m) (tm m) := @var m .

Notation "x '__tm'" := (var x) (at level 5, format "x __tm") : subst_scope.
Notation "'var'" := (var) (only printing, at level 1) : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.
Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm {m n : nat} : Up_tm _ _ := @up_tm_tm m n .

Notation "s [ sigma ]" := (subst_tm sigma s) (at level 7, left associativity, only printing) : subst_scope.
Notation "[ sigma ]" := (subst_tm sigma) (at level 1, left associativity, only printing) : fscope.
Notation "s ⟨ xi ⟩" := (ren_tm xi s) (at level 7, left associativity, only printing) : subst_scope.
Notation "⟨ xi ⟩" := (ren_tm xi) (at level 1, left associativity, only printing) : fscope.

End AdjointLC.

Ltac auto_unfold :=
  repeat unfold subst1, subst2, Subst1, Subst2, ids, ren1, ren2, Ren1, Ren2, Subst_tm, Ren_tm, VarInstance_tm.
Tactic Notation "auto_unfold" "in" "*" :=
  repeat unfold subst1, subst2, Subst1, Subst2, ids, ren1, ren2, Ren1, Ren2, Subst_tm, Ren_tm, VarInstance_tm in *.

Ltac asimpl' :=
  repeat first
    [ progress rewrite ?instId_tm
    | progress rewrite ?compComp_tm
    | progress rewrite ?compComp'_tm
    | progress rewrite ?rinstId_tm
    | progress rewrite ?compRen_tm
    | progress rewrite ?compRen'_tm
    | progress rewrite ?renComp_tm
    | progress rewrite ?renComp'_tm
    | progress rewrite ?renRen_tm
    | progress rewrite ?renRen'_tm
    | progress rewrite ?varL_tm
    | progress rewrite ?varLRen_tm
    | progress (unfold up_ren, upRen_tm_tm, up_tm_tm)
    | progress (cbn [subst_tm ren_tm])
    | fsimpl ].
Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.
Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.
Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_tm).
Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_tm).

Module Extra.
  Arguments ty {A}.
  Arguments tm {A}.
  Arguments var {A n}.
  Arguments lam {A n}.
  Arguments app {A n}.
  Arguments lift {A n}.
  Arguments unlift {A n}.
  Arguments drop {A n}.
  Arguments letdrop {A n}.
  Arguments ty_lolli {A}.
  Arguments ty_up {A}.
  Arguments ty_down {A}.
  Arguments ren_tm {A m n}.
  Notation "T1 ⊸ T2" := (ty_lolli T1 T2) (at level 51, right associativity).
  Notation "'↑[' m ',' k ']' T" := (ty_up m k T) (at level 30).
  Notation "'↓[' m ',' k ']' T" := (ty_down m k T) (at level 30).
End Extra.
Export Extra.