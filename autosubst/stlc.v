(* λ-calculus types and terms (generated mostly by Autosubst) *)

From Stdlib Require Import Morphisms.
From Autosubst Require Import core fintype.

Module Core.

Inductive ty : Type :=
  | Unit : ty
  | Fun : ty -> ty -> ty.

Lemma congr_Unit : Unit = Unit.
Proof. exact eq_refl. Qed.

Lemma congr_Fun {s0 s1 t0 t1 : ty} (H0 : s0 = t0)
                (H1 : s1 = t1) : Fun s0 s1 = Fun t0 t1.
Proof.
  exact (eq_trans (eq_trans eq_refl (ap (fun x => Fun x s1) H0))
        (ap (fun x => Fun t0 x) H1)).
Qed.

Inductive tm (n : nat) : Type :=
  | var : fin n -> tm n
  | lam : ty -> tm (S n) -> tm n
  | app : tm n -> tm n -> tm n.

Lemma congr_app {m : nat} {s0 s1 t0 t1 : tm m}
                (H0 : s0 = t0) (H1 : s1 = t1) :
  app m s0 s1 = app m t0 t1.
Proof.
  exact (eq_trans (eq_trans eq_refl (ap (fun x => app m x s1) H0))
        (ap (fun x => app m t0 x) H1)).
Qed.

Lemma congr_lam {m : nat} {s0 : ty} {s1 : tm (S m)} {t0 : ty}
                {t1 : tm (S m)} (H0 : s0 = t0) (H1 : s1 = t1) :
  lam m s0 s1 = lam m t0 t1.
Proof.
  exact (eq_trans (eq_trans eq_refl (ap (fun x => lam m x s1) H0))
        (ap (fun x => lam m t0 x) H1)).
Qed.

Lemma upRen_tm_tm {m n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof. exact (up_ren xi). Defined.

Lemma upRen_list_tm_tm (p : nat) {m n : nat} (xi : fin m -> fin n) :
  fin (plus p m) -> fin (plus p n).
Proof. exact (upRen_p p xi). Defined.

Fixpoint ren_tm {m n : nat} (xi : fin m -> fin n)
                (s : tm m) {struct s} : tm n :=
  match s with
  | var _ s0 => var n (xi s0)
  | app _ s0 s1 => app n (ren_tm xi s0) (ren_tm xi s1)
  | lam _ s0 s1 => lam n s0 (ren_tm (upRen_tm_tm xi) s1)
  end.

Lemma up_tm_tm {m n : nat} (sigma : fin m -> tm n) :
  fin (S m) -> tm (S n).
Proof. exact (scons (var (S n) var_zero) (funcomp (ren_tm shift) sigma)). Defined.

Lemma up_list_tm_tm (p : nat) {m n : nat} (sigma : fin m -> tm n) :
  fin (plus p m) -> tm (plus p n).
Proof.
  exact (scons_p p (funcomp (var (plus p n)) (zero_p p))
        (funcomp (ren_tm (shift_p p)) sigma)).
Defined.

Fixpoint subst_tm {m n : nat} (sigma : fin m -> tm n)
                  (s : tm m) {struct s} : tm n :=
  match s with
  | var _ s0 => sigma s0
  | app _ s0 s1 => app n (subst_tm sigma s0) (subst_tm sigma s1)
  | lam _ s0 s1 => lam n s0 (subst_tm (up_tm_tm sigma) s1)
  end.

Lemma upId_tm_tm {m : nat} (sigma : fin m -> tm m)
                 (Eq : forall x, sigma x = var m x) :
  forall x, up_tm_tm sigma x = var (S m) x.
Proof.
  exact (fun n =>
        match n with
        | Some fin_n => ap (ren_tm shift) (Eq fin_n)
        | None => eq_refl
        end).
Qed.

Lemma upId_list_tm_tm {p m : nat} (sigma : fin m -> tm m)
                      (Eq : forall x, sigma x = var m x) :
  forall x, up_list_tm_tm p sigma x = var (plus p m) x.
Proof.
  exact (fun n =>
        scons_p_eta (var (plus p m))
        (fun n => ap (ren_tm (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_tm {m : nat} (sigma : fin m -> tm m)
                    (Eq_tm : forall x, sigma x = var m x) (s : tm m) {struct s} :
  subst_tm sigma s = s :=
    match s with
    | var _ s0 => Eq_tm s0
    | app _ s0 s1 =>
        congr_app (idSubst_tm sigma Eq_tm s0) (idSubst_tm sigma Eq_tm s1)
    | lam _ s0 s1 =>
        congr_lam (eq_refl s0)
          (idSubst_tm (up_tm_tm sigma) (upId_tm_tm _ Eq_tm) s1)
    end.

Lemma upExtRen_tm_tm {m n : nat} (xi : fin m -> fin n)
                     (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x.
Proof.
  exact (fun n =>
        match n with
        | Some fin_n => ap shift (Eq fin_n)
        | None => eq_refl
        end).
Qed.

Lemma upExtRen_list_tm_tm {p m n : nat} (xi : fin m -> fin n)
                          (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_tm_tm p xi x = upRen_list_tm_tm p zeta x.
Proof. exact (fun n => scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))). Qed.

Fixpoint extRen_tm {m n : nat} (xi : fin m -> fin n)
                   (zeta : fin m -> fin n) (Eq_tm : forall x, xi x = zeta x)
                   (s : tm m) {struct s} : ren_tm xi s = ren_tm zeta s :=
  match s with
  | var _ s0 => ap (var n) (Eq_tm s0)
  | app _ s0 s1 =>
      congr_app (extRen_tm xi zeta Eq_tm s0)
        (extRen_tm xi zeta Eq_tm s1)
  | lam _ s0 s1 =>
      congr_lam (eq_refl s0)
        (extRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
  end.

Lemma upExt_tm_tm {m n : nat} (sigma : fin m -> tm n)
                  (tau : fin m -> tm n) (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.
Proof.
  exact (fun n =>
        match n with
        | Some fin_n => ap (ren_tm shift) (Eq fin_n)
        | None => eq_refl
        end).
Qed.

Lemma upExt_list_tm_tm {p m n : nat}
                       (sigma : fin m -> tm n) (tau : fin m -> tm n)
                       (Eq : forall x, sigma x = tau x) :
  forall x, up_list_tm_tm p sigma x = up_list_tm_tm p tau x.
Proof.
  exact (fun n =>
        scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_tm (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_tm {m n : nat} (sigma : fin m -> tm n)
                (tau : fin m -> tm n) (Eq_tm : forall x, sigma x = tau x)
                (s : tm m) {struct s} : subst_tm sigma s = subst_tm tau s :=
  match s with
  | var _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (ext_tm sigma tau Eq_tm s0)
        (ext_tm sigma tau Eq_tm s1)
  | lam _ s0 s1 =>
      congr_lam (eq_refl s0)
        (ext_tm (up_tm_tm sigma) (up_tm_tm tau) (upExt_tm_tm _ _ Eq_tm) s1)
  end.

Lemma up_ren_ren_tm_tm {k l m : nat} (xi : fin k -> fin l)
                       (zeta : fin l -> fin m) (rho : fin k -> fin m)
                       (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.
Proof. exact (up_ren_ren xi zeta rho Eq). Qed.

Lemma up_ren_ren_list_tm_tm {p k l m : nat}
                            (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
                            (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
    funcomp (upRen_list_tm_tm p zeta) (upRen_list_tm_tm p xi) x =
    upRen_list_tm_tm p rho x.
Proof. exact (up_ren_ren_p Eq). Qed.

Fixpoint compRenRen_tm {k l m : nat}
                       (xi : fin m -> fin k) (zeta : fin k -> fin l)
                       (rho_tm : fin m -> fin l)
                       (Eq_tm : forall x, funcomp zeta xi x = rho_tm x) (s : tm m) {struct s} :
  ren_tm zeta (ren_tm xi s) = ren_tm rho_tm s :=
    match s with
    | var _ s0 => ap (var l) (Eq_tm s0)
    | app _ s0 s1 =>
        congr_app (compRenRen_tm xi zeta rho_tm Eq_tm s0)
          (compRenRen_tm xi zeta rho_tm Eq_tm s1)
    | lam _ s0 s1 =>
        congr_lam (eq_refl s0)
          (compRenRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta)
            (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
    end.

Lemma up_ren_subst_tm_tm {k l m : nat}
                         (xi : fin k -> fin l) (tau : fin l -> tm m) (theta : fin k -> tm m)
                         (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.
Proof.
  exact (fun n =>
        match n with
        | Some fin_n => ap (ren_tm shift) (Eq fin_n)
        | None => eq_refl
        end).
Qed.

Lemma up_ren_subst_list_tm_tm {p k l m : nat}
                              (xi : fin k -> fin l) (tau : fin l -> tm m) (theta : fin k -> tm m)
                              (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
    funcomp (up_list_tm_tm p tau) (upRen_list_tm_tm p xi) x =
    up_list_tm_tm p theta x.
Proof.
  exact (fun n =>
        eq_trans (scons_p_comp' _ _ _ n)
          (scons_p_congr (fun z => scons_p_head' _ _ z)
              (fun z =>
              eq_trans (scons_p_tail' _ _ (xi z))
                (ap (ren_tm (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_tm {k l m : nat}
                         (xi : fin m -> fin k) (tau : fin k -> tm l)
                         (theta_tm : fin m -> tm l)
                         (Eq_tm : forall x, funcomp tau xi x = theta_tm x) (s : tm m) {struct s} :
  subst_tm tau (ren_tm xi s) = subst_tm theta_tm s :=
    match s with
    | var _ s0 => Eq_tm s0
    | app _ s0 s1 =>
        congr_app (compRenSubst_tm xi tau theta_tm Eq_tm s0)
          (compRenSubst_tm xi tau theta_tm Eq_tm s1)
    | lam _ s0 s1 =>
        congr_lam (eq_refl s0)
          (compRenSubst_tm (upRen_tm_tm xi) (up_tm_tm tau)
            (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
    end.

Lemma up_subst_ren_tm_tm {k l m : nat}
                         (sigma : fin k -> tm l) (zeta : fin l -> fin m)
                         (theta : fin k -> tm m)
                         (Eq : forall x, funcomp (ren_tm zeta) sigma x = theta x) :
  forall x,
    funcomp (ren_tm (upRen_tm_tm zeta)) (up_tm_tm sigma) x =
    up_tm_tm theta x.
Proof.
  exact (fun n =>
        match n with
        | Some fin_n =>
            eq_trans
              (compRenRen_tm shift (upRen_tm_tm zeta)
                  (funcomp shift zeta) (fun x => eq_refl) (sigma fin_n))
              (eq_trans
                  (eq_sym
                    (compRenRen_tm zeta shift (funcomp shift zeta)
                        (fun x => eq_refl) (sigma fin_n)))
                  (ap (ren_tm shift) (Eq fin_n)))
        | None => eq_refl
        end).
Qed.

Lemma up_subst_ren_list_tm_tm {p k l m : nat}
                              (sigma : fin k -> tm l) (zeta : fin l -> fin m)
                              (theta : fin k -> tm m)
                              (Eq : forall x, funcomp (ren_tm zeta) sigma x = theta x) :
  forall x,
    funcomp (ren_tm (upRen_list_tm_tm p zeta)) (up_list_tm_tm p sigma) x =
    up_list_tm_tm p theta x.
Proof.
  exact (fun n =>
        eq_trans (scons_p_comp' _ _ _ n)
          (scons_p_congr
              (fun x => ap (var (plus p m)) (scons_p_head' _ _ x))
              (fun n =>
              eq_trans
                (compRenRen_tm (shift_p p) (upRen_list_tm_tm p zeta)
                    (funcomp (shift_p p) zeta)
                    (fun x => scons_p_tail' _ _ x) (sigma n))
                (eq_trans
                    (eq_sym
                      (compRenRen_tm zeta (shift_p p)
                          (funcomp (shift_p p) zeta) (fun x => eq_refl)
                          (sigma n))) (ap (ren_tm (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_tm {k l m : nat}
                         (sigma : fin m -> tm k) (zeta : fin k -> fin l)
                         (theta_tm : fin m -> tm l)
                         (Eq_tm : forall x, funcomp (ren_tm zeta) sigma x = theta_tm x)
                         (s : tm m) {struct s} :
  ren_tm zeta (subst_tm sigma s) = subst_tm theta_tm s :=
    match s with
    | var _ s0 => Eq_tm s0
    | app _ s0 s1 =>
        congr_app (compSubstRen_tm sigma zeta theta_tm Eq_tm s0)
          (compSubstRen_tm sigma zeta theta_tm Eq_tm s1)
    | lam _ s0 s1 =>
        congr_lam (eq_refl s0)
          (compSubstRen_tm (up_tm_tm sigma) (upRen_tm_tm zeta)
            (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
    end.

Lemma up_subst_subst_tm_tm {k l m : nat}
                           (sigma : fin k -> tm l) (tau : fin l -> tm m)
                           (theta : fin k -> tm m)
                           (Eq : forall x, funcomp (subst_tm tau) sigma x = theta x) :
  forall x,
    funcomp (subst_tm (up_tm_tm tau)) (up_tm_tm sigma) x = up_tm_tm theta x.
Proof.
  exact (fun n =>
        match n with
        | Some fin_n =>
            eq_trans
              (compRenSubst_tm shift (up_tm_tm tau)
                  (funcomp (up_tm_tm tau) shift) (fun x => eq_refl)
                  (sigma fin_n))
              (eq_trans
                  (eq_sym
                    (compSubstRen_tm tau shift
                        (funcomp (ren_tm shift) tau) (fun x => eq_refl)
                        (sigma fin_n))) (ap (ren_tm shift) (Eq fin_n)))
        | None => eq_refl
        end).
Qed.

Lemma up_subst_subst_list_tm_tm {p k l m : nat}
                                (sigma : fin k -> tm l) (tau : fin l -> tm m)
                                (theta : fin k -> tm m)
                                (Eq : forall x, funcomp (subst_tm tau) sigma x = theta x) :
  forall x,
    funcomp (subst_tm (up_list_tm_tm p tau)) (up_list_tm_tm p sigma) x =
    up_list_tm_tm p theta x.
Proof.
  exact (fun n =>
        eq_trans
          (scons_p_comp' (funcomp (var (plus p l)) (zero_p p)) _ _ n)
          (scons_p_congr
              (fun x => scons_p_head' _ (fun z => ren_tm (shift_p p) _) x)
              (fun n =>
              eq_trans
                (compRenSubst_tm (shift_p p) (up_list_tm_tm p tau)
                    (funcomp (up_list_tm_tm p tau) (shift_p p))
                    (fun x => eq_refl) (sigma n))
                (eq_trans
                    (eq_sym
                      (compSubstRen_tm tau (shift_p p) _
                          (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                    (ap (ren_tm (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_tm {k l m : nat}
                           (sigma : fin m -> tm k) (tau : fin k -> tm l)
                           (theta_tm : fin m -> tm l)
                           (Eq_tm : forall x, funcomp (subst_tm tau) sigma x = theta_tm x)
                           (s : tm m) {struct s} :
  subst_tm tau (subst_tm sigma s) = subst_tm theta_tm s :=
    match s with
    | var _ s0 => Eq_tm s0
    | app _ s0 s1 =>
        congr_app (compSubstSubst_tm sigma tau theta_tm Eq_tm s0)
          (compSubstSubst_tm sigma tau theta_tm Eq_tm s1)
    | lam _ s0 s1 =>
        congr_lam (eq_refl s0)
          (compSubstSubst_tm (up_tm_tm sigma) (up_tm_tm tau)
            (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
    end.

Lemma renRen_tm {k l m : nat}
                (xi : fin m -> fin k) (zeta : fin k -> fin l)
                (s : tm m) :
  ren_tm zeta (ren_tm xi s) = ren_tm (funcomp zeta xi) s.
Proof. exact (compRenRen_tm xi zeta _ (fun n => eq_refl) s). Qed.

Lemma renRen'_tm_pointwise {k l m : nat}
                           (xi : fin m -> fin k) (zeta : fin k -> fin l) :
  pointwise_relation _ eq (funcomp (ren_tm zeta) (ren_tm xi))
    (ren_tm (funcomp zeta xi)).
Proof. exact (fun s => compRenRen_tm xi zeta _ (fun n => eq_refl) s). Qed.

Lemma renSubst_tm {k l m : nat}
                  (xi : fin m -> fin k) (tau : fin k -> tm l) (s : tm m) :
  subst_tm tau (ren_tm xi s) = subst_tm (funcomp tau xi) s.
Proof. exact (compRenSubst_tm xi tau _ (fun n => eq_refl) s). Qed.

Lemma renSubst_tm_pointwise {k l m : nat}
                            (xi : fin m -> fin k) (tau : fin k -> tm l) :
  pointwise_relation _ eq (funcomp (subst_tm tau) (ren_tm xi))
    (subst_tm (funcomp tau xi)).
Proof. exact (fun s => compRenSubst_tm xi tau _ (fun n => eq_refl) s). Qed.

Lemma substRen_tm {k l m : nat}
                  (sigma : fin m -> tm k) (zeta : fin k -> fin l)
                  (s : tm m) :
  ren_tm zeta (subst_tm sigma s) =
  subst_tm (funcomp (ren_tm zeta) sigma) s.
Proof. exact (compSubstRen_tm sigma zeta _ (fun n => eq_refl) s). Qed.

Lemma substRen_tm_pointwise {k l m : nat}
                            (sigma : fin m -> tm k) (zeta : fin k -> fin l) :
  pointwise_relation _ eq (funcomp (ren_tm zeta) (subst_tm sigma))
    (subst_tm (funcomp (ren_tm zeta) sigma)).
Proof. exact (fun s => compSubstRen_tm sigma zeta _ (fun n => eq_refl) s). Qed.

Lemma substSubst_tm {k l m : nat}
                    (sigma : fin m -> tm k) (tau : fin k -> tm l)
                    (s : tm m) :
  subst_tm tau (subst_tm sigma s) =
  subst_tm (funcomp (subst_tm tau) sigma) s.
Proof. exact (compSubstSubst_tm sigma tau _ (fun n => eq_refl) s). Qed.

Lemma substSubst_tm_pointwise {k l m : nat}
                              (sigma : fin m -> tm k) (tau : fin k -> tm l) :
  pointwise_relation _ eq (funcomp (subst_tm tau) (subst_tm sigma))
    (subst_tm (funcomp (subst_tm tau) sigma)).
Proof. exact (fun s => compSubstSubst_tm sigma tau _ (fun n => eq_refl) s). Qed.

Lemma rinstInst_up_tm_tm {m n : nat} (xi : fin m -> fin n)
                         (sigma : fin m -> tm n)
                         (Eq : forall x, funcomp (var n) xi x = sigma x) :
  forall x, funcomp (var (S n)) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
  exact (fun n =>
        match n with
        | Some fin_n => ap (ren_tm shift) (Eq fin_n)
        | None => eq_refl
        end).
Qed.

Lemma rinstInst_up_list_tm_tm {p m n : nat}
                              (xi : fin m -> fin n) (sigma : fin m -> tm n)
                              (Eq : forall x, funcomp (var n) xi x = sigma x) :
  forall x,
    funcomp (var (plus p n)) (upRen_list_tm_tm p xi) x =
    up_list_tm_tm p sigma x.
Proof.
  exact (fun n' =>
        eq_trans (scons_p_comp' _ _ (var (plus p n)) n')
          (scons_p_congr (fun z => eq_refl)
              (fun n' => ap (ren_tm (shift_p p)) (Eq n')))).
Qed.

Fixpoint rinst_inst_tm {m n : nat}
                       (xi : fin m -> fin n) (sigma : fin m -> tm n)
                       (Eq_tm : forall x, funcomp (var n) xi x = sigma x) (s : tm m)
                       {struct s} :
  ren_tm xi s = subst_tm sigma s :=
    match s with
    | var _ s0 => Eq_tm s0
    | app _ s0 s1 =>
        congr_app (rinst_inst_tm xi sigma Eq_tm s0)
          (rinst_inst_tm xi sigma Eq_tm s1)
    | lam _ s0 s1 =>
        congr_lam (eq_refl s0)
          (rinst_inst_tm (upRen_tm_tm xi) (up_tm_tm sigma)
            (rinstInst_up_tm_tm _ _ Eq_tm) s1)
    end.

Lemma rinstInst'_tm {m n : nat} (xi : fin m -> fin n) (s : tm m) :
  ren_tm xi s = subst_tm (funcomp (var n) xi) s.
Proof. exact (rinst_inst_tm xi _ (fun n => eq_refl) s). Qed.

Lemma rinstInst'_tm_pointwise {m n : nat} (xi : fin m -> fin n) :
  pointwise_relation _ eq (ren_tm xi)
    (subst_tm (funcomp (var n) xi)).
Proof. exact (fun s => rinst_inst_tm xi _ (fun n => eq_refl) s). Qed.

Lemma instId'_tm {m : nat} (s : tm m) : subst_tm (var m) s = s.
Proof. exact (idSubst_tm (var m) (fun n => eq_refl) s). Qed.

Lemma instId'_tm_pointwise {m : nat} :
  pointwise_relation _ eq (subst_tm (var m)) id.
Proof. exact (fun s => idSubst_tm (var m) (fun n => eq_refl) s). Qed.

Lemma rinstId'_tm {m : nat} (s : tm m) : ren_tm id s = s.
Proof. exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)). Qed.

Lemma rinstId'_tm_pointwise {m : nat} :
  pointwise_relation _ eq (@ren_tm m m id) id.
Proof. exact (fun s => eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)). Qed.

Lemma varL'_tm {m n : nat} (sigma : fin m -> tm n) (x : fin m) :
  subst_tm sigma (var m x) = sigma x.
Proof. exact eq_refl. Qed.

Lemma varL'_tm_pointwise {m n : nat} (sigma : fin m -> tm n) :
  pointwise_relation _ eq (funcomp (subst_tm sigma) (var m)) sigma.
Proof. exact (fun x => eq_refl). Qed.

Lemma varLRen'_tm {m n : nat} (xi : fin m -> fin n) (x : fin m) :
  ren_tm xi (var m x) = var n (xi x).
Proof. exact eq_refl. Qed.

Lemma varLRen'_tm_pointwise {m n : nat} (xi : fin m -> fin n) :
  pointwise_relation _ eq (funcomp (ren_tm xi) (var m))
    (funcomp (var n) xi).
Proof. exact (fun x => eq_refl). Qed.

Class Up_tm X Y := up_tm : X -> Y.

#[global] Instance Subst_tm  {m n : nat}: (Subst1 _ _ _) := (@subst_tm m n).

#[global] Instance Up_tm_tm  {m n : nat}: (Up_tm _ _) := (@up_tm_tm m n).

#[global] Instance Ren_tm  {m n : nat}: (Ren1 _ _ _) := (@ren_tm m n).

#[global] Instance VarInstance_tm  {n : nat}: (Var _ _) := (@var n).

Notation "[ sigma ]" := (subst_tm sigma)
  (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma ]" := (subst_tm sigma s)
  (at level 7, left associativity, only printing) : subst_scope.

Notation "↑__tm" := up_tm (only printing) : subst_scope.

Notation "↑__tm" := up_tm_tm (only printing) : subst_scope.

Notation "⟨ xi ⟩" := (ren_tm xi)
  (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi ⟩" := (ren_tm xi s)
  (at level 7, left associativity, only printing) : subst_scope.

Notation "'var'" := var (at level 1, only printing) : subst_scope.

Notation "x '__tm'" := (@ids _ _ VarInstance_tm x)
  (at level 5, format "x __tm", only printing) : subst_scope.

Notation "x '__tm'" := (var x) (at level 5, format "x __tm") : subst_scope.

#[global] Instance subst_tm_morphism  {m n : nat} :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_tm m n)).
Proof.
  exact (fun f_tm g_tm Eq_tm s t Eq_st =>
        eq_ind s (fun t' => subst_tm f_tm s = subst_tm g_tm t')
          (ext_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global] Instance subst_tm_morphism2 {m n : nat} :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_tm m n)).
Proof. exact (fun f_tm g_tm Eq_tm s => ext_tm f_tm g_tm Eq_tm s). Qed.

#[global] Instance ren_tm_morphism {m n : nat} :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_tm m n)).
Proof.
  exact (fun f_tm g_tm Eq_tm s t Eq_st =>
        eq_ind s (fun t' => ren_tm f_tm s = ren_tm g_tm t')
          (extRen_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global] Instance ren_tm_morphism2 {m n : nat} :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_tm m n)).
Proof. exact (fun f_tm g_tm Eq_tm s => extRen_tm f_tm g_tm Eq_tm s). Qed.

Ltac auto_unfold := repeat unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                                  Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold VarInstance_tm, Var, ids,
                                                        Ren_tm, Ren1, ren1, Up_tm_tm,
                                                        Up_tm, up_tm, Subst_tm, Subst1,
                                                        subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_tm_pointwise
                 | progress setoid_rewrite substSubst_tm
                 | progress setoid_rewrite substRen_tm_pointwise
                 | progress setoid_rewrite substRen_tm
                 | progress setoid_rewrite renSubst_tm_pointwise
                 | progress setoid_rewrite renSubst_tm
                 | progress setoid_rewrite renRen'_tm_pointwise
                 | progress setoid_rewrite renRen_tm
                 | progress setoid_rewrite varLRen'_tm_pointwise
                 | progress setoid_rewrite varLRen'_tm
                 | progress setoid_rewrite varL'_tm_pointwise
                 | progress setoid_rewrite varL'_tm
                 | progress setoid_rewrite rinstId'_tm_pointwise
                 | progress setoid_rewrite rinstId'_tm
                 | progress setoid_rewrite instId'_tm_pointwise
                 | progress setoid_rewrite instId'_tm
                 | progress
                    unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm,
                     upRen_tm_tm, up_ren
                 | progress cbn[subst_tm ren_tm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                  Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_tm_pointwise;
                  try setoid_rewrite rinstInst'_tm.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_tm_pointwise;
                  try setoid_rewrite_left rinstInst'_tm.

End Core.

Module Extra.
  Import Core.
  Arguments var {n}.
  Arguments lam {n}.
  Arguments app {n}.
  #[global] Hint Opaque subst_tm: rewrite.
  #[global] Hint Opaque ren_tm: rewrite.
End Extra.

Module interface.
  Export Core.
  Export Extra.
End interface.
Export interface.