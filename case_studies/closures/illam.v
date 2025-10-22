(** intrinsic presentation of the linear lambda calculus: 
This version is autartic: does not use MSL
*)

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Unicode.Utf8.
From Coq Require Import Lia.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.
Require Import Program.
Require Import FunctionalExtensionality.


Inductive mult : Type :=
| zero : mult (* used *)
| one : mult (* available linearly *)
.

Inductive mult_op:   mult ->  mult  -> mult -> Prop:=
| m_00 : mult_op zero zero zero
| m_10 : mult_op one zero  one
| m_01 : mult_op zero one one.

Notation "c == a • b" := (mult_op a b c) (at level 50, left associativity).


Variant hal : mult → Prop :=
| halz : hal zero.

Inductive Ty := TOP | ARR (ty1 ty2 : Ty) .


Ltac inv H := inversion H; subst; clear H; trivial.

(** list based contexts*)

Inductive exh {R A: Type} (hal : A -> Prop) : list (R * A) -> Prop :=
| exh_n : exh hal []
| exh_c : forall {Δ : list (R * A)} (X : R) {α : A},
    exh hal Δ -> hal α -> exh hal ((X, α) :: Δ).


Definition mlctx (R: Type) {A: Type} := list (R * A).
(*
Inductive merge {R A: Type} : mlctx R A -> mlctx R A-> mlctx R A-> Prop :=
| mg_n : merge  [] [] []
| mg_c r {delta1 delta2 delta alpha1 alpha2 alpha} :
  mult_op alpha1 alpha2 alpha ->
  merge delta1 delta2 delta ->
  merge ((r, alpha1) :: delta1) ((r, alpha2) :: delta2) ((r, alpha) :: delta)
.
*)


Definition tenv := list( Ty* mult).

Inductive upd :
  tenv  -> Ty-> Ty-> mult -> mult  -> tenv -> Prop :=
| upd_here : forall (Δ : tenv) X X'  A A' ,
    upd ((X, A) :: Δ)  X X' A A' ((X', A') :: Δ)
| upd_there : forall (Δ Δ' : tenv )  (X X' Y : Ty) (A A' B : mult),
    upd Δ X X' A A' Δ' ->
    upd  ((Y, B) :: Δ) X X' A A' ((Y, B) :: Δ').

Inductive merge : list( Ty* mult) -> list ( Ty* mult)-> list ( Ty* mult) -> Prop :=
| mg_n : merge [] [] []
| mg_c r {delta1 delta2 delta alpha1 alpha2 alpha} :
  mult_op alpha1 alpha2 alpha ->
  merge delta1 delta2 delta ->
  merge ((r, alpha1) :: delta1) ((r, alpha2) :: delta2) ((r, alpha) :: delta).

Definition join := merge.

Set Implicit Arguments.




(*=TyEnv *)

(*| LIST (ty : Ty)*)

Definition Env := tenv.
(*=End *)

(*=Syntax*)
(*
Inductive Var : Env -> Ty -> Type := 
| ZVAR : forall E t, Var (t::E) t
| SVAR : forall E t t', Var E t -> Var (t'::E) t.
*)


Inductive Exp E : Ty -> Type :=
| VAR  : forall t E' , upd E    t t one zero E' -> exh (fun x => True) E' -> Exp E t
| UNIT : exh (fun x => True) E -> Exp E TOP
(*
| NIL  : forall t, Exp E (LIST t)
| CONS : forall t, Exp E t -> Exp E (LIST t) -> Exp E (LIST t)
| CASE : forall t1 t2, Exp E (LIST t1) -> Exp E t2 ->
                 Exp (t1 :: (LIST t1) :: E) t2 -> Exp E t2
*)
| LAM  : forall t1 t2, Exp ((t1,one) :: E) t2 -> Exp E (ARR t1 t2)
| APP  : forall t1 t2 E1 E2, Exp E1 (ARR t1 t2) -> Exp E2 t1 -> merge E1 E2 E -> Exp E t2
(*| FIX  : forall t, Exp (t :: E) t -> Exp E t*)
.
(*=End *)

Definition Var E T := exists E' M M', upd E T T M M' E'. 
(*=Substitutions*)
Definition Sub E E' := forall t, Var E t -> Exp E' t.

Definition GSub E := Sub E [].
(*
Definition idSub {E} : Sub E E := @VAR E.

Program Definition consSub {E E' t} (e:Exp E' t) (s:Sub E E') 
  : Sub (t::E) E' :=
  fun t' (v:Var (t::E) t') => 
    match v with
    | ZVAR _ _  => e
    | SVAR _ v' => s _ v'
    end.

Notation "{| e ; .. ; f |}" := (consSub e .. (consSub f idSub) ..).

Lemma Var_nil : forall t, Var [] t -> False.
Proof. intros. inversion H. Defined.

Definition nilSub {E'} : Sub [] E' :=
  fun t v => False_rec (Exp E' t) (Var_nil v).

Definition tlSub {E E' t} (s:Sub (t::E) E') : Sub E E' := 
  fun t' v => s t' (SVAR t v).

Definition hdSub {E E' t} (s:Sub (t::E) E') : Exp E' t := 
  s t (ZVAR _ _).
(*=End *)

(*=Ren *)
Definition Ren E E' := forall t, Var E t -> Var E' t.

Definition Ren_Sub {E E'} (r:Ren E E') := fun t v => VAR (r t v).

Definition idRen {E} : Ren E E := fun t v => v.

(*
Lemma consRen {E E' t} (var0:Var E' t) (r:Ren E E') : Ren (t::E) E'.
Proof.
unfold Ren; intro t'; intro var.

dependent destruction var.
- apply var0.
- apply r; apply var.
Defined.
*)
(*Program 
Definition consRen {E E' t} (var0:Var E' t) (r:Ren E E') : Ren (t::E) E' :=
  fun t' (var:Var (t::E) t') => 
    match var with
    | ZVAR _ _    => var0
    | SVAR _ var' => r _ var'
    end.*)

Definition tlRen {E E' t} (r:Ren (t::E) E') : Ren E E' := 
  fun t' v => r t' (SVAR t v).

Definition hdRen {E E' t} (r:Ren (t::E) E') : Var E' t := 
  r t (ZVAR _ _).
(*=End *)

(*=RTmExp*)
Program Definition RTmL {E E' t}
  (r : Ren E E') : Ren (t::E) (t::E') := fun t' v => 
  match v with
  | ZVAR _ _  => ZVAR _ _
  | SVAR _ v' => SVAR _ (r _ v')
  end.

Fixpoint RTmExp E E' t (r:Ren E E') (e:Exp E t) : Exp E' t :=
  match e with
  | VAR v            => VAR (r _ v)
  | UNIT _           => UNIT E'
  | NIL _ _          => NIL E' _
  | CONS e e1        => CONS (RTmExp r e) (RTmExp r e1)
  | CASE e e1 e2 => CASE (RTmExp r e) (RTmExp r e1) (RTmExp (RTmL (RTmL r)) e2)
  | APP e1 e2    => APP (RTmExp r e1) (RTmExp r e2)
  | LAM e        => LAM (RTmExp (RTmL r) e)
  | FIX e          => FIX (RTmExp (RTmL r) e)
  end.
(*=End *)

(*=STmExp *)
Definition ShTmExp E t t' : Exp E t -> Exp (t'::E) t 
  := RTmExp (fun _ v => SVAR _ v).

Program Definition 
  STmL {E E'} t (s:Sub E E') : Sub (t::E) (t::E') :=  
  fun t' v => 
  match v with
  | ZVAR _ _ => VAR (ZVAR _ _)
  | SVAR _ v' => ShTmExp t (s _ v')
  end.

Fixpoint STmExp E E' t (s:Sub E E') (e:Exp E t) : Exp E' t :=
  match e with
  | VAR v        => s _ v
  | UNIT _       => UNIT E'
  | NIL _ _      => NIL E' _
  | CONS e e1    => CONS (STmExp s e) (STmExp s e1)
  | CASE e e1 e2 => CASE (STmExp s e) (STmExp s e1) (STmExp (STmL (STmL s)) e2)
  | APP e1 e2    => APP (STmExp s e1) (STmExp s e2)
  | LAM e        => LAM (STmExp (STmL s) e)
  | FIX e        => FIX (STmExp (STmL s) e)
  end.
(*=End *)

(*=Compose *)
Definition RcR {E E' E''} (r : Ren E' E'') r' := 
  (fun t v => r t (r' t v)) : Ren E E''.
Definition ScR {E E' E''} (s : Sub E' E'') r  := 
  (fun t v => s t (r  t v)) : Sub E E''.
Definition RcS {E E' E''} (r : Ren E' E'') s  := 
  (fun t v => RTmExp r (s t v)) : Sub E E''.
Definition ScS {E E' E''} (s : Sub E' E'') s' := 
  (fun t v => STmExp s (s' t v)) : Sub E E''.
(*=End *)

(*=Tactics *)
Ltac Rewrites E := 
  (intros; simpl; try rewrite E; 
   repeat (match goal with | [H : context[eq _ _] |- _] => rewrite H end); 
   auto).

Ltac ExtVar :=
 match goal with
    [ |- eq ?X ?Y ] => 
    (apply (@functional_extensionality_dep _ _ X Y) ; 
     let t := fresh "t" in intro t;
     apply functional_extensionality; 
     let v := fresh "v" in intro v; 
     dependent destruction v; auto) 
  end.
(*=End *)

(*=Ren_Sub Lemmas*)
Lemma Lift_Ren_Sub : forall E E' (r:Ren E E') t, Ren_Sub (RTmL (t:=t) r) = STmL (Ren_Sub r).
Proof. intros. ExtVar. Qed.

Lemma Action_Ren_Sub : forall E t (e:Exp E t) E' (r:Ren E E'), RTmExp r e = STmExp (Ren_Sub r) e.
Proof. induction e; repeat Rewrites Lift_Ren_Sub. Qed.
(*=End*)

(*=IdLemmas *)
Lemma LiftIdSub : forall E t, STmL (@idSub E) = @idSub (t::E). 
Proof. intros. ExtVar. Qed.

Lemma ActionIdSub : forall E t (e : Exp E t), STmExp idSub e = e. 
Proof. induction e; Rewrites LiftIdSub; Rewrites LiftIdSub. Qed.
(*=End *)

(*=Grnd Sub Lemmas*)
Lemma Grnd_GSub_Id : forall g : GSub [], g = idSub.
intro.
apply functional_extensionality_dep; intro.
apply functional_extensionality; intro.
inversion x0.
Qed.

Lemma Grnd_GSub : forall t (e:Exp [] t) (g:GSub _), STmExp g e = e.
Proof.
intros.
rewrite (Grnd_GSub_Id g).
rewrite ActionIdSub.
reflexivity.
Qed.
(*=End*)

(*=ComposeLemmas *)
Lemma LiftRcR : forall E E' E'' t (r:Ren E' E'') (r':Ren E E'), 
  RTmL (t:=t) (RcR r r') = RcR (RTmL r) (RTmL r').
Proof. intros. ExtVar. Qed.

Lemma ActionRcR : forall E t (e:Exp E t) E' E'' (r:Ren E' E'') (r':Ren E E'), 
  RTmExp (RcR r r') e = RTmExp r (RTmExp r' e).
Proof. induction e; Rewrites LiftRcR; Rewrites LiftRcR. Qed.

Lemma LiftScR : forall E E' E'' t (s:Sub E' E'') (r:Ren E E'), 
  STmL (t:=t) (ScR s r) = ScR (STmL s) (RTmL r).
Proof. intros. ExtVar. Qed.

Lemma ActionScR : forall E t (e:Exp E t) E' E'' (s:Sub E' E'') (r:Ren E E'), 
  STmExp (ScR s r) e = STmExp s (RTmExp r e).
Proof. induction e; Rewrites LiftScR; Rewrites LiftScR. Qed.

Lemma LiftRcS : forall E E' E'' t (r:Ren E' E'') (s:Sub E E'), 
  STmL (t:=t) (RcS r s) = RcS (RTmL r) (STmL s).
Proof. intros. ExtVar. unfold RcS. simpl. 
unfold ShTmExp. rewrite <- 2 ActionRcR. auto. Qed.

Lemma ActionRcS : forall E t (e:Exp E t) E' E'' (r:Ren E' E'') (s:Sub E E'), 
  STmExp (RcS r s) e = RTmExp r (STmExp s e).
Proof. induction e; Rewrites LiftRcS; Rewrites LiftRcS. Qed. 

Lemma LiftScS : forall E E' E'' t (s:Sub E' E'') (s':Sub E E'), 
  STmL (t:=t) (ScS s s') = ScS (STmL s) (STmL s').
Proof. intros. ExtVar. simpl. unfold ScS. simpl. 
unfold ShTmExp. rewrite <- ActionRcS. rewrite <- ActionScR. auto. Qed.

Lemma ActionScS : forall E t (e:Exp E t) E' E'' (s:Sub E' E'') (s':Sub E E'), 
  STmExp (ScS s s') e = STmExp s (STmExp s' e).
Proof. induction e; Rewrites LiftScS; Rewrites LiftScS. Qed. 
(*=End *)

(*=consSub Lemma*)
Lemma Sub_consSub : forall t E E' (s : Sub (t::E) E'), s = consSub (hdSub s) (tlSub s).
Proof. intros. ExtVar. Qed.

Lemma ScR_consSubone : forall E t (e:Exp E t),
            idSub = ScR {|e|} (fun (t0 : Ty) (v : Var E t0) => SVAR t v).
Proof. intros. ExtVar. Qed.

Lemma consSub_ScS : forall E E' t (e:Exp E' t) (s:Sub E E'),
            (consSub e s) = ScS {|e|} (STmL s).
Proof.
intros; unfold ScS; ExtVar; simpl.
unfold ShTmExp.
rewrite <- ActionScR.
rewrite <- ScR_consSubone.
rewrite ActionIdSub.
reflexivity.
Qed.

(*Lemma Sub_nil : forall E' (s:Sub [] E'), s = nilSub.
Proof. intros. ExtVar. Qed.*)

Lemma ActionnilSub : forall E' (g:GSub E'), ScS g nilSub = idSub.
Proof. intros. unfold ScS. ExtVar. Qed.
(*=End *)

(*=Val*)
Inductive Val : forall t, Exp [] t -> Prop :=
| ValUNIT : Val (UNIT _)
| ValNIL  : forall t, Val (NIL _ t)
| ValCONS : forall t (e:Exp _ t) e1, Val (CONS e e1)
| ValLAM  : forall t1 t2 (e:Exp [t1] t2), Val (LAM e).
(*=End*)

(*=Ev *)
Inductive Ev : forall t, Exp nil t -> Exp nil t -> Prop :=
| EvCASEN : forall t1 t2 (e:Exp _ (LIST t1)) (e1:Exp _ t2) e2 x,
    Ev e (NIL _ _) -> Ev e1 x -> Ev (CASE e e1 e2) x
| EvCASEC : forall t1 t2 (e:Exp nil (LIST t1)) h t (e1:Exp nil t2) e2 x,
    Ev e (CONS h t) -> Ev (STmExp {| h ; t |} e2) x -> Ev (CASE e e1 e2) x
| EvAPP   : forall t1 t2 e v (e1 : Exp nil (ARR t1 t2)) e2,
    Ev e1 (LAM e) -> Ev (STmExp {| e2 |} e) v ->
    Ev (APP e1 e2) v
| EvFIX   : forall t (e:Exp _ t) x, Ev (STmExp {| (FIX e) |} e) x -> Ev (FIX e) x
| EvVal   : forall t (e:Exp [] t), Val e -> Ev e e.

(*=End *)

(*=Convrg*)
Definition Convrg : forall t, Exp nil t -> Prop :=
  fun t e => exists f, Ev e f.

(*Lemma ExExp : forall E t, Exp E t.
Proof.
repeat intro; generalize E; clear E.
induction t; intro.
- apply UNIT.
- apply LAM.
  apply IHt2.
- apply NIL.
Qed.*)

Lemma ExConvrg : forall E t, exists (e:Exp E t), forall g, Convrg (STmExp g e).
Proof.
intros.
induction t.
- exists (UNIT _).
  intro; simpl.
  repeat econstructor.
- destruct IHt2; exists (LAM (ShTmExp _ x)).
  intro; simpl.
  repeat econstructor.
- exists (NIL _ _).
  intro; simpl.
  repeat econstructor.
Qed.

Lemma ExNotConvrg : forall E t, exists (e:Exp E t), forall g, not (Convrg (STmExp g e)).
Proof.
intros.
exists (FIX (VAR (ZVAR _ _))).
simpl; repeat intro.
dependent destruction H.
dependent induction H.
- apply IHEv.
  + apply g.
  + reflexivity.
- inversion H.
Qed.

(*=End *)

(*=Determinacy *)
Lemma Determinacy :
  forall t (e : Exp nil t) v1, Ev e v1 -> forall v2, Ev e v2 -> v1 = v2.
(*=End *)
Proof.
intros t e v1 ev1. induction ev1; intros v2 ev2.
dependent destruction ev2.
  specialize (IHev1_2 _ ev2_2); auto.
  specialize (IHev1_1 _ ev2_1); inversion IHev1_1.
  inversion H.
dependent destruction ev2.
  specialize (IHev1_1 _ ev2_1); inversion IHev1_1.
  specialize (IHev1_1 _ ev2_1); dependent destruction IHev1_1;
    specialize (IHev1_2 _ ev2_2); auto.
  inversion H.
dependent destruction ev2; try reflexivity.
  specialize (IHev1_1 _ ev2_1); dependent destruction IHev1_1;
  specialize (IHev1_2 _ ev2_2); dependent destruction IHev1_2; auto.
  inversion H.
dependent destruction ev2.
  specialize (IHev1 _ ev2); auto.
  inversion H.
dependent destruction H; dependent destruction ev2; reflexivity.
Qed.


Lemma Ev_Val_end : forall t (e f:Exp [] t), Ev e f -> Val f.
Proof.
intros.
elim H; auto.
Qed.

(*=End*)
*)
