From Hammer Require Import Hammer.
Require Import VST.msl.sepalg.

Section OptionAlg.
  Variable A  : Type.
  Variable JA : Join A.
  Variable PA : Perm_alg A.
  Variable SA : Sep_alg A.
  Variable CA : Canc_alg A.

  #[global] Instance Join_opt : Join (option A) :=
    (fun (x y z: option A) =>
       match x, y, z with
       | Some x, Some y, Some z => JA x y z
       | None, None, None => True
       | _, _, _ => False
       end).
  (* | JSome {x y z} : JA x y z -> join_opt (Some x) (Some y) (Some z) *)
  (* | JNone : join_opt None None None. *)

  #[global] Instance Perm_opt: Perm_alg (option A).
  Proof.
    constructor; intros.

    * induction x, y, z, z'; unfold join, Join_opt in *; try (f_equal; intuition); destruct PA; strivial.

    * destruct PA; clear join_eq join_comm join_positivity.
      induction a, b, c, d, e; unfold join, Join_opt in *;
        try destruct (join_assoc _ _ _ _ _ H H0) as [f [?L ?R]];
        try exists (Some f); try exists None; intuition.

    * destruct PA; clear join_eq join_assoc join_positivity.
      induction a, b, c; unfold join, Join_opt in *; sauto.

    * destruct PA; clear join_eq join_assoc join_comm.
      induction a, a', b, b';
        unfold join, Join_opt in *; simpl in *; try f_equal; strivial.
  Qed.

  #[global] Instance Sep_opt: Sep_alg (option A).
  Proof.
    exists (fun s : option A =>
         match s with
         | Some a => Some (core a)
         | None => None
         end).

    intro t; induction t; sauto.

    destruct SA; intros a b c J; induction a, b, c; unfold join_sub, join, Join_opt in *; simpl in *; intuition;
      try (destruct (join_core_sub  _ _ _ J) as [?b ?Jb]; exists (Some b); auto);
      try (exists None; auto).

    destruct SA; intro a; induction a; strivial.
  Qed.

  #[global] Instance Canc_opt: Canc_alg (option A).
  Proof.
    unfold Canc_alg; intros a1 a2 a3 c; induction a1, a2, a3, c; hauto unfold: Canc_alg, join, Join_opt use: f_equal.
  Qed.
End OptionAlg.
