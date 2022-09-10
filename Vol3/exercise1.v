Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.  (* for manual grading *)
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.

Definition geb (n m : nat) := m <=? n.
(* Hint Unfold geb : core. *)
Infix ">=?" := geb (at level 70) : nat_scope.
Definition gtb (n m : nat) := m <? n.
(* Hint Unfold gtb : core. *)
Infix ">?" := gtb (at level 70) : nat_scope.

(* Try lia. *)
Example lia_example :
  forall i j k,
    i > j -> k > i + 3 -> k > j.
Proof.
  intros. lia.
Qed.

Definition swap(l : list nat) : list nat :=
  match l with
  | a :: b :: l' => if a >? b then b :: a :: l' else l
  | _ => l
  end.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.
Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.
Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.
Lemma gtb_reflect : forall x y, reflect (x > y) (x >? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.
Lemma geb_reflect : forall x y, reflect (x >= y) (x >=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Example reflect_example1: forall a,
    (if a <? 5 then a else 2) < 6.
Proof.
  intros.
  destruct (ltb_reflect a 5); lia.
Qed.

Hint Resolve ltb_reflect leb_reflect gtb_reflect geb_reflect eqb_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [ auto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].


Theorem swap_is_idempotent : forall l,
  swap (swap l) = swap l.
Proof.
  intros. destruct l as [| lhs l].
  - reflexivity.
  - destruct l as [| rhs l].
    + reflexivity.
    + simpl. bdestruct (lhs >? rhs).
      * simpl. bdestruct (rhs >? lhs). lia. trivial.
      * simpl. bdestruct (lhs >? rhs). lia. trivial.
Qed.

Check perm_skip.
Check perm_trans.
Check Permutation_refl.
Check Permutation_app_comm.
Check app_assoc.
Check app_nil_r.
Check app_comm_cons.

Example permut_example: forall (a b: list nat),
  Permutation (5 :: 6 :: a ++ b) ((5 :: b) ++ (6 :: a ++ [])).
Proof.
  intros.
  simpl. rewrite app_nil_r.
  apply perm_trans with (5 :: 6 :: (b ++ a)).
  - apply perm_skip. apply perm_skip. apply Permutation_app_comm.
  - apply perm_skip. apply perm_trans with (6 :: a ++ b).
    + apply perm_skip. apply Permutation_app_comm.
    + replace (6 :: a ++ b) with ((6 :: a) ++ b). apply Permutation_app_comm. trivial.
Qed.

Check Permutation_cons_inv.
Check Permutation_length_1_inv.

(* The point is, [1] != [2]. *)
Example not_a_permutation:
  ~ Permutation [1;1] [1;2].
Proof.
  unfold not. intros.
  apply Permutation_cons_inv in H. inversion H.
  apply Permutation_length_1_inv in H0.
  apply Permutation_sym in H1. apply Permutation_length_1_inv in H1.
  rewrite H0 in H1. inversion H1.
Qed.

(* 
Now we can prove that maybe_swap is a permutation: it reorders elements but does not add or remove any.
*)

Theorem swap_perm : forall l,
  Permutation l (swap l).
Proof.
  intros. destruct l.
  - trivial.
  - destruct l.
    + trivial.
    + simpl. bdestruct (n >? n0).
      * apply perm_swap.
      * trivial.
Qed.

Definition first_le_second (l : list nat) : Prop :=
  match l with
  | a :: b :: l' => a <= b
  | _ => True
  end.

Theorem swap_correct : forall l,
  Permutation l (swap l) /\ first_le_second (swap l).
Proof.
  intros. split.
  - apply swap_perm.
  - destruct l.
    + reflexivity.
    + simpl. destruct l.
      * reflexivity.
      * unfold first_le_second. bdestruct (n >? n0); lia.
Qed.

(* Forall is Coq library's version of the All proposition defined in Logic, but defined as an inductive
proposition rather than a fixpoint. Prove this lemma by induction. You will need to decide what to induct
on: al, bl, Permutation al bl, and Forall f al are possibilities. *)
Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl ->
  Forall f al -> Forall f bl.
Proof.
  intros. induction H.
  - apply H0.
  - apply Forall_cons. apply Forall_inv in H0.
    apply H0. apply Forall_inv_tail in H0.
    apply IHPermutation in H0. apply H0.
  - apply Forall_cons. apply Forall_inv_tail in H0. apply Forall_inv in H0. apply H0.
    apply Forall_cons. apply Forall_inv in H0. apply H0. apply Forall_inv_tail in H0. apply Forall_inv_tail in H0. apply H0.
  - apply IHPermutation2. apply IHPermutation1. apply H0.
Qed.