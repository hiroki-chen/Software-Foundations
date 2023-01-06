Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From VFA Require Import exercise1.

Fixpoint insert (n : nat) (l : list nat) : list nat :=
  match l with
  | [] => [n]
  | n' :: l' => if n' >? n then n :: n' :: l' else n' :: (insert n l')
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | n :: l' => insert n (sort l')
  end.

Inductive sorted : list nat -> Prop :=
  | sorted_nil :
      sorted []
  | sorted_1 : forall x,
      sorted [x]
  | sorted_cons : forall x y l,
      x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Definition sorted' (l : list nat) := forall i j iv jv,
  i < j ->
  nth_error l i = Some iv ->
  nth_error l j = Some jv ->
  iv <= jv.

Definition sorted'' (l : list nat) := forall i j,
  i < j < length l ->
  nth i l 0 <= nth j l 0.

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall l,
  Permutation l (f l) /\ sorted (f l).

Lemma le_gt_false : forall x y,
  x <= y -> x >? y = false.
Proof.
  intros. bdestruct (x >? y).
  - lia.
  - reflexivity.
Qed.

(* **** Exercise: 3 stars, standard (insert_sorted) *)
(* Prove that insertion maintains sortedness. Make use of tactic
    bdestruct, defined in Perm. *)
Lemma sorted_is_sorted : forall x y,
  x <= y -> sorted [x; y].
Proof.
  intros. apply sorted_cons. apply H. apply sorted_1.
Qed.

Lemma ge_false : forall x y,
  x >= y -> ~ (y > x).
Proof.
  intros. lia.
Qed.

Lemma insert_sorted:
  forall a l, sorted l -> sorted (insert a l).
Proof.
  intros. induction H.
  - apply sorted_1.
  - simpl. bdestruct (x >? a); apply sorted_is_sorted; lia.
  - simpl. bdestruct (x >? a). apply sorted_cons. lia. apply sorted_cons. lia. apply H0.
    bdestruct (y >? a). apply sorted_cons. lia. apply sorted_cons. lia. apply H0.
    apply sorted_cons. apply H.
    simpl in IHsorted.
    bdestruct (y >? a).
    * apply ge_false in H2. unfold not in H2. apply H2 in H3. inversion H3.
    * apply IHsorted.
Qed.

(** **** Exercise: 2 stars, standard (sort_sorted) *)
(* Using insert_sorted, prove that insertion sort makes a list sorted. *)
Theorem sort_sorted: forall l, sorted (sort l).
Proof.
  intros. induction l.
  - apply sorted_nil.
  - simpl. apply insert_sorted. apply IHl.
Qed.

(** **** Exercise: 3 stars, standard (insert_perm) *)
(* The following lemma will be useful soon as a helper. Take advantage of helpful theorems from the
Permutation library. *)
Lemma insert_perm: forall x l,
    Permutation (x :: l) (insert x l).
Proof.
  intros. induction l.
  - simpl. apply Permutation_refl.
  - simpl. bdestruct (a >? x).
    + apply Permutation_refl.
    + apply perm_trans with (a :: x :: l).
      * apply perm_swap.
      * apply perm_skip. apply IHl.
Qed.

(** **** Exercise: 3 stars, standard (sort_perm) *)
(* Prove that sort is a permutation, using insert_perm. *)
Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  intros. induction l.
  - apply perm_nil.
  - simpl. apply perm_trans with (a :: sort l).
    + apply perm_skip. apply IHl.
    + apply insert_perm.
Qed.

(* Exercise: 1 star, standard (insertion_sort_correct) *)
(* Finish the proof of correctness! *)
Theorem insertion_sort_correct:
    is_a_sorting_algorithm sort.
Proof.
  intros. split.
  - apply sort_perm.
  - apply sort_sorted.
Qed.

(* Summary: *)
(* 
  First, we need to define what a sorting algorithm is:
    - It should be a permutation of the original list.
    - It should be a 
*)