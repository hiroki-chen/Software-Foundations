From LF Require Export exercise1.
From LF Require Export exercise2.
From LF Require Export exercise3.
From LF Require Export exercise4.

Theorem eq_is_eq : forall (X : Type) (n m : X),
  n = m ->
  n = m.
Proof.
  intros X n m eq. apply eq.
Qed.

(** **** Exercise: 2 stars, standard, optional (silly_ex) *)
(* Complete the following proof using only intros and apply. *)
Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros p H1 H2 H3.
  apply H2. apply H1. apply H3.
Qed.

(** **** Exercise: 2 stars, standard (apply_exercise1) *)
(* You can use apply with previously defined theorems, not just hypotheses in the context. Use Search to find a previously-defined theorem about rev from Lists. Use that theorem as part of your (relatively short) solution to this exercise.
You do not need induction. *)
Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros. rewrite H. rewrite rev_involutive. reflexivity.
Qed.

Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.
Qed.

Fixpoint minustwo (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n') => minustwo n'
  end.

(** **** Exercise: 3 stars, standard, optional (trans_eq_exercise) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2.
  transitivity m. apply H2. apply H1.
Qed.

Theorem nat_injective: forall (n m : nat),
	S n = S m ->
	n = m.
Proof.
	intros n m H.
	injection H as Hnm. apply Hnm.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros. injection H as H1 H2.
  assert(H': z :: l = y :: l).
    {
      transitivity j. symmetry. apply H0. symmetry. apply H2.
    }
  rewrite H1.
  injection H'. apply eq_is_eq.
Qed.
Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.
Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

(** **** Exercise: 1 star, standard (discriminate_ex3) *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros. induction l as [| n l H'].
  - simpl. discriminate H.
  - simpl. apply H'. discriminate.
Qed.

Theorem double_injective: forall n m : nat,
	double n = double m ->
	n = m.
Proof.
  intros n. induction n as [| n' H].
  - simpl. intros m eq. destruct m.
    + reflexivity.
    + discriminate eq.
  - intros m eq. destruct m as [| m'].
    + discriminate.
    + apply f_equal. apply H.
      simpl in eq. injection eq as goal.
      apply goal.
Qed.

(** **** Exercise: 2 stars, standard (eqb_true) *)
Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros m. induction m as [| m' H].
  - intros n H'. destruct n.
    + reflexivity.
    + discriminate.
  - intros n H'. destruct n.
    + discriminate.
    + simpl in H'. apply f_equal. apply H. apply H'.
Qed.


(** **** Exercise: 3 stars, standard, especially useful (plus_n_n_injective) *)
(* In addition to being careful about how you use intros, practice using "in"
variants in this proof. (Hint: use plus_n_Sm.) *)
Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros. rewrite <- double_plus in H. rewrite <- double_plus in H.
  apply double_injective. apply H.
Qed.

(** **** Exercise: 3 stars, standard, especially useful (gen_dep_practice) *)
(* Prove this by induction on l. *)
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| n' l' IHl].
  - intros. reflexivity.
  - intros. destruct n.
    + discriminate.
    + simpl. apply IHl. simpl in H. injection H. apply eq_is_eq.
Qed.

Definition square n : nat := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc. 
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    {
      rewrite mul_comm.
      rewrite <- mult_assoc.
      reflexivity.
    }
  rewrite H. reflexivity.
Qed.

