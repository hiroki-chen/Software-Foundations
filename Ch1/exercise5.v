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

(* In fact, this is injection. *)
Lemma pair_eq : forall X Y (x1 x2: X) (y1 y2 : Y),
  (x1, y1) = (x2, y2) ->
  x1 = x2 /\ y1 = y2.
Proof.
  intros. injection H as H1 H2.
  split.
  - apply H1.
  - apply H2.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| n l' IHl].
  - intros. simpl in H. apply pair_eq in H.
    destruct H. rewrite <- H. rewrite <- H0. reflexivity.
  - destruct n as [n1 n2]. simpl. destruct (split l').
    + simpl. intros l1 l2 H.
      apply pair_eq in H. destruct H. rewrite <- H. rewrite <- H0.
      assert(H' : combine x y = l').
      {
        apply IHl. reflexivity.
      }
      rewrite <- H'. reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

  Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn: Heqn3.
  - apply eqb_true in Heqn3. rewrite Heqn3. reflexivity.
  - destruct (n =? 5) eqn : Heqn5.
    + apply eqb_true in Heqn5. rewrite Heqn5. reflexivity.
    + discriminate eq.
Qed.

(** **** Exercise: 2 stars, standard (destruct_eqn_practice) *)
Theorem bool_fn_applied_thrice : forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros. destruct b.
  - destruct (f true) eqn: H1.
    + rewrite H1. apply H1.
    + destruct (f false) eqn: H2.
      * apply H1.
      * apply H2.
  - destruct (f false) eqn: H1.
    +  destruct (f true) eqn : H2.
      * apply H2.
      * apply H1.
    + rewrite H1. apply H1.
Qed.

(** **** Exercise: 3 stars, standard (eqb_sym) *)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n. induction n as [| n' H].
  - intros m. destruct m.
    * reflexivity.
    * reflexivity.
  - intros m. destruct m.
    * reflexivity.
    * simpl. apply H.
Qed.


(** **** Exercise: 3 stars, standard, optional (eqb_trans) *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros. apply eqb_true in H. apply eqb_true in H0.
  rewrite H. rewrite <- H0. apply eqb_refl.
Qed.


(** **** Exercise: 3 stars, advanced (split_combine) *)
(* We proved, in an exercise above, that combine is the inverse of split. Complete the definition of split_combine_statement below with a property that
states that split is the inverse of combine. Then, prove that the property
holds. *)
(* Hint: Take a look at the definition of combine in Poly. Your property will
need to account for the behavior of combine in its base cases, which possibly
drop some list elements. *)
Definition split_combine_statement : Prop :=
  forall (X: Type) (l1 l2: list X),
  length l1 = length l2 ->
  split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X l1. induction l1 as [| n l1' H].
  - intros. simpl. destruct l2.
    + reflexivity.
    + inversion H.
  - intros. destruct l2.
    + simpl. inversion H0.
    + inversion H0. apply H in H2. simpl. rewrite H2. simpl. reflexivity.
Qed.
  
