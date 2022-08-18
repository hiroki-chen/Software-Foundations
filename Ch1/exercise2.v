From LF Require Export exercise1.

Theorem add_0_r: forall n : nat,
  n + 0 = n.
Proof.
  intros n. induction n as [ | n' H].
  - reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.

Theorem add_0_l: forall n : nat,
  n = n + 0.
Proof.
  intros n. induction n as [ | n' H].
  - reflexivity.
  - simpl. rewrite <- H. reflexivity.
Qed.

Theorem minus_n_n: forall n : nat,
  n - n = 0.
Proof.
  intros n. induction n as [ | n' H].
  - reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (basic_induction)*)
(** Prove the following using induction. You might need previously proven results. *)
Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [ | n' H].
  - reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [ | n' H].
  - reflexivity.
  - simpl. rewrite <- H. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [ | n' H].
  - rewrite -> add_0_r. reflexivity.
  - simpl. rewrite -> H. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [ | n' H ].
  - rewrite -> add_0_l. rewrite <- add_0_l. reflexivity.
  - simpl. rewrite <- plus_Sn_m. rewrite <- H. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (double_plus) *)
(** Consider the following function, which doubles its argument: *)
Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n,
  double n = n + n.
Proof.
  intros n. induction n as [ | n' H ].
  - reflexivity.
  - simpl. rewrite -> H. rewrite <- plus_n_Sm. reflexivity.
Qed.


(** **** Exercise: 2 stars, standard (eqb_refl) *)
(** The following theorem relates the computational equality =? 
  on nat with the definitional equality = on bool. *)
Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n. induction n as [ | n' H].
  - reflexivity.
  - rewrite <- H. simpl. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, optional (even_S) *)
(** One inconvenient aspect of our definition of even n is the recursive call on n - 2. This makes proofs about even n harder when done by induction on n, since we may need an induction hypothesis about n - 2. The following lemma gives an alternative characterization of even (S n) that works better with induction: *)
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [ | n' H].
  - reflexivity.
  - rewrite H. rewrite -> negb_involutive. reflexivity.
Qed.

Check even_S.