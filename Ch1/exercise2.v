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
Theorem mul_0_r : forall n : nat,
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
(** One inconvenient aspect of our definition of even n is the recursive call on n - 2. This makes 
proofs about even n harder when done by induction on n, since we may need an induction hypothesis about 
n - 2. The following lemma gives an alternative characterization of even (S n) that works better with
induction: *)
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [ | n' H].
  - reflexivity.
  - rewrite H. rewrite -> negb_involutive. reflexivity.
Qed.

Check even_S.

(** **** Exercise: 3 stars, standard, especially useful (mul_comm) *)
(** Use assert to help prove add_shuffle3. You don't need to use induction yet. *)
Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: n + m = m + n).
    { rewrite add_comm. reflexivity. }
  rewrite add_assoc. rewrite add_assoc. rewrite H. reflexivity.
Qed.

(** Now prove commutativity of multiplication. You will probably want to look for (or define and prove)
a "helper" theorem to be used in the proof of this one. Hint: what is n * (1 + k)? *)
Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n. induction m as [ | m' H].
  - simpl. apply mult_n_O.
  - simpl. rewrite -> H. rewrite <- mult_n_Sm. apply add_comm.
Qed.


(** **** Exercise: 2 stars, standard, optional (plus_leb_compat_l) *)
(** If a hypothesis has the form H: P → a = b, then rewrite H will rewrite a to b in the goal,
and add P as a new subgoal. Use that in the inductive step of this exercise. *)
Check leb.
Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H0. induction p as [ | p' H1].
  - simpl. rewrite -> H0. reflexivity.
  - simpl. rewrite -> H1. reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, optional (more_exercises) *)
(* Take a piece of paper. For each of the following theorems, first think about whether (a) it can be
proved using only simplification and rewriting, (b) it also requires case analysis (destruct), or (c) it also requires induction. Write down your prediction. Then fill in the proof. (There is no need to turn
in your piece of paper; this is just to encourage you to reflect before you hack!) *)
Theorem leb_refl : forall n : nat,
  (n <=? n) = true.
Proof.
  intros n. induction n as [ | n' H].
  - reflexivity.
  - apply H.
Qed.

Theorem zero_neqb_S : forall n : nat,
  0 =? (S n) = false.
Proof.
  simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n : nat,
  1 * n = n.
Proof.
  simpl. apply add_0_r.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Lemma add_assoc_gap: forall a b c : nat,
  a + b + c = c + b + a.
Proof.
  intros a b c. induction c as [ | c' H].
  - simpl. rewrite add_0_r. apply add_comm.
  - simpl. rewrite <- H. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros p. induction p as [ | p' H].
  - reflexivity.
  - simpl. intros n m. rewrite -> H. rewrite add_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros p. induction p as [ | p' H].
  - simpl. reflexivity.
  - intros n m. simpl. rewrite -> H. rewrite <- mult_plus_distr_r. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, optional (add_shuffle3') *)
(**  The replace tactic allows you to specify a particular subterm to rewrite and what you want it
rewritten to: replace (t) with (u) replaces (all copies of) expression t in the goal by expression u,
and generates t = u as an additional subgoal. This is often useful when a plain rewrite acts on the
wrong part of the goal.
Use the replace tactic to do a proof of add_shuffle3', just like add_shuffle3 but without needing assert. *)
Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc. rewrite -> add_assoc.
  replace (n + m) with (m + n).
  - rewrite add_comm. reflexivity.
  - rewrite add_comm. reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, especially useful (binary_commute) *)
(* Prove that the following diagram commutes:
                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S
That is, incrementing a binary number and then converting it to a (unary) natural number yields the same result as first converting it to a natural number and then incrementing.
If you want to change your previous definitions of incr or bin_to_nat to make the property easier to
prove, feel free to do so! *)
Lemma add_one_right: forall n : nat,
  n + 1 = S n.
Proof.
  intros n. induction n as [| n' H].
  - reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.

Lemma bin_to_nat_to_S: forall b : bin,
  bin_to_nat (B1 b) = S (bin_to_nat (B0 b)).
Proof.
  intros b.
  simpl. rewrite -> add_0_r. rewrite -> plus_n_Sm.
  replace (S (bin_to_nat b)) with (bin_to_nat b + 1).
    - rewrite add_assoc. reflexivity.
    - apply add_one_right.
Qed.

(* A complex proof. There must be more concise way to do so:) *)
Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  simpl.
  induction b as [| b' | b'].
  - reflexivity.
  - replace (incr (B0 b')) with (B1 b').
    + apply bin_to_nat_to_S.
    + reflexivity.
  - replace (bin_to_nat(incr (B1 b'))) with (bin_to_nat (B0 (incr b'))).
    + simpl. rewrite -> IHb'.  rewrite plus_Sn_m. rewrite -> add_0_r.
      rewrite <- plus_n_Sm. rewrite -> add_one_right. rewrite -> add_0_r. reflexivity.
    + replace (incr (B1 b')) with (B0 (incr b')).
      * reflexivity.
      * simpl. destruct b'.
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
Qed.