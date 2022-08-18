Inductive bool: Type :=
  | true
  | false.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true =>
    match b2 with
    | true =>
      match b3 with
      | true => true 
      | false => false
      end
    | false => false
    end
  | false => false
  end.

Definition andb (lhs rhs : bool) : bool :=
  match lhs with
  | true => rhs
  | false => false
  end.

Definition orb (lhs rhs : bool) : bool :=
  match lhs with
  | true => true
  | false => rhs
  end.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise factorial. *)
(* Some helper functions. *)
Fixpoint add (lhs rhs: nat) : nat :=
  match lhs with
  | O => rhs
  | S n' => S (add n' rhs)
  end.

Fixpoint minus (lhs rhs: nat) : nat :=
  match lhs, rhs with
  | O, _ => O
  | S _, O => lhs
  | S n', S m' => minus n' m'
  end.

Fixpoint mul (lhs rhs: nat) : nat :=
  match lhs with
  | O => O
  | S n' => add (rhs) (mul n' rhs)
  end.

Fixpoint fact (n: nat) : nat :=
  match n with
  | O => S O
  | S n' => mul (S n') (fact n')
  end.

Example test_factorial1: (fact 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (fact 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.


Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

(* Implementation of <. *)
(* a < b <=> (a <= b) /\ !(a = b). *)
Definition ltb (lhs rhs: nat) : bool :=
  match (leb lhs rhs) with
  | false => false
  | true =>
    match (eqb lhs rhs) with
    | true => false
    | false => true
    end
  end.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Proof *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H0 H1.
  rewrite <- H1.
  rewrite -> H0.
  (* Apply the hypotheses on both sides of the expression. *)
  simpl.
  reflexivity.
Qed.

(* 0 is also the right-identity element for the additive group. *)
(* There is a lemma from standard library so we just need to apply transivity. *)
Lemma mult_0_l : forall n : nat,
  n * 0 = 0.
Proof.
  intros n.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

(* Proof using theorems already proved *)
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  (* p * 1 => p * 0 + p *)
  rewrite <- mult_n_Sm.
  (* p * 0 + p=> 0 + p *)
  rewrite -> mult_0_l.
  (* 0 +  => p. *)
  rewrite -> plus_O_n.
  reflexivity.
Qed.

(* Helper theorems. *)
Theorem andb_commutative : forall b c,
  andb b c = andb c b.
Proof.
  intros b c. destruct b eqn: Eb.
  - destruct c eqn: Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn: Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb3_exchange : forall b c d,
  andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn: Eb.
  - destruct c eqn: Ec.
    + reflexivity.
    + simpl. discriminate.
  - destruct c eqn: Ec.
    + simpl. discriminate.
    + simpl. discriminate.
Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.


(* Exercise optional: ill-formed recursion. *)
(* Fixpoint infinite (n : nat) : nat :=
  match n with
  | O => S (infinite O)
  | S n' => S (infinite n')
  end. *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f(b)) = b.
Proof.
  intros H0 H1.
  intros b.
  rewrite -> H1.
  rewrite -> H1.
  reflexivity.
Qed.

Lemma negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
  Qed.

Theorem negation_fn_applied_twice:
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f(b)) = b.
Proof.
  intros H0 H1.
  intros b.
  rewrite -> H1. rewrite -> H1. apply negb_involutive.
Qed.

(* Not the best way. *)
Theorem andb_eq_orb :
  forall(b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + simpl. discriminate.
  - destruct c.
    + simpl. discriminate.
    + reflexivity.
Qed.

(** **** Exercise: 3 stars, optional (andb_eq_orb)  *)
(** Prove the following theorem.  (Hint: This one can be a bit tricky,
    depending on how you approach it.  You will probably need both
    [destruct] and [rewrite], but destructing everything in sight is
    not the best way.) *)
Theorem andb_eq_orb_2 :
  forall(b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b.
  - simpl. intros H. rewrite <- H. reflexivity.
  - simpl. intros H. rewrite <- H. reflexivity.
Qed.

(** **** Exercise: 3 stars, standard (binary) *)
(** Complete the definitions below of an increment function incr for binary numbers, 
   and a function bin_to_nat to convert binary numbers to unary numbers. *)
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m : bin) : bin :=
  match m with 
  | Z => B1 Z
  | B1 Z => B0 (B1 Z)
  | B0 z' => B1 z'
  | B1 z' => B0 (incr z') 
  end.

Compute incr (B1 (B1 (B1 Z))).

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => O
  | B1 Z => S O
  | B0 z' => S (S O) * bin_to_nat (z')
  | B1 z' => S (S O) * bin_to_nat (z') + S O
  end.

Compute bin_to_nat (incr (incr (B1 Z))).
Compute 2 + bin_to_nat (B1 Z).
Compute bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).