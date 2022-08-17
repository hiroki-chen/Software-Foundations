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

Check mult_n_1.