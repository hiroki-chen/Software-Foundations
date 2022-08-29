Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export exercise5.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros. split.
  - destruct n.
    + reflexivity.
    + discriminate.
  - destruct m.
    + reflexivity.
    + rewrite <- plus_n_Sm in H. discriminate.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP.
Qed.

(** **** Exercise: 1 star, standard, optional (proj2) *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [_ H].
  apply H.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.
Qed.

(* Exercise: 2 stars, standard (and_assoc) *)
(* (In the following proof of associativity, notice how the
nested intros pattern breaks the hypothesis H : P /\ (Q /\ R) down
into HP : P, HQ : Q, and HR : R. Finish the proof from there.) *)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split. apply HP. apply HQ. apply HR.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma or_intro_r : forall A B : Prop, B -> A \/ B.
Proof.
  intros A B HB.
  right.
  apply HB.
Qed.

Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros. induction n.
  - left. reflexivity.
  - destruct m.
    + right. reflexivity.
    + inversion H.
Qed.

(* Exercise: 1 star, standard (or_commut) *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [H1 | H2].
  - right. apply H1.
  - left. apply H2.
Qed.

Theorem ex_falso_quodlibet: forall (P : Prop),
	False -> P.
Proof.
	intros P contra.
	destruct contra.
Qed.


(* Exercise: 2 stars, standard, optional (not_implies_our_not) *)
(* Show that Coq's definition of negation implies the intuitive
one mentioned above. Hint: while getting accustomed to Coq's
definition of not, you might find it helpful to unfold not near
the beginning of proofs. *)
Theorem not_implies_our_not : forall (P : Prop),
  ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  unfold not. intros.
  apply ex_falso_quodlibet.
  apply H. apply H0.
Qed.

Theorem not_implies_our_not2 : forall (P : Prop),
  ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  intros. destruct H. apply H0.
Qed.


(* Inequality is a frequent enough form of negated statement that there is a special notation for it, x ≠ y: *)
Notation "x <> y" := (~(x = y)).

(** **** Exercise: 2 stars, advanced (double_neg_inf) *)
(* Write an informal proof of double_neg:
Theorem: P implies ~~P, for any proposition P. *)
Theorem double_neg_inf : forall (P : Prop),
  P -> ~~ P.
Proof.
  intros. unfold not.
  intros. apply H0 in H. apply H.
Qed.


(** **** Exercise: 2 stars, standard, especially useful (contrapositive) *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not. intros.
  apply H in H1. apply H0 in H1. apply H1.
Qed.


(** **** Exercise: 1 star, standard (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  unfold not. intros P [H1 H2]. apply H2 in H1. apply H1.
Qed.

(** **** Exercise: 2 stars, standard (de_morgan_not_or) *)
(* De Morgan's Laws, named for Augustus De Morgan, describe how
negation interacts with conjunction and disjunction. The
following law says that "the negation of a disjunction is the
conjunction of the negations." There is a corresponding law
de_morgan_not_and_not that we will return to at the end of thi
 chapter. *)
Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not. intros.
  split.
  - intros. apply H. apply or_intro_l. apply H0.
  - intros. apply H. apply or_intro_r. apply H0.
Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.
Qed.

Theorem not_true_is_false : forall(b : bool),
  b <> true ->  b = false.
Proof.
  intros. destruct b eqn: Hb.
  - unfold not in H. apply ex_falso_quodlibet.
    apply H. reflexivity.
  - reflexivity.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  unfold iff. intros. split.
  - intros. split.
    + destruct H.
      * apply or_intro_l. apply H.
      * apply proj1 in H. apply or_intro_r. apply H.
    + destruct H.
      * apply or_intro_l. apply H.
      * apply proj2 in H. apply or_intro_r. apply H.
  - intros [[|] [|]].
    + apply or_intro_l. apply H.
    + left. apply H.
    + left. apply H0.
    + right. split. apply H. apply H0.
Qed.