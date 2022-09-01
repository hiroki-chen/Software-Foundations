Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export exercise5.
From Coq Require Import Setoids.Setoid.

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

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
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

Lemma mul_eq_0 : forall (n m : nat),
  n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros. split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc: forall P Q R : Prop,
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros. split.
  - intros [ H | [H | H] ].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [ [H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mul_eq_0_ternary : forall n m p,
  n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros. 
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard, especially useful (dist_not_exists) *)
(* Prove that "P holds for all x" implies "there is no x for which P does not
hold." (Hint: destruct H as [x E] works on existential assumptions!) *)
Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not. intros.
  destruct H0 as [x E]. apply E. apply H.
Qed.

(** **** Exercise: 2 stars, standard (dist_exists_or) *)
(* Prove that existential quantification distributes over disjunction. *)
Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  - intros. destruct H. destruct H.
    + left. exists x. apply H.
    + right. exists x. apply H.
  - intros. destruct H.
    + destruct H. exists x. left. apply H.
    + destruct H. exists x. right. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (leb_plus_exists) *)
Theorem leb_plus_exists: forall n m,
  n <=? m = true -> exists x, m = n + x.
Proof.
  intros n. induction n as [|n' H].
  - intros. exists m. reflexivity.
  - destruct m.
    + simpl. discriminate.
    + simpl. intros. apply H in H0. destruct H0.
      rewrite H0. exists x. reflexivity.
Qed.

Theorem plus_exists_leb : forall n m,
  exists x, m = n + x -> n <=? m = true.
Proof.
  intros. exists 0. rewrite add_0_r.
  intros. rewrite H. apply leb_refl.
Qed.

Fixpoint In {X : Type} (x : X) (l : list X) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Theorem in_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x. induction l as [| x' l' IHl].
  - simpl. intros. apply H.
  - simpl. intros [H | H].
    + left. rewrite H. reflexivity.
    + right. apply IHl. apply H.
Qed.

(** **** Exercise: 3 stars, standard (In_map_iff) *)
Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - intros H. induction l as [| x' l' IHl].
    + simpl in H. simpl. apply ex_falso_quodlibet. apply H.
    + simpl in H. destruct H.
      * exists x'. simpl. split. apply H. left. reflexivity.
      * apply IHl in H. destruct H. exists x. simpl. split.
        destruct H. apply H. right. destruct H. apply H0.
  - intros. destruct H. destruct H. rewrite <- H. apply in_map. apply H0.
Qed.


(** **** Exercise: 3 stars, standard, especially useful (All) *)
(* Recall that functions returning propositions can be seen as properties of
their arguments. For instance, if P has type nat -> Prop, then P n states that
property P holds of n. *)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x' :: l' => P x' /\ All P l'
  end.

Lemma ex_falso_quodlibet_ext : forall (T : Type) (P : T -> Prop),
  (forall x : T, False -> P x).
Proof.
Admitted.

Theorem All_in :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros. split.
  - induction l as [| x' l' IHl].
    + simpl. reflexivity.
    + simpl. intros. split.
      * apply H. left. reflexivity.
      * apply IHl. intros. apply H. right. apply H0.
  - induction l as [| x' l' IHl].
    + simpl. intros. apply ex_falso_quodlibet. apply H0.
    + simpl. intros. destruct H0.
      * rewrite H0 in H. apply proj1 in H. apply H.
      * destruct H. apply IHl. apply H1. apply H0.
Qed.

(** **** Exercise: 2 stars, standard, optional (combine_odd_even) *)
(* Complete the definition of the combine_odd_even function below. It takes as
arguments two properties of numbers, Podd and Peven, and it should return a
property P such that P n is equivalent to Podd n when n is odd and equivalent
to Peven n otherwise. *)
Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if odd n then Podd n else Peven n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros. unfold even in H, H0.
  unfold combine_odd_even.
  destruct n.
  - simpl. apply H0. simpl. reflexivity.
  - destruct (odd (S n)).
    + apply H. reflexivity.
    + apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros. unfold combine_odd_even in H.
  destruct (odd n).
  - apply H.
  - discriminate H0.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros. unfold combine_odd_even in H.
  destruct (odd n).
  - discriminate.
  - apply H.
Qed.