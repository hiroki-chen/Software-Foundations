Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export exercise6.
From Coq Require Import Lia.

Fixpoint div2 (n : nat) :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition f (n : nat) :=
  if even n then div2 n
  else 3 * n + 1.

Fail Fixpoint reaches_1_in (n : nat) :=
  if n =? 1 then 0
  else 1 + reaches_1_in (f n).

Inductive reaches_1 : nat -> Prop :=
  | term_done : reaches_1 1
  | term_more (n : nat) : reaches_1 (f n) -> reaches_1 n.

Conjecture collatz : forall n, reaches_1 n.

Module LePlayground.

Inductive le : nat -> nat -> Prop :=
| le_n (n : nat) : le n n
| le_S (n m : nat) : le n m -> le n (S m).

End LePlayground.

(* Basic requirement for a closure : R \subsetof C. *)
Inductive clos_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | t_step (x y : X) :
    R x y ->
    clos_trans R x y
  | t_trans (x y z : X) :
    clos_trans R x y ->
    clos_trans R y z ->
    clos_trans R x z.

(* Exercise: 1 star, standard, optional (close_refl_trans) *)
(* How would you modify this definition so that it defines reflexive and
transitive closure? How about reflexive, symmetric, and transitive closure? *)
Inductive clos_refl_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | rt_step (x y : X) : R x y -> clos_refl_trans R x y (* contain *)
  | rt_refl (x : X) : clos_refl_trans R x x            (* reflexivity. *)
  | rt_trans (x y z : X) :
    clos_refl_trans R x y -> clos_refl_trans R y z -> clos_refl_trans R x z.
    (* transivity. *)

Inductive clos_refl_trans_symm {X : Type} (R : X -> X -> Prop) :
  X -> X -> Prop :=
  | rts_step(x y : X) : R x y -> clos_refl_trans_symm R x y
  | rts_symm(x y : X) : clos_refl_trans_symm R x y -> clos_refl_trans_symm R y x
  | rts_refl(x : X) : clos_refl_trans_symm R x x
  | rts_trans(x y z : X) : 
    clos_refl_trans_symm R x y ->
    clos_refl_trans_symm R y z ->
    clos_refl_trans_symm R x z.

Inductive Perm3 {X : Type}: list X -> list X -> Prop :=
  | perm3_swap12 (x y z : X) :
    Perm3 [x;y;z] [y;x;z]
  | perm3_swap23 (x y z : X) :
    Perm3 [x;y;z] [x;z;y]
  | perm3_trans (l1 l2 l3 : list X) :
    Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(* These evidence constructors can be thought of as "primitive evidence of
evenness", and they can be used just like proven theorems. *)
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem ev_4: ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros. induction n as [| n' H].
  - simpl. apply ev_0.
  - rewrite double_incr. apply ev_SS. apply H.
Qed.

Theorem ev_inversion : forall n : nat,
  ev n ->
  (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros. destruct H.
  - left. reflexivity.
  - right. exists n. split. reflexivity. apply H.
Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros. apply ev_inversion in H. destruct H as [H1 | H2].
  - discriminate.
  - destruct H2 as [n' [H3 H4]]. injection H3. intros. rewrite H. apply H4.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  unfold not. intros. inversion H.
Qed.

(** **** Exercise: 1 star, standard (inversion_practice) *)
(* Prove the following result using inversion. (For extra practice, you can also
prove it using the inversion lemma.) *)
Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros. inversion H. inversion H1.
  apply H3.
Qed.

(** **** Exercise: 1 star, standard (ev5_nonsense) *)
(* Prove the following result using inversion. *)
Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros. inversion H.
  inversion H1. inversion H3.
Qed.

Theorem ev_Even : forall n,
  ev n -> Even n.
Proof.
  unfold Even. intros. induction H as [| n' H].
  - exists 0. reflexivity.
  - destruct IHH as [nd H'].
    rewrite H'. rewrite <- double_incr. exists (S nd). reflexivity.
Qed.

Theorem Even_ev : forall n,
  Even n -> ev n.
Proof.
  unfold Even. intros.
  destruct H.
  rewrite H. apply ev_double.
Qed.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  split. apply ev_Even. apply Even_ev.
Qed.

(** **** Exercise: 2 stars, standard (ev_sum) *)
Theorem ev_sum : forall n m,
  ev n -> ev m -> ev (n + m).
Proof.
  intros. induction H.
  - simpl. apply H0.
  - simpl. apply ev_SS. apply IHev.
Qed.


(** **** Exercise: 4 stars, advanced, optional (ev'_ev) *)
(* In general, there may be multiple ways of defining a property inductively. For
example, here's a (slightly contrived) alternative definition for ev: *)
Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Lemma plus_1_r : forall n,
  S n = n + 1.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem ev'_ev : forall n,
  ev' n <-> ev n.
Proof.
  split.
  - intros. induction H.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum. apply IHev'1. apply IHev'2.
  - intros. induction H.
    + apply ev'_0.
    + replace (S (S n)) with (n + 2).
      * apply ev'_sum. apply IHev. apply ev'_2.
      * rewrite plus_1_r. rewrite add_assoc.
      rewrite <- plus_1_r. rewrite <- plus_1_r. reflexivity.
Qed.


(** **** Exercise: 3 stars, advanced, especially useful (ev_ev__ev) *)
Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  intros. induction H0.
  - simpl in H. apply H.
  - apply IHev. apply ev_sum. apply H0. simpl in H. apply evSS_ev in H.
    apply IHev in H. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus) *)
(* This exercise can be completed without induction or case analysis. But, you
will need a clever assertion and some tedious rewriting.
Hint: Is (n+m) + (n+p) even? <- acturally we can prove it by introduce another p *)
Theorem ev_plus_plus : forall n m p,
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p H.
  (* Do not introduce all. We need to take use of the previously proved theorem. *)
  apply ev_ev__ev.
  (* Organize all p's together. *)
  rewrite <- add_assoc. rewrite (add_comm p (m + p)).
  rewrite add_assoc. rewrite add_assoc. rewrite <- add_assoc.
  (* Extract 2 terms. *)
  apply ev_sum.
  apply H.
  (* trivial. *)
  rewrite <- double_plus. apply ev_double.
Qed.

Module Playground.
Inductive le : nat -> nat -> Prop :=
	| le_n (n : nat) : le n n 
	| le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m " := (le n m).

Theorem test_le_1 : 3 <= 3.
Proof.
  apply le_n.
Qed.

Theorem test_l2_2: 3 <= 6.
Proof.
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Theorem test_le_3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros.
  inversion H.
  inversion H2.
Qed.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).
End Playground.

(** **** Exercise: 2 stars, standard, optional (total_relation) *)
(* Define an inductive binary relation total_relation that holds between every pair of natural numbers. *)
Inductive total_relation : nat -> nat -> Prop := total n m : total_relation n m.


Theorem total_relation_is_total : forall n m, total_relation n m.
Proof.
  intros. apply total.
Qed.


(** **** Exercise: 2 stars, standard, optional (empty_relation) *)
(* Define an inductive binary relation empty_relation (on numbers) that never holds. *)
Inductive empty_relation : nat -> nat -> Prop :=.

Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
Proof.
  unfold not. intros. inversion H.
Qed.

Lemma le_trans : forall n m o, m <= n -> n <= o -> m <= o.
Proof.
  intros. transitivity n. apply H. apply H0.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n.
  - reflexivity.
  - apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Lemma Sn_le_m__n_le_m : forall n m,
S n <= m -> n <= m.
Proof.
  intros. induction H.
  - apply le_S. apply le_n.
  - apply le_S. apply IHle.
Qed. 

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. inversion H.
  - apply le_n.
  - apply Sn_le_m__n_le_m. apply H1.
Qed.

Lemma O_lt_Sn : forall n,
  0 < S n.
Proof.
  intros. induction n.
  - unfold lt. reflexivity.
  - apply le_S. unfold lt in IHn. apply IHn.
Qed.

Lemma Sn_le_0_0 : forall n,
  n <= 0 -> n = 0.
Proof.
  intros. inversion H. reflexivity.
Qed.

Lemma n_lt_m__Sn_lt_Sm (n m : nat) : n < m -> S n < S m.
Proof.
(* trivial. omit here. *)
Admitted.

Theorem ge_two_meanings : forall n m,
  n <= m -> n < m \/ n = m.
Proof.
  intros n. induction n.
  - intros. destruct m.
    + right. reflexivity.
    + left. apply O_lt_Sn.
  - intros. destruct m.
    + apply Sn_le_0_0 in H. right. apply H.
    + apply Sn_le_Sm__n_le_m in H. apply IHn in H. destruct H.
      * left. apply n_lt_m__Sn_lt_Sm. apply H.
      * right. rewrite H. reflexivity.
Qed.

Theorem ge_two_meanings_strong : forall n m,
  n <= m -> n < m \/ n >= m.
Proof.
  intros. apply ge_two_meanings in H.
  destruct H.
  * left. apply H.
  * right. rewrite H. unfold ge. reflexivity.
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros. induction n.
  - destruct m.
    + right. unfold ge. reflexivity.
    + left. apply O_lt_Sn.
  - destruct m.
    + right. unfold ge. apply O_le_n.
    + destruct IHn.
      * apply ge_two_meanings_strong. unfold lt in H. apply H.
      * right. unfold ge. unfold ge in H.
        apply Sn_le_m__n_le_m in H. apply n_le_m__Sn_le_Sm. apply H.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros. induction b.
  - rewrite add_0_r. reflexivity.
  - rewrite plus_1_r. rewrite add_assoc. rewrite <- plus_1_r.
    apply le_S. apply IHb.
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros. split.
  - induction n2.
    + rewrite add_0_r in H. apply H.
    + rewrite plus_1_r in H. rewrite add_assoc in H. rewrite <- plus_1_r in H.
      apply Sn_le_m__n_le_m in H. apply IHn2 in H. apply H.
  - induction n1.
    + simpl in H. apply H.
    + simpl in H. apply Sn_le_m__n_le_m in H. apply IHn1 in H. apply H.
Qed.

Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.  
  intros n. induction n.
  - intros. left. apply O_le_n.
  - intros. destruct p.
    + simpl in H. apply Sn_le_m__n_le_m in H. right. 
      apply plus_le in H. destruct H as [_ H]. apply H.
    + simpl in H. apply Sn_le_Sm__n_le_m in H. apply IHn in H.
      destruct H.
      * left. apply n_le_m__Sn_le_Sm in H. apply H.
      * right. apply H.
Qed.

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros. induction p. generalize dependent n. generalize dependent m.
  - simpl. intros. apply H.
  - simpl. apply n_le_m__Sn_le_Sm in IHp. apply IHp.
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros. induction p. generalize dependent n. generalize dependent m.
  - intros. rewrite add_0_r. rewrite add_0_r. apply H.
  - rewrite plus_1_r. rewrite (add_comm p 1). rewrite add_assoc. rewrite add_assoc.
    replace (n + 1) with (S n). replace (m + 1) with (S m). simpl.
    apply n_le_m__Sn_le_Sm in IHp. apply IHp.
    apply plus_1_r. apply plus_1_r.
Qed.

