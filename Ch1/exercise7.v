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