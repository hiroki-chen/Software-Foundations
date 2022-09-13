From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Check String.eqb_refl.

Definition total_map(A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) : total_map A :=
  fun x' => if String.eqb x x' then v else m x'.

(* This definition is a nice example of higher-order programming: t_update takes a function m and yields a
new function fun x' ⇒ ... that behaves like the desired map. *)

(* First, we use the following notation to represent an empty total map with a default value. *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

(* We next introduce a convenient notation for extending an existing map with a new binding. *)
Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).


(** **** Exercise: 1 star, standard, optional (t_apply_empty) *)
(* First, the empty map returns its default element for all keys: *)
Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
  trivial.
Qed.

(** **** Exercise: 2 stars, standard, optional (t_update_eq) *)
(* Next, if we update a map m at a key x with a new value v and then look up x in the map resulting from
the update, we get back v: *)
Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite String.eqb_refl. reflexivity.
Qed.

(* Exercise: 2 stars, standard, optional (t_update_neq) *)
(* On the other hand, if we update a map m at a key x1 and then look up a different key x2 in the resulting
map, we get the same result that m would have given: *)
Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros. unfold t_update. apply String.eqb_neq in H. rewrite H. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, optional (t_update_shadow) *)
(* If we update a map m at a key x with a value v1 and then update again with the same key x and another
value v2, the resulting map behaves the same (gives the same result when applied to any key) as the simpler
map obtained by performing just the second update on m: *)
Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros. unfold t_update. extensionality x'.
  destruct (x =? x')%string; reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (t_update_same) *)
(* Given strings x1 and x2, we can use the tactic destruct (eqb_spec x1 x2) to simultaneously perform case
analysis on the result of String.eqb x1 x2 and generate hypotheses about the equality (in the sense of =)
of x1 and x2. With the example in chapter IndProp as a template, use String.eqb_spec to prove the following
theorem, which states that if we update a map to assign key x the same value as it already has in m, then
the result is equal to m: *)
Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros. unfold t_update. extensionality x'.
  destruct (x =? x')%string eqn: H.
  - apply String.eqb_eq in H. rewrite H. trivial.
  - trivial.
Qed.

(** **** Exercise: 3 stars, standard, especially useful (t_update_permute) *)
(* Similarly, use String.eqb_spec to prove one final property of the update function: If we update a map m
at two distinct keys, it doesn't matter in which order we do the updates. *)
Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros. unfold t_update. extensionality x'.
  destruct (x1 =? x')%string eqn : H1.
  - destruct (x2 =? x')%string eqn : H2.
    + apply String.eqb_eq in H1, H2. rewrite H1 in H. rewrite H2 in H. unfold not in H.
      apply String.eqb_neq in H. rewrite String.eqb_refl in H. discriminate H.
    + trivial.
  - destruct (x2 =? x')%string eqn : H2.
    + trivial.
    + trivial.
Qed.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '\-> v" := (update empty x v)
  (at level 100).

  Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.


Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin, update, t_update. intros.
  destruct (x =? x0)%string.
  - apply H0.
  - apply H. apply H0.
Qed.

