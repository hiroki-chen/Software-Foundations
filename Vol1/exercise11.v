Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia.
From LF Require Import exercise8.

Example auto_example_1: forall (P Q R : Prop),
	(P -> Q) -> (Q -> R) -> P -> R.
Proof.
	intros.
  apply H0. apply H. assumption.
Qed.

Example auto_example_1': forall (P Q R : Prop),
	(P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* When it cannot solve the goal, auto does nothing *)
  auto.
  (* Let's see where auto gets stuck using debug auto *)
  debug auto.
  (* Optional argument says how deep to search (default is 5) *)
  auto 6.
Qed.

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.

Example auto_example_5: 2 = 2.
Proof.
  (* Check which lemma / theorem auto is using. *)
  info_auto.
Qed.

Lemma le_antisym : forall  n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. lia. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto using le_antisym.
Qed.

