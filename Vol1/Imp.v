Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import exercise8.

Module AExp.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Compute aeval (APlus (ANum 2) (ANum 2)). (* it evaluates to 4. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BNeq a1 a2 => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BGt a1 a2 => negb ((aeval a1) <=? (aeval a2))
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros. induction a.
  - trivial.
  - destruct a1; try destruct n; try destruct a2; simpl; auto.
  - simpl. auto.
  - simpl. auto.
Qed.

(* Since the optimize_0plus transformation doesn't change the value of aexps, we should be able to apply
it to all the aexps that appear in a bexp without changing the bexp's value. Write a function that
performs this transformation on bexps and prove it is sound. Use the tacticals we've just seen to make
the proof as short and elegant as possible. *)
Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  | _ => b
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros. induction b; simpl; repeat rewrite optimize_0plus_sound; trivial.
  - rewrite IHb. trivial.
  - rewrite IHb1. rewrite IHb2. trivial.
Qed.

Ltac invert H := inversion H; subst; clear H.

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2) ==> (n1 * n2)

      where "e '==>' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  split; intros.
  - induction H; simpl; auto.
  - generalize dependent n.
    induction a; simpl; intros; subst; constructor; 
    try apply IHa1; try apply IHa2; trivial.
Qed.

Reserved Notation "e '==>b' b" (at level 90, left associativity).

Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : BTrue ==>b true
  | E_BFalse : BFalse ==>b false
  | E_BEq (e1 e2 : aexp) (n1 n2 : nat) :
    e1 ==> n1 ->
    e2 ==> n2 ->
    (BEq e1 e2 ==>b n1 =? n2)
  | E_BNeq (e1 e2 : aexp) (n1 n2 : nat) :
    e1 ==> n1 ->
    e2 ==> n2 ->
    (BNeq e1 e2 ==>b negb (n1 =? n2))
  | E_BLe (e1 e2 : aexp) (n1 n2 : nat) :
    e1 ==> n1 ->
    e2 ==> n2 ->
    (BLe e1 e2 ==>b n1 <=? n2)
  | E_BGt (e1 e2 : aexp) (n1 n2 : nat) :
    e1 ==> n1 ->
    e2 ==> n2 ->
    (BGt e1 e2 ==>b negb (n1 <=? n2))
  | E_BNot (e : bexp) (b : bool) :
    e ==>b b ->
    BNot e ==>b negb b
  | E_BAnd (e1 e2 : bexp) (b1 b2 : bool) :
    (e1 ==>b b1) ->
    (e2 ==>b b2) ->
    BAnd e1 e2 ==>b andb b1 b2

  where "e '==>b' b" := (bevalR e b) : type_scope.

Lemma beval_iff_bevalR : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
  split; intro.
  - induction H; simpl; auto; try apply aeval_iff_aevalR in H, H0; try rewrite H, H0; trivial.
    + rewrite IHbevalR. trivial.
    + rewrite IHbevalR1, IHbevalR2. trivial.
  - generalize dependent bv. 
    induction b; simpl; intros; subst; constructor; try apply aeval_iff_aevalR; trivial.
    + apply IHb. trivial.
    + apply IHb1. trivial.
    + apply IHb2. trivial.
Qed.

End AExp.