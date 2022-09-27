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

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y" := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y" := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.

(* We can now write 3 + (X × 2) instead of APlus 3 (AMult X 2), and true && ~(X ≤ 4) instead of BAnd 
true (BNot (BLe X 4)). *)

Fixpoint aeval (st : state) (* <--- NEW *) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (* <--- NEW *) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

(* singleton state *)
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'" :=
    CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
    (CAsgn x y)
       (in custom com at level 0, x constr at level 0,
        y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
    (CSeq x y)
      (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
    (CIf x y z)
      (in custom com at level 89, x at level 99,
       y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
    (CWhile x y)
       (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ x := a }> =>
        (x !-> (aeval st a) ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | <{ while b do c end }> =>
        st (* bogus *)
  end.

(* Operational Semantics *)
Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Asgn. trivial.
  - apply E_IfFalse.
    + trivial.
    + apply E_Asgn. trivial.
Qed.

Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - apply E_Asgn. trivial.
  - apply E_Seq with (Y !-> 1; X !-> 0); (* Treat as a whole. *)
  apply E_Asgn; trivial.
Qed.

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while Z <> 0 do
       Y := Y * Z;
       Z := Z - 1
     end }>.

(* Write an Imp program that sums the numbers from 1 to X (inclusive: 1 + 2 + ... + X) in the variable Y.  *)
Definition pup_to_n : com :=
  <{
    Y := 0;
    while X <> 0 do
      Y := Y + X;
      X := X - 1
    end
  }>.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2). 
  (* can be treated as a reverse-ordered state list? *)
  (* final, prev1, prev2, initial. *)
Proof.
  unfold pup_to_n.
  apply E_Seq with (Y !-> 0 ; X !-> 2).
  - apply E_Asgn. trivial.
  - apply E_WhileTrue with (X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
    * trivial.
    * apply E_Seq with (Y !-> 2; Y !-> 0; X !-> 2); apply E_Asgn; trivial.
    * apply E_WhileTrue with (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
      + trivial.
      + apply E_Seq with (Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2); apply E_Asgn; trivial.
      + apply E_WhileFalse. trivial.
Qed.