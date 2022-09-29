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

Theorem ceval_deterministic : forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros; inversion E2; subst.
  - trivial.
  - trivial.
  - apply IHE1_2. apply IHE1_1 in H1. subst. apply H4.
  - apply IHE1. apply H6.
  - rewrite H in H5. discriminate.
  - rewrite H in H5. discriminate.
  - apply IHE1. apply H6.
  - trivial.
  - rewrite H in H2. discriminate.
  - rewrite H in H4. discriminate.
  - apply IHE1_2. apply IHE1_1 in H3. rewrite H3. apply H6.
Qed.

Definition plus2 : com :=
  <{ X := X + 2 }>.

Theorem plus2_spec: forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  unfold plus2. intros. inversion H0. subst.
  trivial.
Qed.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

Theorem XtimesYinZ_spec: forall st n1 n2 st',
  st X = n1 ->
  st Y = n2 ->
  st =[ XtimesYinZ ]=> st' ->
  st' Z = n1 * n2.
Proof.
  unfold XtimesYinZ. intros.
  inversion H1. subst.
  trivial.
Qed.

Definition loop : com :=
  <{ while true do
       skip
     end }>.

Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn : Heqloopdef.
  induction contra; try discriminate. 
  - inversion Heqloopdef. rewrite H1 in H. discriminate.
  - inversion Heqloopdef. subst. apply IHcontra2. apply Heqloopdef.
Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> =>
      true
  | <{ _ := _ }> =>
      true
  | <{ c1 ; c2 }> =>
      andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }> =>
      false
  end.

Inductive no_whilesR: com -> Prop :=
  | R_skip : no_whilesR <{ skip }>
  | R_asgn : forall lhs rhs, no_whilesR <{ lhs := rhs }>
  | R_seq : forall c1 c2, no_whilesR c1 -> no_whilesR c2 -> no_whilesR <{ c1 ; c2 }>
  | R_ifesle : forall exp c1 c2, no_whilesR c1 -> no_whilesR c2 -> no_whilesR <{ if exp then c1 else c2 end }>.

Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split; intros.
  - induction c.
    + apply R_skip.
    + apply R_asgn.
    + inversion H. apply andb_true_iff in H1. destruct H1. apply R_seq. apply IHc1. auto. apply IHc2. auto.
    + inversion H. apply andb_true_iff in H1. destruct H1. apply R_ifesle. apply IHc1. auto. apply IHc2. auto.
    + inversion H.
  - induction H; auto; simpl; apply andb_true_iff; split; auto.
Qed.

Theorem no_whiles_terminating : forall st c,
  no_whilesR c ->
  exists st', st =[ c ]=> st'.
Proof.
  intros. (* There is no meaning introducing st. *)
  generalize dependent st. induction H; intros.
  - exists st. apply E_Skip.
  - exists (lhs !-> aeval st rhs; st). apply E_Asgn. trivial.
  - destruct IHno_whilesR1 with st. destruct IHno_whilesR2 with x. (* fix some existing state. *)
    exists x0. apply E_Seq with x; auto.
  - destruct IHno_whilesR1 with st. destruct IHno_whilesR2 with st.
    destruct (beval st exp) eqn : H'. (* destruct condition. *)
    + exists x. apply E_IfTrue. apply H'. apply H1.
    + exists x0. apply E_IfFalse. apply H'. apply H2.
Qed.

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.


Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
  match prog with
  | [] => stack
  | cons inst l' =>
      match inst with
      | SPush n => s_execute (st) (n :: stack)  (l')
      | SLoad x => s_execute (st) ((aeval st (AId x)) :: stack) (l')
      | SPlus => 
        match stack with
        | n1 :: n2 :: l'' => s_execute (st) ((n2 + n1) :: l'') (l')
        | _ => s_execute st stack l'
        end
      | SMinus => 
        match stack with
        | n1 :: n2 :: l'' => s_execute (st) ((n2 - n1) :: l'') (l')
        | _ => s_execute st stack l'
        end
      | SMult =>
        match stack with
        | n1 :: n2 :: l'' => s_execute (st) ((n2 * n1) :: l'') (l')
        | _ => s_execute st stack l'
        end
      end
  end.

Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof. trivial. Qed.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. trivial. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus exp1 exp2 => s_compile (exp1) ++ s_compile (exp2) ++ [SPlus]
  | AMinus exp1 exp2 => s_compile (exp1) ++ s_compile (exp2) ++ [SMinus]
  | AMult exp1 exp2 => s_compile (exp1) ++ s_compile (exp2) ++ [SMult]
  end.

Example s_compile1 :
  s_compile <{ X - (2 * Y) }>
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. trivial. Qed.

Theorem execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  induction p1.
  - trivial.
  - induction a; intros.
    + simpl. auto.
    + simpl. auto.
    + induction stack; simpl; auto; induction stack; simpl; auto.
    + induction stack; simpl; auto; induction stack; simpl; auto.
    + induction stack; simpl; auto; induction stack; simpl; auto.
Qed.

Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  induction e; trivial; intros; simpl;
  try (rewrite app_assoc; repeat rewrite execute_app; rewrite IHe1; rewrite IHe2; trivial).
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. rewrite s_compile_correct_aux. trivial.
Qed.

Fixpoint beval_sc (st : state) (* <--- NEW *) (b : bexp) : bool :=
  match b with
  | <{b1 && b2}> => if negb (beval_sc st b1) then false else beval_sc st b2
  | _ => beval st b
  end.

Theorem beval_sc_is_beval : forall st b,
  beval st b = beval_sc st b.
Proof.
  induction b; trivial; simpl.
  destruct (negb (beval_sc st b1)) eqn : H.
  - apply negb_true_iff in H. rewrite H in IHb1. rewrite IHb1. trivial.
  - apply negb_false_iff in H. rewrite H in IHb1. rewrite IHb1. trivial.
Qed.