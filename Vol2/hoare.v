Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.

From Coq Require Import Logic.FunctionalExtensionality.

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop := forall st,
  P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.


Definition Aexp : Type := state -> nat.
Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.
Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.
Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.
Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.
Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.
Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).
Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st -> assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <-> assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.


Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).

Definition hoare_triple
	(P : Assertion) (c : com) (Q : Assertion) : Prop :=
	forall st st',
		st =[ c ]=> st' ->
		P st ->
		Q st'.

Notation "{{ P }} c {{ Q }}" :=
	(hoare_triple P c Q) (at level 90, c custom com at level 99) : hoare_spec_scope.

(** **** Exercise: 1 star, standard (hoare_post_true) *)
(* Prove that if Q holds in every state, then any triple with Q as its postcondition is valid. *)
Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple.
  intros.
  apply H.
Qed.

(** **** Exercise: 1 star, standard (hoare_pre_false) *)
(* Prove that if P holds in no state, then any triple with P as its precondition is valid. *)
Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, not. intros.
  apply H in H1. inversion H1.
Qed.

Theorem hoare_skip: forall P, {{ P }} skip {{ P }}.
Proof.
  unfold hoare_triple. intros.
  inversion H. subst. apply H0.
Qed.

Theorem hoare_seq :forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  unfold hoare_triple. intros.
  inversion H1.
  apply H with st'0. apply H8. apply H0 with st. apply H5. apply H2.
Qed.

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com).

Theorem hoare_asgn : forall Q X a,
  {{Q [X|-> a]}} X := a {{Q}}.
Proof.
  unfold assn_sub, hoare_triple.
  intros.
  inversion H. rewrite <- H5. apply H0.
Qed.

Example assn_sub_example :
  {{(X < 5) [X |-> X + 1]}}
    X := X + 1
  {{X < 5}}.
Proof.
  apply hoare_asgn.
Qed.

(** **** Exercise: 2 stars, standard, optional (hoare_asgn_examples1) *)
Example hoare_asgn_examples1 :
  exists P,
    {{ P }}
      X := 2 * X
    {{ X <= 10 }}.
Proof.
  exists ((X <= 10) [X |-> 2 * X]).
  simpl. apply hoare_asgn.
Qed.

(** **** Exercise: 2 stars, standard, optional (hoare_asgn_examples2) *)
Example hoare_asgn_examples2 :
  exists P,
    {{ P }}
      X := 3
    {{ 0 <= X /\ X <= 5 }}.
Proof.
  exists ((0 <= X /\ X <= 5) [X |-> 3]).
  simpl. apply hoare_asgn.
Qed.

(* The assignment rule looks backward to almost everyone the first time they see it.
If it still seems puzzling to you, it may help to think a little about alternative "forward" rules. Here is a seemingly natural one:

  	(hoare_asgn_wrong)  
{{ True }} X := a {{ X = a }}	

*)

(* a cannot be dependent on X; otherwise the proposition does not hold. *)
Definition hoare_asgn_wrong_example := {{ True }} X := X + 1 {{ X = X + 1}}.

Lemma hoare_asgn_fwd_helper : forall st X (n : nat),
  (X !-> st X; X !-> n; st) = st.
Proof.
  intros. unfold "!->". extensionality x'.
  destruct (X =? x')%string eqn : H.
  - apply String.eqb_eq in H. subst. trivial.
  - trivial.
Qed.

(* Note: !-> indicates update st X m  *)
Theorem hoare_asgn_fwd : forall m a P,
  {{ fun st => P st /\ st X = m }}
    X := a
  {{ fun st => P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}.
  (* X is evaluated with the previous state. *)
Proof.
  unfold hoare_triple. intros. destruct H0.
  inversion H. subst. rewrite hoare_asgn_fwd_helper. split; auto.
Qed.

(* If st' is obtainable from st, we are able to construct a state that could reverse to st. *)
Lemma hoare_asgn_fwd_exists_helper : forall st st' X a,
  st =[ X := a ]=> st' -> exists m, (X !-> m; st') = st.
Proof.
  intros.
  inversion H. subst.
  exists (st X). apply hoare_asgn_fwd_helper.
Qed.

Theorem hoare_asgn_fwd_exists :
  forall a P,
  {{fun st => P st}}
    X := a
  {{fun st => exists m, P (X !-> m ; st) /\
                st X = aeval (X !-> m ; st) a }}.
Proof.
  unfold hoare_triple. intros.
  inversion H. subst.
  destruct (hoare_asgn_fwd_exists_helper st (X !-> aeval st a; st) X a); auto.
  exists x. split; rewrite H1; auto.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold assert_implies, hoare_triple. intros.
  apply H in H1; try apply H0 in H2; auto.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold assert_implies, hoare_triple. intros.
  apply H in H1; try apply H0 in H1; auto.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold assert_implies, hoare_triple. intros.
  apply H in H2. apply H1 in H2. auto. apply H0 in H3. auto.
Qed.

Hint Unfold assert_implies hoare_triple assn_sub t_update : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

Example hoare_asgn_example1' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - eapply hoare_asgn.
  - auto.
Qed.

Example assn_sub_example2' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>", assn_sub, "!->".
    intros. simpl in *. lia.
Qed. 

(* A custom tactic for dealing with assignment. *)
Ltac assn_auto :=
  try auto; (* as in example 1, above *)
  try (unfold "->>", assn_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)

Example assn_sub_ex1' :
  {{ X <= 5 }}
    X := 2 * X
  {{ X <= 10 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assn_auto.
Qed.

Example assn_sub_ex2' :
  {{ 0 <= 3 /\ 3 <= 5 }}
    X := 3
  {{ 0 <= X /\ X <= 5 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto.
Qed.

Example hoare_asgn_example3 : forall (a : aexp) (n : nat),
  {{a = n}}
    X := a;
    skip
  {{X = n}}.
Proof.
  intros. eapply hoare_seq.
  - apply hoare_skip.
  - simpl. eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + auto.
Qed.

Example hoare_asgn_example4 :
  {{ True }}
    X := 1;
    Y := 2
  {{ X = 1 /\ Y = 2 }}.
Proof.
  apply hoare_seq with (Q := (X = 1)%assertion);
  (* The annotation %assertion is needed here to help Coq parse correctly. *)
  simpl; eapply hoare_consequence_pre; try apply hoare_asgn; auto.
Qed.

Definition swap_program : com :=
  <{
    Z := X ;
    X := Y ;
    Y := Z
  }>.

Theorem swap_exercise :
  {{X <= Y}}
    swap_program
  {{Y <= X}}.
Proof.
  unfold swap_program.
  eapply hoare_seq.
  - simpl. eapply hoare_seq; apply hoare_asgn.
  - simpl. eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + auto.
Qed.

(* Note that a is an arithmetic expression, so it can contain the identifier X.
   The key point is that X is modified.
*)
Theorem invalid_triple : ~ (
  forall (a : aexp) (n : nat),
  {{ a = n }}
    X := 3;
    Y := a
  {{ Y = n }}
).
Proof.
(* The thing is, if we follow the rule in the assumption, we have a conclusion that is
contradictory to the correct rule of inference. *)
  unfold hoare_triple, not. intros.
  specialize H with (a := X) (n := 1). simpl in H.
  (* Use the evaluation rules (E_Seq and E_Asgn) to show that Y has a different value y2 
  in the same final state st' *)
  assert (H': (X !-> 1) =[ X := 3; Y := X ]=> (Y !-> 3; X !-> 3; X !-> 1)).
  - eapply E_Seq. apply E_Asgn. auto.
    apply E_Asgn. trivial.

  (* Use the (assumed) validity of the given hoare triple to derive a state st' in which Y has 
  some value y1 *)
  - assert (H'' : 3 = 1).
    apply H in H'. apply H'. auto.
  
  discriminate H''.
Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Coercion bassn : bexp >-> Assertion.
Arguments bassn /.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  (* In fact, we can use congruence. *)
  intros. unfold not.
  induction b; simpl in *; intros; try rewrite H in H0; discriminate.
Qed.

Hint Resolve bexp_eval_false : core.

Theorem hoare_if : forall P Q (b : bexp) c1 c2,
  {{ P /\ b }} c1 {{ Q }} ->
  {{ P /\ ~b }} c2 {{ Q }} ->
  {{ P }} if b then c1 else c2 end {{ Q }}.
Proof.
  unfold hoare_triple. intros.
  inversion H1; subst; eauto.
Qed.

Ltac assn_auto' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.

Example if_example'' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  eapply hoare_if; eapply hoare_consequence_pre; try apply hoare_asgn; assn_auto'.
Qed.

(* For later proofs, it will help to extend assn_auto' to handle inequalities, too. *)
Ltac assn_auto'' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *; (* for inequalities *)
  auto; try lia.

Theorem if_minus_plus :
  {{True}}
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  {{ Y = X + Z }}.
Proof.
  eapply hoare_if; eapply hoare_consequence_pre; try apply hoare_asgn; assn_auto''.
Qed.

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'if1' x 'then' y 'end'" :=
         (CIf1 x y)
         (in custom com at level 0, x custom com at level 99).
Notation "'skip'" :=
         CSkip 
         (in custom com at level 0).
Notation "x := y" :=
         (CAsgn x y)
         (in custom com at level 0, x constr at level 0, y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
         (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
         (in custom com at level 89, x at level 99, y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
         (in custom com at level 89, x at level 99, y at level 99).

Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st constr, st' constr at next level).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  | E_If1True : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st =[ if1 b then c end ]=> st'
  | E_If1False : forall st b c,
      beval st b = false ->
      st =[ if1 b then c end ]=> st
  where "st =[ c ]=> st'" := (ceval c st st').

Hint Constructors ceval : core.

Example if1true_test : empty_st =[ if1 X = 0 then X := 1 end ]=> (X !-> 1).
Proof. eauto. Qed.

Example if1false_test : (X !-> 2) =[ if1 X = 0 then X := 1 end ]=> (X !-> 2).
Proof. eauto. Qed.

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.
Hint Unfold hoare_triple : core.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                (at level 90, c custom com at level 99)
                                : hoare_spec_scope.

Theorem hoare_if1: forall P Q (b:bexp) c,
  {{ P /\ b }} c {{Q}} ->
  (P /\ ~b)%assertion ->> Q ->
  {{P}} if1 b then c end {{Q}}.
Proof.
  unfold hoare_triple. intros. inversion H1. subst.
  - eauto.
  - subst. apply H0. split. apply H2. congruence.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.
Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X := a) {{Q}}.
Proof.
  intros Q X a st st' Heval HQ.
  inversion Heval; subst.
  auto.
Qed.

Example hoare_if1_good: 
  {{ X + Y = Z }}
  if1 ~(Y = 0) then
    X := X + Y
  end
  {{ X = Z }}.
Proof.
  apply hoare_if1; simpl.
  - eapply hoare_consequence_pre. apply hoare_asgn. assn_auto.
  - assn_auto''. destruct H. apply eq_true_negb_classical in H0. apply beq_nat_true in H0.
    rewrite H0 in H. rewrite plus_0_r in H. auto.
Qed.

End If1.