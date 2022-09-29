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