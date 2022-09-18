Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export exercise7.

(** **** Exercise: 2 stars, standard (eight_is_even) *)
(* Give a tactic proof and a proof object showing that ev 8. *)
Theorem ev_8 : ev 8.
Proof.
  repeat apply ev_SS. apply ev_0.
Qed.

Definition ev_8' : ev 8 := ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

Definition add1 : nat -> nat.
  intros n.
  apply S.
  apply n.  Defined.

(** **** Exercise: 2 stars, standard (conj_fact) *)
(* Construct a proof object for the following proposition. *)
Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (H1: P /\ Q) (H2: Q /\ R) =>
    match H1, H2 with
    | conj p q, conj q' r => conj p r
    end.

(** **** Exercise: 2 stars, standard (or_commut') *)
(* Construct a proof object for the following proposition. *)
Definition or_commut: forall P Q, P \/ Q -> Q \/ P :=
  fun (P Q : Prop) (H: P \/ Q) =>
    match H with
    | or_introl p => or_intror p (* Extract and then apply reversely. *)
    | or_intror q => or_introl q
    end.

(* Inductive ex {A : Type} (P : A → Prop) : Prop :=
  | ex_intro : ∀ x : A, P x → ex P.
  
  First, ex_intro (P) will introduce a universal quantifier forall x : Type, P(x)
  so that we need to find the specific value for proving P(x).

  Then we fill the value and the evidence.

  *)

(** **** Exercise: 2 stars, standard (ex_ev_Sn) *)
(* Construct a proof object for the following proposition. *)
Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  (* Prop + existential value + evidence. *)
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).

(** **** Exercise: 1 star, standard (p_implies_true)
Construct a proof object for the following proposition. *)
Definition p_implies_true : forall P, P -> True :=
  fun P H => I.

(** **** Exercise: 1 star, standard (ex_falso_quodlibet') *)
(* Construct a proof object for the following proposition. *)
Definition ex_falso_quodlibet' : forall P, False -> P :=
  fun P H => match H with end.

Module EqualityPlayground.

Inductive eq {X:  Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                       (at level 70, no associativity)
                     : type_scope.

Definition singleton : forall (X : Type) (x : X), [ ] ++ [x] == x :: [ ] :=
  fun (X : Type) (x : X) => eq_refl [x].

Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
fun n1 n2 Heq =>
  match Heq with
  | eq_refl n => eq_refl (S n)
  end.

(** **** Exercise: 2 stars, standard (eq_cons) *)
(* Construct the proof object for this theorem. Use pattern matching against the equality hypotheses. *)
Definition eq_cons : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
    h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2 :=
  fun (X : Type) (h1 h2 : X) (t1 t2 : list X) H1 H2 =>
    match H1, H2 with
    | (eq_refl h), (eq_refl t) => eq_refl (h :: t)
    end.

(** **** Exercise: 2 stars, standard (equality__leibniz_equality) *)
(* The inductive definition of equality implies Leibniz equality: what we mean when we say "x and y are 
equal" is that every property on P that is true of x is also true of y. Prove that. *)
Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall (P : X -> Prop), P x -> P y.
Proof.
  intros.
  destruct H. apply H0.
Qed.

(** **** Exercise: 2 stars, standard (equality__leibniz_equality_term) *)
(* Construct the proof object for the previous exercise. All it requires is anonymous functions and
pattern-matching; the large proof term constructed by tactics in the previous exercise is needessly
complicated. Hint: pattern-match as soon as possible. *)
Definition equality__leibniz_equality_term : forall (X : Type) (x y: X),
    x == y -> forall P : (X -> Prop), P x -> P y :=
  fun X x y H =>
    match H with
    | eq_refl x =>
      fun P H0 => H0
    end.


(** **** Exercise: 3 stars, standard, optional (leibniz_equality__equality) *)
(* Show that, in fact, the inductive definition of equality is equivalent to Leibniz equality. Hint: the
proof is quite short; about all you need to do is to invent a clever property P to instantiate the
antecedent. *)
Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P : X -> Prop, P x -> P y) -> x == y.
Proof.
  intros.
  apply (H (eq x)). apply (eq_refl x).
Qed.

End EqualityPlayground.

Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

Theorem pe_implies_or_eq :
  propositional_extensionality ->
  forall (P Q : Prop), (P \/ Q) = (Q \/ P).
Proof.
  unfold propositional_extensionality.
  intros. apply H. split.
  - intros. destruct H0. right. apply H0. left. apply H0.
  - intros. destruct H0. right. apply H0. left. apply H0.
Qed.

Lemma pe_implies_true_eq :
  propositional_extensionality ->
  forall (P : Prop), P -> True = P.
Proof.
  unfold propositional_extensionality.
  intros.
  apply H. split.
  - intros. apply H0.
  - apply p_implies_true.
Qed.

Definition proof_irrelevance : Prop :=
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

Theorem pe_implies_pi :
  propositional_extensionality -> proof_irrelevance.
Proof.
  unfold proof_irrelevance. intros.
  apply pe_implies_true_eq with P in pf1 as H'. destruct H'.
  - destruct pf1, pf2. trivial.
  - apply H.
Qed.