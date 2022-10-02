Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import hoare.

Definition reduce_to_zero' : com :=
  <{ while X <> 0 do
       X := X - 1
     end }>.

Theorem reduce_to_zero_correct' :
  {{True}}
    reduce_to_zero'
  {{X = 0}}.
Proof.
  unfold reduce_to_zero'.
  eapply hoare_consequence_post.
  - eapply hoare_while. eauto.
  - assn_auto''. destruct H. clear H.
    apply eq_true_negb_classical in H0. apply eqb_eq in H0. auto.
Qed.

Ltac verify_assn :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try lia.

Inductive dcom : Type :=
| DCSkip (Q : Assertion)
  (* skip {{ Q }} *)
| DCSeq (d1 d2 : dcom)
  (* d1 ; d2 *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* X := a {{ Q }} *)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
  (* if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }} *)
| DCWhile (b : bexp) (P : Assertion) (d : dcom)
          (Q : Assertion)
  (* while b do {{ P }} d end {{ Q }} *)
| DCPre (P : Assertion) (d : dcom)
  (* ->> {{ P }} d *)
| DCPost (d : dcom) (Q : Assertion)
  (* d ->> {{ Q }} *).

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.

Declare Scope dcom_scope.
Notation "'skip' {{ P }}"
      := (DCSkip P)
      (in custom com at level 0, P constr) : dcom_scope.
Notation "l ':=' a {{ P }}"
      := (DCAsgn l a P)
      (in custom com at level 0, l constr at level 0,
          a custom com at level 85, P constr, no associativity) : dcom_scope.
Notation "'while' b 'do' {{ Pbody }} d 'end' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
           (in custom com at level 89, b custom com at level 99,
           Pbody constr, Ppost constr) : dcom_scope.
Notation "'if' b 'then' {{ P }} d 'else' {{ P' }} d' 'end' {{ Q }}"
      := (DCIf b P d P' d' Q)
           (in custom com at level 89, b custom com at level 99,
               P constr, P' constr, Q constr) : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (in custom com at level 12, right associativity, P constr) : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (in custom com at level 10, right associativity, P constr) : dcom_scope.
Notation " d ; d' "
      := (DCSeq d d')
      (in custom com at level 90, right associativity) : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
      (in custom com at level 91, P constr) : dcom_scope.
Local Open Scope dcom_scope.

Example dec_while : decorated :=
  <{
  {{ True }}
    while X <> 0
    do
                 {{ True /\ (X <> 0) }}
      X := X - 1
                 {{ True }}
    end
  {{ True /\ X = 0}} ->>
  {{ X = 0 }} }>.

Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _ => CSkip
  | DCSeq d1 d2 => CSeq (extract d1) (extract d2)
  | DCAsgn X a _ => CAsgn X a
  | DCIf b _ d1 _ d2 _ => CIf b (extract d1) (extract d2)
  | DCWhile b _ d _ => CWhile b (extract d)
  | DCPre _ d => extract d
  | DCPost d _ => extract d
  end.

Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => extract d
  end.

Example extract_while_ex :
    extract_dec dec_while
  = <{while X <> 0 do X := X - 1 end}>.
Proof.
  unfold dec_while.
  reflexivity.
Qed.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCSeq _ d2 => post d2
  | DCAsgn _ _ Q => Q
  | DCIf _ _ _ _ _ Q => Q
  | DCWhile _ _ _ Q => Q
  | DCPre _ d => post d
  | DCPost _ Q => Q
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

Definition outer_triple_valid (dec : decorated) :=
  {{pre_dec dec}} extract_dec dec {{post_dec dec}}.

Example dec_while_triple_correct :
     outer_triple_valid dec_while
   =
     {{ True }}
       while X <> 0 do X := X - 1 end
     {{ X = 0 }}.
Proof. trivial. Qed.

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((P /\ b) ->> P1)%assertion
      /\ ((P /\ ~ b) ->> P2)%assertion
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (* post d is the loop invariant and the initial
         precondition *)
      (P ->> post d)
      /\ ((post d /\ b) ->> Pbody)%assertion
      /\ ((post d /\ ~ b) ->> Ppost)%assertion
      /\ verification_conditions Pbody d
  | DCPre P' d =>
      (P ->> P')
      /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d
      /\ (post d ->> Q)
  end.

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} extract d {{post d}}.
Proof.
  induction d; intros; simpl in *.
  - eapply hoare_consequence_pre. apply hoare_skip. auto.
  - destruct H. eapply hoare_seq; eauto.
  - eapply hoare_consequence_pre. apply hoare_asgn. auto.
  - destruct H. destruct H0. destruct H1. destruct H2. destruct H3.
    apply IHd1 in H3. apply IHd2 in H4.
    eapply hoare_if; eapply hoare_consequence; eauto.
  - destruct H. destruct H0. destruct H1. apply IHd in H2.
    eapply hoare_consequence; eauto. eapply hoare_while; eauto.
  - destruct H. eapply hoare_consequence; eauto.
  - destruct H. eapply hoare_consequence; eauto.
Qed.

Definition verification_conditions_dec
              (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.

Corollary verification_correct_dec : forall dec,
  verification_conditions_dec dec ->
  outer_triple_valid dec.
Proof.
  intros [P d]. apply verification_correct.
Qed.

Ltac verify :=
  intros;
  apply verification_correct;
  verify_assn.

Definition swap_dec (m n : nat) : decorated :=
  <{
    {{ X = m /\ Y = n}} ->>
         {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
    X := X + Y
         {{ X - (X - Y) = n /\ X - Y = m }};
    Y := X - Y
         {{ X - Y = n /\ Y = m }};
    X := X - Y
    {{ X = n /\ Y = m}}
  }>.

Theorem swap_correct : forall m n,
  outer_triple_valid (swap_dec m n).
Proof. verify. Qed.

Definition if_minus_plus_dec :=
  <{
  {{True}}
  if (X <= Y) then
              {{ True /\ X <= Y }} ->>
              {{ Y = X + (Y - X) }}
    Z := Y - X
              {{ Y = X + Z }}
  else
              {{ True /\ ~ (X <= Y) }} ->>
              {{ Y = Y }}
    Y := X + Z
              {{ Y = X + Z }}
  end
  {{ Y = X + Z}} }>.

Theorem if_minus_plus_correct :
  outer_triple_valid if_minus_plus_dec.
Proof. verify. Qed.

(* Note: X -> remainder Y -> quotient *)
(* Key poinrt: consider the while program reversely. *)
Definition div_mod_dec (a b : nat) : decorated :=
  <{
  {{ True }} ->>
  {{ b * 0 + a = a }}
    X := a
             {{ b * 0 + X = a }};
    Y := 0
             {{ b * Y + X = a  }};
    while b <= X do
             {{ b <= X /\ Y * b + X = a }} ->>
             {{ (Y + 1) * b + (X - b) = a }}
      X := X - b
             {{ (Y + 1) * b + X = a }};
      Y := Y + 1
             {{ Y * b + X = a }}
    end
  {{ Y * b + X = a /\ ~ (b <= X) }} ->>
  {{ Y * b + X = a /\ X < b}} }>.

Theorem div_mod_dec_correct: forall a b,
  outer_triple_valid (div_mod_dec a b).
Proof. verify. Qed.

Example subtract_slowly_dec (m : nat) (p : nat) : decorated :=
  <{
  {{ X = m /\ Z = p }} ->>
  {{ Z - X = p - m }}
    while X <> 0 do
                  {{ Z - X = p - m /\ X <> 0 }} ->>
                  {{ (Z - 1) - (X - 1) = p - m }}
       Z := Z - 1
                  {{ Z - (X - 1) = p - m }} ;
       X := X - 1
                  {{ Z - X = p - m }}
    end
  {{ Z - X = p - m /\ X = 0 }} ->>
  {{ Z = p - m }} }>.

Theorem subtract_slowly_dec_correct: forall m p,
  outer_triple_valid (subtract_slowly_dec m p).
Proof. verify. Qed.

Example slow_assignment_dec (m : nat) : decorated :=
  <{
    {{ X = m }}
      Y := 0
                    {{ X = m /\ Y = 0 }} ->>
                    {{ X + Y = m }} ;
      while X <> 0 do
                    {{ X <> 0 /\ X + Y = m}} ->>
                    {{ (X - 1) + (Y + 1) = m }}
         X := X - 1
                    {{ X + (Y + 1) = m }} ;
         Y := Y + 1
                    {{ X + Y = m }}
      end
    {{ X + Y = m /\ ~(X <> 0) }} ->>
    {{ Y = m }}
  }>.

Theorem slow_assignment_dec_correct: forall m,
  outer_triple_valid (slow_assignment_dec m).
Proof. verify. Qed.

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  intros. induction x.
  - trivial.
  - destruct x.
    + lia.
    + simpl. rewrite sub_0_r. trivial.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity x = x.
Proof.
  destruct x.
  - trivial.
  - intros. destruct x.
    + trivial.
    + simpl. lia.
Qed.

Definition parity_dec (m : nat) : decorated :=
  <{
  {{ X = m }} ->>
  {{ ap parity X = parity m }}
    while 2 <= X do
                  {{ 2 <= X /\ parity m = ap parity X }} ->>
                  {{ parity m = ap parity (X - 2) }}
      X := X - 2
                  {{ parity m = ap parity X }}
    end
  {{ ~(X <= 2) /\ ap parity X = parity m}} ->>
  {{ X = parity m }} }>.

Theorem parity_dec_correct: forall m,
  outer_triple_valid (parity_dec m).
Proof.
  intros.
  apply hoare_consequence_pre with (P' := assert (ap parity X = parity m)).
  - eapply hoare_consequence_post.
    + simpl. eapply hoare_while.
      eapply hoare_consequence_pre. eapply hoare_asgn.
      verify_assn. remember (st X) as x. rewrite <- H.
      apply parity_ge_2. destruct x. lia. destruct x; lia.
    + verify_assn. rewrite <- H. remember (st X) as x. destruct x.
      trivial. destruct x. trivial. lia.
  - verify_assn.
Qed.

(* X = m remains unchanged. *)
Definition sqrt_dec (m:nat) : decorated :=
  <{
    {{ X = m }} ->>
    {{ X = m /\ 0 * 0 <= m }}
      Z := 0
                   {{ X = m /\ Z * Z <= m }};
      while ((Z + 1) * (Z + 1) <= X) do
                   {{ X = m /\ Z * Z <= m /\ (Z + 1) * (Z + 1) <= X }} ->>
                   {{ X = m /\ (Z + 1) * (Z + 1) <= m}}
        Z := Z + 1
                   {{ X = m /\ Z * Z <= m }}
      end
    {{ X = m /\ Z * Z <= m /\~((Z + 1) * (Z + 1) <= X) }} ->>
    {{ Z * Z <= m /\ m < (Z + 1) * (Z + 1) }}
  }>.

Theorem sqrt_dec_correct: forall m,
  outer_triple_valid (sqrt_dec m).
Proof. verify. Qed.

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * fact n'
  end.

(* y = fact m / fact X *)
Definition factorial_dec (m:nat) : decorated :=
  <{
    {{ X = m /\ Y = 1 }} ->>
    {{ fact m = Y * ap fact X }}
    while X <> 0 do
      {{ X <> 0 /\ fact m = Y * ap fact X }} ->>
      {{ fact m = (X * ap fact (X - 1)) * Y }}
        Y := X * Y
      {{ fact m = Y * ap fact (X - 1) }} ;
        X := X - 1
      {{ fact m = Y * ap fact X }}
    end
    {{ X = 0 /\ fact m = Y * ap fact X }} ->>
    {{ Y = fact m }}
  }>.

Lemma fact_fact : forall n : nat,
  n <> 0 ->
  n * fact (n - 1) = fact n.
Proof.
  destruct n.
  - lia.
  - intros. simpl. rewrite sub_0_r. trivial.
Qed.

Theorem factorial_dec_correct: forall m,
  outer_triple_valid (factorial_dec m).
Proof.
  verify.
  - rewrite fact_fact; try rewrite mult_comm; auto.
  - simpl in H0. rewrite mult_1_r in H0. auto.
Qed.

(* Z+1 + (min x y) - 1 as Z + min x y. *)
Definition minimum_dec (a b : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ 0 + 1 + ap2 min a b - 1 = ap2 min a b }}
      X := a
             {{ 0 + 1 + ap2 min X b - 1 = ap2 min a b }};
      Y := b
             {{ 0 + 1 + ap2 min X Y - 1 = ap2 min a b }};
      Z := 0
             {{ Z + 1 + ap2 min X Y - 1 = ap2 min a b }};
      while X <> 0 && Y <> 0 do
             {{ (X <> 0 /\ Y <> 0) /\ (Z + 1 + ap2 min X Y - 1 = ap2 min a b) }} ->>
             {{ Z + 1 + 1 + ap2 min (X - 1) (Y - 1) - 1 = ap2 min a b }}
        X := X - 1
             {{ Z + 1 + 1 + ap2 min X (Y - 1) - 1 = ap2 min a b }};
        Y := Y - 1
             {{ Z + 1 + 1 + ap2 min X Y - 1 = ap2 min a b }};
        Z := Z + 1
             {{ Z + 1 + ap2 min X Y - 1 = ap2 min a b }}
      end
    {{ ~(X <> 0 /\ Y <> 0) /\ (Z + 1 + ap2 min X Y - 1 = ap2 min a b) }} ->>
    {{ Z = min a b }}
  }>.

Theorem minimum_dec_correct : forall a b,
  outer_triple_valid (minimum_dec a b).
Proof.
  verify.
  - symmetry in H0. apply andb_true_eq in H0. destruct H0. symmetry in H0, H1.
    apply negb_true_iff in H0, H1. apply eqb_neq in H0, H1. auto.
  - symmetry in H0. apply andb_true_eq in H0. destruct H0. symmetry in H0, H1.
    apply negb_true_iff in H0, H1. apply eqb_neq in H0, H1. auto.
  - (* Cannot use repeated tactics or one of the hypotheses will vanish.? *)
    rewrite andb_false_iff in H0; destruct H0; rewrite negb_false_iff in H0; unfold not; intros; destruct H1.
    + apply H1. rewrite eqb_eq in H0. auto.
    + apply H2. rewrite eqb_eq in H0. auto.
Qed.