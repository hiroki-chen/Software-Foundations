Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.

Inductive tm : Type :=
  | C : nat -> tm (* Constant *)
  | P : tm -> tm -> tm. (* Plus *)

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
    C n ==> n
  | E_Plust : forall t1 t2 v1 v2,
    t1 ==> v1 ->
    t2 ==> v2 ->
    P t1 t2 ==> (v1 + v2)
  
  where " t '==>' n " := (eval t n).

Module SimpleArith1.

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      t2 --> t2' ->
      P (C v1) t2 --> P (C v1) t2'

  where " t '-->' t' " := (step t t').

Example test_step_1 :
  P
    (P (C 1) (C 3))
    (P (C 2) (C 4))
  -->
  P
    (C 4)
    (P (C 2) (C 4)).
Proof. 
  apply ST_Plus1. apply ST_PlusConstConst.
Qed.

Example test_step_2 :
  P
    (C 0)
    (P
      (C 2)
      (P (C 1) (C 3)))
  -->
  P
    (C 0)
    (P
      (C 2)
      (C 4)).
Proof.
  repeat apply ST_Plus2. apply ST_PlusConstConst.
Qed.

End SimpleArith1.


Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem deterministic_step : deterministic step.
Proof.
  unfold deterministic. intros.
  generalize dependent y2.
  induction H; intros.
  - inversion H0; subst; auto.
    + inversion H3.
    + inversion H3.
  - inversion H0; subst.
    + inversion H.
    + apply IHstep in H4. subst. auto.
    + inversion H.
  - inversion H0. subst.
    + inversion H.
    + inversion H4.
    + subst. apply IHstep in H4. subst. auto.
Qed.

End SimpleArith2.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Module SimpleArith3.
Import SimpleArith1.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith3.

Inductive value : tm -> Prop :=
  | v_const: forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
          P (C v1) (C v2)
      --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 -> (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Theorem step_deterministic :
  deterministic step.
Proof.
  unfold deterministic. intros. generalize dependent y2.
  induction H; intros; inversion H0; subst; auto.
  - inversion H3.
  - inversion H4.
  - inversion H.
  - apply IHstep in H4. subst. auto.
  - inversion H3. subst. inversion H.
  (* t1 is already the final state. *)
  - inversion H. subst. inversion H1; subst.
    + inversion H5.
    + apply IHstep in H6. rewrite H6. auto.
  - inversion H. subst. inversion H1; subst.
    + inversion H6.
    + apply IHstep in H7. rewrite H7. auto.
  - inversion H. subst. inversion H1; subst.
    + inversion H7.
    + apply IHstep in H8. rewrite H8. auto.
Qed.

(* This important property is called strong progress, 
because every term either is a value or can "make progress"
by stepping to some other term. *)
Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - left. constructor.
  - right. destruct IHt1.
    + destruct IHt2.
      * inversion H. inversion H0. exists (C (n + n0)).
        constructor.
      * destruct H0. exists (P t1 x). constructor; auto.
    + destruct IHt2; destruct H; exists (P x t2); constructor; auto.
Qed.

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form, not. intros.
  inversion H. subst.
  destruct H0. inversion H0.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof.
  unfold normal_form, not. intros.
  specialize strong_progress with t. intros.
  destruct H0. auto. apply H in H0. inversion H0.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof. split. apply nf_is_value. apply value_is_nf. Qed.

Module Temp1.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_funny : forall t1 v2,
                value (P t1 (C v2)). (* <--- *)
Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists(P (C 0) (C 0)). split.
  - constructor.
  - unfold normal_form, not. intros. apply H.
    exists (C (0 + 0)). constructor.
Qed.

End Temp1.

Module Temp2.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n). (* Original definition *)
Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n --> P (C n) (C 0) (* <--- NEW *)
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists (C 0). split.
  - constructor.
  - unfold normal_form, not. intros. apply H.
    exists (P (C 0) (C 0)). apply ST_Funny.
Qed.

End Temp2.

Module Temp3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2

  where " t '-->' t' " := (step t t').

(* (Note that ST_Plus2 is missing.) *)

Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  exists (P (C 0) (P (C 0) (C 0))). split.
  - unfold not. intros. inversion H.
  - unfold normal_form, not. intros. destruct H. 
    inversion H. subst. inversion H3.
Qed.

End Temp3.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '-->*' t' " := (multi step t t') (at level 40).

(* Converts from -->* to --> *)
Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
  R x y -> (multi R) x y.
Proof.
  intros. apply multi_step with y. apply H. constructor.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros.
  induction H.
  - auto.
  - apply multi_step with y. auto. apply IHmulti. auto.
Qed.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  induction P11.
  - inversion P21; subst.
    + trivial.
    + unfold step_normal_form in *. unfold normal_form in *. unfold not in *.
      exfalso. apply P12. exists y. auto.
  - inversion P21; subst.
    + apply IHP11. trivial.
      exfalso. unfold step_normal_form in *. unfold normal_form in *. unfold not in *.
      apply P22. exists y. trivial.
    + apply IHP11. trivial.
      assert (G : y = y0).
      * apply (step_deterministic _ _ _ H H0).
      * subst. auto.
Qed.

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

Lemma multistep_congr_1 :forall t1 t1' t2,
  t1 -->* t1' ->
  P t1 t2 -->* P t1' t2.
Proof.
  intros.
  induction H.
  - constructor.
  - apply multi_step with (P y t2).
    + apply ST_Plus1. auto.
    + auto.
Qed.

Lemma multistep_congr_2 : forall v1 t2 t2',
     value v1 ->
     t2 -->* t2' ->
     P v1 t2 -->* P v1 t2'.
Proof.
  intros.
  induction H0.
  - constructor.
  - apply multi_step with (P v1 y).
    apply ST_Plus2; auto.
    auto.
Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing. intros. induction t.
  - exists (C n). split.
    + constructor.
    + unfold normal_form, not. intros.
      destruct H. inversion H.
  - destruct IHt1. destruct IHt2.
    destruct H, H0.
    apply nf_same_as_value in H1, H2.
    destruct H1, H2.
    exists (C (n + n0)). split.
    + apply multi_trans with (P (C n) t2).
      * apply multistep_congr_1. auto.
      * apply multi_trans with (P (C n) (C n0)).
        -- apply multistep_congr_2. constructor. auto.
        -- apply multi_R. constructor.
    + unfold normal_form. unfold not. intros. destruct H1.
      inversion H1.
Qed.

(* Should be obvious. *)
Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.
Proof.
  intros. induction H.
  - constructor.
  - induction t1.
    + induction t2.
      * inversion IHeval1; inversion IHeval2; subst.
        -- apply multi_R. constructor.
        -- apply multi_trans with (P (C v1) (C v2)).
           apply multistep_congr_2. constructor. auto.
           apply multi_R. constructor.
        -- apply multi_trans with (P (C v1) (C v2)).
           apply multistep_congr_1. auto.
           apply multi_R. constructor.
        -- apply multi_trans with (P (C n) (C v2)).
           apply multistep_congr_2. constructor. auto.
           apply multi_trans with (P (C v1) (C v2)).
           apply multistep_congr_1. auto.
           apply multi_R. constructor.
      * assert (G: P (C n) (P t2_1 t2_2) -->* P (C n) (C v2)).
        -- apply multistep_congr_2. constructor. auto.
        -- apply multi_trans with (P (C v1) (C v2)).
           apply multi_trans with (P (C n) (C v2)).
           apply G. apply multistep_congr_1. auto. apply multi_R. constructor.
    + assert (G: P (P t1_1 t1_2) t2 -->* P (C v1) t2).
      * apply multistep_congr_1. auto.
      * apply multi_trans with (P (C v1) t2).
        -- auto.
        -- apply multi_trans with (P (C v1) (C v2)).
           apply multistep_congr_2. constructor. auto.
           apply multi_R. constructor.
Qed.

Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t ==> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs; intros.
  - inversion H. constructor; constructor.
  - inversion H. subst. apply IHHs in H2.
    constructor; auto.
  - inversion H0. subst. apply IHHs in H5.
    constructor; auto.
Qed.

Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  induction t; intros; unfold normal_form_of in *; destruct H.
  - exists n. split.
    + inversion H; subst; auto; try inversion H1.
    + constructor.
  - assert (G : exists n1, t1 ==> n1).
    + (* We have to craft forall t' : tm, t1 -->* t' /\ step_normal_form t' *)
      (* Accidentally, we have step_normal_form -> normalizing -> 
         t1 -->* t' /\ step_normal_form t'. *)

      destruct (step_normalizing t1).
      Check step_normalizing.
      Check normalizing.
      apply IHt1 in H1. destruct H1. exists x0. destruct H1. auto.
    + assert (G' : exists n2, t2 ==> n2).
      (* step is normalizing, so this must be true. *)
      * destruct (step_normalizing t2).
        apply IHt2 in H1. destruct H1. exists x0. destruct H1. auto.
      * destruct G, G'. exists (x + x0).
        split. apply eval__multistep in H1, H2.

        (* Transitivities. *)
        assert (S: P t1 t2 -->* P (C x) t2).
        apply multistep_congr_1. auto.

        assert (S': P (C x) t2 -->* P (C x) (C x0)).
        apply multistep_congr_2. constructor. auto.

        assert (S'': P (t1) (t2) -->* P(C x) (C x0)).
        apply multi_trans with (P (C x) t2); auto.

        assert (S''': P (t1) (t2) -->* C (x + x0)).
        eapply multi_trans. eauto. apply multi_R. constructor.
        
        assert (S'''': t' = C (x + x0)).
        (* H: P t1 t2 -->* t'
           H0: step_normal_form t' *)
        apply (normal_forms_unique (P t1 t2)).
        unfold normal_form_of. split; auto.
        unfold normal_form_of. split; auto.
        unfold step_normal_form, normal_form. unfold not. intros.
        destruct H3. inversion H3. auto.

        constructor; auto.
Qed.

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.

Theorem evalF_eval : forall t n,
  evalF t = n <-> t ==> n.
Proof.
  induction t; split; intros.
  - induction H. simpl. constructor.
  - inversion H. subst. trivial.
  - simpl in H. rewrite <- H.
    constructor. 
    + apply IHt1. trivial.
    + apply IHt2. trivial.
  - simpl. inversion H. subst.
    apply IHt1 in H2. apply IHt2 in H4. subst. trivial.
Qed.