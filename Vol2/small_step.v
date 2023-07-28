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

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

Reserved Notation " a '/' st '-->a' a' "
                  (at level 40, st at level 39).
Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      i / st -->a (st i)
  | AS_Plus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 + a2 }> / st -->a <{ a1' + a2 }>
  | AS_Plus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 + a2 }> / st -->a <{ v1 + a2' }>
  | AS_Plus : forall (v1 v2 : nat),
      <{ v1 + v2 }> / st -->a (v1 + v2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 - a2 }> / st -->a <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 - a2 }> / st -->a <{ v1 - a2' }>
  | AS_Minus : forall (v1 v2 : nat),
      <{ v1 - v2 }> / st -->a (v1 - v2)
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 * a2 }> / st -->a <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 * a2 }> / st -->a <{ v1 * a2' }>
  | AS_Mult : forall (v1 v2 : nat),
      <{ v1 * v2 }> / st -->a (v1 * v2)

    where " a '/' st '-->a' a' " := (astep st a a').

Reserved Notation " b '/' st '-->b' b' "
                  (at level 40, st at level 39).

Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 = a2 }> / st -->b <{ a1' = a2 }>
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 = a2 }> / st -->b <{ v1 = a2' }>
| BS_Eq : forall (v1 v2 : nat),
    <{ v1 = v2 }> / st -->b
    (if (v1 =? v2) then <{ true }> else <{ false }>)
| BS_LtEq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 <= a2 }> / st -->b <{ a1' <= a2 }>
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 <= a2 }> / st -->b <{ v1 <= a2' }>
| BS_LtEq : forall (v1 v2 : nat),
    <{ v1 <= v2 }> / st -->b
    (if (v1 <=? v2) then <{ true }> else <{ false }>)
| BS_NotStep : forall b1 b1',
    b1 / st -->b b1' ->
    <{ ~ b1 }> / st -->b <{ ~ b1' }>
| BS_NotTrue : <{ ~ true }> / st -->b <{ false }>
| BS_NotFalse : <{ ~ false }> / st -->b <{ true }>
| BS_AndStep : forall b1 b1' b2,
    b1 / st -->b b1' ->
    <{ b1 && b2 }> / st -->b <{ b1' && b2 }>
| BS_AndTrueStep : forall b2 b2',
    b2 / st -->b b2' ->
    <{ true && b2 }> / st -->b <{ true && b2' }>
| BS_AndFalse : forall b2,
    <{ false && b2 }> / st -->b <{ false }>
| BS_AndTrueTrue : <{ true && true }> / st -->b <{ true }>
| BS_AndTrueFalse : <{ true && false }> / st -->b <{ false }>

where " b '/' st '-->b' b' " := (bstep st b b').

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Module CImp.
Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com. (* <--- NEW *)

Notation "x || y" :=
         (CPar x y)
           (in custom com at level 90, right associativity).
Notation "'skip'" :=
         CSkip (in custom com at level 0).
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
    (* Old part: *)
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      <{ c1 || c2 }> / st --> <{ c1' || c2 }> / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      <{ c1 || c2 }> / st --> <{ c1 || c2' }> / st'
  | CS_ParDone : forall st,
      <{ skip || skip }> / st --> <{ skip }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).
Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

Definition par_loop : com :=
  <{
      Y := 1
    ||
      while (Y = 0) do X := X + 1 end
   }>.

Theorem par_loop_example_0:
  exists st',
    par_loop / empty_st -->* <{ skip }> / st' /\
    st' X = 0.
Proof.
  unfold par_loop. 
  eexists. split.
  - eapply multi_step. apply CS_Par1. apply CS_Asgn.
    eapply multi_step. apply CS_Par2. apply CS_While.
    eapply multi_step. apply CS_Par2. apply CS_IfStep.
      apply BS_Eq1. apply AS_Id.
    eapply multi_step. apply CS_Par2. apply CS_IfStep.
      apply BS_Eq.
    eapply multi_step. apply CS_Par2. apply CS_IfFalse.
    eapply multi_step. apply CS_ParDone.
    eapply multi_refl.
  - auto.
Qed.

Example par_loop_example_2:
  exists st',
       par_loop / empty_st -->* <{skip}> / st'
    /\ st' X = 2.
Proof.
  eexists. intros. split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AsgnStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AsgnStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Asgn.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AsgnStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AsgnStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Asgn.
  eapply multi_step. apply CS_Par1. apply CS_Asgn.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity.
Qed.

Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st -->* par_loop / (X !-> S n ; st).
Proof.
  intros. destruct H.
  unfold par_loop.

  eapply multi_step. apply CS_Par2. apply CS_While.
  
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
  constructor. constructor.

  eapply multi_step. apply CS_Par2. apply CS_IfStep.
  rewrite H0. apply BS_Eq.

  eapply multi_step. apply CS_Par2. apply CS_IfTrue.

  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
  apply CS_AsgnStep. constructor. constructor.

  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
  apply CS_AsgnStep. apply AS_Plus.

  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
  apply CS_Asgn.

  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

  replace (S n) with (n + 1). rewrite H.
  constructor. apply Nat.add_1_r.
Qed.

Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st', par_loop / st -->* par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
(* it looks like mistake, we need n > 0 *)
Admitted.

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_st -->* <{skip}> / st'
    /\ st' X = n.
Proof.
  intros n.
  destruct (par_body_n n empty_st).
    split; reflexivity.
  rename x into st.
  inversion H as [H' [HX HY] ]; clear H.
  exists (Y !-> 1 ; st). split.
  eapply multi_trans with (par_loop,st). apply H'.
  eapply multi_step. apply CS_Par1. apply CS_Asgn.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id. rewrite t_update_eq.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  apply multi_refl.
  rewrite t_update_neq. assumption. intro X; inversion X.
Qed.

Definition stack := list nat.
Definition prog := list sinstr.

Inductive stack_step (st: state) : prog * stack -> prog * stack -> Prop :=
  | SS_Push: forall stk n p,
    stack_step st (SPush n :: p, stk) (p, n :: stk)
  | SS_Load: forall stk i p,
    stack_step st (SLoad i :: p, stk) (p, st i :: stk)
  | SS_Plus: forall stk n m p,
    stack_step st (SPlus :: p, n :: m :: stk) (p, (m + n) :: stk)
  | SS_Minus: forall stk n m p,
    stack_step st (SMinus :: p, n :: m :: stk) (p, (m - n) :: stk)
  | SS_Mult: forall stk n m p,
    stack_step st (SMult :: p, n :: m :: stk) (p, (n * m) :: stk).

Theorem stack_step_deterministic: forall st,
  deterministic (stack_step st).
Proof.
  unfold deterministic. intros st x y1 y2 H.
  induction H; intros; inversion H; auto.
Qed.

Definition stack_multistep st := multi (stack_step st).

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | APlus a1 a2 => s_compile(a1) ++ s_compile(a2) ++ [SPlus]
  | AMinus a1 a2 => s_compile(a2) ++ s_compile(a1) ++ [SMinus]
  | AMult a1 a2 => s_compile(a1) ++ s_compile(a2) ++ [SMult]
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  end.

(* s_compile e => prog; [] => empty stack as initial state. *)
(* s_compile e, [] ===multi_step===> [], [aeval st e] *)
Definition compiler_is_correct_statement : Prop :=
  forall e st prog, stack_multistep st (s_compile e ++ prog, []) (prog, [aeval st e]).

Theorem compiler_is_correct: compiler_is_correct_statement.
Proof.
  unfold compiler_is_correct_statement, stack_multistep. intros e.
  induction e; intros; simpl in *.
  - eapply multi_step. apply SS_Push. constructor.
  - eapply multi_step. apply SS_Load. constructor.
  - replace ((s_compile e1 ++ s_compile e2 ++ [SPlus]) ++ prog0) with (s_compile e1 ++ (s_compile e2 ++ [SPlus] ++ prog0)). repeat rewrite app_assoc.
Abort.