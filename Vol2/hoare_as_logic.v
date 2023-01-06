Set Warnings "-deprecated-hint-without-locality,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import hoare.

From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Bool.

Hint Constructors ceval : core.

Definition valid (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
    st =[ c ]=> st' ->
    P st ->
    Q st'.

Inductive derivable : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      derivable P <{skip}> P
  | H_Asgn : forall Q V a,
      derivable (Q [V |-> a]) <{V := a}> Q
  | H_Seq : forall P c Q d R,
      derivable P c Q -> derivable Q d R -> derivable P <{c;d}> R
  | H_If : forall P Q b c1 c2,
    derivable (fun st=> P st /\ bassn b st) c1 Q ->
    derivable (fun st=> P st /\ ~(bassn b st)) c2 Q ->
    derivable P <{if b then c1 else c2 end}> Q
  | H_While : forall P b c,
    derivable (fun st=> P st /\ bassn b st) c P ->
    derivable P <{while b do c end}> (fun st=> P st /\ ~ (bassn b st))
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
    derivable P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.

Lemma H_Consequence_pre: forall (P Q P': Assertion) c,
  derivable P' c Q ->
  (forall st, P st -> P' st) ->
  derivable P c Q.
Proof. eauto using H_Consequence. Qed.

Lemma H_Consequence_post: forall (P Q Q' : Assertion) c,
  derivable P c Q' ->
  (forall st, Q' st -> Q st) ->
  derivable P c Q.
Proof. eauto using H_Consequence. Qed.

Theorem provable_true_post: forall c P,
  derivable P c True.
Proof.
  induction c; intros.
  - eapply H_Consequence_post. apply H_Skip. auto.
  - eapply H_Consequence_pre. apply H_Asgn. auto.
  - eapply H_Seq; auto.
  - eapply H_Consequence_pre. apply H_If; auto. intros. apply H.
  - eapply H_Consequence. apply H_While; auto. auto. auto.
Qed.

Theorem provable_false_pre : forall c Q,
  derivable False c Q.
Proof.
  induction c; intros.
  - eapply H_Consequence_pre. apply H_Skip. intros. inversion H.
  - eapply H_Consequence_pre. apply H_Asgn. intros. inversion H.
  - eapply H_Consequence_pre. eapply H_Seq; auto. trivial.
  - apply H_If. eapply H_Consequence_pre.
    + trivial.
    + intros. destruct H. auto.
    + eapply H_Consequence_pre. auto. intros. destruct H. auto.
  - eapply H_Consequence_post.
    + apply H_While. simpl. eapply H_Consequence_pre.
      trivial. intros. inversion H. eauto.
    + intros. simpl. inversion H. inversion H0.
Qed. 

(* A logic is sound if everything that is derivable is valid.
A logic is complete if everything that is valid is derivable. *)
Theorem hoare_sound : forall P c Q,
  derivable P c Q -> valid P c Q.
Proof.
  intros. induction X; intros st st' Hcom H'.
  - inversion Hcom. subst. auto.
  - inversion Hcom. subst. auto.
  - inversion Hcom. subst. auto. eapply IHX2. eauto. eapply IHX1; eauto.
  - inversion Hcom. subst.
    + eapply IHX1. eauto. split; auto.
    + eapply IHX2. eauto. split; auto.
  - remember <{ while b do c end }> as com.
    induction Hcom; try discriminate Heqcom.
    + inversion Heqcom. subst. clear Heqcom. split; auto.
    + inversion Heqcom. subst. clear Heqcom.
      apply IHHcom2. trivial.
      eapply IHX. eauto. split; trivial.
  - apply q. eapply IHX. eauto. apply p. auto.
Qed.

Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.

Hint Unfold wp : core.

Theorem wp_is_precondition : forall c Q,
  {{wp c Q}} c {{Q}}.
Proof. auto. Qed.

Theorem wp_is_weakest : forall c Q P',
    {{P'}} c {{Q}} ->
    P' ->> (wp c Q).
Proof. eauto. Qed.

Lemma wp_seq : forall P Q c1 c2,
    derivable P c1 (wp c2 Q) ->
    derivable (wp c2 Q) c2 Q ->
    derivable P <{c1; c2}> Q.
Proof.
  intros.
  eapply H_Seq; eauto.
Qed.

Lemma wp_invariant : forall b c Q,
    valid (wp <{while b do c end}> Q /\ b) c (wp <{while b do c end}> Q).
Proof.
  unfold valid, wp. intros. destruct H0. specialize H0 with s'.
  apply H0. eauto.
Qed.

Theorem hoare_complete: forall P c Q,
  valid P c Q -> derivable P c Q.
Proof.
  unfold valid. intros P c. generalize dependent P.
  induction c; intros P Q HT.
  - eapply H_Consequence_pre. apply H_Skip.
    intros. apply HT with st; auto.
  - eapply H_Consequence_pre. apply H_Asgn.
    intros. apply HT with st; auto.
  - apply wp_seq.
    + apply IHc1. unfold wp. intros. eapply HT; eauto.
    + apply IHc2. unfold wp. intros. eapply H0; eauto.
  - apply H_If.
    + apply IHc1. intros. apply HT with st; destruct H0; eauto.
    + apply IHc2. intros. apply HT with st; destruct H0; simpl in H1;
      try apply not_true_is_false in H1; eauto.
  - eapply H_Consequence. apply H_While.
    + apply IHc. apply wp_invariant.
    + apply wp_is_weakest. eauto.
    + intros. destruct H. apply H.
      simpl in *. apply not_true_is_false in H0.
      eauto.
      (* b must be explicitly false so that eauto can prove the goal. *)
Qed.
