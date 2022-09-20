From LF Require Export exercise9.

Theorem mul_0_r' : forall n : nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - trivial.
  - intros. simpl. apply H.
Qed.

(** **** Exercise: 2 stars, standard (plus_one_r') *)
(* Complete this proof without using the induction tactic. *)
Theorem plus_one_r' : forall n : nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - trivial.
  - intros. simpl. rewrite H. trivial.
Qed.

Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).

Definition booltree_ind': Prop := forall P : booltree -> Prop,
  P bt_empty -> (* Initial state holds. *)
  (forall b : bool, P (bt_leaf b)) ->  (* Leaf state holds. *)
  (forall (b : bool) (t1 : booltree),
    P t1 -> forall t2 : booltree, P t2 -> P (bt_branch b t1 t2)) -> (* t1, t2 holds. *)
  (forall t : booltree, P t).

Definition booltree_property_type : Type := booltree -> Prop.

Definition base_case (P : booltree_property_type) : Prop := P bt_empty.

Definition leaf_case (P : booltree_property_type) : Prop :=
  forall (b: bool), P (bt_leaf b).
 
Definition branch_case (P : booltree_property_type) : Prop :=
  forall (b : bool) (t1 : booltree), P t1 ->
  forall (t2 : booltree), P t2 -> P (bt_branch b t1 t2).

Definition booltree_ind_type :=
  forall (P : booltree_property_type),
    base_case P ->
    leaf_case P ->
    branch_case P ->
    forall (b : booltree), P b.

Theorem booltree_ind_type_correct : booltree_ind_type.
Proof.
  exact booltree_ind.
Qed.

(* Here is an induction principle for a toy type:
  forall P : Toy -> Prop,
    (forall b : bool, P (con1 b)) ->
    (forall (n : nat) (t : Toy), P t -> P (con2 n t)) ->
    forall t : Toy, P t *)
(* Give an Inductive definition of Toy, such that the induction principle Coq generates is that given above: *)
Inductive Toy : Type :=
  | con1 (b : bool)
  | con2 (n : nat) (t : Toy).

Check Toy_ind.

Theorem Toy_correct : exists f g,
  forall P : Toy -> Prop,
    (forall b : bool, P (f b)) ->
    (forall (n : nat) (t : Toy), P t -> P (g n t)) ->
    forall t : Toy, P t.
Proof. 
  exists con1, con2. (* Do not forget con1, con2 is directly defined. *)
  exact Toy_ind.
Qed.

Inductive tree (X : Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).
Check tree_ind.

(* Find an inductive definition that gives rise to the following induction principle:
      mytype_ind :
        forall (X : Type) (P : mytype X -> Prop),
            (forall x : X, P (constr1 X x)) ->
            (forall n : nat, P (constr2 X n)) ->
            (forall m : mytype X, P m ->
               forall n : nat, P (constr3 X m n)) ->
            forall m : mytype X, P m *)
Inductive mytype (X : Type) : Type := 
  | constr1 (x : X)
  | constr2 (x : X) (n : nat)
  | constr3 (m : mytype X) (n : nat).

Check mytype_ind.

(* Find an inductive definition that gives rise to the following induction principle:
      foo_ind :
        forall (X Y : Type) (P : foo X Y -> Prop),
             (forall x : X, P (bar X Y x)) ->
             (forall y : Y, P (baz X Y y)) ->
             (forall f1 : nat -> foo X Y,
               (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
             forall f2 : foo X Y, P f2 *)
Inductive foo (X : Type) (Y : Type) : Type :=
  | bar (x : X)
  | baz (y : Y)
  | quux (f1 : nat -> foo X Y).

Check foo_ind.

Inductive foo' (X : Type) : Type :=
  | C1 (l : list X) (f : foo' X)
  | C2.

Definition foo'_ind' : Prop :=
  forall (X : Type) (P: foo' X -> Prop),
    (* C1 *)
    forall (l : list X) (f : foo' X), P f -> P ((C1 X l f)) ->
    (* C2 *)
    P (C2 X) ->
    forall f1 : foo' X, P f1.

Check foo'_ind.

