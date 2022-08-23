From LF Require Export exercise3.
From LF Require Export exercise2.
From LF Require Export exercise1.

Inductive list (X: Type) : Type :=
  | nil
  | cons (x: X) (l : list X).

Arguments nil {X}.
Arguments cons {X}.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Definition mynil := @nil nat.
Check mynil.
Fail Definition mynil' := nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** **** Exercise: 2 stars, standard (poly_exercises)
Here are a few simple exercises, just like ones in the Lists chapter, for practice with polymorphism. Complete the proofs below. *)
Theorem app_nil_r : forall (X : Type), forall l : list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [| n l' H].
  - reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (more_poly_exercises) *)
(* Here are some slightly more interesting ones... *)
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).
Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
  : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* Prints @pair: forall X Y, Type, X -> Y -> X * Y. *)
Check @pair.
(* Prints  [(1, false); (2, false)] *)
Compute (combine [1;2] [false;false;true;true]).

(** **** Exercise: 2 stars, standard, especially useful (split) *)
(* The function split is the right inverse of combine: it takes a list of pairs and returns a pair of lists. In many functional languages, it is called unzip. *)
(* Fill in the definition of split below. Make sure it passes the given unit test. *)
Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) := 
  match l with
  | [] => ([], [])
  | (x, y) :: l' => ((x :: fst (split l')), (y :: snd (split l')))
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl. reflexivity. Qed.

Fixpoint filter {X : Type} (pred : X -> bool) (l : list X) : list X :=
  match l with
  | nil => nil
  | h :: t => 
    if pred h then h :: (filter pred t)
    else (filter pred t)
  end.

Example test_filter2:
  filter (fun l => (length l) =? 1 )
         [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. simpl. reflexivity. Qed.

(** **** Exercise: 3 stars, standard (partition) *)
(* Use filter to write a Coq function partition:
      partition : ∀ X : Type,
                  (X → bool) → list X → list X × list X
Given a set X, a predicate of type X → bool and a list X, partition should return a pair of lists. The first
member of the pair is the sublist of the original list containing the elements that satisfy the test, and the
second is the sublist containing those that fail the test. The order of elements in the two sublists should be
the same as their order in the original list. *)
Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  match l with
  | [] => ([], [])
  | _ => ((filter test l), (filter (fun X => negb (test X)) (l)))
  end.

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. simpl. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. simpl. reflexivity. Qed.

(* It takes a function f and a list l = [n1, n2, n3, ...] and returns the list [f n1, f n2, f n3,...]. *)
Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

(** **** Exercise: 3 stars, standard (map_rev) *)
(* Show that map and rev commute. You may need to define an auxiliary lemma. *)
Lemma map_f_assoc: forall (X Y: Type) (f : X -> Y) (l1 l2: list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite <- IHl. rewrite -> map_f_assoc. reflexivity.
Qed.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

(** **** Exercise: 2 stars, standard, especially useful (flat_map) *)
(* The function map maps a list X to a list Y using a function of type X → Y. We can define a similar function,
flat_map, which maps a list X to a list Y using a function f of type X → list Y. Your definition should work by
'flattening' the results of f, like so:
        flat_map (fun n ⇒ [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12]. *)
Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : list Y :=
  match l with
  | [] => []
  | h :: t => ((f h) ++ (flat_map f t))
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. simpl. reflexivity. Qed.

Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)
  end.
