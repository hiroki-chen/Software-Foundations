From LF Require Import exercise1.
From LF Require Import exercise2.

Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).


Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | pair x y => pair y x
  end.

Notation "( x , y )" := (pair x y).

Theorem surjective_pairing : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof. reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p. reflexivity.
Qed.

(** **** Exercise: 1 star, standard (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p. simpl. reflexivity.
Qed.

(** **** Exercise: 1 star, standard, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p. simpl. reflexivity.
Qed.

Inductive natlist: Type :=
  | nil
  | cons (n: nat) (l: natlist).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count: nat) : natlist :=
  match count with
  | O => nil
  | S c' => cons (n) (repeat n c')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | cons _ l' => 1 + length l'
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | cons n l => cons n (app l l2)
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

(* Here are two smaller examples of programming with lists. The hd function returns the first element (the "head") of the list, while tl returns everything but the first element (the "tail"). Since the empty list has no first element, we pass a default value to be returned in that case. *)
Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | cons n _ => n
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | cons _ l' => l'
  end.


(** **** Exercise: 2 stars, standard, especially useful (list_funs) *)
(* Complete the definitions of nonzeros, oddmembers, and countoddmembers below.
Have a look at the tests to understand what these functions should do. *)
(* Returns all non-zero elements. *)
Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | nil => nil
  | cons O l'     => nonzeros l'
  | cons n l' => cons n (nonzeros l')
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

(* Returns all odd elements. *)
Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | nil => nil 
  | cons n l' => match even n with
                 | true => oddmembers l'
                 | false => cons n (oddmembers l')
                 end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

(* For countoddmembers, we're giving you a header that uses keyword Definition instead of Fixpoint. The point of stating the question this way is to encourage you to implement the function by using already-defined functions, rather than writing your own recursive definition. *)
Definition countoddmembers (l : natlist) : nat :=
  match l with
  | nil => O
  | cons n l' => match even n with
                 | true => length ( oddmembers l' ) 
                 | false => length ( oddmembers l' ) + 1
                 end 
  end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.
  

(** **** Exercise: 3 stars, advanced (alternate) *)
(* Complete the following definition of alternate, which interleaves two lists into one, alternating
between elements taken from the first list and elements from the second. See the tests below for more
specific examples.
Hint: there is an elegant way of writing alternate that fails to satisfy Coq's requirement that all
Fixpoint definitions be structurally recursing, as mentioned in Basics. If you encounter that
difficulty, consider pattern matching against both lists at the same time with the "multiple pattern"
syntax we've seen before. *)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  (* Pick exactly one element from each list alternately. *)
  match l1, l2 with
  | nil, nil => nil
  | _, nil => l1
  | nil, _ => l2
  | (cons n1 l1'), (cons n2 l2') => [n1;n2] ++ (alternate l1' l2')
  end.

Compute alternate [1;2;3] [4;5;6].

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

(** **** Exercise: 3 stars, standard, especially useful (bag_functions) *)
(* Complete the following definitions for the functions count, sum, add, and member for bags. *)
Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => O
  | cons n l' => match eqb n v with
                 | true => 1 + (count v l')
                 | false => (count v l')
                 end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum (lhs rhs : bag) : bag :=
  match lhs, rhs with
  | _, _ => lhs ++ rhs
  end.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
  match s with
  | nil => [v]
  | cons _ _ => [v] ++ s
  end.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | nil => false
  | cons v' s' => match eqb v' v with
                  | false => (member v s')
                  | true => true
                  end
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: 3 stars, standard, optional (bag_more_functions) *)
(* Here are some more bag functions for you to practice with.
When remove_one is applied to a bag without the number to remove, it should return the same bag
unchanged. *)
Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | nil => s
  | cons v' s' => match eqb v' v with
                  | true => s'
                  | false => cons v' (remove_one v s')
                  end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
  | nil => s
  | cons v' s' => match eqb v' v with
                  | true => (remove_all v s')
                  | false => cons v' (remove_all v s')
                  end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | nil => true
  | cons n s' => match member n s2 with
                 | true => included s' (remove_one n s2)
                 | false => false
                 end
  end.

Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.


(** **** Exercise: 2 stars, standard, especially useful (add_inc_count) *)
(* Adding a value to a bag should increase the value's count by one.
   State this as a theorem and prove it. *)
Theorem add_inc_count : forall (n : nat) (s : bag),
  count n (add n s) = count n s + 1.
Proof.
  intros n s. destruct s.
  - simpl. rewrite eqb_refl. reflexivity.
  - simpl. rewrite eqb_refl. rewrite <- plus_n_Sm. rewrite add_0_r. reflexivity.
Qed.

(* ++ is defined right associative.. *)
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil => nil 
  | cons n l' => app (rev l') [n]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

(* For something a bit more challenging than the proofs we've seen so far, let's prove that reversing a
list does not change its length. Our first attempt gets stuck in the successor case... *)
Lemma app_length: forall l1 l2 : natlist,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros l1 l2. induction l1 as [| n l' H].
  - reflexivity.
  - simpl.  rewrite -> H. reflexivity.
Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' H].
  - reflexivity.
  - simpl. rewrite -> app_length. rewrite -> H. apply add_one_right.
Qed.


(** **** Exercise: 3 stars, standard (list_exercises) *)
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [ | n l' H].
  - reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l' H].
  - rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> H. rewrite -> app_assoc. reflexivity.
Qed.

(* An involution is a function that is its own inverse. That is, applying the function twice yield the
original input. *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| n l' H].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> H. reflexivity.
Qed.

(* There is a short solution to the next one. If you find yourself getting tangled up, step back and try
to look for a simpler way. *)
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* Apply association twice. *)
  intros.
  rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
Qed.

(* An exercise about your implementation of nonzeros: *)
Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n l' H].
  - simpl. reflexivity.
  - simpl. rewrite -> H. destruct l2.
    + rewrite -> app_nil_r. simpl. rewrite -> app_nil_r. reflexivity.
    + simpl. destruct n.
      * reflexivity.
      * reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (eqblist) *)
(* Fill in the definition of eqblist, which compares lists of numbers for equality. Prove that eqblist l
l yields true for every list l. *)
Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true 
  | _, nil => false
  | nil, _ => false
  | cons n1 l1', cons n2 l2' =>
    match eqb n1 n2 with 
      | true => (eqblist l1' l2')
      | false => false
    end
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. simpl. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
  Proof. simpl. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. simpl. reflexivity. Qed.

Theorem eqblist_refl : forall l : natlist,
  true = eqblist l l.
Proof.
  intros l. induction l.
  - reflexivity.
  - simpl. rewrite <- IHl. rewrite eqb_refl. reflexivity.
Qed.


(** **** Exercise: 1 star, standard (count_member_nonzero) *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s. destruct s.
  - reflexivity.
  - reflexivity.
Qed.

(* The following lemma about leb might help you in the next exercise (it will also be useful in later 
chapters). *)
Theorem leb_n_Sn : forall n : nat,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
  Qed.

(** **** Exercise: 3 stars, advanced (remove_does_not_increase_count) *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s as [| n s' H].
  - reflexivity.
  - simpl. rewrite <- H. destruct n.
    + rewrite eqb_refl. rewrite leb_n_Sn. rewrite H. reflexivity.
    + reflexivity.
Qed.


(** **** Exercise: 3 stars, standard, optional (bag_count_sum) *)
(* Write down an interesting theorem bag_count_sum about bags involving the functions count and sum, and
prove it using Coq. (You may find that the difficulty of the proof depends on how you defined count!
Hint: If you defined count using =? you may find it useful to know that destruct works on arbitrary
expressions, not just simple identifiers.) *)
Theorem bag_count_sum: forall s1 s2 : bag,
  count 0 (sum s1 s2) = (count 0 s1) + (count 0 s2).
Proof.
  intros. induction s1 as [| n s1' H].
  - reflexivity.
  - destruct n.
    + simpl. rewrite H. reflexivity.
    + simpl. apply H.
Qed.

(** **** Exercise: 3 stars, advanced (involution_injective) *)
(* Prove that every involution is injective. Involutions were defined above in rev_involutive. An involution injective function is one-to-one: it maps distinct inputs to distinct outputs, without any collisions. *)
Theorem involution_injective : forall (f : nat -> nat),
  (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f H0 n1 n2.
  intros H1.
  rewrite H0. rewrite <- H1. apply H0.
Qed.

(** **** Exercise: 2 stars, advanced (rev_injective) *)
(* Prove that rev is injective. Do not prove this by induction -- that would be hard. Instead, re-use
the same proof technique that you used for involution_injective. Do not try to use that exercise
directly as a lemma: the types are not the same. *)
Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive. rewrite <- H. rewrite -> rev_involutive. reflexivity.
Qed. 

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
  match l with
  | nil => None
  | cons n' l'
    => match n with
       | 0 => (Some n')
       | S next => (nth_error l' next)
       end
  end.

(* unwrap_or *)
Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | cons n _ => Some n
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. simpl. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. simpl. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: 1 star, standard, optional (option_elim_hd) *)
(* This exercise relates your new hd_error to the old hd. *)
Theorem option_elim_hd : forall (l : natlist) (default : nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros. destruct l.
  - reflexivity.
  - reflexivity.
Qed.

End NatList.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

(** **** Exercise: 1 star, standard (eqb_id_refl) *)
Theorem eqb_id_refl : forall x,
  eqb_id x x = true.
Proof.
  intros x. destruct x as [n].
  destruct n as [| n'].
  - reflexivity.
  - simpl. rewrite eqb_refl. reflexivity.
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).


(* The update function overrides the entry for a given key in a partial map by shadowing it with a new one
(or simply adds a new entry if the given key is not already present). *)
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                      then Some v
                      else find x d'
  end.

(* Exercise: 1 star, standard (update_eq) *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros. simpl. rewrite -> eqb_id_refl. reflexivity.
Qed.


(** **** Exercise: 1 star, standard (update_neq) *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros. simpl. rewrite -> H. reflexivity.
Qed.

End PartialMap.