{-# OPTIONS --sized-types #-}

module Recursion where

open import Data.List using (List; []) renaming (_∷_ to _::_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

-- In this module you'll learn how to prove termination of programs.
--
-- Every single function in Agda is supposed to be terminating. If it
-- wasn't, it would very easy to prove false things, making Agda
-- unsound.
--
-- Agda has a very powerful termination checker. In many cases, Agda
-- is able to figure out that a function is terminating by
-- itself. Sometimes it can't though. See the example below for an
-- explanation.

drop1 : List ℕ -> List ℕ
drop1 [] = []
drop1 (head :: tail) = tail

------------------------------------------------------------------------------
-- Unsafe

-- This non-sensical function serves only as a demonstration of the
-- termination issue and the ways to solve it. It drops list elements
-- one-by-one, until it's empty, at which point it returns 0.
{-# TERMINATING #-}
reccy0 : List ℕ -> ℕ
reccy0 [] = 0
reccy0 l = reccy0 (drop1 l)

-- Note, the «TERMINATING» /pragma/ used above. Try removing it. Agda
-- will complain about being unable to check that «reccy0»
-- terminates. The pragma allows us to explicitly assure Agda that it
-- does in fact terminate. Naturally, it is a very dangerous pragma,
-- given the inevitability of human errors.
--
-- There must be a better way. There is.

------------------------------------------------------------------------------
-- Well-founded recursion

-- One pretty standard way to deal with termination issues is to use
-- /well-founded recursion/. The idea, informally, is to introduce a
-- /metric/ on the arguments. Then, each time we need to make a
-- recursive call, we prove that the metric of the new argument is
-- /less than/ the metric of the current argument.

-- «<\'» for «<′».
open import Data.Nat.Induction using (Acc; acc; <′-wellFounded)
open import Data.Nat using (_<′_; ≤′-refl)
open import Data.List using (length)

-- In Agda, the standard way to employ well-founded recursion is to
-- add an «Acc _<′_ (length l)» argument to your function. That
-- argument means that we are using metric «length» for argument «l»
-- and relation «<′» as «less than». Note, that we could have used the
-- standard «<» instead, but it would make the proofs a bit harder.
--
-- Note that in other functions you could use something else instead
-- of «length» or «l» or «<′».
reccy1Aux : (l : List ℕ) -> Acc _<′_ (length l) -> ℕ
reccy1Aux [] _ = 0
reccy1Aux (x :: xs) (acc rec) = reccy1Aux (drop1 (x :: xs)) (rec ≤′-refl)
-- ^ In the line above, we supply `rec` with a proof that the new
-- argument (which is «drop1 (x :: xs)») has length less than «x ::
-- xs». The proof is as simple as «≤′-refl».

-- Finally, we use the helper function to define a new «reccy».
reccy1 : List ℕ -> ℕ
reccy1 l = reccy1Aux l (<′-wellFounded _)

-- Unfortunately, I haven't found a good simple tutorial on
-- well-founded recursion. It might help to read the following though:
-- http://blog.ezyang.com/2010/06/well-founded-recursion-in-agda/

open Relation.Binary.PropositionalEquality.≡-Reasoning

reccy0-eq-reccy1Aux : ∀ (l : List ℕ)
  -> reccy0 l ≡ reccy1Aux l (<′-wellFounded _)
reccy0-eq-reccy1Aux [] = refl
reccy0-eq-reccy1Aux (x :: l) =
  begin
    reccy0 l
  ≡⟨ reccy0-eq-reccy1Aux l ⟩
    reccy1Aux l _
  ∎

reccy0-eq-reccy1 : ∀ (l : List ℕ)
  -> reccy0 l ≡ reccy1 l
reccy0-eq-reccy1 [] = refl
reccy0-eq-reccy1 (x :: l) =
  begin
    reccy0 l
  ≡⟨ reccy0-eq-reccy1 l ⟩
    reccy1 l
  ∎
-- Sized types

open import Size using (Size; ↑_)

-- Sized types are another way to address the termination issue. Sized
-- types store the «size» information together with the type of
-- expression. That allows Agda to easily see that the «size»
-- decreases in recursive calls, leading to a termination proof.

-- So, below we define a sized list. It's either empty, in which case
-- it can be any size; or, it's one element larger in size than its
-- tail.
--
-- You might ask, why doesn't «S[]» have size zero. I actually don't
-- know why, but sizes are relative.
--
-- To write «i + 1» where «i» is a size you need to type «↑ i».

data SList (a : Set) : {Size} -> Set where
  S[] : {i : Size} -> SList a {i}
  _S::_ : {i : Size} -> a -> SList a {i} -> SList a {↑ i}

unsize : {a : Set} -> SList a -> List a
unsize S[] = []
unsize (x S:: xs) = x :: unsize xs

sized : {a : Set} -> List a -> SList a
sized [] = S[]
sized (x :: xs) = x S:: sized xs

drop1'Ty : {i : Size} -> SList ℕ {↑ i} -> Set
drop1'Ty {i} S[] = SList ℕ {↑ i}
drop1'Ty {i} (x S:: xs) = SList ℕ {i}

-- «drop1'»'s result is one smaller for «_S::_» lists and the same
-- size for «S[]» lists.
drop1' : {i : Size} -> (l : SList ℕ {↑ i}) -> drop1'Ty l
drop1' S[] = S[]
drop1' (x S:: xs) = xs

reccy2Aux : {i : Size} -> SList ℕ {i} -> ℕ
reccy2Aux S[] = 0
-- here, the argument has size «↑ i», but the recursive call has
-- argument of size «i»
reccy2Aux .{↑ i} (_S::_ {i} x xs) = reccy2Aux {i} (drop1' (x S:: xs))

reccy2 : List ℕ -> ℕ
reccy2 l = reccy2Aux (sized l)

reccy1-eq-reccy2 : ∀ l -> reccy1 l ≡ reccy2 l
reccy1-eq-reccy2 [] = refl
reccy1-eq-reccy2 (x :: l) =
  begin
    reccy1 l
  ≡⟨ reccy1-eq-reccy2 l ⟩
    reccy2 l
  ∎
 