-- «Maybe A» maybe holds a value of A! To be more precise, it either
-- holds «nothing» (see the constructor below), or «just x», where «x»
-- is the value of type «A». It can be useful to represent failure.
data Maybe (A : Set) : Set where
  just : A -> Maybe A
  nothing : Maybe A

-- You can define inner modules!! Don't bother about it too much, it's
-- there just to forbid you from using the list constructors while
-- using the list type itself.
module List where
  import Data.List using (List; []) renaming (_∷_ to _::_)

  -- «head» returns the first element of the list, or «nothing» if the
  -- list is empty
  head : {A : Set} -> Data.List.List A -> Maybe A
  head Data.List.[] = nothing
  head (h Data.List.:: _) = just h

  List : Set -> Set
  List = Data.List.List

open List
-- /Do not/ import list constructors.

open import Data.Nat using (ℕ; _+_; _>_; _⊔_)
open import Data.Bool using (Bool; if_then_else_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl)
-- «headIfThenElse» takes the head of the boolean list. If the head is
-- «true», it returns the head of the first list of naturals, if
-- «false» -- of the second one. If either head is absent, the
-- function returns «nothing».
--
-- This function is meant to familiarize you with the
-- with-construction and it's syntax. It is like pattern-matching but
-- not on arguments of the functions but on arbitrary
-- computations. You can read more about it at
-- https://agda.readthedocs.io/en/latest/language/with-abstraction.html
headIfThenElse : List Bool -> List ℕ -> List ℕ -> Maybe ℕ
headIfThenElse cond t f
  with head cond
... | nothing = nothing
... | just cond'
      with head (if cond' then t else f)
...     | nothing = nothing
...     | just res = just res

-- The same as «headIfThenElse». The only difference is that we
-- pattern-match on the «just» case first. Due to agda quirks, it
-- dramatically changes the syntax… Try to use the «...» syntax from
-- before, it won't work! You have to duplicate the whole line each
-- time. Meh.
headIfThenElse' : List Bool -> List ℕ -> List ℕ -> Maybe ℕ
headIfThenElse' cond t f with head cond
headIfThenElse' cond t f | just cond' with head (if cond' then t else f)
headIfThenElse' cond t f | just cond' | just res = just res 
headIfThenElse' cond t f | just cond' | nothing = nothing 
headIfThenElse' cond t f | nothing = nothing


-- Returns the maximum of two heads! If either list is empty, return
-- «nothing».
--
-- Here, you will learn the simultaneous with-construction.
headMax : List ℕ -> List ℕ -> Maybe ℕ
headMax a b
  with head a | head b
... | just a' | just b' = just ( a' ⊔ b')
... | _ | _ = nothing
 