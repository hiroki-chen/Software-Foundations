{-# OPTIONS --allow-unsolved-metas #-}

module List-2 where

open import Data.Bool using (Bool; if_then_else_; true; false)
open import Data.List using (List; []; any) renaming (_∷_ to _::_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_; _==_)
open import Relation.Nullary.Decidable using (False)

variable
  s t : String

data _∈_ {A : Set} : (String × A) -> List (String × A) -> Set where
  here : ∀ {x : A} {l} → (s , x) ∈ ((s , x) :: l)
  skip : ∀ {x y : A} {l} → False (s ≟ t) ->
    ((s , x) ∈ l) -> ((s , x) ∈ ((t , y) :: l))

-- «s ∈ₛ ss» returns whether a string in list «ss» is equal to «s»
_∈ₛ_ : String → List String → Bool
x ∈ₛ [] = false
x ∈ₛ (x₁ :: ys) = if x₁ == x then true else x ∈ₛ ys

-- «xs ∪ ys» returns the /union/ of «xs» in «ys». That means, that if
-- an element from «xs» is already in «ys», it shouldn't be added
-- again.
infixl 10 _∪_
_∪_ : List String → List String → List String
[] ∪ ys = ys
(x :: xs) ∪ ys = if x ∈ₛ ys then xs ∪ ys else x :: (xs ∪ ys)

-- «ys \\ x» is a set difference. It should return only those elements
-- of «ys», which are not equal to «x».
_\\_ : List String → String → List String
[] \\ x = []
(x₁ :: ys) \\ x = if x₁ == x then ys \\ x else x₁ :: (ys \\ x)
