module List where

open import Data.Nat using (ℕ; _*_)
open import Data.List using (List; _∷_; []; map; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Note, «∷» is not a double colon. Instead, it's «\::».

squares : List ℕ -> List ℕ
squares = map (\x -> x * x)

test-squares : squares (1 ∷ 2 ∷ 9 ∷ []) ≡ (1 ∷ 4 ∷ 81 ∷ [])
test-squares = refl

triplicate : ∀ {a : Set} → List a → List a
triplicate = foldr (\a r -> a ∷ a ∷ a ∷ r) []

test-triplicate : triplicate (1 ∷ 2 ∷ 9 ∷ []) ≡ (1 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 2 ∷ 9 ∷ 9 ∷ 9 ∷ [])
test-triplicate = refl

-- Read the definition of «foldr» and use it to complete the function
-- «mul». The tests below should pass.

mul : List ℕ → ℕ
mul = foldr (λ a r -> a * r) 1

test-mul-0 : mul (1 ∷ 0 ∷ 9 ∷ []) ≡ 0
test-mul-0 = refl

test-mul-1 : mul (1 ∷ 2 ∷ 9 ∷ []) ≡ 18
test-mul-1 = refl

test-mul-2 : mul (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ 120
test-mul-2 = refl
