module b522-playground where

import Relation.Binary.PropositionalEquality as Eq

open import Data.List using (List; []; _∷_; _++_)
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties using (+-assoc)

fact : ℕ → ℕ
fact 0 = 1
fact (suc n) = suc n * (fact n)

sumList : List ℕ → ℕ
sumList [] = 0
sumList (x ∷ ns) = x + sumList ns

test1 : sumList (2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ 14
test1 = refl

sum-assoc : ∀ (n m : List ℕ) → sumList (n ++ m) ≡ sumList n + sumList m
sum-assoc [] m = refl
sum-assoc (n ∷ ns) m = 
  begin
    sumList ((n ∷ ns) ++ m)
  ≡⟨ refl ⟩
    sumList (n ∷ (ns ++ m))
  ≡⟨ refl ⟩
    n + sumList (ns ++ m)
    -- x is a proof for equality and we use this lambda to derive a new equality
    -- in the form of `n + x` so that if `x = x` then `n + x = n + x`
  ≡⟨ cong (λ x → n + x) (sum-assoc ns m) ⟩
    n + (sumList ns + sumList m)
  ≡⟨ sym (+-assoc n (sumList ns) (sumList m)) ⟩
    (n + sumList ns) + sumList m
  ≡⟨ refl ⟩
    sumList (n ∷ ns) + sumList m
  ∎ 

list1 list2 : List ℕ
list1 = 1 ∷ 2 ∷ 3 ∷ []
list2 = 2 ∷ 4 ∷ []

check : sumList (list1 ++ list2) ≡ sumList list1 + sumList list2
check = sum-assoc list1 list2


