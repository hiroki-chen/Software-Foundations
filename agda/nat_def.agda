module nat_def where

-- Constructor for natural numbers.
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

seven = suc (suc (suc (suc (suc (suc (suc 0))))))

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
0 + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
0 * n = 0
suc m * n = n + (m * n)

_-_ : ℕ → ℕ → ℕ
n - 0 = 0
0 - n = 0
suc m - suc n = m - n

five = 8 - 3
another_five = 7 - 2

_ =
  begin
    2 * 3
  ≡⟨⟩ 
    3 + (1 * 3)
  ≡⟨⟩ 
    3 + (3 + (0 * 3))
  ≡⟨⟩ 
    3 + (3 + 0)
  ≡⟨⟩ 
    6
  ∎

_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    (4 + (4 + (4 + 0)))
  ≡⟨⟩
    (4 + (4 + 4))
  ≡⟨⟩
    4 + 8
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
n ^ 0 = 1
n ^ (suc m) = n * (n ^ m)

_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    3 * (3 * (3 * 3))
  ≡⟨⟩
    3 * (3 * 9)
  ≡⟨⟩
    3 * 27
  ≡⟨⟩
    81
  ∎

