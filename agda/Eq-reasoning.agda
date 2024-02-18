module Eq-reasoning where

open import Data.Nat using (ℕ; _+_; _*_)

-- In this module you will learn to prove slightly more complicated
-- equalities.

data even : ℕ -> Set where
  even-0 : even 0
  even-+2 : ∀ {n} -> even n -> even (n + 2)

open import Relation.Binary.PropositionalEquality
  using (cong; module ≡-Reasoning; _≡_; refl; subst)
open import Data.Nat.Properties using (*-distribˡ-+; +-suc; +-identityʳ; *-zeroʳ)

-- The outline of the proof below, specifically «h1», showcases usage
-- of «≡-Reasoning». The idea is that you move from one value to
-- another by a chain of transitive equalities.
--
-- It's possible to complete the proof without importing anything
-- besides what is imported already. However, feel free to import more
-- functions from the existing import modules.

even-def : ∀ {m n : ℕ} -> (2 * m ≡ n) -> even n
even-def {ℕ.zero} {n} 2m-eq-n = subst (\x -> even x) h even-0
  where
  h : 0 ≡ n
  h = begin
    0 ≡˘⟨ *-zeroʳ 2 ⟩
    2 * 0
    ≡⟨ 2m-eq-n ⟩
    n ∎
   where open ≡-Reasoning

even-def {ℕ.suc m} {n} 2m-eq-n = subst (\x -> even _ -> even x) h1 even-+2 h2
 where
  h1 : 2 * m + 2 ≡ n
  h1 = begin
    2 * m + 2 ≡˘⟨ *-distribˡ-+ 2 m 1 ⟩
    2 * (m + 1) ≡⟨ (cong (2 *_) (+-suc m 0)) ⟩
    2 * ℕ.suc (m + 0) ≡⟨ cong (λ x -> 2 * ℕ.suc x) (+-identityʳ m) ⟩
    2 * ℕ.suc (m) ≡⟨ 2m-eq-n ⟩
    n ∎ -- the last line should be «n ∎»
   where open ≡-Reasoning

  h2 : even (2 * m)
  h2 = even-def {m} refl
