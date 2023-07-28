
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc 0 n p =
  begin
    (0 + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    0 + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-zero-elim : ∀ (n : ℕ) → n + 0 ≡ n
+-zero-elim 0 =
  begin
    0 + 0
  ≡⟨⟩
    0
  ∎
+-zero-elim (suc n) =
  begin
    suc n + 0
  ≡⟨⟩
    suc (n + 0)
  ≡⟨ cong suc (+-zero-elim n) ⟩
    suc n
  ∎

+-right-suc : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n) 
+-right-suc 0 n =
  begin
    0 + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (0 + n)
  ∎

+-right-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-right-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm m 0 =
  begin
    m + 0
  ≡⟨ +-zero-elim m ⟩
    m
  ≡⟨⟩
    0 + m
  ∎

+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-right-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎
