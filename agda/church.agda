{-# OPTIONS --type-in-type #-}
-- ^ You don't need to understand this, but in short, it's to allow
-- the factorial to work


module Church where

open import Data.Nat using (ℕ)

-- to test functions
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- A Church encoded Nat. We'll have to define all operations for it
manually.

N.B. «Set» not being named «Type» is widely considered to be a
(historic) mistake.
-}
Nat = (α : Set) -> α -> (α -> α) -> α

-- «\bN» for «ℕ».
{- Converts a Church Nat to a builtin Nat. Useful for testing. -}
natToℕ : Nat -> ℕ
natToℕ a = a ℕ ℕ.zero ℕ.suc

n0 : Nat
n0 α zero suc = zero

-- «\==» for «≡»

{- Verifies that «natToℕ n0» is indeed propositionally equal to «n0».

For such a simple statement, Agda is able to infer the proof
automatically: just type «refl». This will be discussed in more
details later.
-}
test-n0 : natToℕ n0 ≡ 0
test-n0 = refl

n1 : Nat
n1 α zero suc = suc zero

test-n1 : natToℕ n1 ≡ 1
test-n1 = refl

n2 : Nat
n2 α zero suc = suc (n1 α zero suc)

n3 : Nat
n3 α zero suc = suc (n2 α zero suc)

n4 : Nat
n4 α zero suc = suc (n3 α zero suc)

addNats : Nat -> Nat -> Nat
-- a f (bfx)
addNats a b = λ α zero suc -> a α (b α zero suc) suc

test-addNats : natToℕ (addNats n1 n2) ≡ natToℕ n3
test-addNats = refl

mulNats : Nat -> Nat -> Nat
-- a (bf) x the iterator can be constructed via a lambda term?
mulNats a b = λ α zero suc -> a α zero (λ n -> b α n suc)

{- A Church encoded pair! We'll have to define a bunch of operations
for it manually as well.
-}
Pair : Set -> Set -> Set
Pair α β = (ρ : Set) -> (α -> β -> ρ) -> ρ

mkPair : (α β : Set) -> α -> β -> Pair α β
mkPair α β a b = λ ρ r -> r a b

-- Note that unlike «fst» from «Intro.agda», this one takes type
-- variables as explicit arguments. So, every time you use it, you
-- will have to specify the type parameters of the pair.
fst : (α β : Set) -> Pair α β -> α
fst α β pair = pair α (λ a b -> a)

snd : (α β : Set) -> Pair α β -> β
snd α β pair = pair β (λ a b -> b)

factorial : Nat -> Nat
-- (1, 1) => (1, 2) => (2, 3) => (6, 4)
factorial n = (fst Nat Nat (n _ (mkPair Nat Nat n1 n1) (λ p -> mkPair Nat Nat (mulNats (fst Nat Nat p) (snd Nat Nat p)) (addNats (snd Nat Nat p) n1))))

