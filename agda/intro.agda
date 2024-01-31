module Intro where

-- you can import more things if you want to
open import Data.Nat using (ℕ; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- Builtin natural numbers.

They have already been defined for us, along with several useful
operations, e.g. «+», «*» etc.
-}
Nat = ℕ

{- Adds two natural numbers -}
addNats : Nat -> Nat -> Nat
addNats x y = x + y

{- Multiplies two natural numbers -}
mulNats : Nat -> Nat -> Nat
mulNats 0 y = 0
mulNats (suc x) y = addNats x (mulNats x y)

{- Adds 1 to the given number -}
add1 : Nat -> Nat
add1 x = addNats 1 x

{- Adds 3 to the given number -}
add3 : Nat -> Nat
add3 = \x -> addNats 3 x

-- You can use a λ symbol to create functions instead. To type this
-- symbol (and others) in Emacs agda-mode and VS Code agda plugin,
-- type «\» followed by, usually, a LaTeX name for the symbol. E.g.,
-- «\lambda» for «λ», «\->» or «\rightarrow» for «→»:

{- Adds 3 to the given number -}
add3' : Nat → Nat
add3' = λ x → addNats 3 x

{- Adds 5 to the given number -}
add5 : Nat -> Nat
add5 = addNats 5

{- Multiplies the given number by 7 -}
mul7 : Nat -> Nat
mul7 = \x -> mulNats 7 x

{- Multiplies the given number by 0 -}
mul0 : Nat -> Nat
mul0 = \x -> mulNats 0 x

----------

open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Sigma using (fst; snd)

{- Builtin natural numbers.

They have already been defined for us, along with several useful
operations, e.g. «fst», «snd» etc.
-}
Pair : Set -> Set -> Set
Pair = (_×_)

-- «\alpha» for «α», «\beta» for «β», etc.

{- Create a Pair of an element of type α and an element of type β.

  Note that _first_ we are introducing type varialbes «(α β :
  Set)». The type variables can stand for ~any type, or any element of
  «Set». (N.B. not quite, but it's a talk for another day)

  The following arguments «depend» on «α» and «β» by referring to them
  by name: «α -> β -> Pair α β».
-}
mkPair : (α β : Set) -> α -> β -> Pair α β
mkPair α β a b = (a , b)

-- Note, how we first apply «mkPair» to «Nat» and «Nat». It's natural,
-- because they are the first arguments of «mkPair»: the
-- aforementioned «(α β : Set)».
pair-1-3 : Pair Nat Nat
pair-1-3 = mkPair Nat Nat 1 3

n3 : Nat
n3 = snd pair-1-3

{- Well, guess what this does. -}
exchange : (α β γ : Set) -> Pair α (Pair β γ) -> Pair (Pair α β) γ
exchange α β γ pair = ((fst pair , (fst (snd pair))) ,  snd (snd pair))
