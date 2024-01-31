{-# OPTIONS --type-in-type #-}

module Church-implicit where

-- Note how in the previous module you had to always explicity specify
-- types parameters for Nats and Pair functions. It was probably
-- annoying. Turns out, it's not always necessary. Sometimes, type
-- parameters can inferred from the terms that inhabit those
-- types. For example, in «(α β : Set) -> α -> β -> Pair α β», surely,
-- if given the second argument with a known type, we can infer that
-- «α» automatically.
--
-- Agda has a mechanism to facilitate such situations. It's called
-- implicit types. If you want a type to be implicit, just wrap it in
-- curly brackets instead of the round ones: «{α β : Set}» instead of
-- «(α β : Set)».
--
-- In this module, you are going to rewrite all Pair related
-- definitions, but with all _implicit_ type variables. To be precise,
-- you should have «Pair», «mkPair», «fst», «snd», «factorial».

open import Church using (Nat; n1; mulNats; addNats)

{- A Church encoded pair! We'll have to define a bunch of operations
for it manually as well.
-}
Pair : Set -> Set -> Set
Pair α β = {ρ : Set} -> (α -> β -> ρ) -> ρ

mkPair : {α β : Set} -> α -> β -> Pair α β
mkPair a b = λ r -> r a b

fst : {α β : Set} -> Pair α β -> α
fst pair = pair (λ a b -> a)

snd : {α β : Set} -> Pair α β -> β
snd pair = pair (λ a b -> b)

factorial : Nat -> Nat
-- Now we cannot omit the type of n because Agda cannot guess it if all arguments are implicit.
factorial n = (fst (n (Pair Nat Nat) (mkPair n1 n1) (λ p -> mkPair (mulNats (fst p) (snd p)) (addNats (snd p) n1))))
