module Props where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ)

-- In this module, we'll showcase simple propositional proofs by
-- utilizing the Curry-Howard isomorphism. For that, we'll need to
-- have falsity «⊥» («\bot»), negation «¬» («\lnot»), conjunction «∧»
-- («\and»), disjuction «∨» («\or») and implication «->». The good
-- thing is, the implication is already builtin! It's the function
-- type and we have used it many times already. Let's define the rest
-- and prove some familiar lemmas.

-- This is to avoid declaring these variables in each function
-- separately.
variable
  A B C : Set

-- Prove some implication lemmas first

id : A -> A
id = λ z → z

imp1 : A -> B -> A
imp1 a b = a

comp1 : (A -> B) -> (B -> C) -> (A -> C)
comp1 f g = λ z → g (f z)

comp2 : (B -> C) -> (A -> B) -> (A -> C)
comp2 g f = λ z → g (f z)

comp3 : (A -> B -> C) -> (A -> B) -> A -> C
comp3 f g a = f a (g a)

-- In type theory falsity is represented as an empty type with no
-- elements, the «bottom». Here's a way to define an empty type in
-- Agda:
data ⊥ : Set where

-- If you've proven falsity, you can prove anything. Note, you might
-- need that later.
⊥-elim : ⊥ -> A
⊥-elim () -- agda.readthedocs.io/en/latest/language/function-definitions.html#absurd-patterns

-- It's a common encoding to define «¬ e» as «e → falsity».
¬ : Set -> Set
¬ A = A -> ⊥

-- Remember, «¬ e» is just a function «e → False». Think what the
-- types of «a» and «not-a» are.
contra0 : ¬ A -> A -> ⊥
contra0 not-a a = not-a a

contra1 : A -> ¬ (¬ A)
contra1 a not-a = not-a a

contra2 : ¬ (¬ (¬ A)) -> ¬ A
contra2 nnna a = nnna λ z → z a

contra-pos : (A -> B) -> ¬ B -> ¬ A
contra-pos = λ a b c -> b (a c)

-- The conjunction of types is a product type. You've already used
-- this type, named as «Pair» in Intro.agda. This time, we'll define
-- it ourselves.
record _∧_ (A : Set) (B : Set) : Set where
  -- | So as to construct elements using the «(1 , 3)» syntax.
  constructor _,_
  field
    fst : A
    snd : B

-- ↑ You can read more about that syntax here:
-- https://agda.readthedocs.io/en/v2.6.1.1/language/record-types.html

a-and-b-implies-a : A ∧ B -> A
a-and-b-implies-a (a , b) = a

and-commutes : A ∧ B -> B ∧ A
and-commutes = λ (a , b) -> (b , a)

-- The disjunction of types «A» and «B» is a sum (or a disjoint union)
-- type. This type holds values of either «A» or «B», _and_ knows
-- whether it belongs to «A» or «B». For example, if «A» is ℕ and «B»
-- is ℕ, the sum type distinguishes between «5» from the «A» ℕ and «5»
-- from the «B» ℕ. Look for the «sum-is-disjoint» proof below for the
-- clearer picture.

data _∨_ (A : Set) (B : Set) : Set where
  left : A -> A ∨ B
  right : B -> A ∨ B

-- ↑ You can read more about that syntax here:
-- https://agda.readthedocs.io/en/v2.6.1.1/language/data-types.html
--
-- You might be curious why constructors «left» and «right» have
-- function-like signatures. The reason is, when you use them to
-- construct, e.g. «left 5» below, they act like functions with the
-- exact signature they are provided with. So, for «left 5» below, the
-- specialized type of «left» is a function from «ℕ» to «ℕ ∧ ℕ»: it
-- takes a natural and constructs the disjunction.

left-5 : ℕ ∨ ℕ
left-5 = left 5

right-5 : ℕ ∨ ℕ
right-5 = right 5

-- left 5 ≠ right 5!!
sum-is-disjoint : ¬ (left-5 ≡ right-5)
sum-is-disjoint ()

-- Actually this pattern matches on the and type.
de-morgan1 : (¬ A ∧ ¬ B) -> ¬ (A ∨ B)
de-morgan1 (f , g) (left a) = f a
de-morgan1 (f , g) (right b) = g b

de-morgan2 : ¬ (A ∨ B) -> (¬ A ∧ ¬ B)
de-morgan2 f = (λ x -> f (left x)) , (λ x → f (right x))

-- feel free to add more clauses to this function (ala «de-morgan1»)
de-morgan3 : ¬ A -> ¬ B -> ¬ (A ∨ B)
de-morgan3 = λ a b -> de-morgan1 (a , b)

-- feel free to add more clauses to this function
contra3 : A ∨ B -> ¬ A -> B
contra3 (left a) not-a = ⊥-elim (not-a a)
contra3 (right b) not-a = b
