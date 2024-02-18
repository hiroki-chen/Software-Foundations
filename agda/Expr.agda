module Expr where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []) renaming (_∷_ to _::_)
open import Data.Nat using (ℕ; _+_; _*_; pred)
import Agda.Builtin.Nat as Nat using (_==_)
open import Data.Product using (_×_; _,_) -- «\x» for «×»
open import Data.String using (String; _==_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- In this task we'll create a simple language, modeled after
-- ISWIM. You can read more about ISWIM in chapter 4 of «Semantics
-- engineering with PLT-Redex».

-- First, let's describe the syntax of the language.

--  Each expression in the language is constructed using one of the
-- following constructors.
data Expr : Set where
  Var : String -> Expr -- ^ to represent variables like «x», «y» etc
  Abs : String -> Expr -> Expr -- ^ «λ x. body»
  App : Expr -> Expr -> Expr -- ^ «(f x)»

  Num : ℕ -> Expr -- «5», «8» etc
  T : Expr -- «true»
  F : Expr -- «false»

  Add : Expr -> Expr -> Expr
  If : Expr -> Expr -> Expr -> Expr

  Eq : Expr -> Expr -> Expr
  Pred : Expr -> Expr
  Mul : Expr -> Expr -> Expr

-- Examples of programs in ISWIM

varX = Var "x"
num5 = Num 5
add5X = Add (Num 5) (Var "x")
add5 = Abs "x" add5X

-- adds 5 to variable «val» if variable «add-5» is set to «true»,
-- otherwise returns «val» as-is.
conditionalAdd =
  Abs "add-5" (Abs "val"
    (If (Var "add-5")
      (App add5 (Var "val"))
      (Var "val")))

-- «Let name value block» should assign «value» to variable «name» and
-- then return the expression in «block» (which might use the variable
-- «name»).
Let : String -> Expr -> Expr -> Expr
-- let x := expr in block ==> (λ x. block) expr
Let name value block = App (Abs name block) value

adderMaker =
  Let "add-x" (Abs "x" (Abs "y" (Add varX (Var "y"))))
    (Let "add-5" (App (Var "add-x") num5)
      (Let "x" (Num 8)
        (App (Var "add-5") (Num 10))))

-- Now that we have the syntax, we need to come up with semantics for
-- the language. One way to define semantics is by constructing an
-- /interpreter/.

-- In class you have learnt an approach involving abstract
-- machines. Before using those though, to have a frame of reference,
-- we'll first create two simple, naive interpreters.

-- First, we'll define a «static» interpreter, then a «dynamic»
-- one. The difference is the following. When called, functions in the
-- static interpreter, use the environment (i.e. variable values) at
-- the definition site. In the dynamic interpreter, on the other hand,
-- functions use the environment at the call site.
--
-- To see how such difference manifests itself, look at the two
-- «test-adderMaker» lemmas below.

module Static where
  -- «Env» is forward declared, because «Result» references it.
  Env : Set
  data Result : Set where
    RNum : ℕ -> Result
    RBool : Bool -> Result
    RFunction : String -> Expr -> Env -> Result
    RError : Result

  Env = List (String × Result)

  module Env where
    -- «find» looks up a variable value in the environment. If not
    -- found, it returns «RError»
    find : String -> Env -> Result
    find var [] = RError
    find var ((var' , val) :: rest) = if var == var' then val else find var rest

  -- «interpret steps expr env» interprets expression «expr» in
  -- environment «env» in at most «steps» steps. The «steps» argument
  -- is solely to ensure termination of the function and is one of the
  -- drawbacks of this approach.
  interpret : ℕ -> Expr -> Env -> Result
  interpret 0 _ _ = RError
  interpret (ℕ.suc step) (Var x) vars = Env.find x vars
  interpret (ℕ.suc step) (Abs x b) vars = RFunction x b vars
  interpret (ℕ.suc step) (App f x) vars
    with interpret step x vars | interpret step f vars
  ... | xRes | RFunction var body env = interpret step body ((var , xRes) :: env)
  ... | _ | _ = RError
  interpret (ℕ.suc step) (Add a b) vars
    with interpret step a vars | interpret step b vars
  ... | RNum a' | RNum b' = RNum (a' + b')
  ... | _ | _ = RError
  interpret (ℕ.suc step) (Num n) _ = RNum n
  interpret (ℕ.suc step) T _ = RBool true
  interpret (ℕ.suc step) F _ = RBool false
  interpret (ℕ.suc step) (If cond t f) vars
    with interpret step cond vars
  ... | RBool true = interpret step t vars
  ... | RBool false = interpret step f vars
  ... | _ = RError
  interpret (ℕ.suc step) (Eq a b) vars
    with interpret step a vars | interpret step b vars
  ... | RNum a' | RNum b' = RBool (a' Nat.== b')
  ... | _ | _ = RError
  interpret (ℕ.suc step) (Pred a) vars
    with interpret step a vars
  ... | RNum 0 = RNum 0
  ... | RNum (ℕ.suc n) = RNum n
  ... | _ = RError
  interpret (ℕ.suc step) (Mul a b) vars
    with interpret step a vars | interpret step b vars
  ... | RNum a' | RNum b' = RNum (a' * b')
  ... | _ | _ = RError

  -- Note that the «steps» argument in the following tests is chosen
  -- arbitrarily, just big enough for interpretation to finish.

  test-varX : interpret 13 varX (("x" , RNum 11) :: []) ≡ RNum 11
  test-varX = refl

  test-add5 : ∀ {env} -> interpret 13 add5 env ≡ RFunction "x" add5X env
  test-add5 = refl

  test-app : interpret 13 (Let "x" (Abs "x" (Add varX (Num 5))) (App varX (Num 5))) [] ≡ RNum 10
  test-app = refl

  test-adderMaker : interpret 13 adderMaker [] ≡ RNum 15
  test-adderMaker = refl

  -- Extend the language with multiplication of numbers, finding a
  -- predecessor of a number and equality of numbers.

  -- Define the Y combinator.

  -- Use it to write the factorial function.

  factorial : Expr
  {--
    Y = λ f. (λ x. f (x x)) (λ x. f (x x))

    Thanks to `let` we have a way to define recursive functions in a natural way.
  --}
  factorial = (
    Let "Y" (Abs "f" (App (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y"))))) (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y")))))))
      (App (Var "Y") (Abs "f" (Abs "n" (If (Eq (Var "n") (Num 0)) (Num 1) (Mul (Var "n") (App (Var "f") (Pred (Var "n")))))))))

  test-factorial : interpret 130 (App factorial (Num 5)) [] ≡ RNum 120
  test-factorial = refl

module Dynamic where
  data Result : Set where
    RNum : ℕ -> Result
    RBool : Bool -> Result
    RFunction : String -> Expr -> Result
    RError : Result

  Env = List (String × Result)

  module Env where
    find : String -> Env -> Result
    find var [] = RError
    find var ((var' , val) :: rest) = if var == var' then val else find var rest

    -- «subst var val env» substitutes variable «var» with value «val» for dynamic scoping.
    subst : String -> Result -> Env -> Env
    subst var val [] = (var , val) :: []
    subst var val ((var' , val') :: rest) = if var == var' then (var , val) :: rest else (var' , val') :: subst var val rest

  interpret : ℕ -> Expr -> Env -> Result
  interpret 0 _ _ = RError
  interpret (ℕ.suc step) (Var x) vars = Env.find x vars
  interpret (ℕ.suc step) (Abs x b) vars = RFunction x b
  interpret (ℕ.suc step) (App f x) vars
    with interpret step x vars | interpret step f vars
  ... | xRes | RFunction var body = interpret step body (Env.subst var xRes vars)
  ... | _ | _ = RError
  interpret (ℕ.suc step) (Add a b) vars
    with interpret step a vars | interpret step b vars
  ... | RNum a' | RNum b' = RNum (a' + b')
  ... | _ | _ = RError
  interpret (ℕ.suc step) (Num n) _ = RNum n
  interpret (ℕ.suc step) T _ = RBool true
  interpret (ℕ.suc step) F _ = RBool false
  interpret (ℕ.suc step) (If cond t f) vars
    with interpret step cond vars
  ... | RBool true = interpret step t vars
  ... | RBool false = interpret step f vars
  ... | _ = RError
  interpret (ℕ.suc step) (Eq a b) vars
    with interpret step a vars | interpret step b vars
  ... | RNum a' | RNum b' = RBool (a' Nat.== b')
  ... | _ | _ = RError
  interpret (ℕ.suc step) (Pred a) vars
    with interpret step a vars
  ... | RNum 0 = RNum 0
  ... | RNum (ℕ.suc n) = RNum n
  ... | _ = RError
  interpret (ℕ.suc step) (Mul a b) vars
    with interpret step a vars | interpret step b vars
  ... | RNum a' | RNum b' = RNum (a' * b')
  ... | _ | _ = RError

  test-varX : interpret 13 varX (("x" , RNum 11) :: []) ≡ RNum 11
  test-varX = refl

  test-add5 : ∀ {env} -> interpret 13 add5 env ≡ RFunction "x" add5X
  test-add5 = refl

  test-adderMaker : interpret 13 adderMaker [] ≡ RNum 18
  test-adderMaker = refl

  -- /Do not/ define the Y combinator.

  -- Write the factorial function /without/ the Y combinator (or Peano
  -- numbers or similar tricks)

  factorial : Expr
  factorial =
    ((Abs "n" 
      (Let "fact"
          (Abs "n"
            (If (Eq (Var "n") (Num 0))
            (Num 1)
            (Mul (Var "n") (App (Var "fact") (Pred (Var "n"))))))
      (App (Var "fact") (Var "n")))))

  test-factorial : interpret 130 (App factorial (Num 5)) [] ≡ RNum 120
  test-factorial = refl