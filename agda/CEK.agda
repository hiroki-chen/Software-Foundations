module CEK where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.String using (String; _≟_; length; _++_)
open import Data.List using (List; []) renaming (_∷_ to _::_)
open import Data.Product using (Σ-syntax; _×_; _,_; Σ)
open import Relation.Nullary.Decidable using (False)

-- In this module you will implement the CEK machine. Read chapter 6.4
-- in the «Semantics Engineering with PLT Redex» textbook.

-- CEK machine semantics

------------------------------------------------------------------------------
-- Syntax

data Expr : Set where
  Var : String → Expr
  Num : ℕ → Expr
  Str : String → Expr
  Add : Expr → Expr → Expr
  Mul : Expr → Expr → Expr
  Cat : Expr → Expr → Expr
  Len : Expr → Expr
  Let : String → Expr → Expr → Expr

variable
  m n : ℕ
  s s' t x y : String
  e e₁ e₂ : Expr

-- Examples

exp₀ exp₁ exp₂ exp₃ exp₄ exp₅ : Expr
exp₀ = Add (Num 5) (Num 2)
exp₁ = Add (Num 3) (Mul (Num 4) (Num 5))
exp₂ = Add (Len (Cat (Str "abc") (Str "de"))) (Num 3)
exp₃ = Let "x" (Num 3) (Add (Var "x") (Var "x"))
exp₄ = Let "x" (Num 3) (Let "y" (Num 4) (Add (Var "x") (Var "y")))
exp₅ = Let "y" (Num 1) (Let "x" (Let "y" (Num 2) (Var "y")) (Var "y"))

------------------------------------------------------------------------------
-- Runtime values

data isVal : Expr → Set where
  VNum : isVal (Num n)
  VStr : isVal (Str s)

-- «Val» is an «Expr» that also «isVal».
record Val : Set where
  constructor _,_
  field
    expr : Expr
    isVal-proof : isVal expr

-- There are alternative ways to define «Val», using the «builtin»
-- Sigma-types, for example:
-- Val = Σ Expr isVal
-- Val = Σ[ e ∈ Expr ] isVal e

variable
  v v' : Val

vnum : ℕ → Val
vnum n = Num n , VNum

vstr : String → Val
vstr s = Str s , VStr

-- Environments

data Env : Set where
  □   : Env -- «\sqw»
  _,_ : (String × Val) → Env → Env

variable
  ρ : Env

data _∈ᵣ_ : (String × Val) → Env → Set where
  hereᵣ : (s , v) ∈ᵣ ((s , v) , ρ)
  skipᵣ : {α : False (s ≟ s')} → (s , v) ∈ᵣ ρ → (s , v) ∈ᵣ ((s' , v') , ρ)

-- Closures

Closure : Set
Closure = Expr × Env

-- Stack frames

-- These frames help implement the «[cek2]», «[cek5]» and «[cek6]»
-- rules from the textbook.
data Frame : Set where
  AddLK : Closure → Frame
  AddRK : Val → Frame

-- Right now, only a subset of frames is implemented. Your goal is to
-- implement the rest of the frames _and_ transitions (shown
-- below).

  MulLK : Closure → Frame
  MulRK : Val → Frame

  LetLK : (String × Expr × Env) → Frame
  CatLK : Closure → Frame
  CatRK : Val → Frame

  LenK  : Frame
--
-- If you implement all the necessary frames, you will be able to
-- construct the proofs required for the holes at the bottom of this
-- file.

-- Continuations

Cont : Set
Cont = List Frame

variable
  κ : Cont -- «\kappa»

-- CEK machine states

data State : Set where
  Enter  : Closure → Cont → State
  Return : Cont → Val → State

variable
  σ σ' σ₁ σ₂ σ₃ : State

-- CEK machine transitions

-- «\mapsto» for «↦».
data _↦_ : State → State → Set where
  Var0   :
    ((x , v) ∈ᵣ ρ) → (Enter (Var x , ρ) κ) ↦ (Return κ v)
  Let0   :
    (Enter (Let x e₁ e₂ , ρ) κ) ↦ (Enter (e₁ , ρ) (LetLK (x , e₂ , ρ) :: κ))
  Let1   :
    (Return (LetLK (x , e₂ , ρ) :: κ) v) ↦ (Enter (e₂ , (x , v) , ρ) κ)
  Num0   :
    (Enter (Num n , ρ) κ) ↦ (Return κ (vnum n))
  Str0   :
    (Enter (Str s , ρ) κ) ↦ (Return κ (vstr s))
  Add0  :
    (Enter (Add e₁ e₂ , ρ) κ) ↦ (Enter (e₁ , ρ) (AddLK (e₂ , ρ) :: κ))
  Add1  :
    (Return (AddLK (e₂ , ρ) :: κ) v) ↦ (Enter (e₂ , ρ) (AddRK v :: κ))
  Add2  :
    (Return (AddRK (Num m , VNum) :: κ) (Num n , VNum)) ↦
         (Return κ (vnum (m + n)))
  Mul0  :
    (Enter (Mul e₁ e₂ , ρ) κ) ↦ (Enter (e₁ , ρ) (MulLK (e₂ , ρ) :: κ))
  Mul1  :
    (Return (MulLK (e₂ , ρ) :: κ) v) ↦ (Enter (e₂ , ρ) (MulRK v :: κ))
  Mul2  :
    (Return (MulRK (Num m , VNum) :: κ) (Num n , VNum)) ↦
         (Return κ (vnum (m * n)))
  Cat0  :
    (Enter (Cat e₁ e₂ , ρ) κ) ↦ (Enter (e₁ , ρ) (CatLK (e₂ , ρ) :: κ))
  Cat1  :
    (Return (CatLK (e₂ , ρ) :: κ) v) ↦ (Enter (e₂ , ρ) (CatRK v :: κ))
  Cat2  :
    (Return (CatRK (Str s , VStr) :: κ) (Str t , VStr)) ↦
         (Return κ (vstr (s ++ t)))
  Len0  :
    (Enter (Len e , ρ) κ) ↦ (Enter (e , ρ) (LenK :: κ))
  Len1  :
    (Return (LenK :: κ) (Str s , VStr)) ↦ (Return κ (vnum (length s)))

-- Trace of evaluation

infixr 10 _•_

data _↦*_ : State → State → Set where
  ∎   : σ ↦* σ -- «\qed»
  _•_ : σ₁ ↦ σ₂ → σ₂ ↦* σ₃ → σ₁ ↦* σ₃ -- «\bub»

-- Evaluation using CEK transitions

-- «Eval e v» states that the expression «e» evaluates to value «v».
Eval : Expr → Val → Set
Eval e v = (Enter (e , □) []) ↦* (Return [] v)

-- 1. Add necessary constructors to «Frame»
-- 2. Add necessary constructors to «↦»
-- 3. Complete the proofs below.

-- e₀ = Add (Num 5) (Num 2)
tr₀ : Eval exp₀ (vnum 7)
tr₀ = Add0 • Num0 • Add1 • Num0 • Add2 • ∎

-- e₁ = Add (Num 3) (Mul (Num 4) (Num 5))
tr₁ : Eval exp₁ (vnum 23)
tr₁ = Add0 • Num0 • Add1 • Mul0 • Num0 • Mul1 • Num0 • Mul2 • Add2 • ∎

-- e₂ = Add (Len (Cat (Str "abc") (Str "de"))) (Num 3)
tr₂ : Eval exp₂ (vnum 8)
tr₂ =  Add0 • Len0 • Cat0 • Str0 • Cat1 • Str0 • Cat2 • Len1 • Add1 • Num0 • Add2 • ∎

-- e₃ = Let "x" (Num 3) (Add (Var "x") (Var "x"))
tr₃ : Eval exp₃ (vnum 6)
tr₃ = Let0 • Num0 • Let1 • Add0 • Var0 (hereᵣ) • Add1 • Var0 (hereᵣ) • Add2 • ∎

-- e₄ = Let "x" (Num 3) (Let "y" (Num 4) (Add (Var "x") (Var "y")))
tr₄ : Eval exp₄ (vnum 7)
tr₄ = Let0 • Num0 • Let1 • Let0 • Num0 • Let1 • Add0 • Var0 (skipᵣ hereᵣ) • Add1 • Var0 (hereᵣ) • Add2 • ∎

-- e₅ = Let "y" (Num 1) (Let "x" (Let "y" (Num 2) (Var "y")) (Var "y"))
tr₅ : Eval exp₅ (vnum 1)
tr₅ = Let0 • Num0 • Let1 • Let0 • Let0 • Num0 • Let1 • Var0 (hereᵣ) • Let1 • Var0 (skipᵣ hereᵣ) • ∎


------------------------------------------------------------------------------
 