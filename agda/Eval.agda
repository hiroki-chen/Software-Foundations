{-# OPTIONS --allow-unsolved-metas #-}

module Eval where

open import Data.List using (List) renaming (_∷_ to _::_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)

import Substitute
open import Expr-2 using (Expr; Var; Abs; App; Fix; Num; Add; If0)
open import List-2 using (_∈_)

data Typ : Set where
  num : Typ
  fun : Typ -> Typ -> Typ

infixr 30 _~>_
_~>_ = fun

Context = List (String × Typ)

variable
  x : String
  σ τ : Typ -- «\sigma», «\tau»

-- «Γ ⊢ e : σ» should state that expression «e» has type «σ» in
-- context «Γ».

-- Complete the typing relation.
data _⊢_::_ (Γ : Context) : Expr -> Typ -> Set where -- «\vdash» for «⊢»
  VarT : (x , σ) ∈ Γ ->
    --------------------------------------------------
    Γ ⊢ Var x :: σ

Env = List (String × Expr)

variable Γ : Context; env : Env

-- «Redux» is a relation stating direct/semantic transitions within
-- terms, e.g. the rule for β-redexes. In the «PLT-redex» textbook
-- it's called «single-step reduction» (chapter 1.2).

-- Complete it to contain all appropriate single-step reductions in
-- «Expr»
open Substitute.Unsafe using (subst)
data Redux (env : Env) : Expr -> Expr -> Set where
  Var : ∀ {x e} -> ((x , e) ∈ env) -> Redux env (Var x) e

variable e e' e₁ e₂ : Expr

-- «env ⊢ e ⟶ e'» is a /compatible closure/ of «Redux» (chapter 1.5).

-- Complete the closure.
data _⊢_⟶_ (env : Env) : Expr -> Expr -> Set where
  Direct : (Redux env e₁ e₂) -> env ⊢ e₁ ⟶ e₂

-- Note that, unlike in previous exercises, successful compilation of
-- this file doesn't necessitate the correctness of your work. Be
-- extra careful.
