{-# OPTIONS --allow-unsolved-metas #-}

module Expr-2 where

open import Data.Nat using (ℕ)
open import Data.String using (String)

data Expr : Set where
  Var : String -> Expr
  Abs : String -> Expr -> Expr
  App : Expr -> Expr -> Expr
  Fix : String -> String -> Expr -> Expr
  Num : ℕ -> Expr
  Add : Expr -> Expr -> Expr
  If0 : Expr -> Expr -> Expr -> Expr

-- This can be any expression.
factorial : Expr
factorial = Var "x"
