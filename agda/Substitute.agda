{-# OPTIONS --allow-unsolved-metas --sized-types #-}

module Substitute where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List as List
open import Data.List using (List; []; [_]) renaming (_∷_ to _::_) -- :: For our convenience
open import Data.Nat using (ℕ; _⊔_; _+_) -- «_⊔_» for maximum
open import Data.Nat.Show using (show)
open import Data.String as String
open import Data.String using (String; _==_; _++_)

-- To avoid name conflict I renamed them.
open import Expr-2 using (Expr; Var; Abs; App; Fix; Num; Add; If0)
open import List-2 using (_∪_; _\\_; _∈ₛ_)

-- «freeVars e» returns a /set/ of free variables in «e».
freeVars : Expr -> List String
freeVars (Var x) = [ x ]
freeVars (Abs x e) = (freeVars e \\ x)
freeVars (App e e₁) = freeVars e ∪ freeVars e₁
freeVars (Fix x x₁ e) = (freeVars e \\ x) ∪ (freeVars e \\ x₁)
freeVars (Num x) = []
freeVars (Add e e₁) = freeVars e ∪ freeVars e₁
freeVars (If0 e e₁ e₂) = freeVars e ∪ freeVars e₁ ∪ freeVars e₂

index :  List String -> String -> ℕ
index [] _ = 0
index (x :: xs) y = if x == y then 0 else 1 + index xs y

lex : Expr -> Expr
lex x = lexHelper x []
  where
  lexHelper : Expr → List String → Expr
  lexHelper (Var x) l = Var (Data.Nat.Show.show (index l x))
  lexHelper (Abs x e) l = Abs (Data.Nat.Show.show (List.length l)) (lexHelper e (x :: l))
  lexHelper (App e e₁) l = App (lexHelper e l) (lexHelper e₁ l)
  lexHelper (Fix x x₁ e) l = Fix (Data.Nat.Show.show (List.length l)) (Data.Nat.Show.show (List.length l + 1)) (lexHelper e (x :: x₁ :: l))
  lexHelper (Num x) l = Num x
  lexHelper (Add e e₁) l = Add (lexHelper e l) (lexHelper e₁ l)
  lexHelper (If0 e e₁ e₂) l = If0 (lexHelper e l) (lexHelper e₁ l) (lexHelper e₂ l)

-- «fresh conflicts» returns a new variable name, different from all
-- names in «conflicts».
--
-- The best implementation is going to be used in the reference
-- solutions.
fresh : List String -> String
fresh = λ l -> Data.Nat.Show.show (List.length l)

module Unsafe where
  -- «rename what for wher» renames all free variables named «what» in
  -- expression «wher» to be named «for».
  {-# TERMINATING #-}
  rename : String -> String -> Expr -> Expr
  rename what for (Var x) = Var (if what == x then for else x)
  rename what for (Abs x body) =
    if what == x then Abs x body
    else if for == x then Abs x' (rename what for (rename x x' body))
    else Abs x' (rename what for body)
   where
    conflicts = freeVars body
    x' = fresh conflicts
  rename what for (App f x) =
    App (rename what for f) (rename what for x)
  rename what for (Fix f x body)
    with what == f | what == x
  ... | true | _ = Fix f x body
  ... | _ | true = Fix f x body
  ... | false | false = Fix f' x' (rename what for body')
   where
     conflicts = freeVars body
     f' = fresh conflicts
     x' = fresh (conflicts ∪ [ f' ])
     body' = rename x x' (rename f f' body)
  rename what for (Num n) = Num n
  rename what for (Add a b) =
    Add (rename what for a) (rename what for b)
  rename what for (If0 c t f) =
    If0 (rename what for c) (rename what for t) (rename what for f)

  -- «subst what for wher» performs a typical λ-calculus substitution
  -- of variable «what» for expression «for» in expression «wher».
  {-# TERMINATING #-}
  subst : String -> Expr -> Expr -> Expr
  subst what for (Var x) = if what == x then for else Var x
  subst what for (Abs x body) =
    if what == x then Abs x body
    else Abs x' (subst what for (rename x x' body))
   where
    conflicts = [ what ] ∪ freeVars for ∪ freeVars (Abs x body)
    x' = fresh conflicts
  subst what for (App f x) = App (subst what for f) (subst what for x)
  subst what for (Fix f x body)
    with what == f | what == x
  ... | true | _ = Fix f x body
  ... | _ | true = Fix f x body
  ... | false | false = Fix f' x' (subst what for body')
   where
    conflicts = [ what ] ∪ freeVars for ∪ freeVars (Fix f x body)
    f' = fresh conflicts
    x' = fresh (conflicts ∪ [ f' ])
    body' = rename x x' (rename f f' body)
  subst what for (Num n) = Num n
  subst what for (Add a b) = Add (subst what for a) (subst what for b)
  subst what for (If0 c t f) =
    If0 (subst what for c) (subst what for t) (subst what for f)

-- Provides the same functions as «Unsafe» but with termination being
-- proven using the well-founded recursion.
--
-- This one is the most complicated of all. If you have difficulties,
-- abandon it and do other tasks first.
module WF where
  open import Data.Nat.Induction using (Acc; acc; <′-wellFounded)
  open import Data.Nat using (_<′_; ≤′-refl)
  open import Data.Nat.Properties using (s≤′s; m≤′m+n; n≤′m+n; ≤′-trans)
  open import Relation.Nullary using (yes; no)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; cong)
    renaming (subst to subst')

  metric : Expr -> ℕ
  metric (Var s) = 0
  metric (Abs s body) = ℕ.suc (metric body)
  metric (App f x) = ℕ.suc (metric f + metric x)
  metric (Fix f x body) = ℕ.suc (metric body)
  metric (Num n) = 0
  metric (Add a b) = ℕ.suc (metric a + metric b)
  metric (If0 c t f) = ℕ.suc (metric c + metric t + metric f)

  m<′suc-m+n : ∀ {m n} -> m <′ ℕ.suc (m + n)
  m<′suc-m+n = {!!}

  n<′suc-m+n : ∀ {m n} -> n <′ ℕ.suc (m + n)
  n<′suc-m+n = {!!}

  m<′suc-m+n+l : ∀ {m n l} -> m <′ ℕ.suc (m + n + l)
  m<′suc-m+n+l = {!!}

  n<′suc-m+n+l : ∀ {m n l} -> n <′ ℕ.suc (m + n + l)
  n<′suc-m+n+l = {!!}

  l<′suc-m+n+l : ∀ {m n l} -> l <′ ℕ.suc (m + n + l)
  l<′suc-m+n+l = {!!}

  renameAux : String -> String -> (e : Expr) -> Acc _<′_ (metric e) -> Expr
  rename-preserves-metric : ∀ (e) {what for} {rec}
    -> metric e ≡ metric (renameAux what for e rec)

  renameAux = {!!}
  rename-preserves-metric = {!!}

  rename : String -> String -> Expr -> Expr
  rename = {!!}

  substAux : String -> Expr -> (e : Expr) -> Acc _<′_ (metric e) -> Expr
  substAux = {!!}

  subst : String -> Expr -> Expr -> Expr
  subst = {!!}

-- Provides the same functions as «Unsafe» but with termination being
-- proven using sized types.
module Sized where
  open import Size using (Size; ↑_)

  data SExpr : {Size} -> Set where

  unsize : SExpr -> Expr
  unsize = {!!}

  sized : Expr -> SExpr
  sized = {!!}

  rename : String -> String -> Expr -> Expr
  rename = {!!}

  subst : String -> Expr -> Expr -> Expr
  subst = {!!}
 