module typing where

open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)

data τ : Set where
  nat : τ
  arr : τ → τ → τ

data Term : Set where
  var : String → Term
  abs : String → Term → Term
  app : Term → Term → Term
  -- This is fix f x . e
  fixp : String → String → Term → Term
  num : ℕ → Term
  _⊕_ : Term → Term → Term
  ifelse : Term → Term → Term → Term
  
data Value : Set where
  vnum : ℕ → Value
  vabs : String → Term → Value
  vfix : Term → Term → Term → Value
  verror : Value

data env : Set where
  ⊥ : env
  extend : String → τ → env → env

data _∈_ : String → env → Set where
  here : ∀ {x τ Γ} → x ∈ extend x τ Γ
  there : ∀ {x y τ Γ} → x ∈ Γ → x ∈ extend y τ Γ

variable
  Γ : env

infixl 20 _⊢_::_
data _⊢_::_ : env → Term → τ → Set where
  tvar : ∀ {x τ} → x ∈ Γ → Γ ⊢ var x :: τ
  tnat : ∀ {n} → Γ ⊢ num n :: nat
  tbin : ∀ {t₁ t₂} → Γ ⊢ t₁ :: nat → Γ ⊢ t₂ :: nat → Γ ⊢ t₁ ⊕ t₂ :: nat
  tabs : ∀ {x t τ₁ τ₂} → extend x τ₁ Γ ⊢ t :: τ₂ → Γ ⊢ abs x t :: arr τ₁ τ₂
  tifelse : ∀ {t₁ t₂ t₃ τ} →
              Γ ⊢ t₁ :: nat →
              Γ ⊢ t₂ :: τ →
              Γ ⊢ t₃ :: τ →
              -------------------
              Γ ⊢ ifelse t₁ t₂ t₃ :: τ
  tapp : ∀ {t₁ t₂ τ₁ τ₂} →
          Γ ⊢ t₁ :: arr τ₁ τ₂ →
          Γ ⊢ t₂ :: τ₁ →
          -------------------
          Γ ⊢ app t₁ t₂ :: τ₂
  tfix : ∀ {f x e τ₁ τ₂} →
          extend f (arr τ₁ τ₂) (extend x τ₁ Γ) ⊢ e :: τ₂ →
          -------------------
          Γ ⊢ fixp f x e :: arr τ₁ τ₂

sample_expr : Term
sample_expr = fixp "f" "x" (ifelse (var "x") (num 0) (app (var "f") (var "x")))

expr_type : Γ ⊢ sample_expr :: arr nat nat
expr_type = tfix (tifelse (tvar (there here)) tnat
            (tapp {_} {_} {_} {nat} {_} (tvar here) (tvar (there here))))

-- Next, we are trying to prove type safety.
-- Basically, type safety is a property that says that well-typed terms do not get stuck.
-- This means:
-- 1. If ⊢ e : τ and eval e = v, then v : τ.
-- 2. If ⊢ e : τ and eval e = v, then v is a Value or there exists e' such that e → e'.

-- We will prove this by induction on the typing relation.

infixl 20 _->*_
data eenv : Set where
  ⊥ᵉ : eenv
  eextend : String → Value → eenv → eenv
variable
  Σ : eenv

data _∈ᵉ_>_ : String → eenv → Value → Set where
  ehere : ∀ {x v Σ} → x ∈ᵉ eextend x v Σ > v
  ethere : ∀ {x y v Σ} → x ∈ᵉ Σ > v → x ∈ᵉ eextend y v Σ > v

data _->*_ : Term → Value → Set where
  e_num : ∀ {n} → num n ->* vnum n
  e_var : ∀ {x v} → x ∈ᵉ Σ > v → var x ->* v
  e_abs : ∀ {x t} → abs x t ->* vabs x t