module type_safety where

open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality

data τ : Set where
  nat : τ
  arr : τ → τ → τ

data env : Set where
  ⊥ : env
  extend : String → τ → env → env

data _∈_ : String → env → Set where
  here : ∀ {x τ Γ} → x ∈ extend x τ Γ
  there : ∀ {x y τ Γ} → x ∈ Γ → x ∈ extend y τ Γ

variable
  Γ : env

data Term : Set where
  var : String → Term
  abs : String → Term → Term
  app : Term → Term → Term
  num : ℕ → Term

infixl 20 _⇓_
data Eenv : Set where
  ⊥ᵉ : Eenv
  eextend : String → Term → Eenv → Eenv

variable
  Σ : Eenv

data _∈ᵉ_>_ : String → Eenv → Term → Set where
  ehere : ∀ {x v Σ} → x ∈ᵉ eextend x v Σ > v
  ethere : ∀ {x y v Σ} → x ∈ᵉ Σ > v → x ∈ᵉ eextend y v Σ > v

data _⇓_ : (Term × Eenv) → (Term × Eenv) → Set where
  e_num : ∀ {n Σ} → (num n , Σ) ⇓ (num n , Σ)
  e_var : ∀ {x v Σ} → x ∈ᵉ Σ > v → (var x , Σ) ⇓ (v , Σ)
  e_abs : ∀ {x t Σ} → (abs x t , Σ) ⇓ (abs x t , Σ)
  e_app1 : ∀ {x e v Σ} → (app (abs x e) v , Σ) ⇓ (e , eextend x v Σ)
  e_app2 : ∀ {e₁ e₂ e Σ₁ Σ₂} → (e₁ , Σ₁) ⇓ (e₂ , Σ₂) → (app e₁ e , Σ₁) ⇓ (app e₂ e , Σ₂)
  e_app3 : ∀ {e₁ e₂ e Σ₁ Σ₂} → (e₁ , Σ₁) ⇓ (e₂ , Σ₂) → (app e e₁ , Σ₁) ⇓ (app e e₂ , Σ₂)


-- We will prove the first part of type safety, that is, if ⊢ e : τ and eval e = v, then v : τ.

infixl 20 _⊢_≔_

data _⊢_≔_ : env → Term → τ → Set where
  var : ∀ {x τ Γ} → x ∈ Γ → Γ ⊢ var x ≔ τ
  abs : ∀ {x e τ₁ τ₂ Γ} → extend x τ₁ Γ ⊢ e ≔ τ₂ → Γ ⊢ abs x e ≔ arr τ₁ τ₂
  app : ∀ {e₁ e₂ τ₁ τ₂ Γ} → Γ ⊢ e₁ ≔ arr τ₁ τ₂ → Γ ⊢ e₂ ≔ τ₁ → Γ ⊢ app e₁ e₂ ≔ τ₂
  num : ∀ {n Γ} → Γ ⊢ num n ≔ nat

var_x_same : ∀ {x₁ x₂ Σ} → (var x₁ , Σ) ⇓ (var x₂ , Σ) → x₁ ≡ x₂
var_x_same {x₁} {x₂} {⊥ᵉ} = {!   !}
var_x_same {x₁} {x₂} {eextend y v Σ} = {!   !}

preservation : ∀ {e₁ e₂ τ Γ Σ} → Γ ⊢ e₁ ≔ τ → (e₁ , Σ) ⇓ (e₂ , Σ) → Γ ⊢ e₂ ≔ τ
preservation {e₁ = var x} {var x₁} {τ = nat} {Γ} = λ ty h → subst (λ z → Γ ⊢ var z ≔ nat) (var_x_same h) ty
preservation {e₁ = var x} {abs x₁ e₂} {τ = nat} {Γ} {Σ} = {!   !}
preservation {e₁ = var x} {app e₂ e₃} {τ = nat} = {!   !}
preservation {e₁ = var x} {num x₁} {τ = nat} = λ _ _ → num
preservation {e₁ = var x} {var x₁} {τ = arr τ₁ τ₂} = {!   !}
preservation {e₁ = var x} {abs x₁ e₂} {τ = arr τ₁ τ₂} = {!   !}
preservation {e₁ = var x} {app e₂ e₃} {τ = arr τ₁ τ₂} = {!   !}
preservation {e₁ = var x} {num x₁} {τ = arr τ₁ τ₂} = {!   !}
preservation {e₁ = abs x e₁} {var x₁} {nat} = λ _ ()
preservation {e₁ = abs x e₁} {var x₁} {arr τ₁ τ₂} = λ _ ()
preservation {e₁ = abs x e₁} {abs x₁ e₂} {nat} = λ ()
preservation {e₁ = abs x e₁} {abs x₁ e₂} {arr τ₁ τ₂} = λ _ _ → abs (preservation (var here) e ehere {_} {_} {⊥ᵉ} var)
preservation {e₁ = abs x e₁} {app e₂ e₃} = λ _ ()
preservation {e₁ = abs x e₁} {num x₁} = λ _ ()
preservation {e₁ = app e₁ e₂} {var x} {nat} = {!   !}
preservation {e₁ = app e₁ e₂} {var x} {arr τ₁ τ₂} = {!   !}
preservation {e₁ = app e₁ e₂} {abs x e₃} {nat} = {!   !}
preservation {e₁ = app e₁ e₂} {abs x e₃} {arr τ₁ τ₂} = λ _ _ → abs (preservation (var here) e ehere {_} {_} {⊥ᵉ} var)
preservation {e₁ = app e₁ e₂} {app e₃ e₄} = {!   !}
preservation {e₁ = app e₁ e₂} {num x} = {!   !}
preservation {e₁ = num x} {var x₁} {τ = nat} = λ _ ()
preservation {e₁ = num x} {abs x₁ e₂} {τ = nat} = λ _ ()
preservation {e₁ = num x} {app e₂ e₃} {τ = nat} = λ _ ()
preservation {e₁ = num x} {num x₁} {τ = nat} = λ _ _ → num
preservation {e₁ = num x} {τ = arr τ₁ τ₂} = λ ()
  