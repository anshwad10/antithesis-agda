module Prelude where

open import Agda.Primitive public renaming (Set to Type; Setω to Typeω; _⊔_ to _l⊔_)
open import Agda.Builtin.Unit public renaming (⊤ to 𝟙)
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Nat public

private variable
  ℓ ℓ' ℓ'' : Level
  P Q R : Type ℓ

-- intuitionistic logical operators
record Lift (X : Type ℓ) ℓ' : Type (ℓ l⊔ ℓ') where
  constructor lift
  field lower : X

open Lift public

data 𝟘 : Type where

𝟘* : ∀ ℓ → Type ℓ
𝟘* = Lift 𝟘

𝟙* : ∀ ℓ → Type ℓ
𝟙* = Lift 𝟙

_∧_ : Type ℓ → Type ℓ' → Type (ℓ l⊔ ℓ')
P ∧ Q = Σ P λ _ → Q

data _∨_ (P : Type ℓ) (Q : Type ℓ') : Type (ℓ l⊔ ℓ') where
  inl : P → P ∨ Q
  inr : Q → P ∨ Q

infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ l⊔ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B