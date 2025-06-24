module Prelude where

open import Agda.Primitive public renaming (Set to Type; Setω to Typeω; _⊔_ to _ℓ⊔_)
open import Agda.Builtin.Unit public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Nat public

private variable
  ℓ ℓ' ℓ'' : Level
  P Q R : Type ℓ

-- intuitionistic logical operators
record Lift (X : Type ℓ) ℓ' : Type (ℓ ℓ⊔ ℓ') where
  constructor lift
  field lower : X

data ⊥ : Type where

⊥* : ∀ ℓ → Type ℓ
⊥* = Lift ⊥

⊤* : ∀ ℓ → Type ℓ
⊤* = Lift ⊤

_∧_ : Type ℓ → Type ℓ' → Type (ℓ ℓ⊔ ℓ')
P ∧ Q = Σ P λ _ → Q

data _∨_ (P : Type ℓ) (Q : Type ℓ') : Type (ℓ ℓ⊔ ℓ') where
  inl : P → P ∨ Q
  inr : Q → P ∨ Q

