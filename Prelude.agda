module Prelude where

open import Agda.Primitive public renaming (Set to Type; Setω to Typeω; _⊔_ to _l⊔_)
open import Agda.Builtin.Unit public renaming (⊤ to 𝟙)
open import Agda.Builtin.Sigma public

private variable
  ℓ ℓ' ℓ'' : Level
  X Y Z W : Type ℓ

lvlOf : Type ℓ → Level
lvlOf {ℓ = ℓ} _ = ℓ

-- intuitionistic logical operators
record Lift (X : Type ℓ) ℓ' : Type (ℓ l⊔ ℓ') where
  constructor lift
  field lower : X

open Lift public

data 𝟘 : Type where

-- -- Make it definitionally irrelevant
-- record 𝟘 : Type where
--   constructor 𝟘→𝟘'
--   field .𝟘'→𝟘 : 𝟘'

absurd : {X : Type ℓ} → 𝟘 → X
absurd ()

𝟘* : ∀ ℓ → Type ℓ
𝟘* = Lift 𝟘

absurd* : {X : Type ℓ'} → 𝟘* ℓ → X
absurd* ()

𝟙* : ∀ ℓ → Type ℓ
𝟙* = Lift 𝟙

tt* : 𝟙* ℓ
tt* = lift tt

_×_ : Type ℓ → Type ℓ' → Type (ℓ l⊔ ℓ')
P × Q = Σ P λ _ → Q

data _+_ (P : Type ℓ) (Q : Type ℓ') : Type (ℓ l⊔ ℓ') where
  inl : P → P + Q
  inr : Q → P + Q

infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ l⊔ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ꞉ A ] B -- \:4 in emacs

assert-type : (X : Type ℓ) → X → X
assert-type X x = x

syntax assert-type X x = x ꞉ X -- \:4 in emacs

case_of_ : X → (X → Y) → Y
case x of f = f x

infixr 0 _$_

_$_ : (X → Y) → (X → Y)
f $ x = f x