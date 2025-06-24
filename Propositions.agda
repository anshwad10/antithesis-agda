-- The antithesis propositions
module Propositions where

open import Prelude

private variable
  ℓ ℓ' : Level

record ±Prop ℓ : Type (lsuc ℓ) where
  constructor el±
  infix 30 _⁺ _⁻
  field
    _⁺ _⁻ : Type ℓ
    chu : (p+ : _⁺) → (p- : _⁻) → 𝟘

±Prop₀ = ±Prop lzero

open ±Prop public

±Lift : ±Prop ℓ → ∀ ℓ' → ±Prop (ℓ l⊔ ℓ')
±Lift P ℓ' ⁺ = Lift (P ⁺) ℓ'
±Lift P ℓ' ⁻ = Lift (P ⁻) ℓ'
±Lift P ℓ' .chu (lift p+) (lift p-) = P .chu p+ p-

infix 50 ¬_ !_ ¡_ -- ? is a special character in agda

¬_ : ±Prop ℓ → ±Prop ℓ
¬ P ⁺ = P ⁻
¬ P ⁻ = P ⁺
(¬ P) .chu p- p+ = P .chu p+ p-

!_ : ±Prop ℓ → ±Prop ℓ
! P ⁺ = P ⁺
! P ⁻ = P ⁺ → 𝟘
(! P) .chu p+ p- = p- p+

¡_ : ±Prop ℓ → ±Prop ℓ
¡ P = ¬ ! ¬ P

⊤ : ±Prop₀
⊤ ⁺ = 𝟙
⊤ ⁻ = 𝟘

⊥ : ±Prop₀
⊥ = ¬ ⊤

infix 40 _⊓_ _⊔_ _⊠_ _⊞_ _⊸_

_⊓_ : ±Prop ℓ → ±Prop ℓ' → ±Prop (ℓ l⊔ ℓ')
P ⊓ Q ⁺ = P ⁺ ∧ Q ⁺
P ⊓ Q ⁻ = P ⁻ ∨ Q ⁻
(P ⊓ Q) .chu (p+ , q+) (inl p-) = P .chu p+ p-
(P ⊓ Q) .chu (p+ , q+) (inr q-) = Q .chu q+ q-

_⊔_ : ±Prop ℓ → ±Prop ℓ' → ±Prop (ℓ l⊔ ℓ')
P ⊔ Q = ¬ (¬ P ⊓ ¬ Q)

_⊠_ : ±Prop ℓ → ±Prop ℓ' → ±Prop (ℓ l⊔ ℓ')
P ⊠ Q ⁺ = P ⁺ ∧ Q ⁺
P ⊠ Q ⁻ = (P ⁺ → Q ⁻) ∧ (Q ⁺ → P ⁻)
(P ⊠ Q) .chu (p+ , q+) (q- , p-) = P .chu p+ (p- q+)

_⊞_ : ±Prop ℓ → ±Prop ℓ' → ±Prop (ℓ l⊔ ℓ')
P ⊞ Q = ¬ (¬ P ⊠ ¬ Q)

_⊸_ : ±Prop ℓ → ±Prop ℓ' → ±Prop (ℓ l⊔ ℓ')
P ⊸ Q = ¬ (P ⊠ ¬ Q)

_⊢_ : ±Prop ℓ → ±Prop ℓ' → Type (ℓ l⊔ ℓ')
P ⊢ Q = P ⊸ Q ⁺
