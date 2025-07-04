-- The antithesis propositions
module Propositions.Base where

open import Prelude
-- open import Agda.Builtin.Equality

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

infix 30 _⊢_

-- Put it in a record so it is definitionally injective, helps with inference
record _⊢_ (P : ±Prop ℓ) (Q : ±Prop ℓ') : Type (ℓ l⊔ ℓ') where
  constructor make⊢
  field
    to : P ⁺ → Q ⁺
    fo : Q ⁻ → P ⁻

open _⊢_ public

±Lift : ±Prop ℓ → ∀ ℓ' → ±Prop (ℓ l⊔ ℓ')
±Lift P ℓ' ⁺ = Lift (P ⁺) ℓ'
±Lift P ℓ' ⁻ = Lift (P ⁻) ℓ'
±Lift P ℓ' .chu (lift p+) (lift p-) = P .chu p+ p-

infix 50 ¬_ !_ ¡_ -- ? is a special character in agda

¬_ : ±Prop ℓ → ±Prop ℓ
¬ P ⁺ = P ⁻
¬ P ⁻ = P ⁺
(¬ P) .chu p- p+ = P .chu p+ p-

⊤ : ±Prop₀
⊤ ⁺ = 𝟙
⊤ ⁻ = 𝟘

⊥ : ±Prop₀
⊥ = ¬ ⊤

infix 40 _⊓_ _⊔_ _⊠_ _⊞_ _⊸_

_⊓_ : ±Prop ℓ → ±Prop ℓ' → ±Prop (ℓ l⊔ ℓ')
P ⊓ Q ⁺ = P ⁺ × Q ⁺
P ⊓ Q ⁻ = P ⁻ + Q ⁻
(P ⊓ Q) .chu (p+ , q+) (inl p-) = P .chu p+ p-
(P ⊓ Q) .chu (p+ , q+) (inr q-) = Q .chu q+ q-

_⊔_ : ±Prop ℓ → ±Prop ℓ' → ±Prop (ℓ l⊔ ℓ')
P ⊔ Q = ¬ (¬ P ⊓ ¬ Q)

_⊸_ : ±Prop ℓ → ±Prop ℓ' → ±Prop (ℓ l⊔ ℓ')
P ⊸ Q ⁺ = P ⊢ Q
P ⊸ Q ⁻ = P ⁺ × Q ⁻
(P ⊸ Q) .chu p⊢q (p+ , q-) = P .chu p+ (p⊢q .fo q-)

_⊠_ : ±Prop ℓ → ±Prop ℓ' → ±Prop (ℓ l⊔ ℓ')
P ⊠ Q = ¬ (P ⊸ ¬ Q)

_⊞_ : ±Prop ℓ → ±Prop ℓ' → ±Prop (ℓ l⊔ ℓ')
P ⊞ Q = ¬ P ⊸ Q

infix 2 ⊓-syntax ⊔-syntax

⊓-syntax : (X : Type ℓ) → (X → ±Prop ℓ') → ±Prop (ℓ l⊔ ℓ')
⊓-syntax X P ⁺ = ∀(x : X) → P x ⁺
⊓-syntax X P ⁻ = Σ[ x ꞉ X ] P x ⁻
⊓-syntax X P .chu p+ (x , px-) = P x .chu (p+ x) px-

⊔-syntax : (X : Type ℓ) → (X → ±Prop ℓ') → ±Prop (ℓ l⊔ ℓ')
⊔-syntax X P = ¬ ⊓-syntax X λ x → ¬ P x

syntax ⊓-syntax X (λ x → P) = ⊓[ x ꞉ X ] P
syntax ⊔-syntax X (λ x → P) = ⊔[ x ꞉ X ] P

!_ : ±Prop ℓ → ±Prop ℓ
! P ⁺ = P ⁺
! P ⁻ = P ⁺ → 𝟘
(! P) .chu p+ p- = p- p+

¡_ : ±Prop ℓ → ±Prop ℓ
¡ P = ¬ ! ¬ P

private variable
  P Q R : ±Prop ℓ