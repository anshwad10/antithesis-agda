module Setoid.Instances.Functions where

open import Prelude
open import Propositions.Base
open import Propositions.Properties
open import Setoid.Base

private variable
  ℓ ℓ' ℓ'' : Level
  X Y : Type ℓ

module _ {X : Type ℓ} ⦃ _ : Equality Y ℓ' ⦄ where
  infixr 40 _≗f_
  
  _≗f_ : (X → Y) → (X → Y) → ±Prop (ℓ l⊔ ℓ')
  f ≗f g = ⊓[ x ꞉ _ ] f x ≗ g x

  frefl : ∀ f → f ≗f f ⁺
  frefl f x = refl (f x)

  