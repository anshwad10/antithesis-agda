module Poset.Base where

open import Prelude
open import Propositions.Base
open import Setoid.Base
open import Propositions.Properties

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  X Y : Type ℓ

record IsPreord {X : Type ℓ} (_⊑_ : X → X → ±Prop ℓ') : Type (ℓ l⊔ ℓ') where
  field
    ⊑refl : ∀ x → (x ⊑ x) ⁺
    ⊑trans : ∀ x y z → (x ⊑ y) ⊠ (y ⊑ z) ⊢ (x ⊑ z)

record Preord (X : Type ℓ) ℓ' : Type (ℓ l⊔ lsuc ℓ') where
  infix 40 _⊑_ _⊏_

  field
    _⊑_ : X → X → ±Prop ℓ'
    isPreord : IsPreord _⊑_
  
  _⊏_ : X → X → ±Prop ℓ'
  x ⊏ y = ¬ (y ⊑ x)

  open IsPreord isPreord public

open Preord ⦃...⦄

record OrdIsStrong (X : Type ℓ) ⦃ PreordX : Preord X ℓ' ⦄ : Type (ℓ l⊔ ℓ') where
  field
    ⊑strongTrans : (x y z : X) → (x ⊑ y) ⊓ (y ⊑ z) ⊢ (x ⊑ z)

open OrdIsStrong ⦃...⦄

record IsOrd (X : Type ℓ) ⦃ EqX : Eq X ℓ' ⦄ ⦃ PreordX : Preord X ℓ'' ⦄ : Type (ℓ l⊔ ℓ' l⊔ ℓ'') where
  field
    ⊑antisym : (x y : X) → (x ⊑ y) ⊓ (y ⊑ x) ⊢ (x ≗ y)

record Ord (X : Type ℓ) ℓ' ℓ'' : Type (ℓ l⊔ lsuc ℓ' l⊔ lsuc ℓ'') where
  field
    overlap ⦃ EqX ⦄ : Eq X ℓ'
    overlap ⦃ PreordX ⦄ : Preord X ℓ''
    overlap ⦃ isOrd ⦄ : IsOrd X

-- Any preorder has a canonical equality that makes it a partial order

module _ {X : Type ℓ} ⦃ OrdX : Preord X ℓ' ⦄ where

  PreordEq : Eq X ℓ'
  PreordEq .Eq._≗_ x y = (x ⊑ y) ⊓ (y ⊑ x)
  PreordEq .Eq.isEq .IsEq.refl x = ⊑refl x , ⊑refl x
  PreordEq .Eq.isEq .IsEq.sym x y = ⊓comm
  PreordEq .Eq.isEq .IsEq.trans x y z = ⊓intro (⊢trans (⊠map ⊓outl ⊓outl) (⊑trans x y z))
                                               (⊢trans (⊠map ⊓outr ⊓outr) (⊢trans ⊠comm (⊑trans z y x)))
  
  PreordEqMakesOrd : IsOrd X ⦃ EqX = PreordEq ⦄
  PreordEqMakesOrd .IsOrd.⊑antisym x y = ⊢refl
