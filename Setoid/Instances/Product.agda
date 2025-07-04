module Setoid.Instances.Product where

open import Prelude
open import Propositions.Base
open import Propositions.Properties
open import Setoid.Base

private variable
  ℓ ℓ' ℓ'' : Level
  X Y : Type ℓ

module _ ⦃ _ : Equality X ℓ ⦄ ⦃ _ : Equality Y ℓ' ⦄ where
  infix 40 _≗×_

  _≗×_ : X × Y → X × Y → ±Prop (ℓ l⊔ ℓ')
  (x₁ , y₁) ≗× (x₂ , y₂) = (x₁ ≗ x₂) ⊓ (y₁ ≗ y₂)

  ×refl : ∀ x → x ≗× x ⁺
  ×refl x = refl (x .fst) , refl (x .snd)

  ×sym : ∀ x y → x ≗× y ⊢ y ≗× x
  ×sym x y = ⊓map (sym _ _) (sym _ _)

  ×trans : ∀ x y z → (x ≗× y) ⊠ (y ≗× z) ⊢ x ≗× z
  ×trans x y z = ⊓intro (⊢trans (⊠map ⊓outl ⊓outl) (trans (x .fst) (y .fst) _))
                        (⊢trans (⊠map ⊓outr ⊓outr) (trans (x .snd) (y .snd) _))
  
  instance
    ×Eq : Equality (X × Y) (ℓ l⊔ ℓ')
    ×Eq .Equality._≗_ = _≗×_
    ×Eq .Equality.isEquality .IsEquality.refl = ×refl
    ×Eq .Equality.isEquality .IsEquality.sym = ×sym
    ×Eq .Equality.isEquality .IsEquality.trans = ×trans
  
  module _ ⦃ _ : IsStrong X ⦄ ⦃ _ : IsStrong Y ⦄ where
    ×strongTrans : ∀ x y z → (x ≗× y) ⊓ (y ≗× z) ⊢ x ≗× z
    ×strongTrans x y z = ⊓intro (⊢trans (⊓map ⊓outl ⊓outl) (strongTrans (x .fst) (y .fst) _))
                                (⊢trans (⊓map ⊓outr ⊓outr) (strongTrans (x .snd) (y .snd) _))

    instance
      ×Strong : IsStrong (X × Y)
      ×Strong .IsStrong.strongTrans = ×strongTrans
