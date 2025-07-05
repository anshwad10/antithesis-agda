-- The antithesis setoids

module Setoid.Base where

open import Prelude
open import Propositions.Base

private variable
  ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ''''' : Level
  X Y : Type ℓ

record IsEq {X : Type ℓ} (_≗_ : X → X → ±Prop ℓ') : Type (ℓ l⊔ ℓ') where
  field
    refl : ∀ x → (x ≗ x) ⁺
    sym : ∀ x y → (x ≗ y) ⊢ (y ≗ x)
    trans : ∀ x y z → (x ≗ y) ⊠ (y ≗ z) ⊢ (x ≗ z)

record Eq (X : Type ℓ) ℓ' : Type (ℓ l⊔ lsuc ℓ') where
  infix 40 _≗_

  field
    _≗_ : X → X → ±Prop ℓ'
    isEq : IsEq _≗_

  open IsEq isEq public

open Eq ⦃...⦄ public

record IsStrong (X : Type ℓ) ⦃ EqX : Eq X ℓ' ⦄ : Type (ℓ l⊔ ℓ') where
  field
    strongTrans : (x y z : X) → (x ≗ y) ⊓ (y ≗ z) ⊢ (x ≗ z)

open IsStrong ⦃...⦄ public

record Setoid ℓ ℓ' : Type (lsuc (ℓ l⊔ ℓ')) where
  no-eta-equality
  field
    Carrier : Type ℓ
    ⦃ CarrierEq ⦄ : Eq Carrier ℓ'
  
  open Eq CarrierEq public

open Setoid using () renaming (Carrier to ⟨_⟩) public

module _ (f : X → Y) ⦃ _ : Eq X ℓ ⦄ ⦃ _ : Eq Y ℓ' ⦄ where
  record IsRespectful : Type (lvlOf X l⊔ ℓ l⊔ ℓ') where
    field ≗cong : ∀ x y → x ≗ y ⊢ f x ≗ f y

  open IsRespectful ⦃...⦄ public

module _ {X : Type ℓ} ⦃ _ : Eq X ℓ' ⦄ where
  record _≡_ (x y : X) : Type ℓ' where
    constructor lift
    field lower : x ≗ y ⁺

  open _≡_
  
  ≡refl : ∀ {x} → x ≡ x
  ≡refl = lift (refl _)

  ≡sym : ∀ {x y} → x ≡ y → y ≡ x
  ≡sym (lift x≡y) = lift (sym _ _ .to x≡y)

  ≡trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  ≡trans (lift x≡y) (lift y≡z) = lift (trans _ _ _ .to (x≡y , y≡z))

  record _#_ (x y : X) : Type ℓ' where
    constructor lift
    field lower : x ≗ y ⁻
  
  open _≡_
  
  #irrefl : ∀ {x} → x # x → 𝟘
  #irrefl {x = x} (lift x#x) = (x ≗ x) .chu (lower ≡refl) x#x

  #sym : ∀ {x y} → x # y → y # x
  #sym (lift x#y) = lift (sym _ _ .fo x#y)

  #respectl : ∀ {x y z} → x ≡ y → x # z → y # z
  #respectl (lift x≡y) (lift x#z) = lift (trans _ _ _ .fo x#z .to x≡y)

  #respectr : ∀ {x y z} → x ≡ y → z # x → z # y
  #respectr (lift x≡y) (lift z#x) = lift (trans _ _ _ .fo z#x .fo (sym _ _ .to x≡y))

  module _ ⦃ _ : IsStrong X ⦄ where
    #cotrans : ∀ {x y} z → x # y → (x # z) + (z # y)
    #cotrans z (lift x#y) with strongTrans _ z _ .fo x#y
    ... | inl x#z = inl (lift x#z)
    ... | inr z#y = inr (lift z#y)

open _≡_ public
open _#_ public

module _ (f : X → Y) ⦃ _ : Eq X ℓ'' ⦄ ⦃ _ : Eq Y ℓ''' ⦄ ⦃ _ : IsRespectful f ⦄ where
  ≡cong : ∀ {x y} → x ≡ y → f x ≡ f y
  ≡cong p .lower = ≗cong _ _ .to (p .lower)

  #cong : ∀ {x y} → f x # f y → x # y
  #cong p .lower = ≗cong _ _ .fo (p .lower)