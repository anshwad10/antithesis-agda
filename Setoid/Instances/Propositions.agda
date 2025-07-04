module Setoid.Instances.Propositions where

open import Prelude
open import Propositions.Base
open import Setoid.Base

private variable
  ℓ ℓ' : Level
  P Q R : ±Prop ℓ

-- The equality on the type of antithesis propositions

infix 40 _≡Ω_

_≡Ω_ : ±Prop ℓ → ±Prop ℓ' → ±Prop (ℓ l⊔ ℓ')
P ≡Ω Q = (P ⊸ Q) ⊓ (Q ⊸ P)

-- Mostly written by auto
Ωrefl : P ≡Ω P ⁺
Ωrefl .fst .to x = x
Ωrefl .fst .fo x = x
Ωrefl .snd .to x = x
Ωrefl .snd .fo x = x

Ωsym : P ≡Ω Q ⊢ Q ≡Ω P
Ωsym .to x .fst .to = x .snd .to
Ωsym .to x .fst .fo = x .snd .fo
Ωsym .to x .snd .to = x .fst .to
Ωsym .to x .snd .fo = x .fst .fo
Ωsym .fo (inl x) = inr x
Ωsym .fo (inr x) = inl x

Ωtrans : (P ≡Ω Q) ⊠ (Q ≡Ω R) ⊢ P ≡Ω R
Ωtrans .to x .fst .to x₁ = x .snd .fst .to (x .fst .fst .to x₁)
Ωtrans .to x .fst .fo x₁ = x .fst .fst .fo (x .snd .fst .fo x₁)
Ωtrans .to x .snd .to x₁ = x .fst .snd .to (x .snd .snd .to x₁)
Ωtrans .to x .snd .fo x₁ = x .snd .snd .fo (x .fst .snd .fo x₁)
Ωtrans .fo (inl x) .to x₁ = inl (x₁ .fst .to (x .fst) , x .snd)
Ωtrans .fo (inr x) .to x₁ = inr (x .fst , x₁ .snd .fo (x .snd))
Ωtrans .fo (inl x) .fo x₁ = inl (x .fst , x₁ .fst .fo (x .snd))
Ωtrans .fo (inr x) .fo x₁ = inr (x₁ .snd .to (x .fst) , x .snd)

instance
  ±PropEq : Equality (±Prop ℓ) ℓ
  ±PropEq .Equality._≗_ = _≡Ω_
  ±PropEq .Equality.isEquality .IsEquality.refl _ = Ωrefl
  ±PropEq .Equality.isEquality .IsEquality.sym _ _ = Ωsym
  ±PropEq .Equality.isEquality .IsEquality.trans _ _ _ = Ωtrans
