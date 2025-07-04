module Setoid.Instances.Nat where

open import Prelude
open import Propositions.Base
open import Propositions.Properties
open import Setoid.Base
open import Agda.Builtin.Nat renaming (Nat to ℕ)

private variable
  ℓ ℓ' : Level

infix 40 _≗ℕ_

_≗ℕ_ : ℕ → ℕ → ±Prop₀
zero ≗ℕ zero = ⊤
zero ≗ℕ suc n = ⊥
suc m ≗ℕ zero = ⊥
suc m ≗ℕ suc n = m ≗ℕ n

ℕrefl : ∀ n → n ≗ℕ n ⁺
ℕrefl zero = tt
ℕrefl (suc n) = ℕrefl n

ℕsym : ∀ m n → m ≗ℕ n ⊢ n ≗ℕ m
ℕsym zero zero = ⊢refl
ℕsym zero (suc n) = ⊢refl
ℕsym (suc m) zero = ⊢refl
ℕsym (suc m) (suc n) = ℕsym m n

ℕstrongtrans : ∀ m n o → (m ≗ℕ n) ⊓ (n ≗ℕ o) ⊢ m ≗ℕ o
ℕstrongtrans zero zero o = ⊓outr
ℕstrongtrans zero (suc n) o = ⊢trans ⊓outl ⊥initial
ℕstrongtrans (suc m) zero o = ⊢trans ⊓outl ⊥initial
ℕstrongtrans (suc m) (suc n) zero = ⊓outr
ℕstrongtrans (suc m) (suc n) (suc o) = ℕstrongtrans m n o

ℕtrans : ∀ m n o → (m ≗ℕ n) ⊠ (n ≗ℕ o) ⊢ m ≗ℕ o
ℕtrans m n o = ⊢trans ⊠weaken⊓ (ℕstrongtrans m n o)

instance
  Eqℕ : Equality ℕ lzero
  Eqℕ .Equality._≗_ = _≗ℕ_
  Eqℕ .Equality.isEquality .IsEquality.refl = ℕrefl
  Eqℕ .Equality.isEquality .IsEquality.sym = ℕsym
  Eqℕ .Equality.isEquality .IsEquality.trans = ℕtrans

  Strongℕ : IsStrong ℕ
  Strongℕ .IsStrong.strongTrans = ℕstrongtrans
