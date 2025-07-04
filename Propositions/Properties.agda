{-# OPTIONS --hidden-argument-puns #-}

module Propositions.Properties where

open import Prelude
open import Propositions.Base
open import Setoid.Base
open import Setoid.Instances.Propositions

private variable
  ℓ ℓ' : Level
  P Q R S : ±Prop ℓ

-- I prove all the properties of ±Prop
-- Most of the following code was written by auto

⊢refl : P ⊢ P
⊢refl .to x = x
⊢refl .fo x = x

⊢trans : P ⊢ Q → Q ⊢ R → P ⊢ R
⊢trans p⊢q q⊢r .to x = q⊢r .to (p⊢q .to x)
⊢trans p⊢q q⊢r .fo x = p⊢q .fo (q⊢r .fo x)

⊢antisym : P ⊢ Q → Q ⊢ P → P ≡ Q
⊢antisym p⊢q q⊢r .lower = p⊢q , q⊢r

⊢refl' : P ≡ Q → P ⊢ Q
⊢refl' p≡q = p≡q .lower .fst

-- Equational reasoning for ⊢
infixr 30 _⊢∎ _⊢⟨_⟩_

_⊢∎ : (P : ±Prop ℓ) → P ⊢ P
_ ⊢∎ = ⊢refl

_⊢⟨_⟩_ : (P : ±Prop ℓ) → P ⊢ Q → Q ⊢ R → P ⊢ R
_ ⊢⟨ p⊢q ⟩ q⊢r = ⊢trans p⊢q q⊢r

-- ¬ is an antitone involution

contrapose : ¬ Q ⊢ ¬ P → P ⊢ Q
contrapose x .to = x .fo
contrapose x .fo = x .to

_⊣⟨_⟩_ : (P : ±Prop ℓ) → ¬ Q ⊢ ¬ P → Q ⊢ R → P ⊢ R
_ ⊣⟨ ¬q⊢¬p ⟩ q⊢r = _ ⊢⟨ contrapose ¬q⊢¬p ⟩ q⊢r

¬invol : ¬ ¬ P ≡ P -- This is definitional due to eta-equality
¬invol = ≡refl

-- ±Prop is a bounded lattice

⊤terminal : P ⊢ ⊤
⊤terminal .to _ = tt
⊤terminal .fo ()

⊓outl : P ⊓ Q ⊢ P
⊓outl .to = fst
⊓outl .fo = inl

⊓outr : P ⊓ Q ⊢ Q
⊓outr .to = snd
⊓outr .fo = inr

⊓intro : R ⊢ P → R ⊢ Q → R ⊢ P ⊓ Q
⊓intro r⊢p r⊢q .to r+ = r⊢p .to r+ , r⊢q .to r+
⊓intro r⊢p r⊢q .fo (inl p-) = r⊢p .fo p-
⊓intro r⊢p r⊢q .fo (inr q-) = r⊢q .fo q-

-- I only had to prove it was meet-semilattice, as the rest of the properties follow by duality

⊥initial : ⊥ ⊢ P
⊥initial = contrapose ⊤terminal

⊔inl : P ⊢ P ⊔ Q
⊔inl = contrapose ⊓outl

⊔inr : Q ⊢ P ⊔ Q
⊔inr = contrapose ⊓outr

⊔elim : P ⊢ R → Q ⊢ R → P ⊔ Q ⊢ R
⊔elim p⊢r q⊢r = contrapose (⊓intro (contrapose p⊢r) (contrapose q⊢r))

-- ⊠ and ⊞ respect ⊢

⊠map : P ⊢ R → Q ⊢ S → P ⊠ Q ⊢ R ⊠ S
⊠map p⊢r q⊢s .to (p+ , q+) = p⊢r .to p+ , q⊢s .to q+
⊠map p⊢r q⊢s .fo r⊢¬s .to p+ = q⊢s .fo (r⊢¬s .to (p⊢r .to p+))
⊠map p⊢r q⊢s .fo r⊢¬s .fo q+ = p⊢r .fo (r⊢¬s .fo (q⊢s .to q+))

⊞map : P ⊢ R → Q ⊢ S → P ⊞ Q ⊢ R ⊞ S
⊞map p⊢r q⊢s = contrapose (⊠map (contrapose p⊢r) (contrapose q⊢s))

-- ⊠ and ⊞ are commutative monoids

⊠assoc : (P ⊠ Q) ⊠ R ≡ P ⊠ (Q ⊠ R)
⊠assoc .lower .fst .to ((p+ , q+) , r+) = p+ , q+ , r+
⊠assoc .lower .fst .fo p⊢¬qr .to (p+ , q+) = p⊢¬qr .to p+ .to q+
⊠assoc .lower .fst .fo p⊢¬qr .fo r+ .to p+ = p⊢¬qr .to p+ .fo r+
⊠assoc .lower .fst .fo p⊢¬qr .fo r+ .fo q+ = p⊢¬qr .fo (q+ , r+)
⊠assoc .lower .snd .to (p+ , q+ , r+) = (p+ , q+) , r+
⊠assoc .lower .snd .fo pq⊢¬r .to p+ .to q+ = pq⊢¬r .to (p+ , q+)
⊠assoc .lower .snd .fo pq⊢¬r .to p+ .fo r+ = pq⊢¬r .fo r+ .to p+
⊠assoc .lower .snd .fo pq⊢¬r .fo (q+ , r+) = pq⊢¬r .fo r+ .fo q+

-- TODO

-- weaken

⊠weaken⊓ : P ⊠ Q ⊢ P ⊓ Q
⊠weaken⊓ .to (p+ , q+) = p+ , q+
⊠weaken⊓ {P} .fo (inl p-) .to p+ = absurd (P .chu p+ p-)
⊠weaken⊓ .fo (inl p-) .fo q- = p-
⊠weaken⊓ .fo (inr q-) .to p- = q-
⊠weaken⊓ {Q} .fo (inr q-) .fo q+ = absurd (Q .chu q+ q-)

⊓map : P ⊢ R → Q ⊢ S → P ⊓ Q ⊢ R ⊓ S
⊓map p⊢r q⊢s = ⊓intro (⊢trans ⊓outl p⊢r) (⊢trans ⊓outr q⊢s)