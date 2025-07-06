module Surreals where

open import Prelude
open import Propositions.Base

private variable
  ℓ : Level
  X : Type ℓ

module No (ℓ : Level) where
  -- The inductive-recursive type of surreal numbers

  infixr 40 _⊑No_ _⊏No_
  infixr 30 _≤No_ _<No_ _≥No_ _>No_

  record No : Type (lsuc ℓ)
  _⊑No_ _⊏No_ : No → No → ±Prop ℓ

  record No where
    inductive
    -- eta-equality -- eta-equality inductive records are weird https://github.com/agda/agda/issues/5842
    pattern -- Without eta, this is basically just syntax sugar for an inductive type
    constructor makeNo
    field
      {lindex rindex} : Type ℓ
      lcut : lindex → No
      rcut : rindex → No
      lcut<rcut : ∀ i j → lcut i ⊏No rcut j ⁺

  open No public

  -- We can replicate Conway's definition here
  x@(makeNo {lindex = xˡ} xˡ! _ _) ⊑No y@(makeNo {rindex = yʳ} _ yʳ! _) =
    (⊓[ i ꞉ xˡ ] xˡ! i ⊏No y) ⊓ (⊓[ i ꞉ yʳ ] x ⊏No yʳ! i)

  x ⊏No y = ¬ (y ⊑No x)

  -- and it translates to the usual constructive pair of predicates
  -- under the antithesis translation
  _≤No_ _<No_ _≥No_ _>No_ : No → No → Type ℓ
  x <No y = x ⊏No y ⁺
  x ≤No y = x ⊑No y ⁺
  x ≥No y = x ⊏No y ⁻
  x >No y = x ⊑No y ⁻

  -- why doesn't this work :sob
  {-# DISPLAY _⁺ (_⊏No_ x y) = x <No y #-}
  {-# DISPLAY _⁺ (_⊑No_ x y) = x ≤No y #-}
  {-# DISPLAY _⁻ (_⊏No_ x y) = x ≥No y #-}
  {-# DISPLAY _⁻ (_⊑No_ x y) = x >No y #-}

  -- Conway's theorem 0, 11.6.4 in the HoTT Book
  mutual
    ≤refl : ∀ x → x ≤No x
    ≤refl x@(makeNo xl xr xl<xr) = lcut< x , rcut> x

    lcut< : ∀ x i → x .lcut i <No x
    lcut< x@(makeNo xl xr xl<xr) i = lemma (xl i) (≤refl (xl i)) where
      lemma : ∀ y → y ≤No xl i → y <No x
      lemma y@(makeNo yl yr yl<yr) y≤xl = inl (i , y≤xl)

    rcut> : ∀ x i → x <No x .rcut i
    rcut> x@(makeNo xl xr xl<xr) i = lemma (xr i) (≤refl (xr i)) where
      lemma : ∀ y → xr i ≤No y → x <No y
      lemma y@(makeNo yl yr yl<yr) xr≤y = inr (i , xr≤y)
  
  mutual
    ≤trans : ∀ x y z → x ≤No y → y ≤No z → x ≤No z
    ≤trans x@(makeNo xl xr xl<xr) y@(makeNo yl yr yl<yr) z@(makeNo zl zr zl<zr) = λ where
      x≤y y≤z .fst i → <≤trans (xl i) y z (x≤y .fst i) y≤z
      x≤y y≤z .snd j → ≤<trans x y (zr j) x≤y (y≤z .snd j)

    <≤trans : ∀ x y z → x <No y → y ≤No z → x <No z
    <≤trans x@(makeNo xl xr xl<xr) y@(makeNo yl yr yl<yr) z@(makeNo zl zr zl<zr) = λ where
      (inl (i , x≤yl)) y≤z → ≤<trans x (yl i) z x≤yl (y≤z .fst i)
      (inr (j , xr≤y)) y≤z → inr (j , ≤trans (xr j) y z xr≤y y≤z)

    ≤<trans : ∀ x y z → x ≤No y → y <No z → x <No z
    ≤<trans x@(makeNo xl xr xl<xr) y@(makeNo yl yr yl<yr) z@(makeNo zl zr zl<zr) = λ where
      x≤y (inl (j , y≤zl)) → inl (j , ≤trans x y (zl j) x≤y y≤zl)
      x≤y (inr (i , yr≤z)) → <≤trans x (yr i) z (x≤y .snd i) yr≤z

  -- -- Equational reasoning for inequalities
  -- _≤∎ : ∀ x → x ≤No x
  -- _≤∎ = ⊑No-refl

  -- _≤⟨_⟩_ : ∀ x {y z} → x ≤No y → y ≤No z → x ≤No z

  mutual
    <weaken≤ : ∀ x y → x <No y → x ≤No y
    <weaken≤ x@(makeNo xl xr xl<xr) y@(makeNo yl yr yl<yr) = λ where
      (inl (i , x≤yl)) .fst j → <trans (xl j) x y (lcut< x j) (≤<trans x (yl i) y x≤yl (lcut< y i))
      (inl (i , x≤yl)) .snd j → ≤<trans x (yl i) (yr j) x≤yl (yl<yr i j)
      (inr (j , xr≤y)) .fst i → <≤trans (xl i) (xr j) y (xl<xr i j) xr≤y
      (inr (j , xr≤y)) .snd i → <trans' x (xr j) (yr i) (rcut> x j) (≤<trans (xr j) y (yr i) xr≤y (rcut> y i))

    <trans : ∀ x y z → x <No y → y <No z → x <No z
    <trans x y z x<y = ≤<trans x y z (<weaken≤ x y x<y)

    <trans' : ∀ x y z → x <No y → y <No z → x <No z
    <trans' x y z x<y y<z = <≤trans x y z x<y (<weaken≤ y z y<z)
  
  