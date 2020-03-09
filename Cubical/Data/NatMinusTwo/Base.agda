{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.NatMinusTwo.Base where

open import Cubical.Core.Primitives
open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Unit

record ℕ₋₂ : Type₀ where
  constructor -2+_
  field
    n : ℕ

pattern neg2 = -2+ zero
pattern neg1 = -2+ (suc zero)
pattern ℕ→ℕ₋₂ n = -2+ (suc (suc n))
pattern -1+_ n = -2+ (suc n)

2+_ : ℕ₋₂ → ℕ
2+ (-2+ n) = n

suc₋₂ : ℕ₋₂ → ℕ₋₂
suc₋₂ (-2+ n) = -2+ (suc n)

pred₋₂ : ℕ₋₂ → ℕ₋₂
pred₋₂ neg2 = neg2
pred₋₂ neg1 = neg2
pred₋₂ (ℕ→ℕ₋₂ zero) = neg1
pred₋₂ (ℕ→ℕ₋₂ (suc n)) = (ℕ→ℕ₋₂ n)

_-₋₂_ : ℕ₋₂ → ℕ₋₂ → ℕ₋₂
n -₋₂ neg2 = suc₋₂ (suc₋₂ n)
n -₋₂ neg1 = suc₋₂ n
n -₋₂ ℕ→ℕ₋₂ zero = n
neg2 -₋₂ ℕ→ℕ₋₂ (suc m) = neg2
neg1 -₋₂ ℕ→ℕ₋₂ (suc m) = neg2
ℕ→ℕ₋₂ zero -₋₂ ℕ→ℕ₋₂ (suc zero) = neg1
ℕ→ℕ₋₂ zero -₋₂ ℕ→ℕ₋₂ (suc (suc m)) = neg2
ℕ→ℕ₋₂ (suc n) -₋₂ ℕ→ℕ₋₂ (suc m) = ℕ→ℕ₋₂ n -₋₂ ℕ→ℕ₋₂ m

_+₋₂_ : ℕ₋₂ → ℕ₋₂ → ℕ₋₂
neg2 +₋₂ m = pred₋₂ (pred₋₂ m)
neg1 +₋₂ m = pred₋₂ m
ℕ→ℕ₋₂ n +₋₂ neg2 = pred₋₂ (pred₋₂ (ℕ→ℕ₋₂ n))
ℕ→ℕ₋₂ n +₋₂ neg1 = pred₋₂ (ℕ→ℕ₋₂ n)
ℕ→ℕ₋₂ n +₋₂ ℕ→ℕ₋₂ m = ℕ→ℕ₋₂ (n + m)

-- Natural number and negative integer literals for ℕ₋₂

instance
  fromNatℕ₋₂ : HasFromNat ℕ₋₂
  fromNatℕ₋₂ = record { Constraint = λ _ → Unit ; fromNat = ℕ→ℕ₋₂ }

instance
  fromNegℕ₋₂ : HasFromNeg ℕ₋₂
  fromNegℕ₋₂ = record { Constraint = λ { (suc (suc (suc _))) → ⊥ ; _ → Unit }
                       ; fromNeg = λ { zero → 0 ; (suc zero) → neg1 ; _ → neg2 } }
