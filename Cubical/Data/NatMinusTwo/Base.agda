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

_+₋₂_ : ℕ₋₂ → ℕ₋₂ → ℕ₋₂
neg2 +₋₂ neg2 = neg2
neg2 +₋₂ suc neg2 = neg2
neg2 +₋₂ suc (suc m) = m
suc neg2 +₋₂ neg2 = neg2
suc neg2 +₋₂ suc m = m
suc (suc neg2) +₋₂ m = m
suc (suc (suc n)) +₋₂ m = suc ((suc (suc n)) +₋₂ m )

_-₋₂_ : ℕ₋₂ → ℕ₋₂ → ℕ₋₂
neg2 -₋₂ neg2 = suc (suc neg2)
neg2 -₋₂ suc neg2 = suc neg2
neg2 -₋₂ suc (suc n) = neg2
suc neg2 -₋₂ neg2 = suc (suc (suc neg2))
suc neg2 -₋₂ suc neg2 = suc (suc neg2)
suc neg2 -₋₂ suc (suc neg2) = suc neg2
suc neg2 -₋₂ suc (suc (suc n)) = neg2
suc (suc neg2) -₋₂ neg2 = suc (suc (suc (suc neg2)))
suc (suc neg2) -₋₂ suc neg2 = suc (suc (suc neg2))
suc (suc neg2) -₋₂ suc (suc neg2) = suc (suc neg2)
suc (suc neg2) -₋₂ suc (suc (suc neg2)) = suc neg2
suc (suc neg2) -₋₂ suc (suc (suc (suc n))) = neg2
suc (suc (suc k)) -₋₂ neg2 = suc (suc (suc (suc (suc k))))
suc (suc (suc k)) -₋₂ suc neg2 = suc (suc (suc (suc k)))
suc (suc (suc k)) -₋₂ suc (suc neg2) = suc (suc (suc k))
suc (suc (suc k)) -₋₂ suc (suc (suc n)) = suc (suc k) -₋₂ (suc (suc n))

pred₋₂ : ℕ₋₂ → ℕ₋₂
pred₋₂ neg2 = neg2
pred₋₂ (suc n) = n

neg2≠suc : (n : ℕ₋₂) → neg2 ≡ suc n → ⊥
neg2≠suc n id = transport (λ i → (cong (λ x → fun x) id) (~ i)) tt where

  fun : ℕ₋₂ → Type₀
  fun neg2 = ⊥
  fun (suc n) = Unit

-- Natural number and negative integer literals for ℕ₋₂

instance
  fromNatℕ₋₂ : HasFromNat ℕ₋₂
  fromNatℕ₋₂ = record { Constraint = λ _ → Unit ; fromNat = ℕ→ℕ₋₂ }

instance
  fromNegℕ₋₂ : HasFromNeg ℕ₋₂
  fromNegℕ₋₂ = record { Constraint = λ { (suc (suc (suc _))) → ⊥ ; _ → Unit }
                       ; fromNeg = λ { zero → 0 ; (suc zero) → neg1 ; _ → neg2 } }
