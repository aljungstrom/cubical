{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.NatMinusTwo.Base where

open import Cubical.Core.Primitives
open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Unit

import Cubical.Data.NatMinusOne as ℕ₋₁
open import Cubical.Data.NatMinusOne using (ℕ₋₁; neg1; suc; ℕ→ℕ₋₁)

data ℕ₋₂ : Set where
  neg2 : ℕ₋₂
  suc  : (n : ℕ₋₂) → ℕ₋₂

1+_ : ℕ₋₂ → ℕ₋₁
1+ neg2 = neg1
1+ suc n = suc (1+ n)

-1+_ : ℕ₋₁ → ℕ₋₂
-1+ neg1 = neg2
-1+ suc n = suc (-1+ n)

ℕ₋₁→ℕ₋₂ : ℕ₋₁ → ℕ₋₂
ℕ₋₁→ℕ₋₂ n = suc (-1+ n)

2+_ : ℕ₋₂ → ℕ
2+ n = ℕ₋₁.1+ (1+ n)

-2+_ : ℕ → ℕ₋₂
-2+ n = -1+ (ℕ₋₁.-1+ n)

ℕ→ℕ₋₂ : ℕ → ℕ₋₂
ℕ→ℕ₋₂ n = ℕ₋₁→ℕ₋₂ (ℕ→ℕ₋₁ n)

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
  fromNatℕ₋₂ = record { Constraint = λ _ → Unit ; fromNat = λ n → ℕ→ℕ₋₂ n }

instance
  fromNegℕ₋₂ : HasFromNeg ℕ₋₂
  fromNegℕ₋₂ = record { Constraint = λ { (suc (suc (suc _))) → ⊥ ; _ → Unit }
                      ; fromNeg = λ { zero → suc (suc neg2) ; (suc zero) → suc neg2 ; _ → neg2 } }
