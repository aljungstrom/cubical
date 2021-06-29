{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Data.Nat.EvenOdd where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

open import Cubical.Data.Sum

is-even : ℕ → Type
is-even zero = Unit
is-even (suc zero) = ⊥
is-even (suc (suc n)) = is-even n

isProp-iseven : (n : ℕ) → isProp (is-even n)
isProp-iseven zero x y = refl
isProp-iseven (suc zero) = isProp⊥
isProp-iseven (suc (suc n)) = isProp-iseven n

is-odd : ℕ → Type
is-odd n = is-even (suc n)

is-even-suc : (n : ℕ) → is-odd n → is-even (suc n)
is-even-suc (suc zero) p = tt
is-even-suc (suc (suc n)) p = is-even-suc n p

is-odd-suc : (n : ℕ) → is-even n → is-odd (suc n)
is-odd-suc zero p = tt
is-odd-suc (suc (suc n)) p = is-odd-suc n p

evenOrOdd : (n : ℕ) → is-even n ⊎ is-odd n
evenOrOdd zero = inl tt
evenOrOdd (suc zero) = inr tt
evenOrOdd (suc (suc n)) = evenOrOdd n

¬evenAndOdd : (n : ℕ) → ¬ is-even n × is-odd n
¬evenAndOdd zero (p , ())
¬evenAndOdd (suc zero) ()
¬evenAndOdd (suc (suc n)) = ¬evenAndOdd n

evenOrOdd-Prop : (n : ℕ) → isProp (is-even n ⊎ is-odd n)
evenOrOdd-Prop n (inl x) (inl x₁) = cong inl (isProp-iseven n x x₁)
evenOrOdd-Prop n (inl x) (inr x₁) = ⊥-rec (¬evenAndOdd n (x , x₁))
evenOrOdd-Prop n (inr x) (inl x₁) = ⊥-rec (¬evenAndOdd (suc n) (x , x₁))
evenOrOdd-Prop n (inr x) (inr x₁) = cong inr (isProp-iseven (suc n) x x₁)
