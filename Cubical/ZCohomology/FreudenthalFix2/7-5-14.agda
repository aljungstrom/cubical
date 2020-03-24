{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.FreudenthalFix2.7-5-14 where


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.FreudenthalFix2.Prelim
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation 
open import Cubical.HITs.Nullification
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation

open import Cubical.Data.Bool
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

-- is-_-Connected : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : ℕ₋₂) (f : A → B) → Type (ℓ-max ℓ ℓ'



Lemma7-5-14 : (n : ℕ₋₂) (f : A → B) → (is- n -Connected f) → ∥ A ∥ n ≃ ∥ B ∥ n
Lemma7-5-14 {A = A} {B = B} neg2 f c = isoToEquiv (iso (λ _ → fst (isOfHLevel∥∥ neg2))
                                                       (λ _ → fst (isOfHLevel∥∥ neg2))
                                                       (λ b → snd (isOfHLevel∥∥ neg2) b)
                                                       (λ b → snd (isOfHLevel∥∥ neg2) b))
Lemma7-5-14 {A = A} {B = B} (-1+ n) f c = isoToEquiv (iso
                                          (∥ f ∥-fun (-1+ n))
                                          (ind (λ _ → isOfHLevel∥∥ (-1+ n)) back)
                                          (ind (λ x → (isOfHLevelSuc (2+ (-1+ n)) (isOfHLevel∥∥ (-1+ n))) _ _) backSection)
                                          (ind (λ x → (isOfHLevelSuc (2+ (-1+ n)) (isOfHLevel∥∥ (-1+ n))) _ _) backRetract))
  where
  back :  B → ∥ A ∥ (-1+ n)
  back  y = ∥ fst ∥-fun (-1+ n) (fst (c y))

  backSection :  (b : B) → _≡_ {A = ∥ B ∥ (-1+ n)} (ind (λ _ → isOfHLevel∥∥ (-1+ n)) (λ a → ∣ f a ∣) (ind {n = (-1+ n)} {B = λ _ → ∥ A ∥ (-1+ n)} (λ _ → isOfHLevel∥∥ (-1+ n)) back ∣ b ∣)) ∣ b ∣
  backSection b = helper {P = λ p → ∥ f ∥-fun (-1+ n) p ≡ ∣ b ∣} (λ x → (isOfHLevelSuc (2+ (-1+ n)) (isOfHLevel∥∥ (-1+ n))) (∥ f ∥-fun (-1+ n) (∥ fst ∥-fun (-1+ n) x)) ∣ b ∣) (λ a p → cong (λ x → ∣ x ∣) p) (fst (c b))

    where
    helper : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {P : ∥ A ∥ (-1+ n) → Type ℓ''} → ((x : ∥ Σ A B ∥ (-2+ ℕ₋₂.n (-1+ n))) → isOfHLevel (2+ (-2+ ℕ₋₂.n (-1+ n))) (P (∥ fst ∥-fun (-1+ n) x))) →  ((a : A) (b : B a) → P ∣ a ∣) →  (p : ∥ Σ A B ∥ (-1+ n)) →  P (∥ fst ∥-fun (-1+ n) p)
    helper hlev pf = ind hlev λ pair → pf (fst pair) (snd pair)

  backRetract : (a : A) → ∥ fst ∥-fun (-1+ n) (fst (c (f a))) ≡ ∣ a ∣
  backRetract a = cong (∥ fst ∥-fun (-1+ n)) (snd (c (f a)) ∣ a , refl ∣)
