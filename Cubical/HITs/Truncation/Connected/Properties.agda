{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Connected.Properties where

open import Cubical.HITs.Truncation.Connected.Base
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-7
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-11
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-14
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.8-6-1
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.8-6-2
open import Cubical.HITs.Truncation.Connected.FreudenthalProof.8-6-4
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Prod.Base
open import Cubical.HITs.Susp
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation.Properties

open import Cubical.Data.HomotopyGroup

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

{- a function from Unit to an (n + 1)-connected type is n-connected -}
trivFunCon : ∀{ℓ} {A : Type ℓ} {a : A} → (n : ℕ₋₂) → (is- (suc₋₂ n) -ConnectedType A) → is- n -Connected (λ (x : Unit) → a)
trivFunCon = Lemma7-5-11

{- n-connected functions induce equivalences between n-truncations -}
conEquiv : (n : ℕ₋₂) (f : A → B) → (is- n -Connected f) → ∥ A ∥ n ≃ ∥ B ∥ n
conEquiv = Lemma7-5-14

{- Wedge connectivity lemma (Lemma 8.6.2 in the HoTT book) -}
WedgeConn : (A : Pointed ℓ) (B : Pointed ℓ') (n m : ℕ) →
            (is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A)) →
            (is- (ℕ→ℕ₋₂ m) -ConnectedType (typ B)) →
            (P : (typ A) → (typ B) → HLevel (ℓ-max ℓ ℓ') (2+ (ℕ→ℕ₋₂ (n + m)))) →
            (f : ((a : (typ A)) → fst (P a (pt B)))) →
            (g : ((b : (typ B)) → fst (P (pt A) b))) →
            (p : f (pt A) ≡ g (pt B)) →
            Σ ((a : typ A) → (b : typ B) → fst (P a b))
              λ h → Σ (((a : typ A) → h a (pt B) ≡ f a) × ((b : typ B) → h (pt A) b ≡ g b))
                       λ pair → p ≡ sym ((proj₁ pair) (pt A) ) ∙ (proj₂ pair) (pt B)
WedgeConn = Lemma8-6-2

private
  σ : A → A → typ (Ω ((Susp A) , north))
  σ a x = merid x ∙ sym (merid a)

σ-2nConnected : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → is- ℕ→ℕ₋₂ (n + n) -Connected (σ a)
σ-2nConnected n a iscon = Thm8-6-4 n a iscon

Freudenthal : (n : ℕ) (A : Pointed ℓ) →
              is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A) →
              ∥ typ A ∥ (ℕ→ℕ₋₂ (n + n)) ≃ ∥ typ (Ω (Susp (typ A) , north)) ∥ ((ℕ→ℕ₋₂ (n + n)))
Freudenthal n A iscon = conEquiv _ (σ (pt A)) (σ-2nConnected n (pt A) iscon)
