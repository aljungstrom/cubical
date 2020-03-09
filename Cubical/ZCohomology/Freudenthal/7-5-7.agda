{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Freudenthal.7-5-7 where


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Freudenthal.Prelim
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


{- TODO: Prove Kₙ ≡ Ω Kₙ₊₁  -}


Lemma757i→ii :  (f : A → B) (n : ℕ₋₂) →
                is- n -Connected f →
                (P : B → HLevel ℓ (2+ n)) →
                isEquiv (inducedFun f P)
Lemma757i→ii {A = A} {B = B} f n isCon P = isoToEquiv (compIso (compIso (compIso firstIso secondIso) thirdIso) fourthIso ) .snd
  where
  fib₀ : (b : B) → ∥ fiber f b ∥ n
  fib₀ b = isCon b .fst

  fibContr : (b : B) (y x :  ∥ fiber f b ∥ n) → y ≡ x
  fibContr b x y = sym (isCon b .snd x) ∙ ((isCon b .snd) y)

  firstIso : Iso ((b : B) → (fst (P b))) (((b : B) → ((∥ fiber f b ∥ n) → fst (P b))))
  firstIso = iso (λ f b x₁ → f b)
                 (λ f b → f b (fib₀ b))
                 (λ b → funExt λ x → funExt λ y i → b x ((fibContr x (isCon x .fst) y) i))
                 λ a  → refl

  secondIso : Iso (((b : B) → ((∥ fiber f b ∥ n) → fst (P b)))) ((b : B) → (fiber f b) → fst (P b))
  secondIso = iso (λ g b → univTrunc.fun n {B = (P b)} (g b))
                  (λ g b → univTrunc.inv n {B = (P b)} (g b))
                  (λ b → funExt λ x → univTrunc.sect n {B = P x} (b x))
                  λ b → funExt λ x → univTrunc.retr n (b x)

  thirdIso : Iso ((b : B) → (fiber f b) → fst (P b)) ((b : B) (a : A) (p : (f a) ≡ b) → fst (P b))
  thirdIso = iso (λ g → (λ x b x₁ → g x (b , x₁)))
                 (λ g b fib → g b (fib .fst) (fib .snd))
                 (λ x → refl)
                 λ x → refl

  fourthIso : Iso ((b : B) (a : A) (p : (f a) ≡ b) → fst (P b)) ((a : A) → fst (P (f a)))
  fourthIso = iso (λ g a → g (f a) a refl)
                  (λ g b a id → transport (λ i → fst (P (id i))) (g a))
                  (λ x → funExt (λ a → transportRefl (x a)))
                  λ b → funExt λ x → funExt λ a → funExt (J (λ x p → transport (λ i → fst (P (p i))) (b (f a) a (λ _ → f a)) ≡ b x a p)
                                                            (transportRefl (b (f a) a refl)))


Lemma757ii→iii : ∀ {ℓ} (f : A → B) (n : ℕ₋₂) →
                (P : B → HLevel ℓ (2+ n)) →
                isEquiv (inducedFun f P) →
                hasSection (inducedFun f P)
Lemma757ii→iii f n P record { equiv-proof = eqpf } = (λ g → (eqpf g) .fst .fst) , (λ b  → (eqpf b) .fst .snd)

Lemma757i→iii : ∀ {ℓ} (f : A → B) (n : ℕ₋₂) →
                is- n -Connected f →
                (P : B → HLevel ℓ (2+ n)) →
                hasSection (inducedFun f P)
Lemma757i→iii f n isCon P = Lemma757ii→iii f n P (Lemma757i→ii f n isCon P )

Lemma757iii→i : (f : A → B) (n : ℕ₋₂) →
                (∀ {ℓ} (P : B → HLevel ℓ (2+ n)) →
                hasSection (inducedFun f P)) →
                is- n -Connected f
Lemma757iii→i {A = A} {B = B} f n P→hasSection = λ b → (c n P→hasSection b) , (λ y → sym (fun n P→hasSection b y))
  where 
  P : (n : ℕ₋₂) → (∀ {ℓ} (P : B → HLevel ℓ (2+ n)) → hasSection (inducedFun f P)) → B → Type _
  P n s b = ∥ fiber f b ∥ n

  c : (n : ℕ₋₂) → (∀ {ℓ} (P : B → HLevel ℓ (2+ n)) → hasSection (inducedFun f P)) → (b : B) → ∥ fiber f b ∥ n
  c n s = (s λ b → ( ∥ fiber f b ∥ n , isOfHLevel∥∥ _)) .fst λ a → ∣ a , refl ∣

  fun : (n : ℕ₋₂) → (s : (∀ {ℓ} (P : B → HLevel ℓ (2+ n)) → hasSection (inducedFun f P))) → (b : B) (w : (∥ fiber f b ∥ n) ) → w ≡ c n s b
  fun neg2 s b w = isOfHLevelSuc (2+ neg2) (isOfHLevel∥∥ neg2) w (c neg2 s b) 
  fun (-1+ n) s b = ind (λ x → (isOfHLevelSuc (2+ (-1+ n)) (isOfHLevel∥∥ {A = (fiber f b)} (-1+ n))) x (c (-1+ n) s b) ) (λ a → witness b (fst a) (snd a))
    where
    eqtyp : ((a : A) → ∣ (a , refl {x = f a}) ∣ ≡ c (-1+ n) s (f a)) ≡ ((b : B) (a : A) (p : f (a) ≡ b) → ∣ (a , p) ∣ ≡ c (-1+ n) s b)
    eqtyp = isoToPath (iso
                         (λ g b a → J (λ b p → ∣ a , p ∣ ≡ c (-1+ n) s b) (g a))
                         (λ g a → g (f a) a refl)
                         (λ h → funExt λ b →
                                funExt λ a →
                                funExt (J (λ b x → (J (λ b₂ p → ∣ a , p ∣ ≡ c (-1+ n) s b₂) (h (f a) a (λ _ → f a)) x ≡ h b a x))
                                          (JRefl (λ b₂ p → ∣ a , p ∣ ≡ c (-1+ n) s b₂) (h (f a) a (λ _ → f a)))))
                         λ h → funExt λ a → JRefl (λ b₁ p → ∣ a , p ∣ ≡ c (-1+ n) s b₁) (h a))

    c* : ((a : A) → ∣ (a , refl {x = f a}) ∣ ≡ c (-1+ n) s (f a))
    c* = λ a → sym (cong (λ x → x a) ((s λ b → ( ∥ fiber f b ∥ (-1+ n) , isOfHLevel∥∥ _)) .snd λ a → ∣ a , refl ∣))

    witness : ((b : B) (a : A) (p : f (a) ≡ b) → ∣ (a , p) ∣ ≡ c (-1+ n) s b)
    witness = transport (λ i → eqtyp i) c*

