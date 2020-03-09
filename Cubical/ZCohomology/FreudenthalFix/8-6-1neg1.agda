{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Freudenthal.8-6-1neg1 where


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Freudenthal.Prelim
open import Cubical.ZCohomology.Freudenthal.7-5-7
open import Cubical.ZCohomology.Freudenthal.8-6-1
open import Cubical.ZCohomology.Freudenthal.trivFunConnected
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation 
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_ ; _-_ ; +-comm )
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.HITs.Truncation

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

private
  2* : ℕ₋₂
  2* = ℕ→ℕ₋₂ 2





Lemma861-fibIdNeg1 : ∀{ℓ} (n k dif : ℕ) (f : A → B) →
                 (is- neg1 -Connected f) →
                 (P : B → HLevel ℓ (2+ (ℕ→ℕ₋₂ (suc k))))  →
                 (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) →
                 (a ≡ b) ≡ (fiber (inducedFun {k = (ℕ→ℕ₋₂ k) } f (λ x → ((fst a) x ≡ (fst b) x ) , (snd (P x)) (fst a x) (fst b x) ) ) (λ x → ((snd a) x) ∙ (sym ((snd b) x))))
Lemma861-fibIdNeg1 {A = A} {B = B} n k dif f isCon P l (g , p) (h , q)  = helper1 _ _ _  ∙ helper2 _ _ _ ∙ (λ j → Σ ((x : B) → g x ≡ h x) (λ r → helper3 l (g , p) (h , q) r j)) ∙ λ j → Σ ((x : B) → g x ≡ h x) (λ r → helper4 l (g , p) (h , q) r j)
    where
    helper1 : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → (a ≡ b) ≡ Σ (fst a ≡ fst b) λ r → PathP (λ i → (x : A) → (r i) (f x) ≡ l x) (snd a) (snd b)
    helper1 l a b = sym (ua (Σ≡ )) 

    helper2 : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → (Σ (fst a ≡ fst b) λ r → PathP (λ i → (x : A) → (r i) (f x) ≡ l x) (snd a) (snd b)) ≡ Σ ((x : B) → (fst a) x ≡ (fst b) x) λ r → PathP (λ i → (x : A) → r (f x) i ≡ l x) (snd a) (snd b)
    helper2 l (g , p) (h , q) = isoToPath (iso lrFun  rlFun (λ b → refl) λ b → refl) where
      lrFun : (Σ (g ≡ h) λ r → PathP (λ i → (x : A) → (r i) (f x) ≡ l x) p q) → Σ ((x : B) → g x ≡ h x) λ r → PathP (λ i → (x : A) → r (f x) i ≡ l x) p q
      lrFun (a , b) = funExt⁻ a , b
      rlFun : (Σ ((x : B) → g x ≡ h x) λ r → PathP (λ i → (x : A) → r (f x) i ≡ l x) p q) → (Σ (g ≡ h) λ r → PathP (λ i → (x : A) → (r i) (f x) ≡ l x) p q)
      rlFun (a , b) = (funExt a) , b
    
    helper3 : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → (r : (x : B) → (fst a) x ≡ (fst b) x) → (PathP (λ i → (x : A) → r (f x) i ≡ l x) (snd a) (snd b)) ≡ ((x : A) → r (f x) ≡ ((snd a) x) ∙ sym ((snd b) x) )
    helper3 l (g , p) (h , q) r j = hcomp (λ k → λ{ (j = i0) → (PathP (λ i → (x : A) → r (f x) (i ∧  i1) ≡ l x) p λ x → (sym (lUnit (q x)) k ))
                                                  ; (j = i1) → throwAbout k})
                                          ((PathP (λ i → (x : A) → r (f x) (i ∧  ~ j) ≡ l x) p λ x → (λ i → r (f x) (~ j ∨ i)) ∙ (q x)))
        where
        throwAbout : (p ≡ λ x → r (f x) ∙ q x) ≡ ((x : A) → (((r (f x))) ≡ (p x) ∙ (sym (q x)))) 
        throwAbout = isoToPath (iso (λ g x → transport (λ i → throwAboutHelper (p x) (r (f x)) (sym (q x)) i ) (funExt⁻ g x) )
                                  (λ g → funExt λ x → transport (λ i → throwAboutHelper (p x) (r (f x)) (sym (q x)) (~ i) ) (g x))
                                  (λ b → funExt λ x → (λ j → transport (λ i → throwAboutHelper (p x) (r (f x)) (λ i₁ → q x (~ i₁)) (i ∨ j)) (transport (λ i₁ → throwAboutHelper (p x) (r (f x)) (λ i₂ → q x (~ i₂)) ((~ i₁) ∨ ( j))) (b x))) ∙ λ j → transportRefl (transportRefl (b x) j) j  )
                                  λ b → (λ j → funExt (λ x → transport (λ i → throwAboutHelper (p x) (r (f x)) (λ i₁ → q x (~ i₁)) (~ i ∧ (~ j)))
                                                                       (transport (λ i → throwAboutHelper (p x) (r (f x)) (λ i₁ → q x (~ i₁)) (i ∧ (~ j)))
                                                                                  (λ i → b i x))))
                                               ∙ (λ j → funExt (λ x → transportRefl ((transportRefl (λ i → b i x)) j) j  ) )) where


          throwAboutHelper : ∀{ℓ} {A : Type ℓ} {a b c : A} →  (p : a ≡ b) (q : a ≡ c) (r : b ≡ c) → (p ≡ q ∙ (sym r) ) ≡ (q ≡ p ∙ r)
          throwAboutHelper {ℓ} {A} {a} {b} {c}  = J {ℓ} {A} {a} (λ b p → (q : a ≡ c) (r : b ≡ c) → (p ≡ q ∙ (sym r) ) ≡ (q ≡ p ∙ r))
                                                (J {ℓ} {A} {a} (λ c q → (r : a ≡ c) → (refl ≡ q ∙ (sym r) ) ≡ (q ≡ refl ∙ r) )
                                                   λ r → (λ i → refl ≡ lUnit (sym r) (~ i)) ∙ isoToPath (iso (λ id → cong (λ x → sym x) id) (λ id → cong (λ x → sym x) id ) (λ b → refl) λ b → refl)  ∙ λ i → (refl ≡ lUnit r i) )

    helper4 : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → (r : (x : B) → (fst a) x ≡ (fst b) x) → ((x : A) → r (f x) ≡ ((snd a) x) ∙ sym ((snd b) x) ) ≡  ((λ (x : A) → r (f x)) ≡ (λ (x : A) → ((snd a) x) ∙ sym ((snd b) x)))
    helper4 l (h , q) (g , p) r = isoToPath (iso (λ p → funExt p) (λ p → funExt⁻ p) (λ b → refl) λ b → refl)

{-

Lemma861-fibId2 : ∀{ℓ} (n k dif : ℕ) (f : A → B) →
                 (is- (ℕ→ℕ₋₂ n) -Connected f) →
                 (P : B → HLevel ℓ (2+ (ℕ→ℕ₋₂ (suc k)))) →
                 (suc k) ≡ (suc dif) + n  →
                 (l : (a : A) → fst (P (f a))) →
                 (fiber (inducedFun {k = (ℕ→ℕ₋₂ (suc k))} f P ) l) ≡ Σ ((b : B) → fst (P b)) λ g → ((a : A) → g (f a) ≡ l a)
Lemma861-fibId2 n k dif f isCon P pf l = isoToPath (iso (λ p → fst p , funExt⁻ (snd p)) (λ p → fst p , funExt (snd p)) (λ b → refl) λ b → refl)

Lemma861 : ∀{ℓ} (n k dif : ℕ) (f : A → B) →
           (is- (ℕ→ℕ₋₂ n) -Connected f) →
           (P : B → HLevel ℓ (2+ (ℕ→ℕ₋₂ k))) → 
           k ≡ dif + n  →
           is- (-2+ (k - n)) -Truncated (inducedFun {k = ℕ→ℕ₋₂ k} f P)
Lemma861 {A = A} {B = B} n k zero f isCon P pf = transport (λ i → is- (-2+ ((λ j → ((pf j) - n)) ∙ (minusId n)) (~ i)) -Truncated (inducedFun {k = ℕ→ℕ₋₂ k} f P) ) (equiv-proof (Lemma757i→ii f (ℕ→ℕ₋₂ k) (transport (λ i → is- (ℕ→ℕ₋₂ (pf (~ i))) -Connected f) isCon) P) )
Lemma861 {A = A} {B = B} n zero (suc dif) f isCon P pf = ⊥-elim (znots pf)
Lemma861 {A = A} {B = B} n (suc k) (suc zero) f isCon P pf = λ l → transport (λ i → isOfHLevel (2+ (-2+ (suc k - n))) (Lemma861-fibId2 {A = A} {B = B} n k zero f isCon P pf l (~ i)))
                                                                             (transport (λ i → isOfHLevel (natId (~ i)) (Σ ((b : B) → fst (P b)) λ g → ((a : A) → g (f a) ≡ l a)))
                                                                                        λ a b → transport (λ i → Lemma861-fibId n k zero f isCon P pf l a b (~ i) )
                                                                                                          (finalTruncLemma l a b (λ x → (snd a x) ∙ sym (snd b x)) .fst))
  where

  natId : (2+ (-2+ (suc k - n))) ≡ suc zero
  natId = (λ i → (2+ (-2+ (pf i - n)))) ∙ (λ i → (2+ (-2+ (helper {n} i)))) where
    helper : {n : ℕ} → (suc n - n) ≡ 1
    helper {zero} = refl
    helper {suc n} = helper {n}

  natId2 : (k - n) ≡ zero
  natId2 = (λ i → (((cong predℕ pf) i) - n)) ∙ helper n where
    helper : (n : ℕ) → (n - n) ≡ zero
    helper zero = refl
    helper (suc n) = helper n

  finalTruncLemma : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → is- (-2+ zero) -Truncated ((inducedFun {k = (ℕ→ℕ₋₂ k)} f (λ x → ((fst a) x ≡ (fst b) x ) , (snd (P x)) (fst a x) (fst b x) ) ))
  finalTruncLemma l a b = (transport (λ i → (is- -2+ (natId2 i) -Truncated (inducedFun {k = (ℕ→ℕ₋₂ k)} f (λ x → (fst a x ≡ fst b x) , snd (P x) (fst a x) (fst b x)))))) (Lemma861 n k zero f isCon ((λ x → ((fst a) x ≡ (fst b) x ) , (snd (P x)) (fst a x) (fst b x) )) (cong (λ x → predℕ x) pf ))
  
Lemma861 {A = A} {B = B} n (suc k) (suc (suc dif)) f isCon P pf = λ l → transport (λ i → isOfHLevel (2+ (-2+ (suc k - n))) (Lemma861-fibId2 {A = A} {B = B} n k (suc dif) f isCon P pf l (~ i))) ((transport (λ i → isOfHLevel (natId pf(~ i)) (Σ ((b : B) → fst (P b)) λ g → ((a : A) → g (f a) ≡ l a))) λ a b → transport (λ i → isOfHLevel (suc dif) (Lemma861-fibId n k (suc dif) f isCon P pf l a b (~ i)) ) (finalTruncLemma l a b λ x → ((snd a x) ∙ sym (snd b x)))))
  where

  natId : {k n : ℕ} (pf : suc k ≡ suc (suc (dif + n))) → (2+ (-2+ (suc k - n))) ≡ (suc (suc dif))
  natId {k} {n} pf = (λ i → (2+ (-2+ ((pf i) - n)))) ∙ -assocHelp {(suc (suc dif))} {n}

  natId2 : (k - n) ≡ (suc dif)
  natId2 = (cong (λ x → ((predℕ x) - n)) pf) ∙ -assocHelp {(suc dif)} {n}
  
  fibId : (l : ((a : A) → fst (P (f a)))) → (fiber (inducedFun {k = (ℕ→ℕ₋₂ (suc k))} f P ) l) ≡ Σ ((b : B) → fst (P b)) λ g → ((a : A) → g (f a) ≡ l a)
  fibId l = isoToPath (iso (λ p → fst p , funExt⁻ (snd p)) (λ p → fst p , funExt (snd p)) (λ b → refl) λ b → refl)

  finalTruncLemma : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → is- (-2+ (suc dif)) -Truncated ((inducedFun {k = (ℕ→ℕ₋₂ k)} f (λ x → ((fst a) x ≡ (fst b) x ) , (snd (P x)) (fst a x) (fst b x) ) ))
  finalTruncLemma l a b =  (transport (λ i → (is- -2+ (natId2 i) -Truncated (inducedFun {k = (ℕ→ℕ₋₂ k)} f (λ x → (fst a x ≡ fst b x) , snd (P x) (fst a x) (fst b x)))))) (Lemma861 n k (suc dif) f isCon ((λ x → ((fst a) x ≡ (fst b) x ) , (snd (P x)) (fst a x) (fst b x) )) (cong (λ x → predℕ x) pf))



Lemma861neg1 : ∀{ℓ} (k : ℕ) (f : A → B) →
           (is- neg1 -Connected f) →
           (P : B → HLevel ℓ (2+ (ℕ→ℕ₋₂ k))) →
           is- (-2+ (k - 1)) -Truncated (inducedFun {k = ℕ→ℕ₋₂ k} f P)
Lemma861neg1 zero dif f iscon P = {!!}
Lemma861neg1 (suc k) dif f iscon P = {!!}
-}
