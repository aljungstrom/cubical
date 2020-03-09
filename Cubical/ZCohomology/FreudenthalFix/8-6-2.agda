{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.FreudenthalFix.8-6-2 where

open import Cubical.Foundations.Prelude


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.FreudenthalFix.Prelim
open import Cubical.ZCohomology.FreudenthalFix.7-5-7
open import Cubical.ZCohomology.FreudenthalFix.trivFunConnected
open import Cubical.ZCohomology.FreudenthalFix.8-6-1
open import Cubical.HITs.Sn
open import Cubical.Foundations.Everything
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation 
open import Cubical.HITs.Nullification
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

      
transpHelper : {a b c : A} (r : b ≡ c) (q : a ≡ b) (p : a ≡ c) → PathP (λ i → a ≡ r i) q p → q ∙ r ≡ p
transpHelper {ℓ} {A} {a} {b} {c} = J {ℓ} {A} {b} (λ c r →  (q : a ≡ b) (p : a ≡ c) → PathP (λ i → a ≡ r i) q p → q ∙ r ≡ p) λ p q path → sym (rUnit p) ∙ path
{- SORRY I HAD TO USE J -}


pt-map : (A : Pointed ℓ)  → Unit → typ A
pt-map A x = pt A

conOfpt-map : (A : Pointed ℓ) (n : ℕ) → (is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A)) → is- (pred₋₂ (ℕ→ℕ₋₂ n)) -Connected (pt-map A)
conOfpt-map A n conA = trivFunConnected (pred₋₂ (ℕ→ℕ₋₂ n)) (transport (λ i → (is- pmId n (~ i) -ConnectedType (typ A))) conA)

module prelims (A : Pointed ℓ) (B : Pointed ℓ') (n m : ℕ)
               (conA : is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A))
               (conB : is- (ℕ→ℕ₋₂ m) -ConnectedType (typ B))
               (P : (typ A) → (typ B) → HLevel (ℓ-max ℓ ℓ') (2+ (ℕ→ℕ₋₂ (n + m))))
               (f : ((a : (typ A)) → fst (P a (pt B))))
               (g : ((b : (typ B)) → fst (P (pt A) b)))  (p : f (pt A) ≡ g (pt B))
       where
       Q : (typ A) → Type (ℓ-max ℓ ℓ')
       Q a = Σ ((b : (typ B)) → fst (P a b )) λ k → f a ≡ k (pt B)

       f-map : (a : typ A) → ((b : typ B) → fst (P a b)) → fst (P a (pt B))
       f-map a g = inducedFun {A = Unit} {B = typ B} {k = (ℕ→ℕ₋₂ (n +  m))} (pt-map B) (P a) g tt

       QisFib : (a : typ A) → Q a ≡ fiber (f-map a) (f a)
       QisFib a = isoToPath (iso (λ x → (x .fst) , (sym (x .snd))) (λ b → (fst b) , (sym (snd b))) (λ a → refl) λ b → refl)

       QisFib2 : (a : typ A) → Q a  ≡ fiber (inducedFun {A = Unit} {B = typ B} {k = (ℕ→ℕ₋₂ (n + m))} (pt-map B) (P a)) λ tt → (f a)
       QisFib2 a = QisFib a ∙ isoToPath (iso (λ x → (fst x) , (funExt (λ y → snd x))) (λ x → (fst x) , (cong (λ x → x tt) (snd x))) (λ x → refl) λ x → refl)

Lemma862 : (A : Pointed ℓ) (B : Pointed ℓ') (n m : ℕ) →
           (is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A)) →
           (is- (ℕ→ℕ₋₂ m) -ConnectedType (typ B)) →
           (P : (typ A) → (typ B) → HLevel (ℓ-max ℓ ℓ') (2+ (ℕ→ℕ₋₂ (n + m)))) →
           (f : ((a : (typ A)) → fst (P a (pt B)))) →
           (g : ((b : (typ B)) → fst (P (pt A) b))) →
           (p : f (pt A) ≡ g (pt B)) →
           Σ ((a : typ A) → (b : typ B) → fst (P a b)) λ h → Σ (((a : typ A) → h a (pt B) ≡ f a) × ((b : typ B) → h (pt A) b ≡ g b) ) λ pair → p ≡ sym ((proj₁ pair) (pt A) ) ∙ (proj₂ pair) (pt B)
Lemma862 {ℓ = ℓ} {ℓ' = ℓ'} A B n zero conA conB P f g p = (λ a b → ((typesQ (pt A) .fst) a) .fst b) , ((((λ a → sym ((typesQ (pt A)) .fst a .snd)))) , (λ b → cong (λ x → (x .fst) b) (((typesQ) (pt A)) .snd))) , (sym (transpHelper _ _ _ (cong (λ x → x .snd) (((typesQ) (pt A)) .snd))))
  where
  lemma2 : (a : typ A) → isOfHLevel (suc n) (fiber (inducedFun {A = Unit} {B = typ B} {k = (ℕ→ℕ₋₂ (n + zero))} (pt-map B) (P a)) λ tt → (f a))
  lemma2 a = Lemma861Gen neg1 (suc n) (λ x y → (2+ ℕ→ℕ₋₂ (predℕ y + zero))) (natHelper n) (pt-map B) (conOfpt-map B zero conB) (P a) (λ tt → f a)
    where
    natHelper : (n : ℕ) → (2+ ℕ→ℕ₋₂ (n + zero)) ≡ suc (n + (2+ neg1))
    natHelper zero = refl
    natHelper (suc n) = cong (λ x → suc x) (natHelper n)
  conOfQ : (a : typ A) → isOfHLevel (2+ ((pred₋₂ (ℕ→ℕ₋₂ n)))) (prelims.Q A B n zero conA conB P f g p a)
  conOfQ a = transport (λ i → isOfHLevel (2+ pred₋₂ (ℕ→ℕ₋₂ n)) (prelims.QisFib2 A B n zero conA conB P f g p a (~ i))) (transport (λ i → isOfHLevel (natHelper n (~ i)) (prelims.QisFib2 A B n zero conA conB P f g p a i1)) (lemma2 a) )
    where
    natHelper : (n : ℕ) → (2+ pred₋₂ (ℕ→ℕ₋₂ n)) ≡ (suc n)
    natHelper zero = refl
    natHelper (suc n) = refl

  typesQ : (a : typ A) → Σ ((a : (typ A)) → (prelims.Q A B n zero conA conB P f g p a)) λ ℓ → ℓ (pt A) ≡ (g , p)
  typesQ a  = (fst (Lemma757i→iii (pt-map A) ((pred₋₂ (ℕ→ℕ₋₂ n))) (conOfpt-map A n conA) (λ a → (prelims.Q A B n (zero) conA conB P f g p a , conOfQ a ))) (λ x → (g , p))) , cong (λ f → f tt) (snd (Lemma757i→iii (pt-map A) ((pred₋₂ (ℕ→ℕ₋₂ n))) (conOfpt-map A n conA) (λ a → (prelims.Q A B n (zero) conA conB P f g p a , conOfQ a ))) (λ x → (g , p)))

Lemma862 {ℓ = ℓ} {ℓ' = ℓ'} A B n (suc m) conA conB P f g p = (λ a b → ((typesQ (pt A) .fst) a) .fst b) , ((((λ a → sym ((typesQ (pt A)) .fst a .snd)))) , (λ b → cong (λ x → (x .fst) b) (((typesQ) (pt A)) .snd))) , (sym (transpHelper _ _ _ (cong (λ x → x .snd) (((typesQ) (pt A)) .snd))))
  where
  lemma2 : (a : typ A) → isOfHLevel (suc n) (fiber (inducedFun {A = Unit} {B = typ B} {k = (ℕ→ℕ₋₂ (n + (suc m)))} (pt-map B) (P a)) λ tt → (f a))
  lemma2 a = Lemma861GenNats m (suc n) (λ x y → 2+ ℕ→ℕ₋₂ (n + suc m)) (natHelper n m) (pt-map B) (conOfpt-map B (suc m) conB) (P a) λ tt → (f a)
    where
    natHelper : (n m : ℕ) → (2+ ℕ→ℕ₋₂ (n + suc m)) ≡ suc (n + (2+ ℕ→ℕ₋₂ m))
    natHelper zero m = refl
    natHelper (suc n) m = cong (λ x → suc x) (natHelper n m)

  conOfQ : (a : typ A) → isOfHLevel (2+ ((pred₋₂ (ℕ→ℕ₋₂ n)))) (prelims.Q A B n (suc m) conA conB P f g p a)
  conOfQ a = transport (λ i → isOfHLevel (helper n i) (prelims.Q A B n (suc m) conA conB P f g p a) ) (transport (λ i → isOfHLevel (suc n) (prelims.QisFib2 A B n (suc m) conA conB P f g p a (~ i))) (lemma2 a))
    where
    helper : (n : ℕ) → (suc n) ≡ (2+ ((pred₋₂ (ℕ→ℕ₋₂ n)))) 
    helper zero = refl
    helper (suc n) = refl

  typesQ : (a : typ A) → Σ ((a : (typ A)) → (prelims.Q A B n (suc m) conA conB P f g p a)) λ ℓ → ℓ (pt A) ≡ (g , p)
  typesQ a  = (fst (Lemma757i→iii (pt-map A) ((pred₋₂ (ℕ→ℕ₋₂ n))) (conOfpt-map A n conA) (λ a → (prelims.Q A B n (suc m) conA conB P f g p a , conOfQ a ))) (λ x → (g , p))) ,
              cong (λ f → f tt) (snd (Lemma757i→iii (pt-map A) ((pred₋₂ (ℕ→ℕ₋₂ n))) (conOfpt-map A n conA) (λ a → (prelims.Q A B n (suc m) conA conB P f g p a , conOfQ a ))) (λ x → (g , p)))
