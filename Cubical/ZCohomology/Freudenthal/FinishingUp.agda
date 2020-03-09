{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Freudenthal.FinishingUp where


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Freudenthal.Prelim
open import Cubical.ZCohomology.Freudenthal.7-5-7
open import Cubical.ZCohomology.Freudenthal.trivFunConnected
open import Cubical.ZCohomology.Freudenthal.8-6-1
open import Cubical.ZCohomology.Freudenthal.8-6-2
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.NatMinusTwo.Base renaming (-1+_ to -1+₋₂_ ; 1+_ to 1+₋₂_)
open import Cubical.Data.NatMinusOne.Base
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

σ : A → {a : A} → typ (Ω ((Susp A) , north))
σ x {a} = merid x ∙ sym (merid a)


code : ∀{ℓ} {A : Type ℓ} {a : A} (n : ℕ) → is- (ℕ→ℕ₋₂ n) -ConnectedType A → (y : Susp A) → (north ≡ y → Type ℓ)
code {A = A} {a = a} n iscon north p = (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))
code {ℓ} {A = A} {a = a} n iscon south q = ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))
code {ℓ} {A = A} {a = a} n iscon (merid c i) = pathToConstruct i where
  pathToConstruct : PathP (λ i → north ≡ merid c i → Type ℓ) (code {a = a} n iscon north) (code {a = a} n iscon south)
  pathToConstruct = toPathP (transport (λ i → transpId (~ i)) λ q → sym (ua ((RlFun q) , (RlFunEquiv q))))
    where

    transpId : (transport (λ i₁ → north ≡ merid c i₁ → Type ℓ) (code {a = a} n iscon north) ≡ code {a = a} n iscon south) ≡
                ((q : north ≡ south) → (code {a = a} n iscon south q) ≡ (code {a = a} n iscon north (q ∙ sym (merid c))))
    transpId = (transport (λ i₁ → north ≡ merid c i₁ → Type ℓ) (code {a = a} n iscon north) ≡ code {a = a} n iscon south)
                             ≡⟨ Lemma296b {A = λ x → north ≡ x} {B = λ _ → Type ℓ} (merid c) (code {a = a} n iscon north) (code {a = a} n iscon south) ⟩
                          ((q : north ≡ south) → code {a = a} n iscon south q ≡ code {a = a} n iscon north (transport (λ i →  north ≡ (merid c (~ i))) q))
                             ≡⟨ (λ i → ((q : north ≡ south) → code {a = a} n iscon south q ≡ code {a = a} n iscon north (helper q (sym (merid c)) i))) ⟩
                          ((q : north ≡ south) → (code {a = a} n iscon south q) ≡ (code {a = a} n iscon north (q ∙ sym (merid c)))) ∎
                          
      where
      helper : ∀{ℓ} {A : Type ℓ} {a b c : A} (q : a ≡ b) (p : b ≡ c) →
                    (transport (λ i →  a ≡ (p i)) q) ≡ (q ∙ p)
      helper {ℓ = ℓ} {A = A} {a = a} {b = b} {c = c} q = J {ℓ} {A} {b}
                                                          (λ c p → (transport (λ i →  a ≡ (p i)) q) ≡ (q ∙ p))
                                                          (transportRefl q ∙ rUnit q)

    
    mutual
    RlFun :  {c : A} (q : north ≡ south) → code {a = a} n iscon north (q ∙ sym (merid c)) → code {a = a} n iscon south q
    claim : (q : north ≡ south) → RlFun {c = a} q ≡ ind (λ _ → isOfHLevel∥∥ _) λ b → ∣ (fst b) , canceller (merid (fst b)) q (sym (merid a)) (snd b)    ∣
    claim q = funExt λ x → ind {B = λ x → RlFun {c = a} q x ≡ ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) (λ b → ∣ fst b , canceller (merid (fst b)) q (sym (merid a)) (snd b) ∣) x} {!!} (λ x i → {! x!}) x
    RlFun  {c = c} q x  = (funHelper a) x
      where
        funHelper :  (a : A) → (∥ Σ A (λ x₁ → merid x₁ ∙ (λ i₁ → merid a (~ i₁)) ≡ q ∙ sym (merid c)) ∥ (ℕ→ℕ₋₂ (n + n))) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n))
        funHelper a = ind (λ x → isOfHLevel∥∥ _) λ r → sufMap (fst r) (snd r)
          where

          sufMap : (x₂ : A) → (merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n))
          sufMap x₂  = fst (Lemma862 (A , a) (A , a) n n iscon iscon (λ x₂ c → (((merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n)) ) , isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevel∥∥ _)) firstFun secondFun  (funExt (λ x → λ j → ∣ (refl j) , (maybe (merid a) q (canceller (merid a) q (sym (merid a)) x ) x j) ∣  ))) x₂ c
            where

            

            firstFun : (a₁ : A) → merid a₁ ∙ (λ i₁ → merid a (~ i₁)) ≡ q ∙ (λ i₁ → merid (pt (A , a)) (~ i₁)) → ∥ Σ A (λ x₁ → merid x₁ ≡ q) ∥ (ℕ→ℕ₋₂ (n + n))
            firstFun x r = ∣ x , canceller (merid x) q (sym (merid a)) r ∣
        
          {-J {ℓ} {A} {b} (λ d r → ((p ∙ r) ≡ (q ∙ r)) ≡ (p ≡ q)) λ i → sym (rUnit p) i ≡ sym (rUnit q) i-}
            secondFun : (b : typ (A , a)) → merid (pt (A , a)) ∙ (λ i₁ → merid a (~ i₁)) ≡ q ∙ (λ i₁ → merid b (~ i₁)) → ∥ Σ A (λ x₁ → merid x₁ ≡ q) ∥ (ℕ→ℕ₋₂ (n + n))
            secondFun b s = ∣ b , switcher (merid a) q (merid b) s ∣

            maybe : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p q : a ≡ b) → (p ≡ q) → (P : p ∙ (sym p) ≡ q ∙ (sym p)) → canceller p q (sym p) P ≡ switcher p q p P
            maybe {ℓ} {A} {a} {b} p q = J {ℓ} {a ≡ b} {p} (λ q _ → (P : p ∙ (sym p) ≡ q ∙ (sym p)) → canceller p q (sym p) P ≡ switcher p q p P) (J {ℓ} {A} {a} (λ b p → (P : p ∙ (sym p) ≡ p ∙ (sym p)) → canceller p p (sym p) P ≡ switcher p p p P) (λ P → switcherCancellerId P) p)
        

    RlFunEquiv : {c : A} → (q : north ≡ south) → isEquiv (RlFun {c = c} q)
    RlFunEquiv {c = c} q = fst (Lemma757i→iii {A = Unit} {B = A} (λ x → a) (ℕ→ℕ₋₂ n) (λ b → {!fst iscon!} , {!!}) (λ a → ((isEquiv (RlFun {c = a} q)) , {!!} ))) (λ t → baseCase) c where
        baseCase : isEquiv (RlFun {c = a} q)
        baseCase = snd (isoToEquiv (iso (RlFun {c = a} q) (ind (λ _ → isOfHLevel∥∥ _) λ a → {!!}) {!!} {!!}))

        
        
        isCona₀ : is- {!!} -Connected (λ (x₁ : Unit) → a)
        isCona₀ = λ b → {!!} , {!!}


Lemma8610 : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a2) → transport (λ i → {!uncurry C ?!}) {!!} ≡ {!(ua ?)!}
Lemma8610 = {!!}

Thm864 : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) {y : Susp A} → (p : north ≡ y) → isContr (code {a = a} n iscon y p)
Thm864 {ℓ} {A} n a iscon =  J {ℓ} {Susp A} {north} (λ y p → (isContr (code {a = a} n iscon y p))) (∣ a , (rCancel _) ∣ , (λ y → {!refl!}))  where
  center : {!!}
  center = {!!}

Freudenthal : (n : ℕ) (A : Pointed ℓ) → is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A) → ∥ typ A ∥ (ℕ→ℕ₋₂ (n + n)) ≡ ∥ typ (Ω (Susp (typ A) , north)) ∥ ((ℕ→ℕ₋₂ (n + n)))
Freudenthal n A isCon = ua ({!!} , {!Lemma757i→ii ? ? ? ?!})
