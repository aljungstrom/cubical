{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.FreudenthalFix2.Code where


open import Cubical.ZCohomology.FreudenthalFix2.Prelim
open import Cubical.ZCohomology.FreudenthalFix2.7-5-7
open import Cubical.ZCohomology.FreudenthalFix2.trivFunConnected
open import Cubical.ZCohomology.FreudenthalFix2.8-6-2
open import Cubical.Foundations.Everything
open import Cubical.Data.NatMinusTwo.Base renaming (-1+_ to -1+₋₂_)
open import Cubical.Data.Prod
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation

open import Cubical.Data.HomotopyGroup
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

natHelper2 : (n : ℕ) → n + 1 ≡ (2+ (-1+₋₂ n))
natHelper2 zero = refl
natHelper2 (suc n) = cong (λ x → suc x) (natHelper2 n)

helperHelper99 : ∀{ℓ} {A : Type ℓ} {a b c : A} (q : a ≡ b) (p : b ≡ c) →
                      (transport (λ i →  a ≡ (p i)) q) ≡ (q ∙ p)
helperHelper99 {ℓ = ℓ} {A = A} {a = a} {b = b} {c = c} q = J {ℓ} {A} {b}
                                                            (λ c p → (transport (λ i →  a ≡ (p i)) q) ≡ (q ∙ p))
                                                            (transportRefl q ∙ rUnit q)

σ : A → {a : A} → typ (Ω ((Susp A) , north))
σ x {a} = merid x ∙ sym (merid a)

abstract
  isEquivCancel2 : {a : A} (n : ℕ) (q : north ≡ south) → isEquiv {A = ∥ fiber (λ y → σ y {a}) (q ∙ sym (merid a)) ∥ ℕ→ℕ₋₂ (n + n)} {B = ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)} (ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣)
  isEquivCancel2 {a = a} n q = isoToEquiv (iso
                                        ((ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣))
                                        (ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ s → ∣ (fst s) , cancellerInv (λ i → (merid a) (~ i)) (merid (fst s)) q (snd s) ∣)
                                        (λ b → ind {B = λ b → ((ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))
                                                                                        λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣))
                                                              ((ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))
                                                                                        λ s → ∣ (fst s) , cancellerInv (sym (merid a)) (merid (fst s)) q (snd s) ∣) b)
                                                         ≡ b}
                                         (λ x →  isOfHLevelSuc (suc (n + n)) (isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)) _ x)) (λ b i → ∣ fst b , cancellerSection (sym (merid a)) (merid (fst b)) q (snd b) i ∣) b)
                                         (λ b → ind {B = λ b → ((ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))
                                                                                        λ b → ∣ (fst b) , cancellerInv (sym (merid a)) (merid (fst b)) q (snd b) ∣))
                                                                ((ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))
                                                                                        λ s → ∣ (fst s) , canceller (sym (merid a)) (merid (fst s)) q (snd s) ∣) b)
                                                         ≡ b} (λ x → isOfHLevelSuc (suc (n + n)) (isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)) _ x)) (λ b i → ∣ fst b , cancellerRetract (sym (merid a)) (merid (fst b)) q (snd b) i ∣) b)) .snd

------------------


sufMap2 : ∀{ℓ} {A : Type ℓ} (n : ℕ) (c a x₂ : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A)  (q : north ≡ south) → (merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n))
sufMap2 {A = A} n c a x₂ iscon q = Lemma862 (A , a) (A , a) n n iscon iscon
                                            (λ x₂ c → ((merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n))) ,
                                               isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))
                                            (λ x r → ∣ x , canceller (sym (merid a)) (merid x) q r ∣) (λ x r → ∣ x , switcher (merid a) q (merid x) r ∣) (funExt (λ x i → ∣ (refl i) , ((switcherCancellerIdGeneral (merid a) q (canceller (sym (merid a)) (merid a) q x ) x i) ) ∣)) .fst x₂ c


sufMap2Id : ∀{ℓ} {A : Type ℓ} (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → sufMap2 n x1 a a iscon (merid x1) ≡ λ r → ∣ x1 , switcher (merid a) (merid x1) (merid x1) r ∣
sufMap2Id {A = A} n a x1 iscon = (proj₂ (Lemma862 (A , a) (A , a) n n iscon iscon
                                            (λ x₂ c → ((merid x₂  ∙ sym (merid a)) ≡ ((merid x1) ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ (merid x1)) ∥ (ℕ→ℕ₋₂ (n + n))) ,
                                               isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))
                                            (λ x r → ∣ x , canceller (sym (merid a)) (merid x) (merid x1) r ∣) (λ x r → ∣ x , switcher (merid a) (merid x1) (merid x) r ∣) (funExt (λ x i → ∣ (refl i) , ((switcherCancellerIdGeneral (merid a) (merid x1) (canceller (sym (merid a)) (merid a) (merid x1) x ) x i) ) ∣)) .snd .fst) x1)
-- sufMap2 n x1 a a iscon (merid x1)



RlFun2 : ∀{ℓ} {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → (q : north ≡ south) →
         (∥ fiber (λ y → σ y {a}) (q ∙ sym (merid c)) ∥ (ℕ→ℕ₋₂ (n + n))) → 
         ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))
RlFun2 {ℓ} {A} a c n iscon  q = ind (λ x → isOfHLevel∥∥ ((ℕ→ℕ₋₂ (n + n)))) λ r → sufMap2 n c a (fst r) iscon q (snd r)

------------------

RlFunId : ∀{ℓ} {A : Type ℓ} (a : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (q : north ≡ south) (b : fiber (λ y → σ y) (q ∙ sym (merid a))) → (RlFun2 a a n iscon q ∣ b ∣) ≡ ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b)∣
RlFunId {A = A} a n iscon q b = (cong (λ x → x (snd b)) (proj₁ (((Lemma862 (A , a) (A , a) n n iscon iscon (λ x₂ c → (((merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n)) ) , isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))) (λ x r → ∣ x , canceller (sym (merid a)) (merid x) q r ∣) (λ b s → ∣ b , switcher (merid a) q (merid b) s ∣)  (funExt (λ x → λ j → ∣ (refl j) , (switcherCancellerIdGeneral (merid a) q (canceller (sym (merid a)) (merid a) q x ) x j) ∣  ))) .snd) .fst) (fst b)))

claim2 : ∀{ℓ} {A : Type ℓ} (a : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (q : north ≡ south) → RlFun2 a a n iscon q ≡ ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣
claim2 {A = A} a n iscon q = funExt (ind {B = λ y → RlFun2 a a n iscon q y ≡ (ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣) y } ((λ z y p → (isOfHLevelSuc (suc (n + n)) ((isOfHLevel∥∥ {A = (fiber merid q)} (ℕ→ℕ₋₂ (n + n))) (RlFun2 a a n iscon q z) ((ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣) z) )) y p  )) λ b → RlFunId a n iscon q b)

baseCase2 : ∀{ℓ} {A : Type ℓ} (a : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (q : north ≡ south) → isEquiv (RlFun2 a a n iscon q)
baseCase2 a n iscon q = transport (λ i → isEquiv (claim2 a n iscon q (~ i))) (isEquivCancel2 n q)

RlFunEquiv2 : {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → (q : north ≡ south) → isEquiv (RlFun2 a c n iscon q)
RlFunEquiv2 {A = A} a c n iscon q = fst (Lemma757i→iii {A = Unit} {B = A} (λ x → a) (-1+₋₂ n) (trivFunConnected _ iscon) λ c → (isEquiv (RlFun2 a c n iscon q)) , transport (λ i → isOfHLevel (natHelper2 n i) (isEquiv (RlFun2 a c n iscon q))) (isOfHLevelPlus {A = isEquiv (RlFun2 a c n iscon q)} n (isPropIsEquiv (RlFun2 a c n iscon q)))) (λ t → baseCase2 a n iscon q) c

finalPath :  {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A)(q : north ≡ south) → (∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)) ≡ (∥ fiber (λ y → σ y) (q ∙ sym (merid c)) ∥ ℕ→ℕ₋₂ (n + n))
finalPath a c n iscon q = sym (ua ((RlFun2 a c n iscon q) , (RlFunEquiv2 a c n iscon q)))

----------------

transpId2 : {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
            (transport (λ i₁ → north ≡ merid c i₁ → Type ℓ) (λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))) ≡ (λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))))
            ≡
            ((q : north ≡ south) → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n)) ≡ (∥ fiber (λ y → σ y {a}) (q ∙ sym (merid c)) ∥ (ℕ→ℕ₋₂ (n + n))))
transpId2 {ℓ = ℓ} {A = A} a c n iscon = (Lemma296b2 {A = λ x → north ≡ x} {B = λ _ → Type ℓ} (merid c) (λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))) ((λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))))) ∙ (λ i → ((q : north ≡ south) → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n)) ≡ (∥ fiber (λ y → σ y {a}) (helperHelper99 q (sym (merid c)) i) ∥ (ℕ→ℕ₋₂ (n + n)))))


---------------

toPathP2 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y : A} (p : x ≡ y) (z : B x) (s : B y) → transport (λ i → B (p i)) z ≡ s → PathP (λ i → B (p i)) z s
toPathP2 {A = A} {B = B} {x = x} {y = y} = (J (λ y p → (z : B x) (s : B y) → transport (λ i → B (p i)) z ≡ s → PathP (λ i → B (p i)) z s) λ z s id → sym (transportRefl z) ∙ id)

finalPathP : {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → PathP (λ i → north ≡ merid c i → Type ℓ) (λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))) (λ q →  ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n)))
finalPathP {ℓ = ℓ} {A = A} a c n iscon = toPathP {A = λ i → north ≡ merid c i → Type ℓ} ((transp (λ i → transpId2 a c n iscon (~ i )) i0 (finalPath a c n iscon)))


-----------

{-
claim :  (q : north ≡ south) → RlFun {c = a} q ≡ ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣
      claim q = funExt (ind {B = λ y → RlFun {c = a} q y ≡ (ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣) y } ((λ z y p → (isOfHLevelSuc (suc (n + n)) ((isOfHLevel∥∥ {A = (fiber merid q)} (ℕ→ℕ₋₂ (n + n))) (RlFun {c = a} q z) ((ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣) z) )) y p  )) λ b → RlFunId2 q b)
        where
        
          RlFunId2 : (q : north ≡ south) (b : fiber (λ y → σ y) (q ∙ sym (merid a))) → (RlFun {c = a} q ∣ b ∣) ≡ ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b)∣
          RlFunId2 q b = (cong (λ x → x (snd b)) (proj₁ (((Lemma862 (A , a) (A , a) n n iscon iscon (λ x₂ c → (((merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n)) ) , isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))) (λ x r → ∣ x , canceller (sym (merid a)) (merid x) q r ∣) (λ b s → ∣ b , switcher (merid a) q (merid b) s ∣)  (funExt (λ x → λ j → ∣ (refl j) , (switcherCancellerIdGeneral (merid a) q (canceller (sym (merid a)) (merid a) q x ) x j) ∣  ))) .snd) .fst) (fst b)))



      RlFunEquiv : {c : A} → (q : north ≡ south) → isEquiv (RlFun {c = c} q)
      RlFunEquiv {c = c} q = fst (Lemma757i→iii {A = Unit} {B = A} (λ x → a) (-1+₋₂ n) (trivFunConnected _ iscon) λ a → (isEquiv (RlFun {c = a} q)) , transport (λ i → isOfHLevel (natHelper n i) (isEquiv (RlFun {c = a} q))) (isOfHLevelPlus {A = isEquiv (RlFun {c = a} q)} n (isPropIsEquiv (RlFun {c = a} q)))) (λ t → baseCase) c
          where
          baseCase : isEquiv (RlFun {c = a} q)
          baseCase = transport (λ i → isEquiv (claim q (~ i))) (isEquivCancel2 n q)

          natHelper : (n : ℕ) → n + 1 ≡ (2+ (-1+₋₂ n))
          natHelper zero = refl
          natHelper (suc n) = cong (λ x → suc x) (natHelper n)
-}

------------------

code : ∀{ℓ} {A : Type ℓ} {a : A} (n : ℕ) → is- (ℕ→ℕ₋₂ n) -ConnectedType A → (y : Susp A) → (north ≡ y → Type ℓ)
code {A = A} {a = a} n iscon north p = (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))
code {ℓ} {A = A} {a = a} n iscon south q = ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))
code {ℓ} {A = A} {a = a} n iscon (merid c i) = finalPathP a c n iscon i --  pathToConstruct i

------------------
-- abstract experiment

abstract
  RlFun2' : ∀{ℓ} {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → (q : north ≡ south) →
           (∥ fiber (λ y → σ y {a}) (q ∙ sym (merid c)) ∥ (ℕ→ℕ₋₂ (n + n))) → 
           ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))
  RlFun2' {ℓ} {A} a c n iscon  q = ind (λ x → isOfHLevel∥∥ ((ℕ→ℕ₋₂ (n + n)))) λ r → sufMap2 n c a (fst r) iscon q (snd r)
  
  
  RlFun2'≡RlFun2 : ∀{ℓ} {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → RlFun2' a c n iscon ≡ RlFun2 a c n iscon
  RlFunEquiv' : {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → (q : north ≡ south) → isEquiv (RlFun2' a c n iscon q)
  RlFunEquiv'≡RlFunEquiv2 : {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → (q : north ≡ south) → _≡_ {A = ∥ fiber (λ y → σ y) (q ∙ sym (merid c)) ∥ ℕ→ℕ₋₂ (n + n) ≃ ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)} (RlFun2' a c n iscon q , RlFunEquiv' a c n iscon q) (RlFun2 a c n iscon q , RlFunEquiv2 a c n iscon q)
  
  RlFunEquiv' a c n iscon q = transport (λ i → isEquiv ((RlFun2'≡RlFun2 a c n iscon i) q) ) (RlFunEquiv2 a c n iscon q)
  RlFun2'≡RlFun2 a c n iscon = refl
  RlFunEquiv'≡RlFunEquiv2 a c n iscon q i = (RlFun2'≡RlFun2 a c n iscon i) q , transportRefl (RlFunEquiv2 a c n iscon q) i

finalPath' :  {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A)(q : north ≡ south) → (∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)) ≡ (∥ fiber (λ y → σ y {a}) (q ∙ sym (merid c)) ∥ ℕ→ℕ₋₂ (n + n))
finalPath' a c n iscon q = sym (ua ((RlFun2' a c n iscon q) , (RlFunEquiv' a c n iscon q)))

finalPathP' : {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → PathP (λ i → north ≡ merid c i → Type ℓ) (λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))) (λ q →  ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n)))
finalPathP' {ℓ = ℓ} {A = A} a c n iscon = toPathP {A = λ i → north ≡ merid c i → Type ℓ} ((transp (λ i → transpId2 a c n iscon (~ i )) i0 (finalPath' a c n iscon)))

code≡code' : ∀{ℓ} {A : Type ℓ} {a : A} (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (x : A) (i : I) → code {a = a} n iscon (merid x i) ≡ toPathP {A = λ i → north ≡ merid x i → Type ℓ} {x = λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))} {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))} ((transport (λ i → transpId2 {ℓ} {A = A} a x n iscon (~ i )) λ q → sym (ua ((RlFun2' {A = A} a x n iscon q) , RlFunEquiv' {A = A} a x n iscon q)))) i
code≡code' {ℓ = ℓ}{A = A}{a = a} n iscon x i j = toPathP {A = λ i → north ≡ merid x i → Type ℓ} {x = λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))} {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))} (transport (λ i → transpId2 a x n iscon (~ i )) (λ q → sym (ua (RlFunEquiv'≡RlFunEquiv2 a x n iscon q (~ j) )))) i

code' : ∀{ℓ} {A : Type ℓ} {a : A} (n : ℕ) → is- (ℕ→ℕ₋₂ n) -ConnectedType A → (y : Susp A) → (north ≡ y → Type ℓ)
code' {A = A} {a = a} n iscon north p = (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))
code' {ℓ} {A = A} {a = a} n iscon south q = ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))
code' {ℓ} {A = A} {a = a} n iscon (merid c i) = finalPathP' a c n iscon i

codeId : ∀{ℓ} {A : Type ℓ} {a : A} (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → code {a = a} n iscon ≡ code' {a = a} n iscon
codeId {ℓ} {A = A} {a = a} n iscon = funExt λ y → helper y
    where
    helper : (y : Susp A) → code {a = a} n iscon y ≡ code' {a = a} n iscon y
    helper north = refl
    helper south = refl
    helper (merid x i) = code≡code' {a = a} n iscon x i


equivTest : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} (p : x ≡ y) {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'}  →
           ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q) →
           (q : x ≡ x) → transport (λ i₁ → Type ℓ') (A q) ≡ B (transport (λ i → x ≡ p i) q )
equivTest {ℓ' = ℓ'} {x = x} = J (λ y p → {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} →
                                        ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q) → (q : x ≡ x) → transport (λ i₁ → Type ℓ') (A q) ≡ B (transport (λ i → x ≡ p i) q ) )
                              λ {A} {B} k q → transportRefl (A q) ∙ cong (λ x → A x) (rUnit q) ∙ k q ∙ cong (λ x → B x) (sym (transportRefl q))

equivTestRefl : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} (p : x ≡ y) {A : x ≡ x → Type ℓ'} {B : x ≡ x → Type ℓ'} → equivTest {X = X} (refl {x = x}) {A = A} {B = B}  ≡ λ k q → transportRefl (A q) ∙ cong (λ x → A x) (rUnit q) ∙ k q ∙ cong (λ x → B x) (sym (transportRefl q)) 
equivTestRefl {ℓ' = ℓ'} {x = x} p {A = A} {B = B} = cong (λ x → x {A} {B}) (JRefl (λ y p → {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} →
                                                  ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q) → (q : x ≡ x) → transport (λ i₁ → Type ℓ') (A q) ≡ B (transport (λ i → x ≡ p i) q ) )
                              λ {A} {B} k q → transportRefl (A q) ∙ cong (λ x → A x) (rUnit q) ∙ k q ∙ cong (λ x → B x) (sym (transportRefl q)))

-- abstract equivTest
abstract
  equivTest' : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} (p : x ≡ y) {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'}  →
           ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q) →
           (q : x ≡ x) → transport (λ i₁ → Type ℓ') (A q) ≡ B (transport (λ i → x ≡ p i) q )
  equivTest'  {x = x} {y = y} = equivTest {x = x} {y = y}
  equivTestId : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} (p : x ≡ y) {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'}  →
           (r : ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q)) →
           equivTest' {x = x}  p {A = A} {B = B} r ≡ equivTest {x = x} p {A = A} {B = B} r
  equivTestId p r = refl




CODE : ∀{ℓ} {A : Type ℓ} {a : A} (n : ℕ) → is- (ℕ→ℕ₋₂ n) -ConnectedType A → (y : Susp A) → (north ≡ y → Type ℓ)
CODE {A = A} {a = a} n iscon north p = (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))
CODE {ℓ} {A = A} {a = a} n iscon south q = ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))
CODE {ℓ} {A = A} {a = a} n iscon (merid c i) = toPathP {A = λ i → north ≡ merid c i → Type ℓ} {x = λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))}
                                                       {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))}
                                                       (Lemma296Funs.inv {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                         (merid c) (λ p → ∥ fiber (λ y → σ y) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (equivTest {X = Susp A} (merid c) {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    λ q → (ua (RlFun2 a c n iscon q , RlFunEquiv2 a c n iscon q)))) i -- ua (RlFun2 a c n iscon (merid c) , RlFunEquiv2 a c n iscon (merid c)) ) i

--- abstract stuff
abstract
  ua' : ∀ {A B : Type ℓ} → A ≃ B → A ≡ B
  ua' = ua

  ua'Id : ∀ {A B : Type ℓ} (X : A ≃ B) → ua X ≡ ua' X
  ua'Id X = refl

  ua'Cancel : ∀ {A B : Type ℓ} → (X : A ≃ B) → transport (λ i → ua' X i ) ≡ (fst X)
  ua'Cancel X = funExt λ x → uaβ X x


CODE' : ∀{ℓ} {A : Type ℓ} {a : A} (n : ℕ) → is- (ℕ→ℕ₋₂ n) -ConnectedType A → (y : Susp A) → (north ≡ y → Type ℓ)
CODE' {A = A} {a = a} n iscon north p = (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))
CODE' {ℓ} {A = A} {a = a} n iscon south q = ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))
CODE' {ℓ} {A = A} {a = a} n iscon (merid c i) = toPathP {A = λ i → north ≡ merid c i → Type ℓ} {x = λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))}
                                                       {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))}
                                                       (Lemma296Funs.inv {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                         (merid c) (λ p → ∥ fiber (λ y → σ y) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (equivTest {X = Susp A} (merid c) {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    λ q → (ua' (RlFun2 a c n iscon q , RlFunEquiv2 a c n iscon q)))) i
                                                                                    
CODEId : ∀{ℓ} {A : Type ℓ} {a : A} (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → CODE {a = a} n iscon ≡ CODE' {a = a} n iscon 
CODEId {ℓ = ℓ} {A = A} {a = a} n iscon  = funExt helper
  where
  helper : (x : Susp A) → CODE {a = a} n iscon x ≡ CODE' {a = a} n iscon x
  helper north = refl
  helper south = refl
  helper (merid c i) = λ j → toPathP {A = λ i → north ≡ merid c i → Type ℓ} {x = λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))}
                                                       {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))}
                                                       (Lemma296Funs.inv {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                         (merid c) (λ p → ∥ fiber (λ y → σ y) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (equivTest {X = Susp A} (merid c) {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    λ q → (ua'Id (RlFun2 a c n iscon q , RlFunEquiv2 a c n iscon q)) j)) i



CODE'' : ∀{ℓ} {A : Type ℓ} {a : A} (n : ℕ) → is- (ℕ→ℕ₋₂ n) -ConnectedType A → (y : Susp A) → (north ≡ y → Type ℓ)
CODE'' {A = A} {a = a} n iscon north p = (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))
CODE'' {ℓ} {A = A} {a = a} n iscon south q = ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))
CODE'' {ℓ} {A = A} {a = a} n iscon (merid c i) = toPathP {A = λ i → north ≡ merid c i → Type ℓ} {x = λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))}
                                                       {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))}
                                                       (Lemma296Funs.inv'' {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                         (merid c) (λ p → ∥ fiber (λ y → σ y) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (equivTest' {X = Susp A} (merid c) {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    λ q → (ua' (RlFun2 a c n iscon q , RlFunEquiv2 a c n iscon q)))) i
CODE''Id : ∀{ℓ} {A : Type ℓ} {a : A} (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → CODE' {a = a} n iscon ≡ CODE'' {a = a} n iscon
CODE''Id {ℓ = ℓ} {A = A}{a = a} n iscon = funExt helper
  where
  helper : (x : Susp A) → CODE' {a = a} n iscon x ≡ CODE'' {a = a} n iscon x
  helper north = refl
  helper south = refl
  helper (merid c i) j = toPathP {A = λ i → north ≡ merid c i → Type ℓ} {x = λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))}
                                                       {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))}
                                                       ((Lemma296Funs.inv''Id {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                         (merid c) (λ p → ∥ fiber (λ y → σ y) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)) j )
                                                                         ((equivTestId {X = Susp A} (merid c) {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    λ q → (ua' (RlFun2 a c n iscon q , RlFunEquiv2 a c n iscon q))) (~ j)) ) i



{- (transport (λ j → ((Lemma296b2 {A = λ x → north ≡ x} {B = λ _ → Type ℓ} (merid c) (λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))) ((λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n)))))) (~ j)) (transport ((λ i → ((q : north ≡ south) → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n)) ≡ (∥ fiber (λ y → σ y {a}) (helperHelper99 q (sym (merid c)) (~ i)) ∥ (ℕ→ℕ₋₂ (n + n)))))) λ g → sym ((ua ((RlFun2' a c n iscon g) , RlFunEquiv' a c n iscon g))))) i --  (transport (λ i → transpId2 a c n iscon (~ i )) (λ q → sym (ua ((RlFun2' a c n iscon q) , RlFunEquiv' a c n iscon q)))) i -}
{-
codeId : ∀{ℓ} {A : Type ℓ} {a : A} (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → code {a = a} n iscon ≡ code' {a = a} n iscon
codeId {ℓ} {A = A} {a = a} n iscon = funExt λ y → helper y
  where
    helper : (y : Susp A) → code {a = a} n iscon y ≡ code' {a = a} n iscon y
    helper north = refl
    helper south = refl
    helper (merid x i) = λ j → toPathP {A = λ i → north ≡ merid x i → Type ℓ} {x = λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))} {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))} (transport (λ i → transpId2 a x n iscon (~ i )) (λ q → sym (ua (RlFunEquiv'≡RlFunEquiv2 a x n iscon q (~ j) )))) i
-}


  {-
  where
  pathToConstruct : PathP (λ i → north ≡ merid c i → Type ℓ) (code {a = a} n iscon north) (code {a = a} n iscon south)
  pathToConstruct = toPathP (transport (λ i → transpId (~ i)) λ q → sym (ua ((RlFun2 a c n iscon q) , (RlFunEquiv q))))
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

      
      sufMap* : (c a x₂ : A) (q : north ≡ south) → (merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n))
      sufMap* c a x₂ q = Lemma862 (A , a) (A , a) n n iscon iscon (λ x₂ c → ((merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n))) , isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) (λ x r → ∣ x , canceller (sym (merid a)) (merid x) q r ∣) (λ x r → ∣ x , switcher (merid a) q (merid x) r ∣) (funExt (λ x i → ∣ (refl i) , ((switcherCancellerIdGeneral (merid a) q (canceller (sym (merid a)) (merid a) q x ) x i) ) ∣)) .fst x₂ c


      RlFun :  {c : A} (q : north ≡ south) → code {a = a} n iscon north (q ∙ sym (merid c)) → code {a = a} n iscon south q
      RlFun  {c = c} q  = ind (λ x → isOfHLevel∥∥ ((ℕ→ℕ₋₂ (n + n)))) λ r → sufMap* c a (fst r) q (snd r) -- (funHelper a) x


      claim : (q : north ≡ south) → RlFun {c = a} q ≡ ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣
      claim q = funExt (ind {B = λ y → RlFun {c = a} q y ≡ (ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣) y } ((λ z y p → (isOfHLevelSuc (suc (n + n)) ((isOfHLevel∥∥ {A = (fiber merid q)} (ℕ→ℕ₋₂ (n + n))) (RlFun {c = a} q z) ((ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣) z) )) y p  )) λ b → RlFunId2 q b)
        where
        
          RlFunId2 : (q : north ≡ south) (b : fiber (λ y → σ y) (q ∙ sym (merid a))) → (RlFun {c = a} q ∣ b ∣) ≡ ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b)∣
          RlFunId2 q b = (cong (λ x → x (snd b)) (proj₁ (((Lemma862 (A , a) (A , a) n n iscon iscon (λ x₂ c → (((merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n)) ) , isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))) (λ x r → ∣ x , canceller (sym (merid a)) (merid x) q r ∣) (λ b s → ∣ b , switcher (merid a) q (merid b) s ∣)  (funExt (λ x → λ j → ∣ (refl j) , (switcherCancellerIdGeneral (merid a) q (canceller (sym (merid a)) (merid a) q x ) x j) ∣  ))) .snd) .fst) (fst b)))



      RlFunEquiv : {c : A} → (q : north ≡ south) → isEquiv (RlFun {c = c} q)
      RlFunEquiv {c = c} q = fst (Lemma757i→iii {A = Unit} {B = A} (λ x → a) (-1+₋₂ n) (trivFunConnected _ iscon) λ a → (isEquiv (RlFun {c = a} q)) , transport (λ i → isOfHLevel (natHelper n i) (isEquiv (RlFun {c = a} q))) (isOfHLevelPlus {A = isEquiv (RlFun {c = a} q)} n (isPropIsEquiv (RlFun {c = a} q)))) (λ t → baseCase) c
          where
          baseCase : isEquiv (RlFun {c = a} q)
          baseCase = transport (λ i → isEquiv (claim q (~ i))) (isEquivCancel2 n q)

          natHelper : (n : ℕ) → n + 1 ≡ (2+ (-1+₋₂ n))
          natHelper zero = refl
          natHelper (suc n) = cong (λ x → suc x) (natHelper n)
  -}
