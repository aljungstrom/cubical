{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.FreudenthalCleanup.Code where


open import Cubical.ZCohomology.FreudenthalCleanup.Prelim
open import Cubical.ZCohomology.FreudenthalCleanup.7-5-7
open import Cubical.ZCohomology.FreudenthalCleanup.trivFunConnected
open import Cubical.ZCohomology.FreudenthalCleanup.8-6-2
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

σ : A → A → typ (Ω ((Susp A) , north))
σ a x = merid x ∙ sym (merid a)

abstract
  isEquivCancel2 : {a : A} (n : ℕ) (q : north ≡ south) → isEquiv {A = ∥ fiber (λ y → σ a y) (q ∙ sym (merid a)) ∥ ℕ→ℕ₋₂ (n + n)} {B = ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)} (ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣)
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
sufMap2 {A = A} n c a x₂ iscon q = WedgeConn (A , a) (A , a) n n iscon iscon
                                            (λ x₂ c → ((merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n))) ,
                                               isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))
                                            (λ x r → ∣ x , canceller (sym (merid a)) (merid x) q r ∣) (λ x r → ∣ x , switcher (merid a) q (merid x) r ∣) (funExt (λ x i → ∣ (refl i) , ((switcherCancellerIdGeneral (merid a) q (canceller (sym (merid a)) (merid a) q x ) x i) ) ∣)) .fst x₂ c


sufMap2Id : ∀{ℓ} {A : Type ℓ} (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → sufMap2 n x1 a a iscon (merid x1) ≡ λ r → ∣ x1 , switcher (merid a) (merid x1) (merid x1) r ∣
sufMap2Id {A = A} n a x1 iscon = (proj₂ (WedgeConn (A , a) (A , a) n n iscon iscon
                                            (λ x₂ c → ((merid x₂  ∙ sym (merid a)) ≡ ((merid x1) ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ (merid x1)) ∥ (ℕ→ℕ₋₂ (n + n))) ,
                                               isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))
                                            (λ x r → ∣ x , canceller (sym (merid a)) (merid x) (merid x1) r ∣) (λ x r → ∣ x , switcher (merid a) (merid x1) (merid x) r ∣) (funExt (λ x i → ∣ (refl i) , ((switcherCancellerIdGeneral (merid a) (merid x1) (canceller (sym (merid a)) (merid a) (merid x1) x ) x i) ) ∣)) .snd .fst) x1)
-- sufMap2 n x1 a a iscon (merid x1)

sufMap2Id2 : ∀{ℓ} {A : Type ℓ} (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → sufMap2 n a a x1 iscon (merid x1) refl ≡ ∣ x1 , canceller (sym (merid a)) (merid x1) (merid x1) refl ∣
sufMap2Id2 {A = A} n a x1 iscon i = (proj₁ (WedgeConn (A , a) (A , a) n n iscon iscon
                                            (λ x₂ c → ((merid x₂  ∙ sym (merid a)) ≡ ((merid x1) ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ (merid x1)) ∥ (ℕ→ℕ₋₂ (n + n))) ,
                                               isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))
                                            (λ x r → ∣ x , canceller (sym (merid a)) (merid x) (merid x1) r ∣) (λ x r → ∣ x , switcher (merid a) (merid x1) (merid x) r ∣) (funExt (λ x i → ∣ (refl i) , ((switcherCancellerIdGeneral (merid a) (merid x1) (canceller (sym (merid a)) (merid a) (merid x1) x ) x i) ) ∣)) .snd .fst) x1) i
                                            refl




RlFun2 : ∀{ℓ} {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → (q : north ≡ south) →
         (∥ fiber (λ y → σ a y) (q ∙ sym (merid c)) ∥ (ℕ→ℕ₋₂ (n + n))) → 
         ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))
RlFun2 {ℓ} {A} a c n iscon  q = ind (λ x → isOfHLevel∥∥ ((ℕ→ℕ₋₂ (n + n)))) λ r → sufMap2 n c a (fst r) iscon q (snd r)

------------------

RlFunId : ∀{ℓ} {A : Type ℓ} (a : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (q : north ≡ south) (b : fiber (λ y → σ a y) (q ∙ sym (merid a))) → (RlFun2 a a n iscon q ∣ b ∣) ≡ ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b)∣
RlFunId {A = A} a n iscon q b = (cong (λ x → x (snd b)) (proj₁ (((WedgeConn (A , a) (A , a) n n iscon iscon (λ x₂ c → (((merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ (ℕ→ℕ₋₂ (n + n)) ) , isOfHLevelPi (2+ ((ℕ→ℕ₋₂ (n + n)))) λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n)))) (λ x r → ∣ x , canceller (sym (merid a)) (merid x) q r ∣) (λ b s → ∣ b , switcher (merid a) q (merid b) s ∣)  (funExt (λ x → λ j → ∣ (refl j) , (switcherCancellerIdGeneral (merid a) q (canceller (sym (merid a)) (merid a) q x ) x j) ∣  ))) .snd) .fst) (fst b)))

claim2 : ∀{ℓ} {A : Type ℓ} (a : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (q : north ≡ south) → RlFun2 a a n iscon q ≡ ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣
claim2 {A = A} a n iscon q = funExt (ind {B = λ y → RlFun2 a a n iscon q y ≡ (ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣) y } ((λ z y p → (isOfHLevelSuc (suc (n + n)) ((isOfHLevel∥∥ {A = (fiber merid q)} (ℕ→ℕ₋₂ (n + n))) (RlFun2 a a n iscon q z) ((ind (λ _ → isOfHLevel∥∥ (ℕ→ℕ₋₂ (n + n))) λ b → ∣ (fst b) , canceller (sym (merid a)) (merid (fst b)) q (snd b) ∣) z) )) y p  )) λ b → RlFunId a n iscon q b)

baseCase2 : ∀{ℓ} {A : Type ℓ} (a : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (q : north ≡ south) → isEquiv (RlFun2 a a n iscon q)
baseCase2 a n iscon q = transport (λ i → isEquiv (claim2 a n iscon q (~ i))) (isEquivCancel2 n q)

RlFunEquiv2 : {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → (q : north ≡ south) → isEquiv (RlFun2 a c n iscon q)
RlFunEquiv2 {A = A} a c n iscon q = fst (conInd-i→iii {A = Unit} {B = A} (λ x → a) (-1+₋₂ n) (trivFunConnected _ iscon) λ c → (isEquiv (RlFun2 a c n iscon q)) , transport (λ i → isOfHLevel (natHelper2 n i) (isEquiv (RlFun2 a c n iscon q))) (isOfHLevelPlus {A = isEquiv (RlFun2 a c n iscon q)} n (isPropIsEquiv (RlFun2 a c n iscon q)))) (λ t → baseCase2 a n iscon q) c

finalPath :  {A : Type ℓ} (a c : A) (n : ℕ) → (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A)(q : north ≡ south) → (∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)) ≡ (∥ fiber (λ y → σ a y) (q ∙ sym (merid c)) ∥ ℕ→ℕ₋₂ (n + n))
finalPath a c n iscon q = sym (ua ((RlFun2 a c n iscon q) , (RlFunEquiv2 a c n iscon q)))



-- abstract equivTest
abstract
  equivTest : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} (p : x ≡ y) {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'}  →
             ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q) →
             (q : x ≡ x) → transport (λ i₁ → Type ℓ') (A q) ≡ B (transport (λ i → x ≡ p i) q )
  equivTest {ℓ' = ℓ'} {x = x} = J (λ y p → {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} →
                                          ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q) → (q : x ≡ x) → transport (λ i₁ → Type ℓ') (A q) ≡ B (transport (λ i → x ≡ p i) q ) )
                                λ {A} {B} k q → transportRefl (A q) ∙ cong (λ x → A x) (rUnit q) ∙ k q ∙ cong (λ x → B x) (sym (transportRefl q))

  equivTestRefl : ∀ {ℓ ℓ'} {X : Type ℓ} {x : X} {A : x ≡ x → Type ℓ'} {B : x ≡ x → Type ℓ'} → equivTest {X = X} (refl {x = x}) {A = A} {B = B}  ≡ λ k q → transportRefl (A q) ∙ cong (λ x → A x) (rUnit q) ∙ k q ∙ cong (λ x → B x) (sym (transportRefl q)) 
  equivTestRefl {ℓ' = ℓ'} {x = x} {A = A} {B = B} = cong (λ x → x {A} {B}) (JRefl (λ y p → {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} →
                                                    ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q) → (q : x ≡ x) → transport (λ i₁ → Type ℓ') (A q) ≡ B (transport (λ i → x ≡ p i) q ) )
                                λ {A} {B} k q → transportRefl (A q) ∙ cong (λ x → A x) (rUnit q) ∙ k q ∙ cong (λ x → B x) (sym (transportRefl q)))

  ua' : ∀ {A B : Type ℓ} → A ≃ B → A ≡ B
  ua' = ua

  ua'Id : ∀ {A B : Type ℓ} (X : A ≃ B) → ua X ≡ ua' X
  ua'Id X = refl

  ua'Cancel : ∀ {A B : Type ℓ} → (X : A ≃ B) → transport (λ i → ua' X i ) ≡ (fst X)
  ua'Cancel X = funExt λ x → uaβ X x

CODE : ∀{ℓ} {A : Type ℓ} (a : A) (n : ℕ) → is- (ℕ→ℕ₋₂ n) -ConnectedType A → (y : Susp A) → (north ≡ y → Type ℓ)
CODE {A = A} a n iscon north p = (∥ fiber (λ y → σ a y) p ∥ (ℕ→ℕ₋₂ (n + n)))
CODE {ℓ} {A = A} a n iscon south q = ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))
CODE {ℓ} {A = A} a n iscon (merid c i) = toPathP {A = λ i → north ≡ merid c i → Type ℓ} {x = λ p → (∥ fiber (λ y → σ a y) p ∥ (ℕ→ℕ₋₂ (n + n)))}
                                                       {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))}
                                                       (Lemma296-fun {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                         (merid c) (λ p → ∥ fiber (λ y → σ a y) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                                         (equivTest {X = Susp A} (merid c) {A = λ q → ∥ fiber (λ y → σ a y) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                    λ q → (ua' (RlFun2 a c n iscon q , RlFunEquiv2 a c n iscon q)))) i
