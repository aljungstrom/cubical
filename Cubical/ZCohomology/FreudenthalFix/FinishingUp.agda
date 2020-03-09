{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.FreudenthalFix.FinishingUp where


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.FreudenthalFix.Prelim
open import Cubical.ZCohomology.FreudenthalFix.7-5-7
open import Cubical.ZCohomology.FreudenthalFix.trivFunConnected
open import Cubical.ZCohomology.FreudenthalFix.8-6-1
open import Cubical.ZCohomology.FreudenthalFix.8-6-2
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.NatMinusTwo.Base renaming (-1+_ to -1+₋₂_ ; 1+_ to 1+₋₂_)
open import Cubical.Data.NatMinusOne.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Prod
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

pair⁼ : ∀ {ℓ'} {B : A → Type ℓ'} {x y : Σ A (λ a → B a)} → (p : fst x ≡ fst y) → transport (λ i → B (p i)) (snd x) ≡ (snd y) → x ≡ y 
pair⁼ {x = x} {y = y} p p2 = sigmaPath→pathSigma x y (p , p2)

σ : A → {a : A} → typ (Ω ((Susp A) , north))
σ x {a} = merid x ∙ sym (merid a)

substComposite-∙ : ∀ {ℓ ℓ′} {A : Type ℓ} → (B : A → Type ℓ′)
                     → {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : B x)
                     → subst B (p ∙ q) u ≡ subst B q (subst B p u)
substComposite-∙ {A = A} B p q u = transport (λ i → subst B (□≡∙ p q i) u ≡ subst B q (subst B p u)) (substComposite-□ B p q u)


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


Lemma8610 : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a2) → transport ((λ i → uncurry C (pair⁼ p (transportTransport⁻ (λ i → B (p i)) b) i) )) ≡ {!univalence {A = ?} {B = ?} .fst !} 
Lemma8610 = {!!}
  where


module test (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) where
  pairLemma2 : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → transport (λ i → a ≡ p i) refl ≡ p
  pairLemma2 {ℓ} {A} {a} = J (λ b p →  transport (λ i → a ≡ p i) refl ≡ p) (transportRefl refl)
  abstract
    c : (y : (Susp A)) (p : north ≡ y) → code {a = a} n iscon y p
    c y p = transport (λ i → (uncurry (code {a = a} n iscon) (pair⁼ p (pairLemma2 p) i))) ∣ a , (rCancel _) ∣

  reflCase2 : (x1 : A) → c north (σ x1) ≡ ∣ x1 , refl ∣
  reflCase2 x1 = (transport (λ i → (uncurry (code {a = a} n iscon) (pair⁼ (merid x1 ∙ (sym (merid a))) (pairLemma2 (merid x1 ∙ (sym (merid a)))) i))) ∣ a , (rCancel _) ∣) ≡⟨ ? ⟩ ?

  mainId : (p : north ≡ north) (d : code {a = a} n iscon north p) →
           d ≡ c north p
  mainId p = ind {!!} base
    where
    base : (x : fiber (λ y → σ y) p) → ∣ x ∣ ≡ c north p
    base (x1 , r) = J (λ p r → ∣ x1 , r ∣ ≡ c north p) (sym reflCase) r
      where
      reflCase  : c north (σ x1) ≡ ∣ x1 , refl ∣
      reflCase = c north (σ x1)
                   ≡⟨ {!!} ⟩
                 transport (λ i → uncurry (code {a = a} n iscon) (pair⁼ (sym (merid a)) ({!!}) i) ) (transport (λ i → uncurry (code {a = a} n iscon) (pair⁼ (merid a) ({!!}) i) ) ∣ a , (rCancel _) ∣) ≡⟨ {!uncurry (code {a = a} n iscon) !} ⟩
                 transport (λ i → uncurry (code {a = a} n iscon) (pair⁼ (sym (merid a)) {!pairLemma2 p!} i)) {!!}
                 ≡⟨ {!!} ⟩
                 {!!}
       where
       pairLemma3 : ∀ {ℓ} {A : Type ℓ} {a1 b : A} (p : a1 ≡ b) (q : b ≡ a1) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q
       pairLemma3 {a1 = a1} = J (λ b p → (q : b ≡ a1) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q) λ q → pairLemma2 q ∙ lUnit q

       functTransp : ∀ {ℓ ℓ'} {A : Type ℓ} {a1 b : A} {C : Σ A (λ b → a1 ≡ b) → Type ℓ' } (p : a1 ≡ b) (q : b ≡ a1) → transport (λ i → C (pair⁼ (p ∙ q) (pairLemma2 (p ∙ q)) i) ) ≡ λ x → transport (λ i → C (pair⁼ q ((pairLemma3 p q)) i)) (transport (λ i → C (pair⁼ p (pairLemma2 p) i)) x)
       functTransp {a1 = a1} {b = b} {C = C} = J (λ b p → (q : b ≡ a1) → transport (λ i → C (pair⁼ (p ∙ q) (pairLemma2 (p ∙ q)) i) ) ≡ λ x → transport (λ i → C (pair⁼ q ((pairLemma3 p q)) i)) (transport (λ i → C (pair⁼ p (pairLemma2 p) i)) x)) λ q → funExt λ x → {!!} ∙ (substComposite-∙ C (pair⁼ refl (pairLemma2 refl)) (pair⁼ q (pairLemma3 refl q)) x)
         where
           helper : (q : a1 ≡ a1) → pair⁼ (refl ∙ q) (pairLemma2 (refl ∙ q)) ≡ (pair⁼ (λ _ → a1) (pairLemma2 (λ _ → a1)) ∙ pair⁼ q (pairLemma3 (λ _ → a1) q))
           helper q = {!(λ i → pair⁼ (lUnit q (~ i)) (pairLemma2 (lUnit q (~ i)))) ∙ ?!}

  test2 : (x : A) → transport (λ i → (uncurry (code {a = a} n iscon) (pair⁼ (merid x ∙ (sym (merid a))) (pairLemma2 (merid x ∙ (sym (merid a)))) i))) ∣ a , (rCancel _) ∣ ≡ {!!}
  test2 = {!!}


Thm864 : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) {y : Susp A} → (p : north ≡ y) → isContr (code {a = a} n iscon y p)
Thm864 {ℓ} {A} n a iscon =  J {ℓ} {Susp A} {north} (λ y p → (isContr (code {a = a} n iscon y p))) (∣ a , (rCancel _) ∣ , (λ y → {!refl!}))  where

  Thm864Refl : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → isContr (code {a = a} n iscon north refl)
  Thm864Refl n a iscon = {!!}
    where
  

  codeCenter : Type ℓ
  codeCenter = ∥ Σ A (λ x → merid x ∙ sym (merid a) ≡ refl {x = north}) ∥ (ℕ→ℕ₋₂ (n + n))

  pairLemma2 : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → transport (λ i → a ≡ p i) refl ≡ p
  pairLemma2 {ℓ} {A} {a} = J (λ b p →  transport (λ i → a ≡ p i) refl ≡ p) (transportRefl refl)

  c : (y : (Susp A)) (p : north ≡ y) → code {a = a} n iscon y p
  c y p = transport (λ i → (uncurry (code {a = a} n iscon) (pair⁼ p (pairLemma2 p) i))) ∣ a , (rCancel _) ∣

  

  mainId : (p : north ≡ north) (d : code {a = a} n iscon north p) →
           d ≡ c north p
  mainId p = ind {!!} base
    where
    base : (x : fiber (λ y → σ y) p) → ∣ x ∣ ≡ c north p
    base (x1 , r) = J (λ p r → ∣ x1 , r ∣ ≡ c north p) (sym reflCase) r
      where
      reflCase  : c north (σ x1) ≡ ∣ x1 , refl ∣
      reflCase = c north (σ x1)
                   ≡⟨ {!!} ⟩
                 transport (λ i → uncurry (code {a = a} n iscon) (pair⁼ (sym (merid a)) ({!!}) i) ) (transport (λ i → uncurry (code {a = a} n iscon) (pair⁼ (merid a) ({!!}) i) ) ∣ a , (rCancel _) ∣) ≡⟨ {!uncurry (code {a = a} n iscon) !} ⟩
                 transport (λ i → uncurry (code {a = a} n iscon) (pair⁼ (sym (merid a)) {!pairLemma2 p!} i)) {!!}
                 ≡⟨ {!!} ⟩
                 {!!}
       where
       pairLemma3 : ∀ {ℓ} {A : Type ℓ} {a1 b : A} (p : a1 ≡ b) (q : b ≡ a1) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q
       pairLemma3 {a1 = a1} = J (λ b p → (q : b ≡ a1) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q) λ q → pairLemma2 q ∙ lUnit q

       functTransp : ∀ {ℓ ℓ'} {A : Type ℓ} {a1 b : A} {C : Σ A (λ b → a1 ≡ b) → Type ℓ' } (p : a1 ≡ b) (q : b ≡ a1) → transport (λ i → C (pair⁼ (p ∙ q) (pairLemma2 (p ∙ q)) i) ) ≡ λ x → transport (λ i → C (pair⁼ q ((pairLemma3 p q)) i)) (transport (λ i → C (pair⁼ p (pairLemma2 p) i)) x)
       functTransp {a1 = a1} {C = C} = J (λ b p → {!!})
                                         {!!} 
  

Freudenthal : (n : ℕ) (A : Pointed ℓ) → is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A) → ∥ typ A ∥ (ℕ→ℕ₋₂ (n + n)) ≡ ∥ typ (Ω (Susp (typ A) , north)) ∥ ((ℕ→ℕ₋₂ (n + n)))
Freudenthal n A isCon = ua ({!!} , {!Lemma757i→ii ? ? ? ?!})
