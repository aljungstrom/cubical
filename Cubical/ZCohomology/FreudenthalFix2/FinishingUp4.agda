{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.FreudenthalFix2.FinishingUp4  where


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.FreudenthalFix2.7-5-14
open import Cubical.ZCohomology.FreudenthalFix2.Prelim
open import Cubical.ZCohomology.FreudenthalFix2.Code
open import Cubical.Foundations.Everything
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Prod
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_ ; _-_ ; +-comm )
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation
open import Cubical.Data.HomotopyGroup

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

{- this file contains a proof that σ is 2n-connected -}


-------------------- Some useful lemmas. Using J to prove them makes life a lot easier later ------------------------------
symDistr : {x y z : A} (p : x ≡ y) (q : y ≡ z) → sym (p ∙ q) ≡ (sym q) ∙ (sym p)
symDistr {x = x} {z = z} = J (λ y p → (q : y ≡ z) → sym (p ∙ q) ≡ (sym q) ∙ (sym p))
                             (J (λ z q → sym (refl ∙ q) ≡ (sym q) ∙ (sym refl) )
                                refl)

toPathCancel : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} → (z : transp A i0 x ≡ y) → fromPathP (toPathP {A = A} {x = x} {y = y} z) ≡ z
toPathCancel {A = A} {x = x} {y = y} z = cong (λ x → fst x) (equiv-proof (toPathP-isEquiv A {x = x} {y = y}) (toPathP z) .snd (z , refl))


transportLemma : {a b : A} {B : (z : A) → Type ℓ'} (p : a ≡ b) (x : B a) (y : B b) → transport (λ i → B (p i)) x ≡ y → transport (λ i → B (p (~ i))) y ≡ x
transportLemma {a = a} {B = B} x y = J (λ b p → (x : B a) (y : B b) → transport (λ i → B (p i)) x ≡ y → transport (λ i → B (p (~ i))) y ≡ x)
                                       (λ x y id → transportRefl y ∙  (sym id) ∙ transportRefl x)
                                        x y 
transportLemmaRefl : {a : A} {B : (z : A) → Type ℓ'} → (x y : B a) →  transportLemma {B = B} (λ _ → a) ≡ λ x y id → transportRefl y ∙  (sym id) ∙ transportRefl x
transportLemmaRefl {ℓ} {A = A} {a = a} {B = B} x y = JRefl {ℓ} {A} {a} (λ b p → (x y : B a) → transport (λ i → B a) x ≡ y → transport (λ i → B a) y ≡ x)
                                       (λ x y id → transportRefl y ∙  (sym id) ∙ transportRefl x)

transpRCancel : (p : A ≡ B) (b : B) → transport p (transport⁻ p b) ≡ b
transpRCancel {A = A} = J (λ B p → (b : B) → transport p (transport⁻ p b) ≡ b) λ b → transportRefl (transport refl b) ∙ transportRefl b

transpRCancelRefl : (a : A) → transpRCancel refl a ≡ transportRefl (transport refl a) ∙ transportRefl a
transpRCancelRefl {A = A} a = cong (λ x → x a) (JRefl (λ A p → (a : A) → transport p (transport⁻ p a) ≡ a) λ b → transportRefl (transport refl b) ∙ transportRefl b)

pairLemma2 : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → transport (λ i → a ≡ p i) refl ≡ p
pairLemma2 {ℓ} {A} {a} = J (λ b p →  transport (λ i → a ≡ p i) refl ≡ p) (transportRefl refl)

pairLemma2Refl : ∀ {ℓ} {A : Type ℓ} {a : A} → pairLemma2 (refl {x = a}) ≡ (transportRefl refl)
pairLemma2Refl {ℓ} {A} {a} = JRefl (λ b p →  transport (λ i → a ≡ p i) refl ≡ p) (transportRefl refl)

pairLemma3 : ∀ {ℓ} {A : Type ℓ} {a1 b c : A} (p : a1 ≡ b) (q : b ≡ c) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q
pairLemma3 {A = A} {a1 = a1} {b = b} {c = c} p q = J (λ b p → (c : A) →  (q : b ≡ c) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q )
                                                      (λ c q → pairLemma2 q ∙ lUnit q)
                                                      p c q

pairLemma3Refl : ∀ {ℓ} {A : Type ℓ} {a1 : A} (q : a1 ≡ a1) → pairLemma3 (λ _ → a1) q ≡ pairLemma2 q ∙ lUnit q
pairLemma3Refl {A = A} {a1 = a1} q = cong (λ x → x a1 q) (JRefl (λ b p → (c : A) →  (q : b ≡ c) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q ) (λ c q → pairLemma2 q ∙ lUnit q))


pairLemma3* : ∀ {ℓ} {A : Type ℓ} {a1 b c : A} (q : b ≡ c) (p : a1 ≡ b) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q
pairLemma3* {a1 = a1} {b = b}  = J (λ c q → (p : a1 ≡ b) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q)
                                   λ p → transportRefl p ∙ rUnit p

pairLemma3*Refl : ∀ {ℓ} {A : Type ℓ} {a1 b : A} (p : a1 ≡ b) → pairLemma3* refl p ≡ transportRefl p ∙ rUnit p
pairLemma3*Refl {a1 = a1} {b = b} p = cong (λ x → x p) (JRefl (λ c q → (p : a1 ≡ b) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q)
                                                               λ p → transportRefl p ∙ rUnit p)

pairLemma3Id : ∀ {ℓ} {A : Type ℓ} {a1 b c : A} (p : a1 ≡ b) (q : b ≡ c)  → pairLemma3 p q ≡ pairLemma3* q p
pairLemma3Id {ℓ} {A} {a1} {b} {c} = J (λ b p → (q : b ≡ c)  → pairLemma3 p q ≡ pairLemma3* q p)
                                      (J (λ c q → pairLemma3 refl q ≡ pairLemma3* q refl)
                                      (pairLemma3Refl refl ∙ sym (pairLemma3*Refl refl ∙ λ k → (pairLemma2Refl (~ k)) ∙ rUnit refl)))

pairLemma3ReflRefl : {a1 : A} → pairLemma3 (λ _ → a1) (λ _ → a1) ≡ (transportRefl refl) ∙ lUnit refl
pairLemma3ReflRefl = pairLemma3Refl refl ∙ λ i → pairLemma2Refl i ∙ lUnit refl

substComposite-∙ : ∀ {ℓ ℓ′} {A : Type ℓ} → (B : A → Type ℓ′)
                     → {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : B x)
                     → subst B (p ∙ q) u ≡ subst B q (subst B p u)
substComposite-∙ {A = A} B p q u = transport (λ i → subst B (□≡∙ p q i) u ≡ subst B q (subst B p u)) (substComposite-□ B p q u)


pair⁼ : ∀ {ℓ'} {B : A → Type ℓ'} {x y : Σ A (λ a → B a)} (p : fst x ≡ fst y) →
          transport (λ i → B (p i)) (snd x) ≡ (snd y) →
          x ≡ y 
pair⁼ {B = B}{x = x1 , x2} {y = y1 , y2} p = J (λ y1 p → ((y2 : B y1) → (transport (λ i → B (p i)) x2 ≡ y2) → (x1 , x2) ≡ (y1 , y2)))
                                               (λ y2 p2 i → x1 , ((sym (transportRefl x2)) ∙ p2) i) p y2

pair⁼Refl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {a : A} {x y : B a} (p : transport (λ i → B a) x ≡ y) →
            pair⁼ {B = B} {x = (a , x)} {y = (a , y)} refl p
              ≡
            λ i → a , ((sym (transportRefl x)) ∙ p) i
pair⁼Refl {A = A} {B = B} {a = a} {x = x} {y = y} p = cong (λ f → f y p)
                                                           (JRefl (λ y1 p → ((y2 : B y1) → (transport (λ i → B (p i)) x ≡ y2) →
                                                                            _≡_ {A = Σ A (λ a → B a)} (a , x) (y1 , y2)))
                                                                  (λ y2 p2 i → a , ((sym (transportRefl x)) ∙ p2) i))

----------- Currently, the code is 
abstract
  pair⁼'' : ∀ {ℓ'} {B : A → Type ℓ'} {x y : Σ A (λ a → B a)} → (p : fst x ≡ fst y) → transport (λ i → B (p i)) (snd x) ≡ (snd y) → x ≡ y 
  pair⁼'' {B = B}{x = x1 , x2} {y = y1 , y2} p = J (λ y1 p → ((y2 : B y1) → (transport (λ i → B (p i)) x2 ≡ y2) → (x1 , x2) ≡ (y1 , y2))) (λ y2 p2 i → refl {x = x1} i , ((sym (transportRefl x2)) ∙ p2) i) p y2

  pair⁼''Refl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {a : A} {x y : B a} → (p : transport (λ i → B a) x ≡ y) → pair⁼'' {B = B} {x = (a , x)} {y = (a , y)} refl p ≡ λ i → a , ((sym (transportRefl x)) ∙ p) i
  pair⁼''Refl {A = A} {B = B} {a = a} {x = x} {y = y} p = cong (λ f → f y p) ((JRefl (λ y1 p → ((y2 : B y1) → (transport (λ i → B (p i)) x ≡ y2) → _≡_ {A = Σ A (λ a → B a)} (a , x) (y1 , y2))) (λ y2 p2 i → a , ((sym (transportRefl x)) ∙ p2) i)))

  pairId : ∀ {ℓ'} {B : A → Type ℓ'} {x y : Σ A (λ a → B a)} → (pair⁼'' {x = x} {y = y}) ≡ (pair⁼ {x = x} {y = y})
  pairId = refl

  pair⁼''Sym : ∀ {ℓ'} {B : A → Type ℓ'} {x y : Σ A (λ a → B a)} → (p : fst x ≡ fst y) → (q : transport (λ i → B (p i)) (snd x) ≡ (snd y)) →
                      sym (pair⁼'' {x = x} {y = y} p q) ≡ pair⁼'' (sym p) (transportLemma {B = B} p (snd x) (snd y) q )
  pair⁼''Sym {ℓ} {A = A} {B = B} {x = x} {y = y} p = J {ℓ} {A} {fst x} (λ fsty p → (sndy : B (fsty)) → (q : transport (λ i → B (p i)) (snd x) ≡ (sndy)) →
                                                                     sym (pair⁼'' p q) ≡ pair⁼'' (sym p) (transportLemma {B = B} p (snd x) (sndy) q ))
                                                                     (λ sndy → J (λ sndy q → sym (pair⁼'' (λ _ → fst x) q)
                                                                                              ≡ pair⁼'' refl (transportLemma {B = B} refl (snd x) sndy q))
                                                                                  ((λ j → (sym (pair⁼''Refl refl j) )) ∙
                                                                                  (λ k i → fst x , ((rUnit (sym (transportRefl (snd x))) (~ k)) (~ i))) ∙
                                                                                  (λ k i → fst x , helper (~ k) i) ∙
                                                                                  sym (pair⁼Refl (transportLemma {B = B} (λ _ → fst x) (snd x) (transport (λ i → B (fst x)) (snd x)) refl))) )
                                                                     p (snd y)
    where
    helper : (sym (transportRefl (transport (λ i₁ → B (fst x)) (snd x)))) ∙
             (transportLemma {B = B} (λ _ → fst x) (snd x)
                                                   (transport (λ i₂ → B (fst x)) (snd x))
                                                   (λ _ → transport (λ i₂ → B (fst x)) (snd x)))
             ≡ (transportRefl (snd x))
    helper = (λ i → sym (transportRefl (transport (λ i₁ → B (fst x)) (snd x))) ∙
             (transportLemmaRefl {B = B} (snd x) (snd x) i) (snd x)
                                                            (transport (λ i₂ → B (fst x)) (snd x))
                                                            (λ _ → transport (λ i₂ → B (fst x)) (snd x)) ) ∙
              (λ i →  sym (transportRefl (transport (λ i₁ → B (fst x)) (snd x))) ∙
                      transportRefl (transport (λ i₂ → B (fst x)) (snd x)) ∙ (λ _ → transport (λ i₂ → B (fst x)) (snd x)) ∙ transportRefl (snd x)) ∙
              (λ i → sym (transportRefl (transport (λ i₁ → B (fst x)) (snd x))) ∙
                      transportRefl (transport (λ i₂ → B (fst x)) (snd x)) ∙
                      lUnit (transportRefl (snd x)) (~ i)) ∙
              assoc (sym (transportRefl (transport (λ i₁ → B (fst x)) (snd x)))) (transportRefl (transport (λ i₁ → B (fst x)) (snd x))) (transportRefl (snd x)) ∙
              (λ i → (lCancel (transportRefl (transport (λ i₁ → B (fst x)) (snd x))) i) ∙ transportRefl (snd x)) ∙
              sym (lUnit (transportRefl (snd x)))
              
  {- We need something slightly stronger than functoriality of transport. Since we will be transporting over dependent pairs, we also need to split the second component -} 
  functTransp2 : ∀ {ℓ ℓ'} {A : Type ℓ} {a1 b : A} {C : Σ A (λ b → a1 ≡ b) → Type ℓ' } (p : a1 ≡ b) (q : b ≡ a1) →
                 transport (λ i → C (pair⁼'' (p ∙ q) (pairLemma2 (p ∙ q)) i) )
                 ≡ λ x → transport (λ i → C (pair⁼'' q ((pairLemma3 p q)) i))
                                   (transport (λ i → C (pair⁼'' p (pairLemma2 p) i)) x)
  functTransp2 {ℓ} {ℓ'} {A = A} {a1 = a1} {b = b} {C = C} =
                        J (λ b p → (q : b ≡ a1) →
                                   transport (λ i → C (pair⁼'' {B = λ a → a1 ≡ a} {x = (a1 , refl {x = a1})} (p ∙ q) (pairLemma2 (p ∙ q)) i) )
                                   ≡ λ x → transport (λ i → C (pair⁼'' q ((pairLemma3 p q)) i)) (transport (λ i → C (pair⁼'' p (pairLemma2 p) i)) x))
                          λ q → (λ j → subst C (hej a1 q (~ j))) ∙
                                (λ j → subst C (pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1)) ∙
                                pair⁼'' q (pairLemmaId q (~ j)))) ∙
                                funExt λ x → (substComposite-∙ C (pair⁼'' refl (pairLemma2 refl)) (pair⁼'' q (pairLemma3 refl q)) x)
           where
             pairLemmaId : (q : a1 ≡ a1) → (pairLemma3 (λ _ → a1) q) ≡ ((pairLemma2 q) ∙ lUnit q)
             pairLemmaId q = pairLemma3Refl q

             hej : (b : A) (q : a1 ≡ b) → (pair⁼'' {A = A} {B = λ a → a1 ≡ a}
                                                   {x = (a1 , λ _ → a1)} {y = (a1 , λ _ → a1)}
                                                   (λ _ → a1) (pairLemma2 {a = a1} {b = a1} (λ _ → a1)) ∙
                                           pair⁼'' q ((pairLemma2 q) ∙ lUnit q))
                                         ≡ pair⁼'' (refl ∙ q) (pairLemma2 (refl {x = a1} ∙ q))
             hej b = J (λ b q → pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1)) ∙
                                pair⁼'' q (pairLemma2 q ∙ lUnit q)
                              ≡ pair⁼'' (refl ∙ q) (pairLemma2 (refl ∙ q)))
                       ((λ i → (helper2 i) ∙ pair⁼'' refl (pairLemma2 refl ∙ lUnit refl)) ∙
                         sym (lUnit (pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1) ∙ lUnit (λ _ → a1)))) ∙
                         desired≡)
               where
               helper2 : (pair⁼'' {A = A} {B = λ a → a1 ≡ a}
                                  {x = (a1 , λ _ → a1)} {y = (a1 , λ _ → a1)}
                                  (λ _ → a1) (pairLemma2 {a = a1} {b = a1} (λ _ → a1)))
                        ≡ refl
               helper2 = (λ i → (JRefl (λ y1 p → ((y2 : a1 ≡ y1) → (transport (λ i → a1 ≡ (p i)) refl ≡ y2) →
                                                 _≡_ {A = Σ A (λ a → a1 ≡ a)} (a1 , refl) (y1 , y2)))
                                       (λ y2 p2 i → refl {x = a1} i , ((sym (transportRefl refl)) ∙ p2) i) i)
                                (λ _ → a1)
                                (pairLemma2 {a = a1} {b = a1} (λ _ → a1))) ∙
                         (λ j → λ i → a1 , ((sym (transportRefl refl)) ∙
                                           JRefl (λ b p →  transport (λ i → a1 ≡ p i) refl ≡ p)
                                                 (transportRefl refl) j ) i) ∙
                          λ j i → a1 , (lCancel (transportRefl refl) j) i

               PathP1 : PathP (λ j → _≡_ {A = Σ A (λ a → a1 ≡ a)} (a1 , (λ _ → a1)) (a1 , lUnit (λ _ → a1) (~ j)))
                              (pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1) ∙ lUnit (λ _ → a1)))
                              refl
               PathP1 j = hcomp (λ k → λ{(j = i0) → pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1) ∙ lUnit (λ _ → a1))
                                       ; (j = i1) → ((λ i → pair⁼'' (λ _ → a1) (rUnit (pairLemma2 (λ _ → a1)) (~ i)) ) ∙ helper2) k})
                                (pair⁼'' refl ((pairLemma2 (λ _ → a1)) ∙ (λ i → lUnit refl (i ∧ (~ j)))))

               PathP2 : PathP (λ j → _≡_ {A = Σ A (λ a → a1 ≡ a)} (a1 , (λ _ → a1)) (a1 , lUnit (λ _ → a1) j))
                              refl
                              (pair⁼'' ((λ _ → a1) ∙ refl) (pairLemma2 ((λ _ → a1) ∙ refl)))
               PathP2 j = hcomp (λ k → λ{(j = i0) → helper2 k
                                       ; (j = i1) → (pair⁼'' ((λ _ → a1) ∙ refl) (pairLemma2 ((λ _ → a1) ∙ refl)))})
                                (pair⁼'' (lUnit (λ _ → a1) j) (pairLemma2 (lUnit (λ _ → a1) j)))

               pathsCancel : (λ j → _≡_ {A = Σ A (λ a → a1 ≡ a)} (a1 , (λ _ → a1)) (a1 , lUnit (λ _ → a1) (~ j))) ∙
                              ((λ j → _≡_ {A = Σ A (λ a → a1 ≡ a)} (a1 , (λ _ → a1)) (a1 , lUnit (λ _ → a1) j)))
                           ≡ refl
               pathsCancel = lCancel (λ j → _≡_ {A = Σ A (λ a → a1 ≡ a)} (a1 , (λ _ → a1)) (a1 , lUnit (λ _ → a1) j))

               desired≡ : pair⁼'' (λ _ → a1) (λ i i₁ → (pairLemma2 (λ _ → a1) ∙ lUnit (λ _ → a1)) i i₁)
                        ≡ pair⁼'' ((λ _ → a1) ∙ refl) (pairLemma2 ((λ _ → a1) ∙ refl))
               desired≡ = transport (λ i → PathP (λ j → pathsCancel i j)
                                                 (pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1) ∙ lUnit (λ _ → a1)))
                                                 (pair⁼'' ((λ _ → a1) ∙ refl) (pairLemma2 ((λ _ → a1) ∙ refl))))
                                    (compPathP PathP1 PathP2)
               
---------------------------------------------------------------------------------------------




---------------------- Lemma 8.6.10. from the HoTT book, and an addition variant of it that will be useful -----------------
Lemma8610fun : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a2) → C a1 (subst B (sym p) b) → C a2 b
Lemma8610fun {ℓ} {ℓ'} {ℓ''} {A = A} {a1 = a1 } {a2 = a2} {B = B} C p b  = transport (λ i → idHelper i ) 
   where
   idHelper : C a1 (subst B (sym p) b) ≡ C a2 b
   idHelper = (sym (cong (λ x → x b) (Lemma294' {A = B} {B = λ _ → Type ℓ''} p (C a1)))) ∙ funExt⁻ (fromPathP λ j → C (p j)) b

Lemma8610 : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a2)  → transport ((λ i → uncurry C (pair⁼ p (transpRCancel (λ i → B (p i)) b) i) )) ≡ Lemma8610fun C p b  
Lemma8610 {ℓ} {ℓ'} {ℓ''} {A = A} {a1 = a1} {B = B} C = J (λ a2 p → (b : B a2)  → transport ((λ i → uncurry C (pair⁼ p (transpRCancel (λ i → B (p i)) b) i) )) ≡ Lemma8610fun C p b  ) λ b j → transport (helper b (~ j))
   where
   helper : (b : B a1) → (sym (cong (λ x → x b) (Lemma294' {A = B} {B = λ _ → Type ℓ''} refl (C a1)))) ∙ funExt⁻ (fromPathP λ j → C a1) b ≡ (λ i → uncurry C (pair⁼ refl (transpRCancel (λ i₁ → B (refl i₁)) b) i))
   helper b = (sym (cong (λ x → x b) (Lemma294' {A = B} {B = λ _ → Type ℓ''} refl (C a1)))) ∙ cong (λ x → C a1 x) (transportRefl b)
              ≡⟨ (λ i → (sym (cong (λ x → x b) (Lemma294'Refl {A = B} {B = λ _ → Type ℓ''} (C a1) i))) ∙ cong (λ x → C a1 x) (transportRefl b)) ⟩
              refl ∙ cong (λ x → C a1 x) (transportRefl b)
              ≡⟨ sym (lUnit (cong (λ x → C a1 x) (transportRefl b)))  ⟩
              cong (λ x → C a1 x) (transportRefl b)
              ≡⟨ (λ j i → uncurry C (a1 , lUnit (transportRefl b) j i)) ⟩
              ((λ i → uncurry C (a1 , (refl ∙ (transportRefl b)) i)))
              ≡⟨ (λ j i → uncurry C (a1 , ((lCancel (transportRefl (transport refl b)) (~ j)) ∙ (transportRefl b)) i)) ⟩
              ((λ  i →  uncurry C (a1 , (((sym (transportRefl ((transport⁻ (λ i₁ → B a1) b)))) ∙ (transportRefl (transport refl b))) ∙ (transportRefl b)) i)) )
              ≡⟨ (λ j i → uncurry C (a1 , ((assoc (sym (transportRefl ((transport⁻ (λ i₁ → B a1) b)))) (transportRefl (transport refl b)) (transportRefl b) (~ j))) i)) ⟩
              ((λ  i →  uncurry C (a1 , (((sym (transportRefl ((transport⁻ (λ i₁ → B a1) b)))) ∙ (transportRefl (transport refl b) ∙ transportRefl b))) i))) 
              ≡⟨ (λ j i →  uncurry C (a1 , (((sym (transportRefl ((transport⁻ (λ i₁ → B a1) b)))) ∙ (transpRCancelRefl b (~ j)))) i)) ⟩ 
              (λ i → uncurry C (a1 , (((sym (transportRefl ((transport⁻ (λ i₁ → B a1) b)))) ∙ (transpRCancel (λ i₁ → B a1) b))) i))
              ≡⟨ (λ j → (λ i → uncurry C (pair⁼Refl (transpRCancel (λ i₁ → B a1) b) (~ j) i))) ⟩
              (λ i → uncurry C (pair⁼ refl (transpRCancel (λ i₁ → B a1) b) i)) ∎

{- abstract version -}
Lemma8610'' : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a2)  → transport ((λ i → uncurry C (pair⁼'' p (transpRCancel (λ i → B (p i)) b) i) )) ≡ Lemma8610fun C p b
Lemma8610'' {A = A} {a1 = a1} {a2 = a2} {B = B} C p b  = (λ j → transport (λ i → uncurry C ((pairId j) p (transpRCancel (λ i₁ → B (p i₁)) b) i))) ∙
                                                          Lemma8610 {A = A} {a1 = a1} {a2 = a2} {B = B} C p b

{-variant for when we have have pair⁼ p refl -}
Lemma8610Reflfun : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a1) → C a1 b ≡ C a2 (subst B p b)
Lemma8610Reflfun {ℓ'' = ℓ''} {a1 = a1} {a2 = a2} {B = B} C p b = (λ i → C a1 (transpRCancel (λ i → (B (p (~ i)))) b (~ i))) ∙ funExt⁻ (fromPathP λ j → C (p j)) (transport (λ i → B (p i)) b)

Lemma8610Refl : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a1)  → transport ((λ i → uncurry C (pair⁼ {x = a1 , b} p refl i) )) ≡ transport (Lemma8610Reflfun {B = B} C p b)
  
Lemma8610Refl {A = A} {a1 = a1} {B = B} C = J (λ a2 p → (b : B a1)  → transport ((λ i → uncurry C (pair⁼ {x = a1 , b} p refl i) )) ≡ transport (Lemma8610Reflfun {B = B} C p b))
                                              λ b → (λ k → transport ((λ i → uncurry C (pair⁼Refl (λ _ → transport (λ i → B a1) b) k i) ))) ∙
                                                    (λ k → transport (λ i → uncurry C (a1 , ((sym (transportRefl b) ∙ (λ _ → transport (λ i → B a1) b)) i)))) ∙
                                                    (λ k → transport (λ i → uncurry C (a1 , (rUnit (sym (transportRefl b)) (~ k) i)))) ∙
                                                    (λ k → transport (rUnit (cong (λ x → C a1 x) (sym (transportRefl b))) k)) ∙
                                                    (λ k → transport ((cong (λ x → C a1 x) (sym (transportRefl b))) ∙
                                                                      lCancel ((funExt⁻ (fromPathP λ j → C a1) (transport (λ i → B a1) b))) (~ k))) ∙
                                                    (λ k → transport (assoc (cong (λ x → C a1 x) (sym (transportRefl b)))
                                                                            (cong (λ x → C a1 x) (sym (transportRefl {A = B a1} (transport (λ _ → B a1) b))))
                                                                            (funExt⁻ (fromPathP λ j → C a1) (transport (λ i → B a1) b)) k)) ∙
                                                    (λ k → transport (congComp2 (λ x → C a1 x)
                                                                                (sym (transportRefl b))
                                                                                (sym (transportRefl {A = B a1} (transport (λ _ → B a1) b))) k  ∙
                                                                      funExt⁻ (fromPathP λ j → C a1) (transport (λ i → B a1) b))) ∙
                                                    (λ k → transport (cong (λ x → C a1 x)
                                                                           (symDistr {x = transport refl (transport (λ _ → B a1) b)}
                                                                           {y = transport (λ _ → B a1) b} {z = b}
                                                                           (transportRefl {A = B a1} (transport (λ _ → B a1) b))
                                                                           (transportRefl b) (~ k)) ∙
                                                                      funExt⁻ (fromPathP λ j → C a1) (transport (λ i → B a1) b)) ) ∙
                                                    (λ k → transport (cong (λ x → C a1 x) (sym (transportRefl {A = B a1} (transport (λ _ → B a1) b) ∙
                                                                                               transportRefl b)) ∙ -- check
                                                                      funExt⁻ (fromPathP λ j → C a1) (transport (λ i → B a1) b))) ∙
                                                    (λ k → transport ((λ i → C a1 ((transportRefl {A = B a1} (transport (λ _ → B a1) b) ∙
                                                                                   transportRefl b) (~ i))) ∙  --check
                                                                     funExt⁻ (fromPathP λ j → C a1) (transport (λ i → B a1) b))) ∙ 
                                                    (λ k → transport ((λ i → C a1 (transpRCancelRefl {A = B a1} b (~ k) (~ i))) ∙
                                                                     funExt⁻ (fromPathP λ j → C a1) (transport (λ i → B a1) b))) ∙
                                                    λ k → transport ((λ i → C a1 (transpRCancel (λ i → (B a1)) b (~ i))) ∙  --check 
                                                                     funExt⁻ (fromPathP λ j → C a1) (transport (λ i → B a1) b))

{- abstract version -}
Lemma8610Refl'' : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a1)  → transport ((λ i → uncurry C (pair⁼'' {x = a1 , b} p refl i) )) ≡ transport ((λ i → C a1 (transpRCancel (λ i → (B (p (~ i)))) b (~ i))) ∙ funExt⁻ (fromPathP λ j → C (p j)) (transport (λ i → B (p i)) b))
  
Lemma8610Refl'' {ℓ} {ℓ'} {ℓ''} {A} {a1} {a2} {B} C p b = transport (λ j → transport (λ i → uncurry C ((pairId {x = a1 , b} (~ j)) p refl i)) ≡ transport (Lemma8610Reflfun {ℓ} {ℓ'} {ℓ''} {A = A} {a1 = a1} {a2 = a2} {B = B} C p b)) ((Lemma8610Refl {ℓ} {ℓ'} {ℓ''} {A = A} {a1 = a1} {a2 = a2} {B = B} C p b))
----------------------------------------------------------------------------------------------------


-------------- Center of contraction of σ -----------------
c : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (y : (Susp A)) (p : north ≡ y) → CODE {a = a} n iscon y p
c n a iscon y p = transport (λ i → (uncurry (CODE {a = a} n iscon) (pair⁼ p (pairLemma2 p) i))) ∣ a , (rCancel (merid a)) ∣

c' : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (y : (Susp A)) (p : north ≡ y) → CODE' {a = a} n iscon y p
c' n a iscon y p = transport (λ i → (uncurry (CODE' {a = a} n iscon) (pair⁼'' p (pairLemma2 p) i))) ∣ a , (rCancel (merid a)) ∣

c'Id : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
       c' n a iscon north (σ x1 {a})
       ≡ transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁)) (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                    (transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' (merid x1) (pairLemma2 (merid x1)) i))
                               ∣ a , rCancel (merid a) ∣)
c'Id n a x1 iscon = cong (λ x → x ∣ a , (rCancel (merid a)) ∣) (functTransp2 {C = uncurry (CODE' {a = a} n iscon)} (merid x1) (sym (merid a)))

c'' : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (y : (Susp A)) (p : north ≡ y) → CODE'' {a = a} n iscon y p
c'' n a iscon y p = transport (λ i → (uncurry (CODE'' {a = a} n iscon) (pair⁼'' p (pairLemma2 p) i))) ∣ a , (rCancel (merid a)) ∣

c''Id : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
       c'' n a iscon north (σ x1 {a})
       ≡ transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁)) (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                    (transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (merid x1) (pairLemma2 (merid x1)) i))
                               ∣ a , rCancel (merid a) ∣)
c''Id n a x1 iscon = cong (λ x → x ∣ a , (rCancel (merid a)) ∣) (functTransp2 {C = uncurry (CODE'' {a = a} n iscon)} (merid x1) (sym (merid a)))







outerTranspId : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
                transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (sym (merid a)) (pairLemma3 (merid x1) (sym (merid a)) ) i)) ∣ x1 , refl ∣
                ≡ transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁)) (transpRCancel (λ i → north ≡ (merid a (~ i))) (merid x1 ∙ (sym (merid a)))) i)) ∣ x1 , rUnit (merid x1) ∙ sym (cong (λ x → merid x1 ∙ x) (lCancel (merid a)))  ∙ assocJ (merid x1) (sym (merid a)) (merid a) ∙ sym (pairLemma3 {a1 = north} (merid x1 ∙ (sym (merid a))) (merid a)) ∣
outerTranspId {ℓ} {A = A} n a x1 iscon = sym (wowie north (sym (merid a)))
   where
   wowie : (y : Susp A) → (q : south ≡ y) → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' q (transpRCancel (λ i → north ≡ q i) ((merid x1) ∙ q)) i))
                                                      ∣ x1 , rUnit (merid x1)  ∙
                                                             sym (cong (λ x → merid x1 ∙ x) (lCancel (sym q))) ∙
                                                             assocJ (merid x1) q (sym q) ∙ sym ((pairLemma3 {a1 = north} (merid x1 ∙ q) (sym q))) ∣
                                          ≡ transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' q (pairLemma3 (merid x1) q ) i)) ∣ x1 , refl ∣
   wowie y = J (λ y q → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' q (transpRCancel (λ i → north ≡ q i) ((merid x1) ∙ q)) i)) ∣ x1 , rUnit (merid x1)  ∙ sym (cong (λ x → merid x1 ∙ x) (lCancel (sym q))) ∙ assocJ (merid x1) q (sym q) ∙ sym ((pairLemma3 {a1 = north} (merid x1 ∙ q) (sym q))) ∣ ≡ transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' q (pairLemma3 (merid x1) q ) i)) ∣ x1 , refl ∣)
               (transport
      (λ i →
         uncurry (CODE'' {a = a} n iscon)
         (pair⁼'' refl
          (transpRCancel (λ i₁ → north ≡ refl i₁) (merid x1 ∙ refl)) i)) ∣ x1 , originalPath ∣
               ≡⟨ (λ j → (transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼''Refl (transpRCancel (λ i₁ → north ≡ south) (merid x1 ∙ refl)) j i))) ∣ x1 , originalPath ∣) ⟩
               (transport (λ i → uncurry (CODE' {a = a} n iscon)
                                 (south , ((sym (transportRefl (transport (λ i → _≡_ {A = Susp A} north south) (merid x1 ∙ (λ _ → south))))) ∙ (
                                           transpRCancel {A = north ≡ south} {B = north ≡ south} (λ _ → _≡_ {A = Susp A} north south)
                                                         (merid x1 ∙ (refl {x = south})))) i) ))
                          ∣ x1 , originalPath ∣
               ≡⟨ (λ j → (transport (λ i → uncurry (CODE'' {a = a} n iscon)
                                    (south , transportCanceller (merid x1 ∙ (λ _ → south)) j i) ))
                                    ∣ x1 , originalPath ∣) ⟩
               (transport (λ i → uncurry (CODE'' {a = a} n iscon) (south , transportRefl (merid x1 ∙ (λ _ → south)) i) ))
                          ∣ x1 , originalPath ∣
               ≡⟨ (λ j → (transport (λ i → uncurry (CODE'' {a = a} n iscon) (south , transportRefl (merid x1 ∙ (λ _ → south)) i) ))
                                   ∣ x1 , rUnit originalPath j ∣) ⟩
               (transport (λ i → uncurry (CODE {a = a} n iscon) (south , transportRefl (merid x1 ∙ (λ _ → south)) i) ))
                          ∣ x1 , originalPath ∙ refl ∣
               ≡⟨ (λ j → (transport (λ i → uncurry (CODE'' {a = a} n iscon) (south , (transportRefl {A = _≡_ {A = Susp A} north south} (merid x1 ∙ (λ _ → south)) (i ∨ j) ) ) ))
                          ∣ x1 , originalPath ∙ (λ k → transportRefl {A = _≡_ {A = Susp A} north south}  (merid x1 ∙ (λ _ → south)) (k ∧ j))  ∣) ⟩
                (transport (λ i → uncurry (CODE'' {a = a} n iscon) (south , (merid x1 ∙ (λ _ → south)) ) ))
                          ∣ x1 , originalPath ∙ transportRefl {A = _≡_ {A = Susp A} north south} (merid x1 ∙ (λ _ → south))  ∣ 
               ≡⟨ (λ j → transport (λ i → uncurry (CODE'' {a = a} n iscon) (south , merid x1 ∙ (λ _ → south)))
                                    ∣ x1 , pathId (merid x1) j ∣) ⟩
               transport (λ i → uncurry (CODE'' {a = a} n iscon) (south , (merid x1 ∙ (λ _ → south)))) ∣ x1 , (λ _ → merid x1) ∙ rUnit (merid x1) ∣
               ≡⟨ (λ j → transport (λ i → uncurry (CODE'' {a = a} n iscon) (south , rUnit (merid x1) (i ∨ (~ j) ))) ∣ x1 , (λ _ → merid x1) ∙ ( λ i → rUnit (merid x1) (i ∧ (~ j))) ∣) ⟩
               transport (λ i → uncurry (CODE'' {a = a} n iscon) (south , rUnit (merid x1)  i)) ∣ x1 , (λ _ → merid x1) ∙ refl ∣
               ≡⟨ (λ j → transport (λ i → uncurry (CODE'' {a = a} n iscon) (south , rUnit (merid x1)  i)) ∣ x1 , rUnit (λ _ → merid x1) (~ j) ∣) ⟩
               transport (λ i → uncurry (CODE'' {a = a} n iscon) (south , rUnit (merid x1)  i)) ∣ x1 , (λ _ → merid x1) ∣
               ≡⟨ (λ j → transport (λ i → uncurry (CODE'' {a = a} n iscon) (south , transportCanceller2 (merid x1) (~ j)  i)) ∣ x1 , (λ _ → merid x1) ∣) ⟩
               transport (λ i → uncurry (CODE'' {a = a} n iscon) (south , (sym (transportRefl (merid x1)) ∙ (pairLemma3 (merid x1) refl)) i)) ∣ x1 , (λ _ → merid x1) ∣
               ≡⟨ (λ j → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼''Refl (pairLemma3 (merid x1) (λ _ → south)) (~ j) i )) ∣ x1 , (λ _ → merid x1) ∣) ⟩
               transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' refl (pairLemma3 (merid x1) refl) i)) ∣ x1 , (λ _ → merid x1) ∣ ∎)

      where
      originalPath : merid x1 ≡ transport (λ i₁ → _≡_ {A = Susp A} north south) (merid x1 ∙ (λ _ → south))
      originalPath = rUnit (merid x1) ∙  (λ i → merid x1 ∙ lCancel (refl {x = south}) (~ i)) ∙ assocJ (merid x1) refl refl ∙
                                         (λ i → pairLemma3 (merid x1 ∙ refl) refl (~ i))

      pathId : ∀ {A : Type ℓ} {x y : A} (p : x ≡ y) → (rUnit p ∙
                                                        (λ i → p ∙ lCancel (refl) (~ i)) ∙
                                                        assocJ p refl refl ∙
                                                        (λ i → pairLemma3 (p ∙ refl) refl (~ i))) ∙
                                                        transportRefl (p ∙ refl)
                                                        ≡
                                                        refl ∙ rUnit p
      pathId {x = x} = J (λ y p → (rUnit p ∙
                                    (λ i → p ∙ lCancel (refl) (~ i)) ∙
                                    assocJ p refl refl ∙
                                    (λ i → pairLemma3 (p ∙ refl) refl (~ i))) ∙
                                    transportRefl (p ∙ refl)
                                    ≡
                                    refl ∙ rUnit p)
                           ((λ j → (rUnit refl ∙
                                    (λ i → refl ∙ lCancel (refl) (~ i)) ∙
                                    assocJRefl j ∙
                                    sym (pairLemma3Id (refl ∙ refl) refl j)) ∙
                                    transportRefl (refl ∙ refl)) ∙
                           (λ j → (rUnit refl ∙
                                    (λ i → refl ∙ lCancel (refl) (~ i)) ∙
                                    ((λ i → refl ∙ rCancel refl i) ∙ rUnit (refl ∙ refl)) ∙
                                    sym (pairLemma3*Refl (refl ∙ refl) j)) ∙
                                    transportRefl (refl ∙ refl)) ∙
                           (λ j → (rUnit refl ∙
                                    (λ i → refl ∙ lCancel (refl) (~ i)) ∙
                                    ((λ i → refl ∙ rCancel refl i) ∙ rUnit (refl ∙ refl)) ∙
                                    symDistr (transportRefl (refl ∙ refl)) (rUnit (refl ∙ refl)) j  ) ∙
                                    transportRefl (refl ∙ refl)) ∙
                           invKiller (rUnit refl) (λ i → refl ∙ lCancel (refl) (~ i)) (rUnit (refl ∙ refl)) (sym (transportRefl (refl ∙ refl)))  ∙
                           lUnit (rUnit refl))
            where
            invKiller : ∀ {ℓ} {A : Type ℓ} {a b c d e : A} (p : a ≡ b) (q : b ≡ c) (r : b ≡ d) (s : b ≡ e) →
                          (p ∙ q ∙ (sym q ∙ r) ∙ sym r ∙ s) ∙ (sym s) ≡ p
            invKiller {a = a} {b = b} {c = c} {d = d} {e = e} p = J (λ c q → (r : b ≡ d) (s : b ≡ e) →
                                                                      (p ∙ q ∙ (sym q ∙ r) ∙ sym r ∙ s) ∙ (sym s) ≡ p)
                                                                      (J (λ d r → (s : b ≡ e) → (p ∙ refl ∙ (refl ∙ r) ∙ sym r ∙ s) ∙ (sym s) ≡ p)
                                                                          (J (λ e s → (p ∙ refl ∙ (refl ∙ refl) ∙ refl ∙ s) ∙ (sym s) ≡ p)
                                                                              ((λ i → rUnit (p ∙ (λ _ → b) ∙ (rUnit refl (~ i)) ∙ refl ∙ refl) (~ i)) ∙
                                                                              (λ i → p ∙ (lUnit (lUnit (lUnit refl (~ i)) (~ i)) (~ i) )) ∙
                                                                              sym (rUnit p))))
            

      transportCanceller : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) →
                           sym (transportRefl (transport (λ i → x ≡ y) p )) ∙ transpRCancel (λ _ → x ≡ y) p ≡ transportRefl p
      transportCanceller {x = x} {y = y} p = (λ j → sym (transportRefl (transport (λ i → x ≡ y) p)) ∙ (transpRCancelRefl p j)) ∙
                                             assoc (sym (transportRefl (transport (λ i → x ≡ y) p)))
                                                   ((transportRefl (transport (λ i → x ≡ y) p)))
                                                   (transportRefl p)  ∙
                                             (λ j → lCancel (transportRefl (transport (λ i → x ≡ y) p)) j ∙ transportRefl p) ∙
                                             sym (lUnit (transportRefl p))

      transportCanceller2 : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) →
                            (sym (transportRefl p) ∙ (pairLemma3 p refl)) ≡ rUnit p
      transportCanceller2 {x = x} = J (λ y p → (sym (transportRefl p) ∙ (pairLemma3 p refl)) ≡ rUnit p)
                                      ((λ j → sym (transportRefl refl) ∙ pairLemma3Refl refl j) ∙
                                      (λ j → sym (transportRefl refl) ∙ pairLemma2Refl j ∙ lUnit refl) ∙
                                      assoc (sym (transportRefl refl)) (transportRefl refl) (lUnit refl) ∙
                                      (λ j → lCancel (transportRefl refl) j ∙ lUnit refl) ∙
                                      sym (lUnit (lUnit refl)) )









codeTranspHelper1 :  ∀{ℓ} {X : Type ℓ} {a b : X}  (q p : a ≡ b) → (A : (a ≡ a) → Type ℓ) (B : (a ≡ b) → Type ℓ) → (f : (q₁ : a ≡ b) → A (q₁ ∙ sym q) ≡ B q₁) →
        (sym (cong (λ x → x p) (Lemma294' {A = λ x → a ≡ x} {B = λ _ → Type ℓ} q A))) ∙ funExt⁻ (fromPathP (toPathP {A = λ i → a ≡ q i → Type ℓ} {x = A} {y = B}
                                                       (Lemma296Funs.inv'' {X = X} {A = λ y → a ≡ y} {B = λ _ → Type ℓ}
                                                                         q A
                                                                         B
                                                                         (equivTest' {X = X} q {A = A}
                                                                                    {B = B}
                                                                                    f)))) p
          ≡ (transportRefl (A (subst (λ x → a ≡ x) (sym q) p)) ∙ cong (λ x → A x) (pairLemma3 p (sym q))) ∙ f p
codeTranspHelper1 {ℓ}  {X = X} {a = a} = J (λ b q → (p : a ≡ b) (A : (a ≡ a) → Type ℓ) (B : (a ≡ b) → Type ℓ) (f : (q₁ : a ≡ b) → A (q₁ ∙ sym q) ≡ B q₁) →
                                       (sym (cong (λ x → x p) (Lemma294' {A = λ x → a ≡ x} {B = λ _ → Type ℓ} q A))) ∙
                                        funExt⁻ (fromPathP (toPathP {A = λ i → a ≡ q i → Type ℓ} {x = A} {y = B}
                                                                    (Lemma296Funs.inv'' {X = X} {A = λ y → a ≡ y}
                                                                                      {B = λ _ → Type ℓ} q A B
                                                                                      (equivTest' {X = X} q {A = A} {B = B} f)))) p
                                       ≡ (transportRefl (A (subst (λ x → a ≡ x) (sym q) p)) ∙
                                          cong (λ x → A x) (pairLemma3 p (sym q))) ∙ f p)
                              λ p A B f → 
                                         (λ k → ((λ i → (Lemma294'Refl {A = λ x → a ≡ x} {B = λ _ → Type ℓ} A k) (~ i) p)) ∙
                                                 (λ i → fromPathP (toPathP {A = λ i → a ≡ a → Type ℓ} {x = A} {y = B}
                                                                           (Lemma296Funs.inv'' {X = X} {A = λ y → a ≡ y} {B = λ _ → Type ℓ} (refl {x = a})
                                                                                             A B (equivTestId {X = X} (refl {x = a}) {A = A} {B = B} f k))) i p)) ∙
                                          (λ k → lUnit ((λ i → fromPathP (toPathP {A = λ i → a ≡ a → Type ℓ} {x = A} {y = B}
                                                                           (Lemma296Funs.inv'' {X = X} {A = λ y → a ≡ y} {B = λ _ → Type ℓ} (refl {x = a})
                                                                                             A B (equivTest {X = X} (refl {x = a}) {A = A} {B = B} f))) i p)) (~ k)) ∙
                                          (λ k i → (toPathCancel {A = λ i → a ≡ a → Type ℓ} {x = A} (Lemma296Funs.inv'' {X = X} {A = λ y → a ≡ y}
                                                                                                    {B = λ _ → Type ℓ} (refl {x = a})
                                                                                             A B (equivTest {X = X} (refl {x = a}) {A = A} {B = B} f)) k) i p) ∙
                                          (λ k i → ((cong (λ x → x (equivTest {X = X} (λ _ → a) f)) (ReflCases.inv''Refl {A = λ y → a ≡ y}
                                                                                                                       {B = λ _ → Type ℓ} A B)) k) i p ) ∙
                                          (λ k i → (transportRefl {A = a ≡ a → Type ℓ} A ∙
                                                   funExt λ z → sym (transportRefl {A = Type ℓ} (A z))  ∙
                                                   cong (λ x → x f z) (equivTestRefl {X = X} {A = A} {B = B} ) k ∙
                                                   λ i → (B (transportRefl {A = a ≡ a} z i))) i p) ∙
                                          sym (congComp2 (λ x → x p) (transportRefl A)
                                                                 (funExt λ z → sym (transportRefl {A = Type ℓ} (A z)) ∙
                                                                 (transportRefl (A z) ∙ cong (λ x → A x) (rUnit z) ∙
                                                                 f z ∙
                                                                 cong (λ x → B x) (sym (transportRefl z))) ∙
                                                                 λ i → (B (transportRefl z i)))) ∙
                                          invCanceller (cong (λ x → x p) (transportRefl A))
                                                       (sym (transportRefl (A p)))
                                                       (λ i → A (rUnit p i))
                                                       (f p)
                                                       (λ i → B (transportRefl p i))  ∙
                                          assoc (λ i → transportRefl A i p)
                                                (λ i → A (rUnit p i))
                                                (f p) ∙
                                          (λ k → ((λ i → transportRefl A i p) ∙ (λ i → A (rUnit p i))) ∙ f p) ∙
                                          (λ k → (transpLemma2 {A = A} p k ∙ (cong (λ x → A x) (rUnit p))) ∙ f p ) ∙
                                          (λ k → ((assoc (transportRefl (A (subst (_≡_ a) (λ i → a) p)))
                                                         (cong (λ x → A x) (transportRefl p))
                                                         (cong (λ x → A x) (rUnit p))) (~ k)) ∙
                                                  f p) ∙
                                          (λ k → ((transportRefl (A (subst (_≡_ a) (λ i → a) p)) ∙ congComp2 (λ x → A x) (transportRefl p) (rUnit p) k)  ∙ f p)) ∙
                                          (λ k → (transportRefl (A (subst (_≡_ a) (λ i → a) p)) ∙
                                                 (λ i → A ((transportRefl p ∙ rUnit p) i))) ∙
                                                 f p) ∙
                                          (λ k → (transportRefl (A (subst (_≡_ a) (λ i → a) p)) ∙ (λ i → A (pairLemma3*Refl p (~ k) i))) ∙ f p) ∙
                                          λ k → (transportRefl (A (subst (_≡_ a) (λ i → a) p)) ∙ (λ i → A (pairLemma3Id p (λ i₁ → a ) (~ k)  i))) ∙ f p

     where
     transpLemma2 : ∀ {ℓ ℓ'} {X : Type ℓ} {x : X} {A : x ≡ x → Type ℓ'} (p : x ≡ x) → (λ i → transportRefl A i p)  ≡ (transportRefl (A (transport (λ i → x ≡ x)  p)) ∙ (λ i → A ((transportRefl p) i)))
     transpLemma2 {ℓ' = ℓ'}{x = x} {A = A} p j = hcomp (λ k → λ{(j = i0) → (sym (lUnit (λ i → transportRefl (A ((transportRefl p) i)) i))) k
                                                             ; (j = i1) → (transportRefl (A (transport (λ i → x ≡ x)  p)) ∙
                                                                          (λ i → A ((transportRefl p) i)))})
                                                     ((λ i → transportRefl (A (transport (λ i → x ≡ x) p )) (i ∧ j)) ∙
                                                     (λ i → transportRefl (A ((transportRefl p) i)) (i ∨ j)))


     invCanceller : ∀ {ℓ} {A : Type ℓ} {a b c d e f : A} (p : a ≡ b) (q : b ≡ c) (r : b ≡ d) (s : d ≡ e) (t : f ≡ e) →
                    p ∙ q ∙ (sym q ∙ r ∙ s ∙ sym t) ∙ t ≡ p ∙ r ∙ s
     invCanceller {a = a} {b = b} {c = c} {d = d} {e = e} {f = f}  = 
                   J (λ b p → (q : b ≡ c) (r : b ≡ d) (s : d ≡ e) (t : f ≡ e) →
                               p ∙ q ∙ (sym q ∙ r ∙ s ∙ sym t) ∙ t ≡ p ∙ r ∙ s)
                               (J (λ c q → (r : a ≡ d) (s : d ≡ e) (t : f ≡ e) →
                                           refl ∙ q ∙ ((λ i → q (~ i)) ∙ r ∙ s ∙ (λ i → t (~ i))) ∙ t ≡ refl ∙ r ∙ s)
                                   (J (λ d r → (s : d ≡ e) (t : f ≡ e) →
                                               (λ _ → a) ∙ (λ _ → a) ∙ ((λ _ → a) ∙ r ∙ s ∙ (λ i → t (~ i))) ∙ t  ≡ (λ _ → a) ∙ r ∙ s)
                                      (J (λ e s → (t : f ≡ e) →
                                                  (λ _ → a) ∙ (λ _ → a) ∙ ((λ _ → a) ∙ (λ _ → a) ∙ s ∙ (λ i → t (~ i))) ∙ t  ≡ (λ _ → a) ∙ (λ _ → a) ∙ s)
                                         λ t → sym (lUnit ((λ _ → a) ∙ ((λ _ → a) ∙ (λ _ → a) ∙ refl ∙ (λ i → t (~ i))) ∙ t)) ∙
                                               sym (lUnit (((λ _ → a) ∙ (λ _ → a) ∙ refl ∙ (λ i → t (~ i))) ∙ t)) ∙
                                               (λ k → (lUnit (lUnit (lUnit (sym t) (~ k)) (~ k)) (~ k)) ∙ t) ∙
                                               lCancel t ∙
                                               λ k → lUnit (lUnit refl k) k)))



{- given things compue properly, we transform the inner transport as follows -}
test : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
       (RlFun2 a x1 n iscon (merid x1)) (transport (λ i → cong (λ p₁ → ∥ fiber (λ y₁ → σ y₁ {a}) p₁ ∥ ℕ→ℕ₋₂ (n + n)) (pairLemma3 (merid x1) (sym (merid x1))) i)
                                                  (transport (λ i → (transportRefl (∥ fiber (λ y₁ → σ y₁ {a})
                                                                    (subst (_≡_ north) (sym (merid x1)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)))i)
                                                   ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣))
        ≡ ∣ x1 , refl ∣
test n a x1 iscon = (RlFun2 a x1 n iscon (merid x1)) (outer (inner guy)) ≡⟨ (λ j → (RlFun2 a x1 n iscon (merid x1)) (outer (innerTransp j))) ⟩
                    (RlFun2 a x1 n iscon (merid x1)) (outer guy) ≡⟨ (λ j → (RlFun2 a x1 n iscon (merid x1)) (outerTransp j)) ⟩
                    (RlFun2 a x1 n iscon (merid x1)) guy2 ≡⟨ refl ⟩
                    sufMap2 n x1 a a iscon (merid x1) (rCancel (merid a) ∙ sym (rCancel (merid x1))) ≡⟨ cong (λ x → x (rCancel (merid a) ∙ sym (rCancel (merid x1))))
                                                                                                             (sufMap2Id n a x1 iscon) ⟩
                    ∣ x1 , switcher (merid a) (merid x1) (merid x1) (rCancel (merid a) ∙ sym (rCancel (merid x1))) ∣ ≡⟨ (λ j → ∣ x1 , switcherLemma (merid a) (merid x1) j ∣) ⟩
                    ∣ x1 , refl ∣ ∎
  where
  switcherLemma : ∀ {ℓ} {A : Type ℓ} {a b c : A} (p : a ≡ b) (q : a ≡ c) → switcher p q q (rCancel p ∙ (sym (rCancel q))) ≡ refl  
  switcherLemma {A = A} {a = a} {c = c} = J (λ b p → (q : a ≡ c) → switcher p q q (rCancel p ∙ (sym (rCancel q))) ≡ refl)
                                            (J (λ c q → switcher refl q q (rCancel refl ∙ (sym (rCancel q))) ≡ refl)
                                                ((λ j → switcher refl refl refl (rCancel (rCancel refl) j )) ∙
                                                 cong (λ x → x refl) (switcherRefl) ∙
                                                 (λ j → lUnit refl ∙
                                                        cong (λ x → x ∙ refl)
                                                        (lUnit refl ∙ (lUnit (sym (lUnit (sym refl))) (~ j))) ∙
                                                        lCancel refl) ∙
                                                 (λ j → lUnit refl ∙
                                                        cong (λ x → x ∙ refl)
                                                        (rCancel (lUnit refl) j ) ∙
                                                        lCancel refl) ∙
                                                 (λ j → lUnit refl ∙
                                                        lUnit (lCancel refl) (~ j)) ∙
                                                 (λ j → rCancel (lUnit refl) j)))
        where
        helper2 : cong (λ x → x ∙ refl) (refl {x = (λ _ → a)})  ≡ refl
        helper2 = refl
  guy : transport (λ _ → Type _) (∥ fiber (λ y₁ → σ y₁ {a}) (subst (_≡_ north) (λ i → merid x1 (~ i)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n))
  guy = ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣

  guy2 : ∥ fiber (λ y → σ y) (merid x1 ∙ sym (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)
  guy2 = ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∣
  
  inner : transport (λ _ → Type _) (∥ fiber (λ y₁ → σ y₁ {a}) (subst (_≡_ north) (λ i → merid x1 (~ i)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)) →
          ∥ fiber (λ y₁ → σ y₁ {a}) (subst (_≡_ north) (λ i → merid x1 (~ i)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)
  inner = transport (λ i → (transportRefl (∥ fiber (λ y₁ → σ y₁ {a}) (subst (_≡_ north) (sym (merid x1)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)))i)
  
  outer : transport (λ _ → Type _) (∥ fiber (λ y₁ → σ y₁ {a}) (subst (_≡_ north) (λ i → merid x1 (~ i)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)) →
          ∥ fiber (λ y → σ y) (merid x1 ∙ sym (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)
  outer = transport (λ i → cong (λ p₁ → ∥ fiber (λ y₁ → σ y₁ {a}) p₁ ∥ ℕ→ℕ₋₂ (n + n)) (pairLemma3 (merid x1) (sym (merid x1))) i)
  
  innerTransp : inner guy ≡ guy
  innerTransp =
     (λ j → (transport (λ i → (transportRefl (∥ fiber (λ y₁ → σ y₁ {a}) (subst (_≡_ north) (sym (merid x1)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n))) (i ∨ j))  guy ))
                                                                    ∙  transportRefl guy
  outerTransp : outer guy ≡ guy2
  outerTransp = (λ j →  transport (λ i → cong (λ p₁ → ∥ fiber (λ y₁ → σ y₁ {a}) p₁ ∥ ℕ→ℕ₋₂ (n + n)) (pairLemma3 (merid x1) (sym (merid x1))) i)
                                  ∣ a , rUnit (rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1)))) j  ∣  ) ∙
                (λ j → transport (λ i → cong (λ p₁ → ∥ fiber (λ y₁ → σ y₁ {a}) p₁ ∥ ℕ→ℕ₋₂ (n + n)) (pairLemma3 (merid x1) (sym (merid x1))) (i ∨ j))
                       ∣ a , (rCancel (merid a) ∙
                             sym (rCancel (merid x1)) ∙
                             sym (pairLemma3 (merid x1) (sym (merid x1)))) ∙
                             (λ i → (pairLemma3 (merid x1) (sym (merid x1))) (i ∧ j)) ∣) ∙
                (λ j → transportRefl (∣ a , (rCancel (merid a) ∙
                                            sym (rCancel (merid x1)) ∙
                                            sym (pairLemma3 (merid x1) (sym (merid x1)))) ∙
                                            (pairLemma3 (merid x1) (sym (merid x1))) ∣) j) ∙
                (λ j → ∣ a , assoc (rCancel (merid a))
                                   (sym (rCancel (merid x1)))
                                   (sym (pairLemma3 (merid x1) (sym (merid x1)))) j
                             ∙ (pairLemma3 (merid x1) (sym (merid x1))) ∣ ) ∙
                (λ j → ∣ a , assoc ((rCancel (merid a)) ∙ (sym (rCancel (merid x1))))
                                   (sym (pairLemma3 (merid x1) (sym (merid x1))))
                                   (pairLemma3 (merid x1) (sym (merid x1))) (~ j) ∣) ∙
                (λ j → ∣ a , ((rCancel (merid a)) ∙ (sym (rCancel (merid x1)))) ∙ (lCancel (pairLemma3 (merid x1) (sym (merid x1))) j)  ∣) ∙
                λ j → ∣ a , rUnit ((rCancel (merid a)) ∙ (sym (rCancel (merid x1)))) (~ j) ∣



wowie : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
        (transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (merid x1) (transpRCancel (λ i₁ → north ≡ merid x1 i₁) (merid x1)) i)))
                   ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣
        ≡ transport (λ i → (uncurry (CODE'' {a = a} n iscon) (pair⁼'' (merid x1) (pairLemma2 (merid x1)) i))) ∣ a , rCancel (merid a) ∣
wowie {ℓ} {A = A} n a x1 iscon = wowie2 (south) (merid x1) 
  where
  wowie2 : (y : Susp A) → (p : north ≡ y) → (transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' p (transpRCancel (λ i₁ → north ≡ p i₁) p) i))) ∣ a , rCancel (merid a) ∙ sym (rCancel p) ∙ sym (pairLemma3 p (sym p)) ∣
           ≡ transport (λ i → (uncurry (CODE'' {a = a} n iscon) (pair⁼'' p (pairLemma2 p) i))) ∣ a , rCancel (merid a) ∣
  wowie2 y = J (λ y p → (transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' p (transpRCancel (λ i₁ → north ≡ p i₁) p) i)))
                                    ∣ a , rCancel (merid a) ∙ sym (rCancel p) ∙ sym (pairLemma3 p (sym p)) ∣
                        ≡ transport (λ i → (uncurry (CODE'' {a = a} n iscon) (pair⁼'' p (pairLemma2 p) i))) ∣ a , rCancel (merid a) ∣ )
                ((transport (λ i → uncurry (CODE'' n iscon) (pair⁼'' refl (transpRCancel (λ i₁ → north ≡ refl i₁) refl) i)))
                               ∣ a , rCancel (merid a) ∙ (sym (rCancel refl)) ∙ (sym (pairLemma3 refl refl)) ∣
                               
                ≡⟨ ((λ j → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' refl (transpRCancelRefl refl j) i))
                                     ∣ a , rCancel (merid a) ∙ (sym (rCancel refl)) ∙ (sym (pairLemma3ReflRefl j)) ∣)) ⟩
                                     
                (transport (λ i → uncurry (CODE'' n iscon) (pair⁼'' refl (transportRefl (transport refl refl) ∙ transportRefl refl) i)))
                               ∣ a , rCancel (merid a) ∙ (sym (rCancel refl)) ∙ sym (transportRefl refl ∙ lUnit refl) ∣
                               
                ≡⟨ stupidAgda ⟩
                
                transport (λ i → uncurry (CODE'' {a = a} n iscon)
                                          (north , (sym (transportRefl ((transport (λ z → _≡_ {A = Susp A} north north) (λ _ → north)))) ∙
                                                         transportRefl (transport (λ z → _≡_ {A = Susp A} north north) (λ _ → north)) ∙
                                                         transportRefl (λ _ → north)) i))
                           ∣ a , rCancel (merid a) ∙ (sym (rCancel refl)) ∙ sym (transportRefl refl ∙ lUnit refl) ∣
                           
                ≡⟨ (λ j → transport (λ i → uncurry (CODE'' {a = a} n iscon)
                                                    (north , assoc ((sym (transportRefl (transport (λ z → _≡_ {A = Susp A}  north north)
                                                                                                   (λ _ → north)))))
                                                                   (transportRefl (transport (λ z → _≡_ {A = Susp A} north  north) (λ _ → north)))
                                                                   (transportRefl (λ _ → north)) j i))
                                     ∣ a , rCancel (merid a) ∙ (sym (rCancel refl)) ∙ sym (transportRefl refl ∙ lUnit refl) ∣) ⟩
                                     
                transport ((λ i → uncurry (CODE'' {a = a} n iscon)
                                          (north , ((sym (transportRefl (transport (λ z → _≡_ {A = Susp A}  north north) (λ _ → north))) ∙
                                                     transportRefl (transport (λ z → _≡_ {A = Susp A} north  north) (λ _ → north))) ∙
                                                     transportRefl (λ _ → north)) i)))
                          ∣ a , rCancel (merid a) ∙ (sym (rCancel refl)) ∙ sym (transportRefl refl ∙ lUnit refl) ∣
                          
                ≡⟨ ((λ j → transport (λ i → uncurry (CODE'' {a = a} n iscon)
                                                    (north , (lCancel (transportRefl (transport (λ z → _≡_ {A = Susp A} north  north)
                                                                                     (λ _ → north))) j ∙
                                                                                     (transportRefl (λ _ → north))) i))
                                     ∣ a , rCancel (merid a) ∙ (sym (rCancel refl)) ∙ sym (transportRefl refl ∙ lUnit refl) ∣)) ⟩
                                     
                 transport (λ i →  uncurry (CODE'' {a = a} n iscon) (north , (refl ∙ (transportRefl (λ _ → north))) i))
                           ∣ a , rCancel (merid a) ∙ (sym (rCancel refl)) ∙ sym (transportRefl refl ∙ lUnit refl) ∣
                           
                ≡⟨ ((λ j → transport (λ i →  uncurry (code' {a = a} n iscon)
                                                     (north , (lUnit (transportRefl (λ _ → north)) (~ j)) i))
                                     ∣ a , rCancel (merid a) ∙ (sym (rCancel refl)) ∙ sym (transportRefl refl ∙ lUnit refl) ∣) ) ⟩
                                     
                transport (λ i →  uncurry (CODE'' {a = a} n iscon)
                                               (north , ((transportRefl (λ _ → north))) i))
                          ∣ a , rCancel (merid a) ∙ (sym (rCancel refl)) ∙ sym (transportRefl refl ∙ lUnit refl) ∣
                          
                ≡⟨ ((λ j → transport (λ i →  uncurry (CODE'' {a = a} n iscon) (north , ((transportRefl (λ _ → north))) i))
                                     ∣ a , cancelHelper j ∣ )) ⟩
                                     
                transport (λ i →  uncurry (CODE'' {a = a} n iscon) (north , ((transportRefl (λ _ → north))) i))
                          ∣ a , rCancel (merid a) ∙ (sym (transportRefl refl)) ∣
                          
                ≡⟨ pathPtest2 ⟩
                
                transport (λ i → uncurry (CODE'' {a = a} n iscon) (north , λ _ → north)) ∣ a , rCancel (merid a)∣
                
                ≡⟨ sym (backAgain) ⟩
                
                (transport (λ i → uncurry (CODE'' n iscon) (pair⁼'' refl (pairLemma2 refl) i))
                           ∣ a , rCancel (merid a) ∣) ∎)
    where
    backAgain : transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' refl (pairLemma2 refl) i))
                                         ∣ a , rCancel (merid a) ∣
              ≡ (transport (λ i → uncurry (CODE'' {a = a} n iscon) (north , λ _ → north))
                           ∣ a , rCancel (merid a)∣)
    backAgain = (λ j → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' refl (pairLemma2Refl j) i)) ∣ a , rCancel (merid a) ∣) ∙
                    (λ j → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼''Refl (transportRefl refl) j i)) ∣ a , rCancel (merid a) ∣)
                    ∙ λ j → transport (λ i → uncurry (CODE'' {a = a} n iscon) (north , lCancel (transportRefl refl) j i)) ∣ a , rCancel (merid a) ∣

    cancelHelper : rCancel (merid a) ∙ (λ i → rCancel (λ _ → north) (~ i)) ∙ sym (transportRefl refl ∙ lUnit refl) ≡ rCancel (merid a) ∙ sym (transportRefl refl)
    cancelHelper = (λ j → rCancel (merid a) ∙ (λ i → rCancel (λ _ → north) (~ i)) ∙ symDistr (transportRefl refl) (lUnit refl) j) ∙
                       (λ j → rCancel (merid a) ∙ assoc (sym (rCancel (λ _ → north))) (sym (lUnit refl)) (sym (transportRefl refl)) j) ∙
                       (λ j → rCancel (merid a) ∙ lCancel (sym (lUnit refl)) j ∙ sym (transportRefl refl)) ∙
                       λ j → rCancel (merid a) ∙ lUnit (sym (transportRefl refl)) (~ j)

    stupidAgda : transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ _ → north) (transportRefl (transport (λ _ → _≡_ {A = Susp A} north north) (λ _ → north)) ∙ transportRefl (λ _ → north)) i))
                           ∣ a , rCancel (merid a) ∙ (λ i → rCancel (λ _ → north) (~ i)) ∙ (λ i → pairLemma3ReflRefl i1 (~ i)) ∣
               ≡ transport (λ i → uncurry (CODE'' {a = a} n iscon)
                                          (north , (sym (transportRefl ((transport (λ z → _≡_ {A = Susp A} north north) (λ _ → north)))) ∙
                                                         transportRefl (transport (λ z → _≡_ {A = Susp A} north north) (λ _ → north)) ∙
                                                         transportRefl (λ _ → north)) i))
                           ∣ a , rCancel (merid a) ∙ (λ i → rCancel (λ _ → north) (~ i)) ∙ (λ i → pairLemma3ReflRefl i1 (~ i)) ∣ 
    stupidAgda j = transport (λ i → uncurry (CODE'' {a = a} n iscon)
                                            ((pair⁼''Refl ((transportRefl (transport (λ _ → _≡_ {A = Susp A} north north) (λ _ → north)) ∙
                                                            transportRefl (λ _ → north))) j) i))
                             ∣ a , rCancel (merid a) ∙ (λ i → rCancel (λ _ → north) (~ i)) ∙ (λ i → pairLemma3ReflRefl i1 (~ i)) ∣

    pathPtest2 : (transport (λ i → uncurry  (CODE'' {a = a} n iscon)
                                            (north , (transportRefl λ _ → north) i))
                            ∣ a , rCancel (merid a) ∙ (sym (transportRefl refl)) ∣)
               ≡ (transport (λ i → uncurry (code' {a = a} n iscon) (north , λ _ → north))
                            ∣ a , rCancel (merid a)∣)
    pathPtest2 = (transport (λ i → uncurry (CODE'' {a = a} n iscon)
                                           (north , (transportRefl (λ _ → north)) i))
                            ∣ a , rCancel (merid a) ∙ (sym (transportRefl (λ _ → north))) ∣)
                     ≡⟨ (λ j → (transport (λ i → uncurry (CODE'' {a = a} n iscon)
                                                         (north , (transportRefl {A = north ≡ north} (λ _ → north) (i ∨ j))))
                                          ∣ a , rCancel (merid a) ∙ ((λ z → transportRefl {A = north ≡ north} ((λ i → north)) ((~ z) ∨ j))) ∣)) ⟩
                     (transport (λ i → uncurry {C = λ a b → Type ℓ} (CODE'' {a = a} n iscon) (north , λ _ → north))
                                               ∣ a , rCancel (merid a) ∙ (λ _ _ → north) ∣)
                     ≡⟨ (λ j → (transport (λ i → uncurry (CODE'' {a = a} n iscon) (north , λ _ → north))
                                          ∣ a , ((rUnit (rCancel (merid a))) (~ j)) ∣)) ⟩
                     transport (λ i → uncurry (CODE'' {a = a} n iscon) (north , (λ _ → north)))
                               ∣ a , rCancel (merid a)∣ ∎



--------- From other file ----------------
littleCanceller : {a b c d e : A} → (p : a ≡ b) (q : a ≡ c) (r : c ≡ d) (s : d ≡ e) →
                                       p ∙ (sym p ∙ q ∙ r ∙ s) ∙ sym s ≡ q ∙ r
littleCanceller {a = a} {b = b} {c = c} p q r s  = p ∙ (sym p ∙ q ∙ r ∙ s) ∙ sym s     ≡⟨ assoc p (sym p ∙ q ∙ r ∙ s) (sym s) ⟩ 
                                                   (p ∙ sym p ∙ q ∙ r ∙ s) ∙ sym s     ≡⟨ (λ j → assoc p (sym p) (q ∙ r ∙ s) j ∙ sym s) ⟩ 
                                                   ((p ∙ sym p) ∙ q ∙ r ∙ s) ∙ sym s   ≡⟨ (λ j → (rCancel p j ∙ q ∙ r ∙ s) ∙ sym s) ⟩ 
                                                   (refl ∙ q ∙ r ∙ s) ∙ sym s          ≡⟨ (λ j → lUnit (q ∙ r ∙ s) (~ j) ∙ sym s) ⟩ 
                                                   (q ∙ r ∙ s) ∙ sym s                 ≡⟨ (λ j → assoc q r s j ∙ sym s) ⟩ 
                                                   ((q ∙ r) ∙ s) ∙ sym s               ≡⟨ sym (assoc (q ∙ r) s (sym s)) ⟩ 
                                                   (q ∙ r) ∙ s ∙ sym s                 ≡⟨ (λ j → (q ∙ r) ∙ (rCancel s j)) ⟩ 
                                                   (q ∙ r) ∙ refl                      ≡⟨ sym (rUnit (q ∙ r)) ⟩
                                                   q ∙ r ∎


littleCanceller2 : {a b c d e : A} → (p : a ≡ b) (q : b ≡ c) (r : b ≡ d) (s : b ≡ e) →
                                       (p ∙ q) ∙ ((sym q) ∙ r) ∙ sym r ∙ s ≡ p ∙ s
littleCanceller2 = {!!}




pairLemmaCancel : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) →
                  pairLemma3 (p ∙ sym (λ _ → y)) (λ _ → y) ∙ sym (assocJ p (λ _ → y) (λ _ → y)) ∙ (λ i → p ∙ lCancel (λ _ → y) i) ∙ sym (rUnit p)
                  ≡
                  transportRefl (p ∙ sym (λ _ → y)) ∙ sym (rUnit p)
pairLemmaCancel {x = x} =
        J (λ y p → pairLemma3 (p ∙ sym (λ _ → y)) (λ _ → y) ∙ sym (assocJ p (λ _ → y) (λ _ → y)) ∙ (λ i → p ∙ lCancel (λ _ → y) i) ∙ sym (rUnit p)
                    ≡
                   transportRefl (p ∙ sym (λ _ → y)) ∙ sym (rUnit p))
          ((λ k → pairLemma3Id (refl ∙ (λ i → x)) (λ _ → x) k ∙
                  (λ i → assocJ refl (λ _ → x) (λ _ → x) (~ i)) ∙
                  (λ i → refl ∙ lCancel (λ _ → x) i) ∙ (λ i → rUnit refl (~ i))) ∙
          (λ k → pairLemma3*Refl (refl ∙ (λ i → x)) k ∙
                  (λ i → assocJRefl k (~ i)) ∙
                  (λ i → refl ∙ lCancel (λ _ → x) i) ∙ (λ i → rUnit refl (~ i))) ∙
          (λ k → (transportRefl (refl ∙ (λ _ → x)) ∙ rUnit (refl ∙ (λ _ → x))) ∙
                  (symDistr (λ i → refl ∙ rCancel refl i) (rUnit (refl ∙ refl)) k ) ∙
                  (λ i → refl ∙ lCancel (λ _ → x) i) ∙ (λ i → rUnit refl (~ i))) ∙
          littleCanceller2 (transportRefl (refl ∙ (λ _ → x))) (rUnit (refl ∙ (λ _ → x))) (λ i → refl ∙ rCancel refl (~ i)) (λ i → rUnit refl (~ i)))




inv-rUnit : ∀ {ℓ} {A : Type ℓ} (x : A) → (λ i → rUnit (rUnit (λ _ → x) (~ i)) i ) ≡ refl
inv-rUnit x = transport (λ i → PathP (λ j → (lCancel (λ k → (λ _ → x) ∙ (λ _ → x) ≡ rUnit (λ _ → x) k) i) j)
                                 (λ i → rUnit (rUnit (λ _ → x) (~ i)) i )
                                 refl)
                    (lemma2 x)
  where
  lemma2 : ∀ {ℓ} {A : Type ℓ} (x : A) →
           PathP (λ i → ((λ k → (λ _ → x) ∙ (λ _ → x) ≡ rUnit (λ _ → x) (~ k)) ∙
                          λ k → (λ _ → x) ∙ (λ _ → x) ≡ rUnit (λ _ → x) k) i)
                 (λ i → rUnit (rUnit (λ _ → x) (~ i)) i )
                 refl
  lemma2 x = compPathP (λ k i → rUnit (rUnit (λ _ → x) (~ i)) (i ∧ (~ k)))
                       λ k i → rUnit (λ _ → x) (~ i ∨ k)


ok : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} {A B : x ≡ y → Type ℓ'} (p : x ≡ y) → 
                                        cong A (rUnit (transport (λ i → x ≡ y) (p ∙ (λ _ → y)))) ∙
                                        cong A (λ i → (transportRefl (p ∙ (λ _ → y)) i) ∙ refl) ∙
                                        refl ∙
                                        cong A (λ i → rUnit p (~ i) ∙ refl)
                                        ≡
                                        cong A (transportRefl (p ∙ (λ _ → y)))
ok {ℓ' = ℓ'} {x = x} {y = y} {A = A} {B = B} p = 
         J (λ y p → (A B : x ≡ y → Type ℓ') →
                    cong A (rUnit (transport (λ i → x ≡ y) (p ∙ (λ _ → y)))) ∙
                    (cong A (λ i → (transportRefl (p ∙ (λ _ → y)) i) ∙ refl)) ∙
                    refl ∙
                    (cong A (λ i → rUnit p (~ i) ∙ refl))
                    ≡
                    cong A (transportRefl (p ∙ (λ _ → y))))
                    (λ A B → ((λ k → (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (refl ∙ (λ _ → x))) (i ∧ (~ k)))) ∙
                                    (λ i → A (rUnit (transportRefl (refl ∙ (λ _ → x)) i) (~ k))) ∙
                                    (λ i → A (rUnit (rUnit ((λ _ → x)) ((~ k) ∨ (~ i))) ((~ k) ∨ i))) ∙
                                    λ i → A ((rUnit (λ _ → x) ((~ i) ∧ (~ k))) ∙ refl)) ) ∙
                             (λ k → lUnit ((λ i → A (transportRefl (refl ∙ (λ _ → x)) i)) ∙
                                           (rUnit (λ i → A (rUnit (rUnit ((λ _ → x)) (~ i)) i )) (~ k))) (~ k)) ∙
                             (λ k → cong A (transportRefl ((λ _ → x) ∙ (λ _ → x))) ∙
                                    λ i → A (inv-rUnit x k i)) ∙
                             sym (rUnit (cong A (transportRefl ((λ _ → x) ∙ (λ _ → x))))))
                    p A B


funExt-part' : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} (ma mx1 : x ≡ y)  →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                                                                  funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y}
                                                                                       ma A
                                                                                       B
                                                                                       (equivTest' {X = X} ma
                                                                                                   {A = A}
                                                                                                   {B = B}
                                                                                         r))
                                                                                        (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
                ≡
                cong (λ f → f (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))) (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} ma A) ∙
                transportRefl (A (transport (λ i → x ≡ ma (~ i)) (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))) ∙
                cong A (pairLemma3 (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)) (sym ma)) ∙
                r (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
funExt-part' {ℓ' = ℓ'} {X = X} {x = x} {y = y} {A = A} {B = B} ma mx1 =

              J (λ y ma → {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} (mx1 : x ≡ y)  →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                                                                  funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y}
                                                                                       ma A
                                                                                       B
                                                                                       (equivTest' {X = X} ma
                                                                                                   {A = A}
                                                                                                   {B = B}
                                                                                         r))
                                                                                        (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
                ≡
                cong (λ f → f (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))) (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} ma A) ∙
                transportRefl (A (transport (λ i → x ≡ ma (~ i)) (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))) ∙
                cong A (pairLemma3 (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)) (sym ma)) ∙
                r (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))
                (λ {A} {B} mx1 r → (λ k →  funExt⁻ (Lemma296Funs.inv''Id {X = X} {A = λ y → x ≡ y} (λ _ → x) A B (~ k)
                                                                         (equivTestId {X = X} (λ _ → x) {A = A} {B = B} r k))
                                                   (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                    (λ k →  funExt⁻ (ReflCases.invRefl {X = X} {A = λ y → x ≡ y} A B k 
                                                                         (equivTestRefl {X = X} {A = A} {B = B} k r))
                                                      (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                    (λ k →  funExt⁻ (transportRefl A ∙
                                                   funExt λ z → sym (transportRefl (A z))  ∙
                                                                (transportRefl (A z) ∙
                                                                cong A (rUnit z) ∙
                                                                r z ∙
                                                                cong B (sym (transportRefl z))) ∙
                                                                λ i → (B (transportRefl z i)))
                                                   (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                    (λ k →  funExt⁻ (transportRefl A ∙
                                                   funExt λ z → littleCanceller (sym (transportRefl (A z)))
                                                                                (cong A (rUnit z))
                                                                                (r z)
                                                                                (cong B (sym (transportRefl z))) k)
                                                   (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                    (λ k → funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                           cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                       (assoc (funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))
                                              ( cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))))
                                              (r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                       (λ k → lemma1 {X = X} {A = A} mx1 k ∙
                                              r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                      (sym (assoc (transportRefl
                                                    (A
                                                     (transport (λ i → x ≡ x)
                                                      (transport (λ i → x ≡ x) (mx1 ∙ (λ i → x))))))
                                                  ((λ i →
                                                       A
                                                       (pairLemma3
                                                        (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ i₁ → x)))
                                                        (λ i₁ → x) i)))
                                                  (r (transport (λ i → x ≡ x) (mx1 ∙ (λ i → x)))))) ∙
                                      (lUnit (transportRefl
                                                    (A
                                                     (transport (λ i → x ≡ x)
                                                      (transport (λ i → x ≡ x) (mx1 ∙ (λ i → x)))))
                                                    ∙
                                                    (λ i →
                                                       A
                                                       (pairLemma3
                                                        (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ i₁ → x)))
                                                        (λ i₁ → x) i))
                                                    ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ i → x))))) ∙
                                      λ k → (λ i →
                                                       Lemma294'Refl {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} A (~ k) i
                                                       (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ i₁ → x))))
                                                    ∙
                                                    transportRefl
                                                    (A
                                                     (transport (λ i → x ≡ x)
                                                      (transport (λ i → x ≡ x) (mx1 ∙ (λ i → x)))))
                                                    ∙
                                                    (λ i →
                                                       A
                                                       (pairLemma3
                                                        (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ i₁ → x)))
                                                        (λ i₁ → x) i))
                                                    ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ i → x))))

                ma {A} {B} mx1
                             where
                             lemma1 : ∀ {ℓ ℓ'} {X : Type ℓ} {x : X} {A : x ≡ x → Type ℓ'} (mx1 : x ≡ x) →
                                        funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                           cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ≡
                                        transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                        (λ i → A (pairLemma3 (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) (λ _ → x) i))
                             lemma1 {x = x} {A = A}  mx1 = sym ((λ k → transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                                                       (λ i → A (pairLemma3Id (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) (λ _ → x) k i))) ∙
                                                      (λ k → transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                                             (λ i → A (pairLemma3*Refl (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) k i))) ∙
                                                      (λ k → transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                                             λ i → A ((transportRefl (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                                                       rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x)))) i)) ∙
                                                      (λ k → transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                                             congComp2 A (transportRefl (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))))
                                                                         (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x)))) (~ k)) ∙
                                                      (λ k → (λ i → transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) (i ∨ k)) ∙
                                                            cong A (transportRefl (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                                             cong A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                                      (sym (lUnit (cong A (transportRefl (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                                             cong A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))))))))

funExt-part'' : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} (ma mx1 : x ≡ y)  →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                cong (λ f → f (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))) (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} ma A) ∙
                transportRefl (A (transport (λ i → x ≡ ma (~ i)) (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))) ∙
                cong A (pairLemma3 (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)) (sym ma)) ∙
                r (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
                ≡
                (cong (λ f → f (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))) (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} ma A) ∙
                transportRefl (A (transport (λ i → x ≡ ma (~ i)) (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))) ∙
                cong A (transpRCancel (λ i → x ≡ ma (~ i)) (mx1 ∙ sym ma))) ∙
                r mx1 ∙
                cong B (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙ sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1)))
funExt-part'' {ℓ' = ℓ'} {X = X} {x = x} {y = y} {A = A} {B = B} ma mx1 =
              J (λ y ma → ( mx1 : x ≡ y) {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'}
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                cong (λ f → f (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))) (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} ma A) ∙
                transportRefl (A (transport (λ i → x ≡ ma (~ i)) (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))) ∙
                cong A (pairLemma3 (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)) (sym ma)) ∙
                r (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
                ≡
                (cong (λ f → f (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))) (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} ma A) ∙
                transportRefl (A (transport (λ i → x ≡ ma (~ i)) (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))) ∙
                cong A (transpRCancel (λ i → x ≡ ma (~ i)) (mx1 ∙ sym ma))) ∙
                r mx1 ∙
                cong B (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙ sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1))))
                (λ p {A} {B} r → (λ k → cong (λ f → f (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) (Lemma294'Refl {A = λ y → x ≡ y} {B = λ _ → Type ℓ'}  A k) ∙
                                        transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (p ∙ (λ _ → x))))) ∙
                                        cong A (pairLemma3 (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) (λ _ → x)) ∙
                                        r (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                 (sym (lUnit (transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (p ∙ (λ _ → x))))) ∙
                                          cong A (pairLemma3 (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) (λ _ → x)) ∙
                                          r (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))))) ∙
                                 (sym (lUnit (cong A (pairLemma3 (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) (λ _ → x)) ∙
                                          r (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))))) ∙
                                 (λ k → cong A (pairLemma3Id (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) (λ _ → x) k) ∙
                                         r (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                 (λ k → cong A (pairLemma3*Refl (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) k) ∙
                                         r (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                 (λ k → cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        r (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                 (fixLater {A = A} {B = B} p r) ∙
                                 (λ k → cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        refl ∙ refl ∙
                                        r (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) ∙
                                        refl ∙ refl) ∙
                                 (λ k → cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        cong A (λ i → (transportRefl (p ∙ (λ _ → x)) (k ∧ i)) ∙ refl) ∙ refl ∙
                                        r (transportRefl (p ∙ (λ _ → x)) k) ∙
                                        refl ∙ cong B λ i → (transportRefl (p ∙ (λ _ → x)) (k ∧ (~ i)))) ∙
                                 (λ k → cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        cong A (λ i → (transportRefl (p ∙ (λ _ → x)) i) ∙ refl) ∙ cong A (λ i → rUnit p (~ k ∨ (~ i)) ∙ refl) ∙
                                        r (rUnit p (~ k)) ∙
                                        cong B (λ i → rUnit p (~ k ∨ i)) ∙ cong B λ i → ((transportRefl (p ∙ (λ _ → x)) (~ i)))) ∙
                                 (λ k → congComp2 A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x))))) (rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x))))
                                        (~ k) ∙
                                        cong A (λ i → (transportRefl (p ∙ (λ _ → x)) i) ∙ refl) ∙
                                        lUnit (cong A (λ i → rUnit p (~ i) ∙ refl)) k ∙
                                        r p ∙
                                        cong B (λ i → rUnit p i) ∙ cong B λ i → (transportRefl (p ∙ (λ _ → x)) (~ i))) ∙
                                 fixLater2 (cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x))))))
                                           (cong A ((rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x))))))
                                           (cong A (λ i → (transportRefl (p ∙ (λ _ → x)) i) ∙ refl))
                                           (cong A (λ i → rUnit p (~ i) ∙ refl))
                                           (r p)
                                           (cong B (λ i → rUnit p i) ∙ cong B λ i → (transportRefl (p ∙ (λ _ → x)) (~ i))) ∙
                                 (λ k → (cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x))))) ∙
                                        ok {A = A} {B = B} p k ) ∙
                                        r p ∙
                                        cong B (λ i → rUnit p i) ∙ cong B λ i → (transportRefl (p ∙ (λ _ → x)) (~ i))) ∙
                                 (λ k → congComp2 A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x))))) (transportRefl (p ∙ (λ _ → x))) k ∙
                                        r p ∙
                                        (congComp2 B (rUnit p) (λ i → (transportRefl (p ∙ (λ _ → x)) (~ i))) k)) ∙
                                 (λ k → cong A (transportRefl (transport refl (p ∙ (λ _ → x))) ∙ transportRefl (p ∙ (λ _ → x))) ∙
                                        r p ∙
                                        cong B (symDistr (transportRefl (p ∙ sym (λ _ → x))) (sym (rUnit p)) (~ k))) ∙
                                 (λ k → cong A (transportRefl (transport refl (p ∙ (λ _ → x))) ∙ transportRefl (p ∙ (λ _ → x))) ∙
                                        r p ∙
                                        cong B (sym (pairLemmaCancel p (~ k)))) ∙
                                 (λ k → cong A (transpRCancelRefl (p ∙ (λ _ → x)) (~ k)) ∙
                                        r p ∙
                                        cong B (sym (pairLemma3 (p ∙ sym (λ _ → x)) (λ _ → x) ∙
                                                    sym (assocJ p (λ _ → x) (λ _ → x)) ∙
                                                    (λ i → p ∙ lCancel (λ _ → x) i) ∙ sym (rUnit p)))) ∙
                                 (λ k → lUnit (lUnit (cong A (transpRCancel (λ i → x ≡ x) (p ∙ (λ _ → x)))) k) k ∙
                                        r p ∙
                                        cong B (sym (pairLemma3 (p ∙ (λ _ → x)) (λ _ → x) ∙
                                                    sym (assocJ p (λ _ → x) (λ _ → x)) ∙
                                                    (λ i → p ∙ lCancel (λ _ → x) i) ∙ sym (rUnit p)))) ∙
                                 λ k → (cong (λ f → f (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) (Lemma294'Refl {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} A (~ k)) ∙
                transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (p ∙ (λ _ → x))))) ∙
                cong A (transpRCancel (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                r p ∙
                cong B (sym (pairLemma3 (p ∙ (λ _ → x)) (λ _ → x) ∙
                            sym (assocJ p (λ _ → x) (λ _ → x)) ∙
                            (λ i → p ∙ lCancel (λ _ → x) i) ∙ sym (rUnit p))))
                ma mx1 {A} {B}
                where
                fixLater : {A : x ≡ x → Type ℓ'} {B : x ≡ x → Type ℓ'} (p : x ≡ x) (r : (mx2 : x ≡ x) → A (mx2 ∙ (λ _ → x)) ≡ B mx2) →
                           cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        r (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) ≡
                           cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        refl ∙ refl ∙
                                        r (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) ∙
                                        refl ∙ refl
                fixLater = {!!}

                fixLater2 : ∀ {ℓ} {A : Type ℓ} {a b c d e f g : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : e ≡ f) (u : f ≡ g) →
                                  (p ∙ q) ∙ r ∙ (refl ∙ s) ∙ t ∙ u ≡ (p ∙ q ∙ r ∙ refl ∙ s) ∙ t ∙ u
                fixLater2 p q r s t u = {!!}

funExt-part''' : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} (ma mx1 : x ≡ y)  →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                (λ i → A (transpRCancel (λ i₁ → x ≡ ma (~ i₁)) (mx1 ∙ sym ma) (~ i))) ∙ 
                funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y} ma A B (equivTest' {X = X} ma
                                                                                          {A = A}
                                                                                          {B = B}
                                                                                         r))
                         (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
                  ≡
                 r mx1 ∙
                 cong B (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙ sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1)))
funExt-part''' {ℓ' = ℓ'} {X = X} {x = x} {A = A} {B = B} ma mx1 r =
               J (λ y ma → (A : x ≡ x → Type ℓ') (B : x ≡ y → Type ℓ') (mx1 : x ≡ y)  →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                (λ i → A (transpRCancel (λ i₁ → x ≡ ma (~ i₁)) (mx1 ∙ sym ma) (~ i))) ∙ 
                funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y} ma A B (equivTest' {X = X} ma
                                                                                          {A = A}
                                                                                          {B = B}
                                                                                         r))
                         (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
                  ≡
                 r mx1 ∙
                 cong B (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙ sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1))))
                 (λ A B mx1 r → (λ k → (λ i → A (transpRCancel (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x)) (~ i))) ∙ 
                                       ((funExt-part' {X = X} {x = x} {A = A} {B = B} (λ _ → x) mx1 r) ∙
                                        (funExt-part'' {X = X} {x = x} {A = A} {B = B} (λ _ → x) mx1 r)) k) ∙
                                (λ k → ((λ i → A (transpRCancelRefl (mx1 ∙ (λ _ → x)) k (~ i)))) ∙
                                       (cong (λ f → f (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) (Lemma294'Refl {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} A k) ∙
                                       transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                       cong A (transpRCancelRefl (mx1 ∙ (λ _ → x)) k)) ∙
                                       r mx1 ∙
                                       cong B (sym (pairLemma3 (mx1 ∙ (λ _ → x)) (λ _ → x) ∙ sym (assocJ mx1 (λ _ → x) (λ _ → x)) ∙
                                                   (λ i → mx1 ∙ lCancel (λ _ → x) i) ∙ sym (rUnit mx1)))) ∙
                                (λ k → (λ i → A ((transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x))) (~ i))) ∙
                                       lUnit (transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                              cong A (transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x)))) (~ k) ∙
                                       r mx1 ∙
                                       cong B (sym (pairLemma3 (mx1 ∙ (λ _ → x)) (λ _ → x) ∙ sym (assocJ mx1 (λ _ → x) (λ _ → x)) ∙
                                                   (λ i → mx1 ∙ lCancel (λ _ → x) i) ∙ sym (rUnit mx1)))) ∙
                                (λ k → (λ i → A ((transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x))) (~ i))) ∙
                                        (lUnit (cong A (transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x)))) (~ k)) ∙
                                       r mx1 ∙
                                       cong B (sym (pairLemma3 (mx1 ∙ (λ _ → x)) (λ _ → x) ∙ sym (assocJ mx1 (λ _ → x) (λ _ → x)) ∙
                                                   (λ i → mx1 ∙ lCancel (λ _ → x) i) ∙ sym (rUnit mx1)))) ∙
                                (assoc (sym (cong A (transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x)))))
                                       (cong A (transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x))))
                                       (r mx1 ∙
                                        cong B (sym (pairLemma3 (mx1 ∙ (λ _ → x)) (λ _ → x) ∙ sym (assocJ mx1 (λ _ → x) (λ _ → x)) ∙
                                                    (λ i → mx1 ∙ lCancel (λ _ → x) i) ∙ sym (rUnit mx1))))) ∙
                                (λ k → lCancel (cong A (transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x)))) k ∙
                                        r mx1 ∙
                                        cong B (sym (pairLemma3 (mx1 ∙ (λ _ → x)) (λ _ → x) ∙ sym (assocJ mx1 (λ _ → x) (λ _ → x)) ∙
                                                    (λ i → mx1 ∙ lCancel (λ _ → x) i) ∙ sym (rUnit mx1)))) ∙
                                sym (lUnit (r mx1 ∙
                                        cong B (sym (pairLemma3 (mx1 ∙ (λ _ → x)) (λ _ → x) ∙ sym (assocJ mx1 (λ _ → x) (λ _ → x)) ∙
                                                    (λ i → mx1 ∙ lCancel (λ _ → x) i) ∙ sym (rUnit mx1))))))
                 ma A B mx1 r




{-

funExt-part' : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} (ma mx1 : x ≡ y)  →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                (((λ i → A (transpRCancel (λ i₁ → x ≡ ma (~ i₁)) (mx1 ∙ sym ma) (~ i))) ∙
                                                                  funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y}
                                                                                       ma A
                                                                                       B
                                                                                       (equivTest' {X = X} ma
                                                                                                   {A = A}
                                                                                                   {B = B}
                                                                                         r))
                                                                                        (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))))
                ≡
                (λ i → A (transpRCancel (λ i₁ → x ≡ ma (~ i₁)) (mx1 ∙ sym ma) (~ i))) ∙
                {!r!} ∙
                {!!} ∙
                {!!}
                -- r mx1 ∙ cong B ((rUnit mx1) ∙ (λ i → mx1 ∙ lCancel ma (~ i)) ∙ (assocJ mx1 (sym ma) ma) ∙ sym (pairLemma3 (mx1 ∙ sym ma) ma))

funExt-part' {ℓ' = ℓ'} {X = X} {x = x} {y = y} {A = A} {B = B} ma mx1 =
              J (λ y ma → (mx1 : x ≡ y) {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                (((λ i → A (transpRCancel (λ i₁ → x ≡ ma (~ i₁)) (mx1 ∙ sym ma) (~ i))) ∙
                                                                  funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y}
                                                                                       ma A
                                                                                       B
                                                                                       (equivTest' {X = X} ma
                                                                                                   {A = A}
                                                                                                   {B = B}
                                                                                         r))
                                                                                        (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))))
                ≡
                   {!!}) -- r mx1 ∙ cong B ((rUnit mx1) ∙ (λ i → mx1 ∙ lCancel ma (~ i)) ∙ (assocJ mx1 (sym ma) ma) ∙ sym (pairLemma3 (mx1 ∙ sym ma) ma)))
                (λ mx1 {A} {B} r → (λ k → (λ i → A (transpRCancel (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                           funExt⁻ (Lemma296Funs.inv''Id {X = X} {A = λ y → x ≡ y} (λ _ → x) A B (~ k)
                                                                        (equivTestId {X = X} (λ _ → x) {A = A} {B = B} r k))
                                                     (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ) ∙
                                   (λ k → (λ i → A ((transpRCancelRefl (mx1 ∙ (λ _ → x)) k) (~ i))) ∙
                                           funExt⁻ (ReflCases.invRefl {X = X} {A = λ y → x ≡ y} A B k 
                                                                        (equivTestRefl {X = X} {A = A} {B = B} k r))
                                                     (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   (λ k → (λ i → A ((transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x))) (~ i))) ∙
                                          funExt⁻ (transportRefl A ∙
                                                  funExt λ z → sym (transportRefl (A z))  ∙
                                                               (transportRefl (A z) ∙
                                                               cong A (rUnit z) ∙
                                                               r z ∙
                                                               cong B (sym (transportRefl z))) ∙
                                                               λ i → (B (transportRefl z i)))
                                                  (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   (λ k → (λ i → A ((transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x))) (~ i))) ∙
                                           funExt⁻ (transportRefl A ∙
                                                  funExt λ z → littleCanceller (sym (transportRefl (A z)))
                                                                               (cong A (rUnit z))
                                                                               (r z)
                                                                               (cong B (sym (transportRefl z))) k)
                                                  (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   (λ k → (λ i → A ((transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x))) (~ i))) ∙
                                          funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                          cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   (λ k → (λ i → A ((symDistr (transportRefl (transport refl (mx1 ∙ (λ _ → x)))) (transportRefl (mx1 ∙ (λ _ → x))) k) i)) ∙
                                          funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                          cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   (λ k → congComp2 A (sym ((transportRefl (mx1 ∙ (λ _ → x))))) (sym (transportRefl (transport refl (mx1 ∙ (λ _ → x))))) (~ k) ∙
                                          funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                          cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   sym (assoc (cong A (sym ((transportRefl (mx1 ∙ (λ _ → x))))))
                                              (cong A (sym (transportRefl (transport refl (mx1 ∙ (λ _ → x))))))
                                              (funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                              cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                   (λ k → cong A (sym ((transportRefl (mx1 ∙ (λ _ → x))))) ∙
                                          assoc (cong A (sym (transportRefl (transport refl (mx1 ∙ (λ _ → x))))))
                                                (funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))
                                                (cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) k) ∙
                                   (λ k → cong A (sym ((transportRefl (mx1 ∙ (λ _ → x))))) ∙
                                          lCancel (funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) k ∙
                                          cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   (λ k → cong A (sym ((transportRefl (mx1 ∙ (λ _ → x))))) ∙
                                          lUnit (cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) (~ k) ) ∙
                                   assoc (cong A (sym ((transportRefl (mx1 ∙ (λ _ → x))))))
                                         (cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))))
                                         (r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))  ∙
                                   ((λ k → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                          (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) i))) ∙
                                          (rUnit (rUnit (lUnit (lUnit (r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) k) k ) k) k))) ∙
                                   (λ k → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                          (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) i))) ∙
                                          (((λ i → A ((transportRefl (mx1 ∙ (λ _ → x)) (i ∧ k)) ∙ (λ _ → x))) ∙ refl ∙
                                          (r (transportRefl (mx1 ∙ (λ _ → x)) k))) ∙ refl) ∙
                                          λ i → B (transportRefl (mx1 ∙ (λ _ → x)) (k ∧ (~ i)))) ∙
                                   (λ k → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                          (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) i))) ∙
                                          (((λ i → A ((transportRefl (mx1 ∙ (λ _ → x)) i) ∙ (λ _ → x))) ∙
                                          (λ i → A (rUnit mx1 ((~ k) ∨ (~ i)) ∙ refl)) ∙
                                          r (rUnit mx1 (~ k))) ∙
                                          λ i → B (rUnit mx1 (~ k ∨ i))) ∙
                                          λ i → B (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                   {!r!} ∙
                                   {!!} ∙
                                   {!(λ k → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                          (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) i))) ∙
                                          ((λ i → A ((transportRefl (mx1 ∙ (λ _ → x)) (i ∧ k)) ∙ (λ _ → x))) ∙
                                          (r (transportRefl (mx1 ∙ (λ _ → x)) k))) ∙
                                          λ i → B (transportRefl (mx1 ∙ (λ _ → x)) (k ∧ (~ i))))!})
                ma mx1 {A} {B}
              where
              check : (mx1 : x ≡ x) → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                          (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) i))) ∙
                                          (((λ i → A ((transportRefl (mx1 ∙ (λ _ → x)) i) ∙ (λ _ → x))) ∙
                                          (λ i → A (rUnit mx1 (~ i) ∙ refl)))) ≡ refl
              check mx1 = (λ k → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                          (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) i))) ∙
                                          (((λ i → A ((transportRefl (mx1 ∙ (λ _ → x)) i) ∙ (λ _ → x))) ∙
                                          (lUnit (λ i → A (rUnit mx1 (~ i) ∙ refl)) k)))) ∙
                          (λ k → 
                                       (((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i ∨ k))) ∙
                                       (λ i → A (rUnit (transportRefl (mx1 ∙ (λ _ → x)) k) (i ∧ (~ k))))) ∙
                                       (((λ i → A (rUnit (transportRefl (mx1 ∙ (λ _ → x)) (i ∨ k)) (~ k))) ∙
                                       (λ i → A ((rUnit (rUnit mx1 ((~ i) ∨ (~ k))) (~ k ∨ i))))
                                       ∙ (λ i → A (rUnit mx1 (~ i ∧ (~ k)) ∙ refl)) )))) ∙
                          {- (λ k → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i ∨ k))) ∙
                                  (λ i → A (rUnit (transportRefl (mx1 ∙ (λ _ → x)) k) (i ∧ (~ k))))) ∙
                                  (((λ i → A (rUnit (transportRefl (mx1 ∙ (λ _ → x)) (i ∨ k)) (~ k))) ∙
                                  (λ i → A (hcomp {!!} {!!}))
                                  ∙ (λ i → A (rUnit mx1 (~ i ∧ (~ k)) ∙ refl)) ))) ∙ -}
                          (λ k → {!!}) ∙
                          (λ k i → A (rUnit (rUnit mx1 ((~ i))) i)) ∙
                          (λ k → {!!}) ∙
                          {!!} ∙
                          {!!} ∙
                          {!!} ∙
                          {!!}

                     where
                     rUnitCancel : ∀ {ℓ} {A : Type ℓ} {x : A} → _≡_ {A = (λ _ → x) ∙ (λ _ → x) ≡ (λ _ → x) ∙ (λ _ → x)}(λ i → (rUnit (rUnit (λ _ → x) (~ i) ) i)) (λ i → (rUnit (rUnit (λ _ → x) i ) (~ i)))
                     rUnitCancel {x = x} k i = rUnit (rUnit ((λ _ → x)) ((~ i ∧ k) ∨ (i ∧ k))) {!!}

-}

symDestroyer : {a b c d e : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) → sym (p ∙ q ∙ r ∙ s) ≡ sym s ∙ sym r ∙ sym q ∙ sym p 
symDestroyer p q r s = sym (p ∙ q ∙ r ∙ s)                          ≡⟨ symDistr p (q ∙ r ∙ s) ⟩
                       (sym (q ∙ r ∙ s)) ∙ sym p                    ≡⟨ (λ k → symDistr q (r ∙ s) k ∙ sym p) ⟩
                       (sym (r ∙ s) ∙ sym q) ∙ sym p                ≡⟨ (λ k → (symDistr r s k ∙ sym q) ∙ sym p) ⟩
                       ((sym s ∙ sym r) ∙ sym q) ∙ sym p            ≡⟨ sym (assoc (sym s ∙ sym r) (sym q) (sym p))  ⟩
                       (sym s ∙ sym r) ∙ sym q ∙ sym p              ≡⟨ sym (assoc (sym s) (sym r) (sym q ∙ sym p) ) ⟩
                       sym s ∙ sym r ∙ sym q ∙ sym p ∎

cancellerLemma : ∀ {ℓ} {A : Type ℓ} {a b c : A} (r : b ≡ c) (p : a ≡ b) → canceller r p p refl ≡ refl
cancellerLemma {a = a} {b = b} {c = c} = J (λ c r → (p : a ≡ b) → canceller r p p refl ≡ refl)
                                             (J (λ b p → canceller refl p p (λ _ → p ∙ refl) ≡ (λ _ → p))
                                                ((λ k → cancellerRefl k refl) ∙
                                                (λ k → rUnit refl ∙ (lUnit (sym (rUnit refl)) (~ k))) ∙
                                                rCancel (rUnit refl)))

funPart : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → RlFun2 a a n iscon (merid x1) ∣ x1 , (λ _ → σ x1 {a}) ∣ ≡ ∣ x1 , refl ∣
funPart n a x1 iscon = (λ k → sufMap2 n a a x1 iscon (merid x1) refl) ∙
                       sufMap2Id2 n a x1 iscon ∙
                       (λ k → ∣ x1 , cancellerLemma (sym (merid a)) (merid x1) k ∣)

finalStep : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
                               transport (cong (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)) (sym (pairLemma3 ((merid x1) ∙ sym (merid a)) (merid a) ∙                                                   sym (assocJ (merid x1) (sym (merid a)) (merid a)) ∙ (λ i → (merid x1) ∙ lCancel (merid a) i) ∙ sym (rUnit (merid x1))))) ∣ x1 , refl ∣
                               ≡ ∣ x1 , rUnit (merid x1) ∙ sym (cong (λ x → merid x1 ∙ x) (lCancel (merid a))) ∙
                                                                                   assocJ (merid x1) (sym (merid a)) (merid a) ∙
                                                                                   sym (pairLemma3 {a1 = north} (merid x1 ∙ (sym (merid a))) (merid a)) ∣
finalStep n a x1 iscon  = (λ k → transport (cong (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                 (λ i → (sym (pairLemma3 ((merid x1) ∙ sym (merid a)) (merid a) ∙
                                                 sym (assocJ (merid x1) (sym (merid a)) (merid a)) ∙
                                                 (λ i → (merid x1) ∙ lCancel (merid a) i) ∙
                                                 sym (rUnit (merid x1)))) (i ∨ k) ))
                                 ∣ x1 , (λ i → (sym (pairLemma3 ((merid x1) ∙ sym (merid a)) (merid a) ∙
                                               sym (assocJ (merid x1) (sym (merid a)) (merid a)) ∙
                                               (λ i → (merid x1) ∙ lCancel (merid a) i) ∙
                                               sym (rUnit (merid x1)))) (i ∧ k)) ∣) ∙
                          (transportRefl ∣ x1 , sym (pairLemma3 ((merid x1) ∙ sym (merid a)) (merid a) ∙
                                                sym (assocJ (merid x1) (sym (merid a)) (merid a)) ∙
                                                (λ i → (merid x1) ∙ lCancel (merid a) i) ∙
                                                sym (rUnit (merid x1))) ∣) ∙
                          (λ k → ∣ x1 , symDestroyer (pairLemma3 ((merid x1) ∙ sym (merid a)) (merid a))
                                                      (sym (assocJ (merid x1) (sym (merid a)) (merid a)))
                                                      (λ i → (merid x1) ∙ lCancel (merid a) i)
                                                      (sym (rUnit (merid x1))) k ∣)



outerTranspId3' : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
                 transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                           (transpRCancel (λ i → north ≡ (merid a (~ i))) (merid x1 ∙ (sym (merid a)))) i))
                           ∣ x1 , rUnit (merid x1) ∙ sym (cong (λ x → merid x1 ∙ x) (lCancel (merid a))) ∙
                                  assocJ (merid x1) (sym (merid a)) (merid a) ∙
                                  sym (pairLemma3 {a1 = north} (merid x1 ∙ (sym (merid a))) (merid a)) ∣ 
                ≡ ∣ x1 , refl ∣
outerTranspId3' {ℓ}{A = A} n a x1 iscon = transportLemma {B = uncurry (CODE'' {a = a} n iscon)}
                                                        (sym (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                      (transpRCancel (λ i → north ≡ (merid a (~ i))) (merid x1 ∙ (sym (merid a))))))
                                                        (∣ x1 , refl ∣)
                                                        (∣ x1 , rUnit (merid x1) ∙ sym (cong (λ x → merid x1 ∙ x) (lCancel (merid a))) ∙
                                                                                   assocJ (merid x1) (sym (merid a)) (merid a) ∙
                                                                                   sym (pairLemma3 {a1 = north} (merid x1 ∙ (sym (merid a))) (merid a)) ∣)
                                         ((λ k → transport (λ i → uncurry (CODE'' {a = a} n iscon)
                                                                           (pair⁼''Sym (λ i₁ → merid a (~ i₁))
                                                                                    (transpRCancel (λ i₁ → north ≡ merid a (~ i₁))
                                                                                                   (merid x1 ∙ (λ i₁ → merid a (~ i₁)))) k i))
                                                  ∣ x1 , (λ _ → σ x1 {a}) ∣)
                                         ∙ (λ k → transport (λ i → uncurry (CODE'' {a = a} n iscon)
                                                                           (pair⁼'' (merid a) (transportLemma {B = λ y → north ≡ y} (sym (merid a)) (transport (λ i₁ → north ≡ merid a i₁) (merid x1 ∙ (sym (merid a) ))) (merid x1 ∙ (sym (merid a))) ((transpRCancel (λ i₁ → north ≡ merid a (~ i₁)) (merid x1 ∙ (λ i₁ → merid a (~ i₁)))))) i) )
                                                  ∣ x1 , (λ _ → σ x1 {a}) ∣) ∙
                                           (λ k → transport (λ i → uncurry (CODE'' {a = a} n iscon)
                                                                           (pair⁼'' (merid a) (wowie2 south (merid a) (merid x1) k) i) )
                                                  ∣ x1 , (λ _ → σ x1 {a}) ∣) ∙
                                           -- cong (λ x → x ∣ x1 , (λ _ → σ x1 {a}) ∣) (Lemma8610Refl'' (CODE' {a = a} n iscon) (merid a) (σ x1 {a})) ∙
                                           cong (λ x → x ∣ x1 , (λ _ → σ x1 {a}) ∣) (Lemma8610Refl'' (CODE'' {a = a} n iscon) (merid a) (σ x1 {a})) ∙
                                           (λ k → transport ((λ i → ∥ fiber (λ y → σ y {a})
                                                              (transpRCancel
                                                                 (λ i₁ → north ≡ merid a (~ i₁)) (σ x1 {a}) (~ i)) ∥ ℕ→ℕ₋₂ (n + n)) ∙
                                                              funExt⁻ (toPathCancel {A = λ i → north ≡ merid a i → Type ℓ}
                                                                                {x = λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))}
                                                                                {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))}
                                                                        (Lemma296Funs.inv'' {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                                            (merid a) (λ p → ∥ fiber (λ y → σ y {a}) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                                            (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                                                            (equivTest' {X = Susp A} (merid a)
                                                                                                        {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                                        {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                              (λ q → ua' (RlFun2 a a n iscon q , RlFunEquiv2 a a n iscon q)))) k )
                                                                      (transport (λ i → north ≡ merid a i) (σ x1 {a})))
                                                             ∣ x1 , (λ _ → σ x1 {a}) ∣)  ∙
                                           (λ k → transport ((((λ i → ∥ fiber (λ y → σ y {a})
                                                              (transpRCancel
                                                                 (λ i₁ → north ≡ merid a (~ i₁)) (σ x1 {a}) (~ i)) ∥ ℕ→ℕ₋₂ (n + n)))) ∙
                                                                 funExt⁻ (Lemma296Funs.inv'' {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                                      (merid a) (λ p → ∥ fiber (λ y → σ y {a}) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                                      (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                                                      (equivTest' {X = Susp A} (merid a)
                                                                                                  {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                                  {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                        (λ q → ua' (RlFun2 a a n iscon q , RlFunEquiv2 a a n iscon q))))
                                                                                       (transport (λ i → north ≡ merid a i) (σ x1 {a})))
                                                             ∣ x1 , ((λ _ → σ x1 {a})) ∣) ∙
                                           (λ k → transport (funExt-part''' {A = λ p → ∥ fiber (λ y → σ y {a}) p ∥ ℕ→ℕ₋₂ (n + n)}
                                                                          {B =  λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                          (merid a) (merid x1)
                                                                          (λ q → ua' (RlFun2 a a n iscon q , RlFunEquiv2 a a n iscon q)) k)
                                                            ∣ x1 , (((λ _ → σ x1 {a}))) ∣) ∙
                                           (λ k → transpFunct {B = λ x → x}
                                                               (ua' (RlFun2 a a n iscon (merid x1) , RlFunEquiv2 a a n iscon (merid x1)))
                                                               (cong (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)) (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙
                                                                     sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1))))
                                                               ∣ x1 , (((λ _ → σ x1 {a}))) ∣ (~ k)) ∙
                                           (λ k → transport (cong (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)) (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙
                                                                   sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1))))
                                                             (ua'Cancel ((RlFun2 a a n iscon (merid x1) , RlFunEquiv2 a a n iscon (merid x1))) k
                                                             ∣ x1 , (((λ _ → σ x1 {a}))) ∣ )) ∙
                                           (λ k → transport (cong (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)) (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙
                                                                   sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1))))
                                                             (funPart n a x1 iscon k)) ∙
                                           finalStep n a x1 iscon)

  where
  ma : _≡_ {A = Susp A} north south
  ma = merid a
  mx1 : _≡_ {A = Susp A} north south
  mx1 = merid x1
  
  guyid : (transport (λ i → north ≡ merid a i) (σ x1 {a})) ≡ merid x1
  guyid = pairLemma3 {a1 = north} (σ x1 {a}) (merid a) ∙ sym (assoc (merid x1) (sym (merid a)) (merid a)) ∙
          (λ i → merid x1 ∙ (lCancel (merid a)) i) ∙ sym (rUnit (merid x1))

  

{-
J (λ y p → (q : x ≡ y) {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'}  →
                                   (r : ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q)) →
                                   funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y}  p A B (equivTest' {X = X} p {A = A} {B = B} r))
                                            (transport (λ i → x ≡ p i) (p ∙ sym q))
                                    ≡
                                    (funExt⁻ (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Set ℓ'} p A) (transport (λ i → x ≡ p i) (p ∙ sym q))) ∙
                                    (transportRefl (A (transport (λ i → x ≡ p (~ i)) (transport (λ i → x ≡ p i) (p ∙ sym q)))) ∙
                                    cong (λ x → A x) (pairLemma3 {a1 = x} (transport (λ i → x ≡ p i) (p ∙ sym q)) (sym p))) ∙
                                    r (transport (λ i → x ≡ p i) (p ∙ sym q)))
                                    ?

-}


  wowie2 : (y : Susp A) (ma mx1 : north ≡ y) → (transportLemma {B = λ y → north ≡ y} (sym ma) (transport (λ i₁ → north ≡ ma i₁) (mx1 ∙ (sym ma))) (mx1 ∙ (sym ma)) (transpRCancel (λ i₁ → north ≡ ma (~ i₁)) (mx1 ∙ (sym ma)))) ≡ refl
  wowie2 y  = J (λ y ma → (mx1 : north ≡ y) → (transportLemma {B = λ y → north ≡ y} (sym ma) (transport (λ i₁ → north ≡ ma i₁) (mx1 ∙ (sym ma))) (mx1 ∙ (sym ma)) (transpRCancel (λ i₁ → north ≡ ma (~ i₁)) (mx1 ∙ (sym ma)))) ≡ refl)
                 λ p → (λ i → transportLemmaRefl {a = north} {B = λ y → _≡_ {A = Susp A} north y}
                                           (λ _ → north) (λ _ → north) i
                                           (transport (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))
                                           (p ∙ (λ _ → north))
                                           (transpRCancel {A = _≡_ {A = Susp A} north north} {B = _≡_ {A = Susp A} north north} (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))) ∙
                       (λ k → transportRefl (p ∙ (λ _ → north)) ∙
                              sym (transpRCancel {A = _≡_ {A = Susp A} north north} {B = _≡_ {A = Susp A} north north}
                                                 (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north))) ∙
                              transportRefl (transport (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))) ∙
                       (λ k → transportRefl (p ∙ (λ _ → north)) ∙
                              sym (transpRCancelRefl {A = north ≡ north} (p ∙ (λ _ → north)) k) ∙
                              transportRefl (transport (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))) ∙
                       (λ k → transportRefl (p ∙ (λ _ → north)) ∙
                              symDistr (transportRefl (transport refl (p ∙ (λ _ → north)))) (transportRefl (p ∙ (λ _ → north))) k  ∙
                              transportRefl (transport (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))) ∙
                       (λ k → transportRefl (p ∙ (λ _ → north)) ∙
                              assoc (sym (transportRefl (p ∙ (λ _ → north))))
                                    (sym (transportRefl (transport refl (p ∙ (λ _ → north)))))
                                    (transportRefl (transport (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))) (~ k) ) ∙
                       (λ k → transportRefl (p ∙ (λ _ → north)) ∙
                              sym (transportRefl (p ∙ (λ _ → north))) ∙
                              lCancel (transportRefl (transport (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))) k) ∙
                       (λ k →  transportRefl (p ∙ (λ _ → north)) ∙ (rUnit (sym (transportRefl (p ∙ (λ _ → north)))) (~ k))) ∙
                       (rCancel (transportRefl (p ∙ (λ _ → north))) )














reflCase  : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → c'' n a iscon north (σ x1 {a}) ≡ ∣ x1 , refl ∣
reflCase {ℓ} {A} n a x1 iscon = transport (λ i → (uncurry (CODE'' {a = a} n iscon) (pair⁼'' (σ x1 {a}) (pairLemma2 (σ x1 {a})) i)))
                                          ∣ a , (rCancel (merid a)) ∣
                                ≡⟨ c''Id n a x1 iscon ⟩
                                transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                           (transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (merid x1) (pairLemma2 (merid x1)) i))
                                                      ∣ a , rCancel (merid a) ∣)
                                ≡⟨ (λ k → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                           (wowie n a x1 iscon (~ k))) ⟩
                                transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                          ((transport (λ i → uncurry (CODE'' {a = a} n iscon)
                                                                     (pair⁼'' (merid x1) (transpRCancel (λ i₁ → north ≡ merid x1 i₁) (merid x1)) i)))
                                                      ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣)
                                ≡⟨ (λ k → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                                    ((Lemma8610'' (CODE'' {a = a} n iscon) (merid x1) (merid x1) k)
                                                     ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣)) ⟩
                                transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                          (transport ((sym (cong (λ x → x (merid x1)) (Lemma294' {A = λ x → north ≡ x}
                                                                                                 {B = λ _ → Type ℓ}
                                                                                                 (merid x1)
                                                                                                 ((CODE'' {a = a} n iscon) north)))) ∙
                                                       funExt⁻ (fromPathP (toPathP {A = λ i → north ≡ merid x1 i → Type ℓ}
                                                                                   {x = λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))}
                                                                                   {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))}
                                                       (Lemma296Funs.inv'' {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                           (merid x1)
                                                                           (λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n))))
                                                                           (λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n)))
                                                                           (equivTest' {X = Susp A} (merid x1)
                                                                                       {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                       {B = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))}
                                                                                       λ q → ua' (RlFun2 a x1 n iscon q , RlFunEquiv2 a x1 n iscon q))))) (merid x1))
                                                     ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣)
                                ≡⟨ (λ k → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                                    (transport (codeTranspHelper1 (merid x1) (merid x1)
                                                                                  (λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n))
                                                                                  (λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n)))
                                                                                  (λ q → ua' (RlFun2 a x1 n iscon q , RlFunEquiv2 a x1 n iscon q)) k)
                                                    ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣)) ⟩
                                transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                                    (transport ((transportRefl (∥ fiber (λ y → σ y {a})
                                                                                        (subst (_≡_ north) (sym (merid x1)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)) ∙
                                                                cong (λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n))
                                                                     (pairLemma3 (merid x1) (sym (merid x1)))) ∙
                                                                ua' (RlFun2 a x1 n iscon (merid x1) , RlFunEquiv2 a x1 n iscon (merid x1)))
                                                    ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣)
                                ≡⟨ (λ k → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                                    (transpFunct {B = λ x → x}
                                                                 (transportRefl (∥ fiber (λ y → σ y {a})
                                                                                        (subst (_≡_ north) (sym (merid x1)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)) ∙
                                                                  cong (λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n))
                                                                       (pairLemma3 (merid x1) (sym (merid x1))))
                                                                 (ua' (RlFun2 a x1 n iscon (merid x1) , RlFunEquiv2 a x1 n iscon (merid x1)))
                                                                 ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙
                                                                       sym (pairLemma3 (merid x1) (sym (merid x1))) ∣ (~ k))) ⟩
                                transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                           (transport (ua' (RlFun2 a x1 n iscon (merid x1) , RlFunEquiv2 a x1 n iscon (merid x1)))
                                                      (transport (λ i → (transportRefl
                                                                         (∥ fiber (λ y → σ y {a})
                                                                                  (subst (_≡_ north) (λ i₁ → merid x1 (~ i₁)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)) ∙
                                                                        (λ i₁ → ∥ fiber (λ y → σ y {a})
                                                                                        (pairLemma3 (merid x1) (λ i₂ → merid x1 (~ i₂)) i₁) ∥ ℕ→ℕ₋₂ (n + n))) i)
                                                      ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣))
                                ≡⟨ (λ k → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                                     ((ua'Cancel (RlFun2 a x1 n iscon (merid x1) , RlFunEquiv2 a x1 n iscon (merid x1)) k)
                                                     (transport (λ i → (transportRefl
                                                                         (∥ fiber (λ y → σ y {a})
                                                                                  (subst (_≡_ north) (λ i₁ → merid x1 (~ i₁)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)) ∙
                                                                        (λ i₁ → ∥ fiber (λ y → σ y {a})
                                                                                        (pairLemma3 (merid x1) (λ i₂ → merid x1 (~ i₂)) i₁) ∥ ℕ→ℕ₋₂ (n + n))) i)
                                                      ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣))) ⟩
                                transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                           (RlFun2 a x1 n iscon (merid x1)
                                                  (transport (λ i → (transportRefl
                                                                         (∥ fiber (λ y → σ y {a})
                                                                                  (subst (_≡_ north) (λ i₁ → merid x1 (~ i₁)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)) ∙
                                                                        (λ i₁ → ∥ fiber (λ y → σ y {a})
                                                                                        (pairLemma3 (merid x1) (λ i₂ → merid x1 (~ i₂)) i₁) ∥ ℕ→ℕ₋₂ (n + n))) i)
                                                      ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣))
                                ≡⟨ (λ k → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                                     (RlFun2 a x1 n iscon (merid x1)
                                                            (transpFunct {B = λ x → x}
                                                                         (transportRefl
                                                                           (∥ fiber (λ y → σ y {a})
                                                                                    (subst (_≡_ north) (λ i₁ → merid x1 (~ i₁)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)))
                                                                         (λ i₁ → ∥ fiber (λ y → σ y {a})
                                                                                        (pairLemma3 (merid x1) (λ i₂ → merid x1 (~ i₂)) i₁) ∥ ℕ→ℕ₋₂ (n + n))
                                                                         ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙
                                                                               sym (pairLemma3 (merid x1) (sym (merid x1))) ∣ (~ k)))) ⟩
                                transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                           (RlFun2 a x1 n iscon (merid x1)
                                                  (transport (λ i₁ → ∥ fiber (λ y → σ y {a})
                                                                                     (pairLemma3 (merid x1) (λ i₂ → merid x1 (~ i₂)) i₁) ∥ ℕ→ℕ₋₂ (n + n))
                                                             (transport (transportRefl
                                                                         (∥ fiber (λ y → σ y {a})
                                                                                  (subst (_≡_ north) (λ i₁ → merid x1 (~ i₁)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)))
                                                                        ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙
                                                                              sym (pairLemma3 (merid x1) (sym (merid x1))) ∣)))
                                ≡⟨ (λ k → transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                                     (test n a x1 iscon k)) ⟩
                                transport (λ i → uncurry (CODE'' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                                            (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                           ∣ x1 , refl ∣
                                ≡⟨ outerTranspId n a x1 iscon ⟩
                                transport (λ i → uncurry (CODE'' n iscon)
                                                          (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                   (transpRCancel (λ i₁ → north ≡ merid a (~ i₁)) (merid x1 ∙ sym (merid a))) i))
                                           ∣ x1 , rUnit (merid x1) ∙ sym (cong (_∙_ (merid x1)) (lCancel (merid a))) ∙
                                                  assocJ (merid x1) (sym (merid a)) (merid a) ∙ sym (pairLemma3 (merid x1 ∙ sym (merid a)) (merid a)) ∣
                                ≡⟨ outerTranspId3' n a x1 iscon ⟩
                                ∣ x1 , refl ∣ ∎


Thm864 : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) {y : Susp A} → (p : north ≡ y) → isContr (CODE'' {a = a} n iscon y p)
Thm864 {ℓ} {A} n a iscon {y = y} = J {ℓ} {Susp A} {north} (λ y p → (isContr (CODE'' {a = a} n iscon y p))) (c'' n a iscon north refl , (λ y → sym (mainId refl y)))
  where
  mainId : (p : north ≡ north) (d : CODE'' {a = a} n iscon north p) →
           d ≡ c'' n a iscon north p
  mainId p = ind (λ x → isOfHLevelSuc (suc (n + n)) (isOfHLevel∥∥ {A = fiber (λ y → σ y {a}) p} (ℕ→ℕ₋₂ (n + n)) x (c'' n a iscon north p)))
                 base
    where
    base : (x : fiber (λ y → σ y {a}) p) → ∣ x ∣ ≡ c'' n a iscon north p
    base (x1 , r) = J (λ p r → ∣ x1 , r ∣ ≡ c'' n a iscon north p) (sym (reflCase n a x1 iscon)) r

Freudenthal : (n : ℕ) (A : Pointed ℓ) → is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A) → ∥ typ A ∥ (ℕ→ℕ₋₂ (n + n)) ≃ ∥ typ (Ω (Susp (typ A) , north)) ∥ ((ℕ→ℕ₋₂ (n + n)))
Freudenthal n A iscon = Lemma7-5-14 _ (λ x → σ x {a = pt A}) (Thm864 n (pt A) iscon)
