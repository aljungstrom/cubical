{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.FreudenthalFix2.FinishingUp4  where


open import Cubical.ZCohomology.Base
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

{-
pairLemma3 : ∀ {ℓ} {A : Type ℓ} {a1 b : A} (p : a1 ≡ b) (q : b ≡ a1) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q
pairLemma3 {a1 = a1} = J (λ b p → (q : b ≡ a1) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q) λ q → pairLemma2 q ∙ lUnit q

pairLemma3Refl : ∀ {ℓ} {A : Type ℓ} {a1 : A} (q : a1 ≡ a1) → pairLemma3 (λ _ → a1) q ≡ pairLemma2 q ∙ lUnit q
pairLemma3Refl {a1 = a1} q = cong (λ x → x q) (JRefl (λ b p → (q : b ≡ a1) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q) λ q → pairLemma2 q ∙ lUnit q)
-}

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

pair⁼ : ∀ {ℓ'} {B : A → Type ℓ'} {x y : Σ A (λ a → B a)} → (p : fst x ≡ fst y) → transport (λ i → B (p i)) (snd x) ≡ (snd y) → x ≡ y 
pair⁼ {B = B}{x = x1 , x2} {y = y1 , y2} p = J (λ y1 p → ((y2 : B y1) → (transport (λ i → B (p i)) x2 ≡ y2) → (x1 , x2) ≡ (y1 , y2))) (λ y2 p2 i → x1 , ((sym (transportRefl x2)) ∙ p2) i) p y2

pair⁼Refl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {a : A} {x y : B a} → (p : transport (λ i → B a) x ≡ y) → pair⁼ {B = B} {x = (a , x)} {y = (a , y)} refl p ≡ λ i → a , ((sym (transportRefl x)) ∙ p) i
pair⁼Refl {A = A} {B = B} {a = a} {x = x} {y = y} p = cong (λ f → f y p) ((JRefl (λ y1 p → ((y2 : B y1) → (transport (λ i → B (p i)) x ≡ y2) → _≡_ {A = Σ A (λ a → B a)} (a , x) (y1 , y2))) (λ y2 p2 i → a , ((sym (transportRefl x)) ∙ p2) i)))

----------- abstract stuff
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

  functTransp2 : ∀ {ℓ ℓ'} {A : Type ℓ} {a1 b : A} {C : Σ A (λ b → a1 ≡ b) → Type ℓ' } (p : a1 ≡ b) (q : b ≡ a1) → transport (λ i → C (pair⁼'' (p ∙ q) (pairLemma2 (p ∙ q)) i) ) ≡ λ x → transport (λ i → C (pair⁼'' q ((pairLemma3 p q)) i)) (transport (λ i → C (pair⁼'' p (pairLemma2 p) i)) x)
  functTransp2 {ℓ} {ℓ'} {A = A} {a1 = a1} {b = b} {C = C} = J (λ b p → (q : b ≡ a1) → transport (λ i → C (pair⁼'' {B = λ a → a1 ≡ a} {x = (a1 , refl {x = a1})} (p ∙ q) (pairLemma2 (p ∙ q)) i) ) ≡ λ x → transport (λ i → C (pair⁼'' q ((pairLemma3 p q)) i)) (transport (λ i → C (pair⁼'' p (pairLemma2 p) i)) x))
                                λ q → (λ j → subst C (hej a1 q (~ j))) ∙ (λ j → subst C (pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1)) ∙ pair⁼'' q (pairLemmaId q (~ j)))) ∙ funExt λ x → (substComposite-∙ C (pair⁼'' refl (pairLemma2 refl)) (pair⁼'' q (pairLemma3 refl q)) x)
           where
             pairLemmaId : (q : a1 ≡ a1) → (pairLemma3 (λ _ → a1) q) ≡ ((pairLemma2 q) ∙ lUnit q)
             pairLemmaId q = pairLemma3Refl q

             hej : (b : A) (q : a1 ≡ b) → (pair⁼'' {A = A} {B = λ a → a1 ≡ a}  {x = (a1 , λ _ → a1)} {y = (a1 , λ _ → a1)} (λ _ → a1) (pairLemma2 {a = a1} {b = a1} (λ _ → a1)) ∙ pair⁼'' q ((pairLemma2 q) ∙ lUnit q)) ≡ pair⁼'' (refl ∙ q) (pairLemma2 (refl {x = a1} ∙ q))
             hej b = J (λ b q → pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1)) ∙ pair⁼'' q (pairLemma2 q ∙ lUnit q) ≡ pair⁼'' (refl ∙ q) (pairLemma2 (refl ∙ q)))
                       ((λ i → (helper2 i) ∙ pair⁼'' refl (pairLemma2 refl ∙ lUnit refl)) ∙ sym (lUnit (pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1) ∙ lUnit (λ _ → a1)))) ∙ desired≡)
               where
               helper2 : (pair⁼'' {A = A} {B = λ a → a1 ≡ a}  {x = (a1 , λ _ → a1)} {y = (a1 , λ _ → a1)} (λ _ → a1) (pairLemma2 {a = a1} {b = a1} (λ _ → a1))) ≡ refl
               helper2 = (λ i → (JRefl (λ y1 p → ((y2 : a1 ≡ y1) → (transport (λ i → a1 ≡ (p i)) refl ≡ y2) → _≡_ {A = Σ A (λ a → a1 ≡ a)} (a1 , refl) (y1 , y2))) (λ y2 p2 i → refl {x = a1} i , ((sym (transportRefl refl)) ∙ p2) i) i) (λ _ → a1) (pairLemma2 {a = a1} {b = a1} (λ _ → a1)) ) ∙ (λ j → λ i → a1 , ((sym (transportRefl refl)) ∙ JRefl (λ b p →  transport (λ i → a1 ≡ p i) refl ≡ p) (transportRefl refl) j ) i) ∙ λ j i → a1 , (lCancel (transportRefl refl) j) i

               PathP1 : PathP (λ j → _≡_ {A = Σ A (λ a → a1 ≡ a)} (a1 , (λ _ → a1)) (a1 , lUnit (λ _ → a1) (~ j))) (pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1) ∙ lUnit (λ _ → a1))) refl
               PathP1 j = hcomp (λ k → λ{(j = i0) → pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1) ∙ lUnit (λ _ → a1))  ; (j = i1) → ((λ i → pair⁼'' (λ _ → a1) (rUnit (pairLemma2 (λ _ → a1)) (~ i)) ) ∙ helper2) k}) (pair⁼'' refl ((pairLemma2 (λ _ → a1)) ∙ (λ i → lUnit refl (i ∧ (~ j)))))

               PathP2 : PathP (λ j → _≡_ {A = Σ A (λ a → a1 ≡ a)} (a1 , (λ _ → a1)) (a1 , lUnit (λ _ → a1) j)) refl (pair⁼'' ((λ _ → a1) ∙ refl) (pairLemma2 ((λ _ → a1) ∙ refl)))
               PathP2 j = hcomp (λ k → λ{(j = i0) → helper2 k ; (j = i1) → (pair⁼'' ((λ _ → a1) ∙ refl) (pairLemma2 ((λ _ → a1) ∙ refl)))}) (pair⁼'' (lUnit (λ _ → a1) j) (pairLemma2 (lUnit (λ _ → a1) j)))

               pathsCancel : (λ j → _≡_ {A = Σ A (λ a → a1 ≡ a)} (a1 , (λ _ → a1)) (a1 , lUnit (λ _ → a1) (~ j))) ∙ ((λ j → _≡_ {A = Σ A (λ a → a1 ≡ a)} (a1 , (λ _ → a1)) (a1 , lUnit (λ _ → a1) j))) ≡ refl
               pathsCancel = lCancel (λ j → _≡_ {A = Σ A (λ a → a1 ≡ a)} (a1 , (λ _ → a1)) (a1 , lUnit (λ _ → a1) j))

               desired≡ : pair⁼'' (λ _ → a1) (λ i i₁ → (pairLemma2 (λ _ → a1) ∙ lUnit (λ _ → a1)) i i₁) ≡ pair⁼'' ((λ _ → a1) ∙ refl) (pairLemma2 ((λ _ → a1) ∙ refl))
               desired≡ = transport (λ i → PathP (λ j → pathsCancel i j) (pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1) ∙ lUnit (λ _ → a1))) (pair⁼'' ((λ _ → a1) ∙ refl) (pairLemma2 ((λ _ → a1) ∙ refl)))) (compPathP PathP1 PathP2)
               
----------------







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


-- Lemma8610fun : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a2) → C a1 (subst B (sym p) b) → C a2 b
-- Lemma8610fun {ℓ} {ℓ'} {ℓ''} {A = A} {a1 = a1 } {a2 = a2} {B = B} C p b  = transport (λ i → idHelper i ) 
--   where
--   idHelper : C a1 (subst B (sym p) b) ≡ C a2 b
--   idHelper = (sym (cong (λ x → x b) (Lemma294' {A = B} {B = λ _ → Type ℓ''} p (C a1)))) ∙ funExt⁻ (fromPathP λ j → C (p j)) b

-- Lemma8610 : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a2)  → transport ((λ i → uncurry C (pair⁼ p (transpRCancel (λ i → B (p i)) b) i) )) ≡ Lemma8610fun C p b  
-- Lemma8610 {ℓ} {ℓ'} {ℓ''} {A = A} {a1 = a1} {B = B} C = J (λ a2 p → (b : B a2)  → transport ((λ i → uncurry C (pair⁼ p (transpRCancel (λ i → B (p i)) b) i) )) ≡ Lemma8610fun C p b  ) λ b j → transport (helper b (~ j))
--   where
--   helper : (b : B a1) → (sym (cong (λ x → x b) (Lemma294' {A = B} {B = λ _ → Type ℓ''} refl (C a1)))) ∙ funExt⁻ (fromPathP λ j → C a1) b ≡ (λ i → uncurry C (pair⁼ refl (transpRCancel (λ i₁ → B (refl i₁)) b) i))
--   helper b = (sym (cong (λ x → x b) (Lemma294' {A = B} {B = λ _ → Type ℓ''} refl (C a1)))) ∙ cong (λ x → C a1 x) (transportRefl b)
--              ≡⟨ (λ i → (sym (cong (λ x → x b) (Lemma294'Refl {A = B} {B = λ _ → Type ℓ''} (C a1) i))) ∙ cong (λ x → C a1 x) (transportRefl b)) ⟩
--              refl ∙ cong (λ x → C a1 x) (transportRefl b)
--              ≡⟨ sym (lUnit (cong (λ x → C a1 x) (transportRefl b)))  ⟩
--              cong (λ x → C a1 x) (transportRefl b)
--              ≡⟨ (λ j i → uncurry C (a1 , lUnit (transportRefl b) j i)) ⟩
--              ((λ i → uncurry C (a1 , (refl ∙ (transportRefl b)) i)))
--              ≡⟨ (λ j i → uncurry C (a1 , ((lCancel (transportRefl (transport refl b)) (~ j)) ∙ (transportRefl b)) i)) ⟩
--              ((λ  i →  uncurry C (a1 , (((sym (transportRefl ((transport⁻ (λ i₁ → B a1) b)))) ∙ (transportRefl (transport refl b))) ∙ (transportRefl b)) i)) )
--              ≡⟨ (λ j i → uncurry C (a1 , ((assoc (sym (transportRefl ((transport⁻ (λ i₁ → B a1) b)))) (transportRefl (transport refl b)) (transportRefl b) (~ j))) i)) ⟩
--              ((λ  i →  uncurry C (a1 , (((sym (transportRefl ((transport⁻ (λ i₁ → B a1) b)))) ∙ (transportRefl (transport refl b) ∙ transportRefl b))) i))) 
--              ≡⟨ (λ j i →  uncurry C (a1 , (((sym (transportRefl ((transport⁻ (λ i₁ → B a1) b)))) ∙ (transpRCancelRefl b (~ j)))) i)) ⟩ 
--              (λ i → uncurry C (a1 , (((sym (transportRefl ((transport⁻ (λ i₁ → B a1) b)))) ∙ (transpRCancel (λ i₁ → B a1) b))) i))
--              ≡⟨ (λ j → (λ i → uncurry C (pair⁼Refl (transpRCancel (λ i₁ → B a1) b) (~ j) i))) ⟩
--              (λ i → uncurry C (pair⁼ refl (transpRCancel (λ i₁ → B a1) b) i)) ∎

-- Lemma8610'' : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a2)  → transport ((λ i → uncurry C (pair⁼'' p (transpRCancel (λ i → B (p i)) b) i) )) ≡ Lemma8610fun C p b
-- Lemma8610'' {A = A} {a1 = a1} {a2 = a2} {B = B} C p b  = (λ j → transport (λ i → uncurry C ((pairId j) p (transpRCancel (λ i₁ → B (p i₁)) b) i))) ∙
--                                                          Lemma8610 {A = A} {a1 = a1} {a2 = a2} {B = B} C p b



Lemma8610Refl'' : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a1)  → transport ((λ i → uncurry C (pair⁼'' {x = a1 , b} p refl i) )) ≡ transport ((λ i → C a1 (transpRCancel (λ i → (B (p (~ i)))) b (~ i))) ∙ funExt⁻ (fromPathP λ j → C (p j)) (transport (λ i → B (p i)) b))
  
Lemma8610Refl'' {ℓ} {ℓ'} {ℓ''} {A} {a1} {a2} {B} C p b = transport (λ j → transport (λ i → uncurry C ((pairId {x = a1 , b} (~ j)) p refl i)) ≡ transport (Lemma8610Reflfun {ℓ} {ℓ'} {ℓ''} {A = A} {a1 = a1} {a2 = a2} {B = B} C p b)) ((Lemma8610Refl {ℓ} {ℓ'} {ℓ''} {A = A} {a1 = a1} {a2 = a2} {B = B} C p b))



-- c : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (y : (Susp A)) (p : north ≡ y) → CODE {a = a} n iscon y p
-- c n a iscon y p = transport (λ i → (uncurry (CODE {a = a} n iscon) (pair⁼ p (pairLemma2 p) i))) ∣ a , (rCancel (merid a)) ∣

-- c' : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (y : (Susp A)) (p : north ≡ y) → CODE' {a = a} n iscon y p
-- c' n a iscon y p = transport (λ i → (uncurry (CODE' {a = a} n iscon) (pair⁼'' p (pairLemma2 p) i))) ∣ a , (rCancel (merid a)) ∣

-- c'Id : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
--        c' n a iscon north (σ x1 {a})
--        ≡ transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁)) (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
--                     (transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' (merid x1) (pairLemma2 (merid x1)) i))
--                                ∣ a , rCancel (merid a) ∣)
-- c'Id n a x1 iscon = cong (λ x → x ∣ a , (rCancel (merid a)) ∣) (functTransp2 {C = uncurry (CODE' {a = a} n iscon)} (merid x1) (sym (merid a)))



{-
outerTranspId4 : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
                 transport (λ i → uncurry (CODE' {a = a} n iscon)
                                          (pair⁼'' (λ i₁ → merid a (~ i₁)) (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i))
                                  ∣ x1 , refl ∣
                 ≡ ∣ x1 , refl ∣
outerTranspId4 {ℓ} {A = A} n a x1 iscon = transportLemma {B = C}
                                              (sym (pair⁼'' (sym Ma) (pairLemma3 (Mx1) (sym Ma))))
                                              ∣ x1 , refl ∣
                                              ∣ x1 , refl ∣
                                              ((λ k → transport (λ i → C (pair⁼''Sym (sym Ma) (pairLemma3 Mx1 (sym Ma)) k i))
                                                                         ∣ x1 , (λ _ → σ x1 {a}) ∣) ∙
                                              (λ k → transport (λ i → C (pair⁼'' Ma
                                                                                 (transportLemma {B = λ y → north ≡ y}
                                                                                                 (sym Ma) Mx1 (σ x1 {a})
                                                                                                 ((pairLemma3 Mx1 (sym Ma)))) i))
                                                       ∣ x1 , (λ _ → σ x1 {a}) ∣) ∙
                                              (λ k → transport (λ i → C (pair⁼'' Ma (throwAbout Ma Mx1 k) i)) ∣ x1 , (λ _ → σ x1 {a}) ∣ ) ∙
                                              (λ k → transport (λ i → C (pair⁼'' Ma (pairLemma3 (merid x1 ∙ sym (merid a)) (merid a) ∙
                                                                                     sym (assocJ (merid x1) (sym (merid a)) (merid a)) ∙
                                                                                     (λ i₁ → merid x1 ∙ lCancel (merid a) i₁) ∙
                                                                                     sym (rUnit (merid x1))) i))
                                                               ∣ x1 , rUnit (λ _ → σ x1 {a}) k ∣) ∙
                                              (λ k → transport (λ i → C (pair⁼'' Ma (pairLemma3 (merid x1 ∙ sym (merid a)) (merid a) ∙
                                                                                       sym (assocJ (merid x1) (sym (merid a)) (merid a)) ∙
                                                                                       (λ i₁ → merid x1 ∙ lCancel (merid a) i₁) ∙
                                                                                       (rUnit (rUnit (sym (rUnit (merid x1))) k) k ))
                                                                                        i))
                                                                 ∣ x1 , (λ _ → σ x1 {a}) ∙ (λ _ → σ x1 {a}) ∣) ∙
                                              (λ k → transport (λ i → C (pair⁼'' Ma (pairLemma3 (merid x1 ∙ sym (merid a)) (merid a) ∙
                                                                                       sym (assocJ (merid x1) (sym (merid a)) (merid a)) ∙
                                                                                       (λ i₁ → merid x1 ∙ lCancel (merid a) i₁) ∙
                                                                                       ((sym (rUnit (merid x1))) ∙ (λ j → (rUnit (merid x1)) (j ∧ k)) ∙ {!λ i → rUnit (Mx1) (k ∨ i) ∙ (sym (pairLemma) )!} ))
                                                                                        i))
                                                                 {!!}) ∙
                                              {!transpRCancel!} ∙
                                              {!!} ∙
                                              {!!} ∙
                                              {!!} ∙
                                              {!!} ∙
                                              {!!} ∙
                                              λ k → transport (λ i → C (pair⁼'' Ma (transpRCancel {!pair⁼''Sym !} {!!} {!!}) i)) ∣ x1 , {!!} ∣)

  where
  C : (p : Σ (Susp A) (λ z → north ≡ z)) → Type ℓ
  C = uncurry (CODE' {a = a} n iscon)

  Ma : _≡_ {A = Susp A} north south
  Ma = merid a

  Mx1 : _≡_ {A = Susp A} north south
  Mx1 = merid x1

  throwAbout2 : ∀ {ℓ } {A : Type ℓ} {a1 x : A} (p q : a1 ≡ x)  → transportLemma {B = λ y → a1 ≡ y} (sym p) q ( q ∙ (sym p) ) (pairLemma3 q ( sym p ) )
                                                               ≡ {!!} ∙ transpRCancel (λ i → a1 ≡ p i) q
  throwAbout2 = {!!}
 
  throwAbout : ∀ {ℓ } {A : Type ℓ} {a1 x : A} (p q : a1 ≡ x)  → transportLemma {B = λ y → a1 ≡ y} (sym p) q ( q ∙ (sym p) ) (pairLemma3 q ( sym p ) ) ≡ pairLemma3 (q ∙ sym p) p ∙ sym (assocJ q (sym p) p) ∙ (λ i → q ∙ (lCancel p i) ) ∙ sym (rUnit q)
  throwAbout {A = A} {a1 = a1} {x = x} = J (λ x p → (q : a1 ≡ x)  → transportLemma {B = λ y → a1 ≡ y} (sym p) q (q ∙ (sym p)) (pairLemma3 q ( sym p ) )
                                                                  ≡ pairLemma3 (q ∙ sym p) p ∙ sym (assocJ q (sym p) p) ∙ (λ i → q ∙ (lCancel p i) ) ∙ sym (rUnit q))
                                            λ q → cong (λ f → f q (q ∙ (λ _ → a1))
                                                  (pairLemma3 q (λ _ → a1)) ) (transportLemmaRefl {A = A} {B = λ y → a1 ≡ y} (λ _ → a1) (λ _ → a1)) ∙
                                                  (λ i → transportRefl (q ∙ (λ _ → a1)) ∙ sym (pairLemma3Id q (λ _ → a1) i) ∙ transportRefl q) ∙
                                                  (λ i → transportRefl (q ∙ (λ _ → a1)) ∙ sym (pairLemma3*Refl q i) ∙ transportRefl q) ∙
                                                  (λ i → transportRefl (q ∙ (λ _ → a1)) ∙ symDistr (transportRefl q) (rUnit q) i ∙ transportRefl q) ∙
                                                  (λ i → transportRefl (q ∙ (λ _ → a1)) ∙ assoc (sym (rUnit q)) (sym (transportRefl q)) (transportRefl q) (~ i) ) ∙
                                                  (λ i → transportRefl (q ∙ (λ _ → a1)) ∙ (sym (rUnit q)) ∙ lCancel (transportRefl q) i) ∙
                                                  (λ i → transportRefl (q ∙ (λ _ → a1)) ∙ rUnit (sym (rUnit q)) (~ i)) ∙
                                                  (λ i → transportRefl (q ∙ (λ _ → a1)) ∙ lUnit (sym (rUnit q)) i) ∙
                                                  (λ i → transportRefl (q ∙ (λ _ → a1)) ∙ moreJ q (~ i) ∙ sym (rUnit q)) ∙
                                                  (λ i → transportRefl (q ∙ (λ _ → a1)) ∙ assoc (rUnit (q ∙ (λ _ → a1)))
                                                                                                (sym (assocJ q (λ _ → a1) (λ _ → a1)))
                                                                                                ((λ i → q ∙ lCancel (λ _ → a1) i)) i ∙
                                                                                          sym (rUnit q)) ∙
                                                  (λ i → transportRefl (q ∙ (λ _ → a1)) ∙ (assoc ((rUnit (q ∙ (λ _ → a1))) ∙
                                                                                                    (sym (assocJ q (λ _ → a1) (λ _ → a1))))
                                                                                                   (λ i → q ∙ lCancel (λ _ → a1) i)
                                                                                                   (sym (rUnit q))) (~ i)) ∙
                                                  (λ i → transportRefl (q ∙ (λ _ → a1)) ∙ (assoc (rUnit (q ∙ (λ _ → a1)))
                                                                                                (sym (assocJ q (λ _ → a1) (λ _ → a1)))
                                                                                                ((λ i → q ∙ lCancel (λ _ → a1) i) ∙ (sym (rUnit q)))) (~ i)) ∙
                                                  assoc (transportRefl (q ∙ (λ _ → a1)))
                                                         (rUnit (q ∙ (λ _ → a1)))
                                                         ((λ i → assocJ q (λ _ → a1) (λ _ → a1) (~ i)) ∙
                                                           (λ i → q ∙ lCancel (λ _ → a1) i) ∙ (λ i → rUnit q (~ i))) ∙
                                                  (λ i → (transportRefl (q ∙ (λ _ → a1)) ∙ rUnit (q ∙ (λ _ → a1))) ∙   -- check
                                                         (λ i → assocJ q (λ _ → a1) (λ _ → a1) (~ i)) ∙
                                                         (λ i → q ∙ lCancel (λ _ → a1) i) ∙ (λ i → rUnit q (~ i))) ∙
                                                  (λ i → pairLemma3*Refl (q ∙ refl) (~ i) ∙
                                                                         (λ i → assocJ q (λ _ → a1) refl (~ i)) ∙ (λ i → q ∙ lCancel refl i) ∙
                                                                         (λ i → rUnit q (~ i))) ∙
                                                  λ i → pairLemma3Id (q ∙ (λ _ → a1)) (λ _ → a1) (~ i) ∙
                                                                     (λ i → assocJ q (λ _ → a1) (λ _ → a1) (~ i)) ∙ (λ i → q ∙ lCancel refl i) ∙
                                                                     (λ i → rUnit q (~ i))
      where
      moreJ : ∀ {ℓ} {A : Type ℓ} {a b : A} (q : a ≡ b) →
                    rUnit (q ∙ (λ _ → b)) ∙ (λ i → assocJ q (λ _ → b) (λ _ → b) (~ i)) ∙ (λ i → q ∙ lCancel (λ _ → b) i) ≡ refl
      moreJ {a = a} = J (λ b q → rUnit (q ∙ (λ _ → b)) ∙ (λ i → assocJ q (λ _ → b) (λ _ → b) (~ i)) ∙ (λ i → q ∙ lCancel (λ _ → b) i) ≡ refl)
                          ((λ i → rUnit (refl ∙ (λ _ → a)) ∙ sym (assocJRefl i)  ∙ (λ i → refl ∙ lCancel (λ _ → a) i)) ∙
                           (λ i → rUnit (refl ∙ (λ _ → a)) ∙ symDistr ((λ i → refl ∙ lCancel (λ _ → a) i)) (rUnit (refl ∙ (λ _ → a))) i  ∙
                                                             (λ i → refl ∙ lCancel (λ _ → a) i)) ∙
                           (λ i → rUnit (refl ∙ (λ _ → a)) ∙ assoc (sym (rUnit (refl ∙ (λ _ → a))))
                                                             (λ i → refl ∙ lCancel (λ _ → a) (~ i))
                                                             (λ i → refl ∙ lCancel (λ _ → a) i) (~ i)) ∙
                           (λ i → rUnit (refl ∙ (λ _ → a)) ∙ sym (rUnit (refl ∙ (λ _ → a))) ∙ lCancel (λ i → refl ∙ lCancel (λ _ → a) i) i) ∙
                           (λ i → rUnit (refl ∙ (λ _ → a)) ∙ rUnit (sym (rUnit (refl ∙ (λ _ → a)))) (~ i)) ∙
                           rCancel (rUnit (refl ∙ (λ _ → a))))
-}

outerTranspId3 : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
                 transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                           (transpRCancel (λ i → north ≡ (merid a (~ i))) (merid x1 ∙ (sym (merid a)))) i))
                           ∣ x1 , rUnit (merid x1) ∙ sym (cong (λ x → merid x1 ∙ x) (lCancel (merid a))) ∙
                                  assocJ (merid x1) (sym (merid a)) (merid a) ∙
                                  sym (pairLemma3 {a1 = north} (merid x1 ∙ (sym (merid a))) (merid a)) ∣ 
                ≡ ∣ x1 , refl ∣
outerTranspId3 {ℓ}{A = A} n a x1 iscon = transportLemma {B = uncurry (CODE' {a = a} n iscon)}
                                                        (sym (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                      (transpRCancel (λ i → north ≡ (merid a (~ i))) (merid x1 ∙ (sym (merid a))))))
                                                        (∣ x1 , refl ∣)
                                                        (∣ x1 , rUnit (merid x1) ∙ sym (cong (λ x → merid x1 ∙ x) (lCancel (merid a))) ∙
                                                                                   assocJ (merid x1) (sym (merid a)) (merid a) ∙
                                                                                   sym (pairLemma3 {a1 = north} (merid x1 ∙ (sym (merid a))) (merid a)) ∣)
                                         ((λ k → transport (λ i → uncurry (CODE' {a = a} n iscon)
                                                                           (pair⁼''Sym (λ i₁ → merid a (~ i₁))
                                                                                    (transpRCancel (λ i₁ → north ≡ merid a (~ i₁))
                                                                                                   (merid x1 ∙ (λ i₁ → merid a (~ i₁)))) k i))
                                                  ∣ x1 , (λ _ → σ x1 {a}) ∣)
                                         ∙ (λ k → transport (λ i → uncurry (CODE' {a = a} n iscon)
                                                                           (pair⁼'' (merid a) (transportLemma {B = λ y → north ≡ y} (sym (merid a)) (transport (λ i₁ → north ≡ merid a i₁) (merid x1 ∙ (sym (merid a) ))) (merid x1 ∙ (sym (merid a))) ((transpRCancel (λ i₁ → north ≡ merid a (~ i₁)) (merid x1 ∙ (λ i₁ → merid a (~ i₁)))))) i) )
                                                  ∣ x1 , (λ _ → σ x1 {a}) ∣) ∙
                                           (λ k → transport (λ i → uncurry (CODE' {a = a} n iscon)
                                                                           (pair⁼'' (merid a) (wowie south (merid a) (merid x1) k) i) )
                                                  ∣ x1 , (λ _ → σ x1 {a}) ∣) ∙
                                           -- cong (λ x → x ∣ x1 , (λ _ → σ x1 {a}) ∣) (Lemma8610Refl'' (CODE' {a = a} n iscon) (merid a) (σ x1 {a})) ∙
                                           (λ k → transport (λ i → uncurry (CODE''Id {A = A} {a = a} n iscon k)
                                                                           (pair⁼'' {x = north , σ x1 {a}} {y = south , _} (merid a) (λ _ → transport (λ i₁ → _≡_ {A = Susp A} north (merid a i₁)) (σ x1 {a})) i) )
                                                  ∣ x1 , (λ _ → σ x1 {a}) ∣) ∙
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
                                           (λ k → transport ((λ i → ∥ fiber (λ y → σ y {a})
                                                              (transpRCancel
                                                                 (λ i₁ → north ≡ merid a (~ i₁)) (σ x1 {a}) (~ i)) ∥ ℕ→ℕ₋₂ (n + n)) ∙
                                                                 {!(Lemma296Funs.inv'' {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                                      (merid a) (λ p → ∥ fiber (λ y → σ y {a}) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                                      (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                                                      (equivTest' {X = Susp A} (merid a)
                                                                                                  {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                                  {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                        (λ q → ua' (RlFun2 a a n iscon q , RlFunEquiv2 a a n iscon q))))
                                                                                       (transport (λ i → north ≡ merid a i) (σ x1 {a}))!})
                                                             ∣ x1 , (λ _ → σ x1 {a}) ∣) ∙
                                           {!!} ∙
                                           {!!} ∙
                                           {!!} ∙
                                           {!!})

  where
  ma : _≡_ {A = Susp A} north south
  ma = merid a
  mx1 : _≡_ {A = Susp A} north south
  mx1 = merid x1
  
  guyid : (transport (λ i → north ≡ merid a i) (σ x1 {a})) ≡ merid x1
  guyid = pairLemma3 {a1 = north} (σ x1 {a}) (merid a) ∙ sym (assoc (merid x1) (sym (merid a)) (merid a)) ∙
          (λ i → merid x1 ∙ (lCancel (merid a)) i) ∙ sym (rUnit (merid x1))

  test : (y : Susp A) (mx1 : north ≡ y) → (transport (λ i → uncurry (CODE' {a = a} n iscon)
                                                                           (pair⁼'' {x = north , {!!}} {y = south , _} (merid a) refl i) )
                                                     ∣ {!!} , {!!} ∣) ≡ {!pair⁼'' {x = north , ?} {y = }!}
                                                     
  test = {!!}

  wowie : (y : Susp A) (ma mx1 : north ≡ y) → (transportLemma {B = λ y → north ≡ y} (sym ma) (transport (λ i₁ → north ≡ ma i₁) (mx1 ∙ (sym ma))) (mx1 ∙ (sym ma)) (transpRCancel (λ i₁ → north ≡ ma (~ i₁)) (mx1 ∙ (sym ma)))) ≡ refl
  wowie y  = J (λ y ma → (mx1 : north ≡ y) → (transportLemma {B = λ y → north ≡ y} (sym ma) (transport (λ i₁ → north ≡ ma i₁) (mx1 ∙ (sym ma))) (mx1 ∙ (sym ma)) (transpRCancel (λ i₁ → north ≡ ma (~ i₁)) (mx1 ∙ (sym ma)))) ≡ refl)
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
    where
    helper : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → transportRefl (p ∙ λ _ → y) ∙ {!sym (transport (λ i₁ → x ≡ y) (p ∙ (λ _ → y))) !} ∙ transportRefl (transport (λ i₁ → x ≡ y) (p ∙ (λ _ → y))) ≡ {!!}
    helper = {!!}

  wowie2 : (transportLemma {B = λ y → north ≡ y} (sym (merid a)) (transport (λ i₁ → north ≡ merid a i₁) (merid x1 ∙ (sym (merid a)))) (merid x1 ∙ (sym (merid a))) (transpRCancel (λ i₁ → north ≡ merid a (~ i₁)) (merid x1 ∙ (sym (merid a))))) ≡ {!!}
  wowie2 = {!!}

-- outerTranspId : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
--                 transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁)) (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i)) ∣ x1 , refl ∣
--                 ≡ transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁)) (transpRCancel (λ i → north ≡ (merid a (~ i))) (merid x1 ∙ (sym (merid a)))) i)) ∣ x1 , rUnit (merid x1) ∙ sym (cong (λ x → merid x1 ∙ x) (lCancel (merid a)))  ∙ assocJ (merid x1) (sym (merid a)) (merid a) ∙ sym (pairLemma3 {a1 = north} (merid x1 ∙ (sym (merid a))) (merid a)) ∣
-- outerTranspId {ℓ} {A = A} n a x1 iscon = sym (wowie north (sym (merid a)))
                
--    where
--    wowie : (y : Susp A) → (q : south ≡ y) → transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' q (transpRCancel (λ i → north ≡ q i) ((merid x1) ∙ q)) i))
--                                                       ∣ x1 , rUnit (merid x1)  ∙
--                                                              sym (cong (λ x → merid x1 ∙ x) (lCancel (sym q))) ∙
--                                                              assocJ (merid x1) q (sym q) ∙ sym ((pairLemma3 {a1 = north} (merid x1 ∙ q) (sym q))) ∣
--                                           ≡ transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' q (pairLemma3 (merid x1) q ) i)) ∣ x1 , refl ∣
--    wowie y = J (λ y q → transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' q (transpRCancel (λ i → north ≡ q i) ((merid x1) ∙ q)) i)) ∣ x1 , rUnit (merid x1)  ∙ sym (cong (λ x → merid x1 ∙ x) (lCancel (sym q))) ∙ assocJ (merid x1) q (sym q) ∙ sym ((pairLemma3 {a1 = north} (merid x1 ∙ q) (sym q))) ∣ ≡ transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' q (pairLemma3 (merid x1) q ) i)) ∣ x1 , refl ∣)
--                (transport
--       (λ i →
--          uncurry (CODE' {a = a} n iscon)
--          (pair⁼'' refl
--           (transpRCancel (λ i₁ → north ≡ refl i₁) (merid x1 ∙ refl)) i)) ∣ x1 , originalPath ∣
--                ≡⟨ (λ j → (transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼''Refl (transpRCancel (λ i₁ → north ≡ south) (merid x1 ∙ refl)) j i))) ∣ x1 , originalPath ∣) ⟩
--                (transport (λ i → uncurry (CODE' {a = a} n iscon)
--                                  (south , ((sym (transportRefl (transport (λ i → _≡_ {A = Susp A} north south) (merid x1 ∙ (λ _ → south))))) ∙ (
--                                            transpRCancel {A = north ≡ south} {B = north ≡ south} (λ _ → _≡_ {A = Susp A} north south)
--                                                          (merid x1 ∙ (refl {x = south})))) i) ))
--                           ∣ x1 , originalPath ∣
--                ≡⟨ (λ j → (transport (λ i → uncurry (CODE' {a = a} n iscon)
--                                     (south , transportCanceller (merid x1 ∙ (λ _ → south)) j i) ))
--                                     ∣ x1 , originalPath ∣) ⟩
--                (transport (λ i → uncurry (CODE' {a = a} n iscon) (south , transportRefl (merid x1 ∙ (λ _ → south)) i) ))
--                           ∣ x1 , originalPath ∣
--                ≡⟨ (λ j → (transport (λ i → uncurry (CODE' {a = a} n iscon) (south , transportRefl (merid x1 ∙ (λ _ → south)) i) ))
--                                    ∣ x1 , rUnit originalPath j ∣) ⟩
--                (transport (λ i → uncurry (CODE {a = a} n iscon) (south , transportRefl (merid x1 ∙ (λ _ → south)) i) ))
--                           ∣ x1 , originalPath ∙ refl ∣
--                ≡⟨ (λ j → (transport (λ i → uncurry (CODE' {a = a} n iscon) (south , (transportRefl {A = _≡_ {A = Susp A} north south} (merid x1 ∙ (λ _ → south)) (i ∨ j) ) ) ))
--                           ∣ x1 , originalPath ∙ (λ k → transportRefl {A = _≡_ {A = Susp A} north south}  (merid x1 ∙ (λ _ → south)) (k ∧ j))  ∣) ⟩
--                 (transport (λ i → uncurry (CODE {a = a} n iscon) (south , (merid x1 ∙ (λ _ → south)) ) ))
--                           ∣ x1 , originalPath ∙ transportRefl {A = _≡_ {A = Susp A} north south} (merid x1 ∙ (λ _ → south))  ∣ 
--                ≡⟨ (λ j → transport (λ i → uncurry (CODE' {a = a} n iscon) (south , merid x1 ∙ (λ _ → south)))
--                                     ∣ x1 , pathId (merid x1) j ∣) ⟩
--                transport (λ i → uncurry (CODE {a = a} n iscon) (south , (merid x1 ∙ (λ _ → south)))) ∣ x1 , (λ _ → merid x1) ∙ rUnit (merid x1) ∣
--                ≡⟨ (λ j → transport (λ i → uncurry (CODE' {a = a} n iscon) (south , rUnit (merid x1) (i ∨ (~ j) ))) ∣ x1 , (λ _ → merid x1) ∙ ( λ i → rUnit (merid x1) (i ∧ (~ j))) ∣) ⟩
--                transport (λ i → uncurry (CODE' {a = a} n iscon) (south , rUnit (merid x1)  i)) ∣ x1 , (λ _ → merid x1) ∙ refl ∣
--                ≡⟨ (λ j → transport (λ i → uncurry (CODE' {a = a} n iscon) (south , rUnit (merid x1)  i)) ∣ x1 , rUnit (λ _ → merid x1) (~ j) ∣) ⟩
--                transport (λ i → uncurry (CODE' {a = a} n iscon) (south , rUnit (merid x1)  i)) ∣ x1 , (λ _ → merid x1) ∣
--                ≡⟨ (λ j → transport (λ i → uncurry (CODE' {a = a} n iscon) (south , transportCanceller2 (merid x1) (~ j)  i)) ∣ x1 , (λ _ → merid x1) ∣) ⟩
--                transport (λ i → uncurry (CODE' {a = a} n iscon) (south , (sym (transportRefl (merid x1)) ∙ (pairLemma3 (merid x1) refl)) i)) ∣ x1 , (λ _ → merid x1) ∣
--                ≡⟨ (λ j → transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼''Refl (pairLemma3 (merid x1) (λ _ → south)) (~ j) i )) ∣ x1 , (λ _ → merid x1) ∣) ⟩
--                transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' refl (pairLemma3 (merid x1) refl) i)) ∣ x1 , (λ _ → merid x1) ∣ ∎)

--       where
--       originalPath : merid x1 ≡ transport (λ i₁ → _≡_ {A = Susp A} north south) (merid x1 ∙ (λ _ → south))
--       originalPath = rUnit (merid x1) ∙  (λ i → merid x1 ∙ lCancel (refl {x = south}) (~ i)) ∙ assocJ (merid x1) refl refl ∙
--                                          (λ i → pairLemma3 (merid x1 ∙ refl) refl (~ i))

--       pathId : ∀ {A : Type ℓ} {x y : A} (p : x ≡ y) → (rUnit p ∙
--                                                         (λ i → p ∙ lCancel (refl) (~ i)) ∙
--                                                         assocJ p refl refl ∙
--                                                         (λ i → pairLemma3 (p ∙ refl) refl (~ i))) ∙
--                                                         transportRefl (p ∙ refl)
--                                                         ≡
--                                                         refl ∙ rUnit p
--       pathId {x = x} = J (λ y p → (rUnit p ∙
--                                     (λ i → p ∙ lCancel (refl) (~ i)) ∙
--                                     assocJ p refl refl ∙
--                                     (λ i → pairLemma3 (p ∙ refl) refl (~ i))) ∙
--                                     transportRefl (p ∙ refl)
--                                     ≡
--                                     refl ∙ rUnit p)
--                            ((λ j → (rUnit refl ∙
--                                     (λ i → refl ∙ lCancel (refl) (~ i)) ∙
--                                     assocJRefl j ∙
--                                     sym (pairLemma3Id (refl ∙ refl) refl j)) ∙
--                                     transportRefl (refl ∙ refl)) ∙
--                            (λ j → (rUnit refl ∙
--                                     (λ i → refl ∙ lCancel (refl) (~ i)) ∙
--                                     ((λ i → refl ∙ rCancel refl i) ∙ rUnit (refl ∙ refl)) ∙
--                                     sym (pairLemma3*Refl (refl ∙ refl) j)) ∙
--                                     transportRefl (refl ∙ refl)) ∙
--                            (λ j → (rUnit refl ∙
--                                     (λ i → refl ∙ lCancel (refl) (~ i)) ∙
--                                     ((λ i → refl ∙ rCancel refl i) ∙ rUnit (refl ∙ refl)) ∙
--                                     symDistr (transportRefl (refl ∙ refl)) (rUnit (refl ∙ refl)) j  ) ∙
--                                     transportRefl (refl ∙ refl)) ∙
--                            invKiller (rUnit refl) (λ i → refl ∙ lCancel (refl) (~ i)) (rUnit (refl ∙ refl)) (sym (transportRefl (refl ∙ refl)))  ∙
--                            lUnit (rUnit refl))
--             where
--             invKiller : ∀ {ℓ} {A : Type ℓ} {a b c d e : A} (p : a ≡ b) (q : b ≡ c) (r : b ≡ d) (s : b ≡ e) →
--                           (p ∙ q ∙ (sym q ∙ r) ∙ sym r ∙ s) ∙ (sym s) ≡ p
--             invKiller {a = a} {b = b} {c = c} {d = d} {e = e} p = J (λ c q → (r : b ≡ d) (s : b ≡ e) →
--                                                                       (p ∙ q ∙ (sym q ∙ r) ∙ sym r ∙ s) ∙ (sym s) ≡ p)
--                                                                       (J (λ d r → (s : b ≡ e) → (p ∙ refl ∙ (refl ∙ r) ∙ sym r ∙ s) ∙ (sym s) ≡ p)
--                                                                           (J (λ e s → (p ∙ refl ∙ (refl ∙ refl) ∙ refl ∙ s) ∙ (sym s) ≡ p)
--                                                                               ((λ i → rUnit (p ∙ (λ _ → b) ∙ (rUnit refl (~ i)) ∙ refl ∙ refl) (~ i)) ∙
--                                                                               (λ i → p ∙ (lUnit (lUnit (lUnit refl (~ i)) (~ i)) (~ i) )) ∙
--                                                                               sym (rUnit p))))
            

--       transportCanceller : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) →
--                            sym (transportRefl (transport (λ i → x ≡ y) p )) ∙ transpRCancel (λ _ → x ≡ y) p ≡ transportRefl p
--       transportCanceller {x = x} {y = y} p = (λ j → sym (transportRefl (transport (λ i → x ≡ y) p)) ∙ (transpRCancelRefl p j)) ∙
--                                              assoc (sym (transportRefl (transport (λ i → x ≡ y) p)))
--                                                    ((transportRefl (transport (λ i → x ≡ y) p)))
--                                                    (transportRefl p)  ∙
--                                              (λ j → lCancel (transportRefl (transport (λ i → x ≡ y) p)) j ∙ transportRefl p) ∙
--                                              sym (lUnit (transportRefl p))

--       transportCanceller2 : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) →
--                             (sym (transportRefl p) ∙ (pairLemma3 p refl)) ≡ rUnit p
--       transportCanceller2 {x = x} = J (λ y p → (sym (transportRefl p) ∙ (pairLemma3 p refl)) ≡ rUnit p)
--                                       ((λ j → sym (transportRefl refl) ∙ pairLemma3Refl refl j) ∙
--                                       (λ j → sym (transportRefl refl) ∙ pairLemma2Refl j ∙ lUnit refl) ∙
--                                       assoc (sym (transportRefl refl)) (transportRefl refl) (lUnit refl) ∙
--                                       (λ j → lCancel (transportRefl refl) j ∙ lUnit refl) ∙
--                                       sym (lUnit (lUnit refl)) )



-- Lemma8610ap : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
--               transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁)) (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i)) ∣ x1 , refl ∣
--               ≡ {!!}
-- Lemma8610ap {ℓ} {A = A} n a x1 iscon = outerTranspId n a x1 iscon ∙
--                            cong (λ x → x guy) (Lemma8610'' (CODE' {a = a} n iscon) (sym (merid a)) (σ x1 {a})) ∙
--                            transport (λ i → ((sym (cong (λ x → x (σ x1 {a})) (Lemma294' {A = λ a → north ≡ a} {B = λ a → _} (sym (merid a)) ((CODE' {a = a} n iscon) south)))) ∙ funExt⁻ (fromPathP (λ j → toPathP {A = λ i → north ≡ merid a i → Type ℓ} {x = λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))}
--                                                        {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))}
--                                                        (Lemma296Funs.inv {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
--                                                                          (merid a) (λ p → ∥ fiber (λ y → σ y) p ∥ ℕ→ℕ₋₂ (n + n))
--                                                                          (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
--                                                                          (equivTest {X = Susp A} (merid a) {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
--                                                                                     {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
--                                                                                     λ q → (ua' (RlFun2 a a n iscon q , RlFunEquiv2 a a n iscon q)))) (~ j))) (σ x1 {a})) i) guy ∙
--                            {! !}
-- {- toPathP
--          (Lemma296Funs.inv (merid x1)
--           (λ p → ∥ fiber (λ y → σ y) p ∥ ℕ→ℕ₋₂ (n + n))
--           (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
--           (equivTest (merid x1)
--            (λ q → ua' (RlFun2 a x1 n iscon q , RlFunEquiv2 a x1 n iscon q))))
--          (~ i) j -}


--   where
--   guy : ∥ fiber merid (subst (λ z → north ≡ z) (sym (λ i → merid a (~ i))) (σ x1)) ∥ ℕ→ℕ₋₂ (n + n)
--   guy = ∣ x1 , rUnit (merid x1) ∙ sym (cong (_∙_ (merid x1)) (lCancel (merid a))) ∙ assocJ (merid x1) (sym (merid a)) (merid a) ∙ sym (pairLemma3 (merid x1 ∙ sym (merid a)) (merid a)) ∣




-- reflCase  : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → c n a iscon north (σ x1) ≡ ∣ x1 , refl ∣
-- reflCase {ℓ} {A} n a x1 iscon = {!Lemma8610 (CODE' {a = a} n iscon)!}


-- -- codeTranspHelper1 :  ∀{ℓ} {X : Type ℓ} {a b : X}  (q p : a ≡ b) → (A : (a ≡ a) → Type ℓ) (B : (a ≡ b) → Type ℓ) → (f : (q₁ : a ≡ b) → A (q₁ ∙ sym q) ≡ B q₁) →
-- --         (sym (cong (λ x → x p) (Lemma294' {A = λ x → a ≡ x} {B = λ _ → Type ℓ} q A))) ∙ funExt⁻ (fromPathP (toPathP {A = λ i → a ≡ q i → Type ℓ} {x = A} {y = B}
-- --                                                        (Lemma296Funs.inv {X = X} {A = λ y → a ≡ y} {B = λ _ → Type ℓ}
-- --                                                                          q A
-- --                                                                          B
-- --                                                                          (equivTest {X = X} q {A = A}
-- --                                                                                     {B = B}
-- --                                                                                     f)))) p
-- --           ≡ (transportRefl (A (subst (λ x → a ≡ x) (sym q) p)) ∙ cong (λ x → A x) (pairLemma3 p (sym q))) ∙ f p
-- -- codeTranspHelper1 {ℓ}  {X = X} {a = a} = J (λ b q → (p : a ≡ b) (A : (a ≡ a) → Type ℓ) (B : (a ≡ b) → Type ℓ) (f : (q₁ : a ≡ b) → A (q₁ ∙ sym q) ≡ B q₁) →
-- --                                        (sym (cong (λ x → x p) (Lemma294' {A = λ x → a ≡ x} {B = λ _ → Type ℓ} q A))) ∙
-- --                                         funExt⁻ (fromPathP (toPathP {A = λ i → a ≡ q i → Type ℓ} {x = A} {y = B}
-- --                                                                     (Lemma296Funs.inv {X = X} {A = λ y → a ≡ y}
-- --                                                                                       {B = λ _ → Type ℓ} q A B
-- --                                                                                       (equivTest {X = X} q {A = A} {B = B} f)))) p
-- --                                        ≡ (transportRefl (A (subst (λ x → a ≡ x) (sym q) p)) ∙
-- --                                           cong (λ x → A x) (pairLemma3 p (sym q))) ∙ f p)
-- --                               λ p A B f → (λ k → ((λ i → (Lemma294'Refl {A = λ x → a ≡ x} {B = λ _ → Type ℓ} A k) (~ i) p)) ∙
-- --                                                  (λ i → fromPathP (toPathP {A = λ i → a ≡ a → Type ℓ} {x = A} {y = B}
-- --                                                                            (Lemma296Funs.inv {X = X} {A = λ y → a ≡ y} {B = λ _ → Type ℓ} (refl {x = a})
-- --                                                                                              A B (equivTest {X = X} (refl {x = a}) {A = A} {B = B} f))) i p)) ∙
-- --                                           (λ k → lUnit ((λ i → fromPathP (toPathP {A = λ i → a ≡ a → Type ℓ} {x = A} {y = B}
-- --                                                                            (Lemma296Funs.inv {X = X} {A = λ y → a ≡ y} {B = λ _ → Type ℓ} (refl {x = a})
-- --                                                                                              A B (equivTest {X = X} (refl {x = a}) {A = A} {B = B} f))) i p)) (~ k)) ∙
-- --                                           (λ k i → (toPathCancel {A = λ i → a ≡ a → Type ℓ} {x = A} (Lemma296Funs.inv {X = X} {A = λ y → a ≡ y}
-- --                                                                                                     {B = λ _ → Type ℓ} (refl {x = a})
-- --                                                                                              A B (equivTest {X = X} (refl {x = a}) {A = A} {B = B} f)) k) i p) ∙
-- --                                           (λ k i → ((cong (λ x → x (equivTest {X = X} (λ _ → a) f)) (ReflCases.invRefl {A = λ y → a ≡ y}
-- --                                                                                                                        {B = λ _ → Type ℓ} A B)) k) i p ) ∙
-- --                                           (λ k i → (transportRefl {A = a ≡ a → Type ℓ} A ∙
-- --                                                    funExt λ z → sym (transportRefl {A = Type ℓ} (A z))  ∙
-- --                                                    cong (λ x → x f z) (equivTestRefl {X = X} p {A = A} {B = B}) k ∙
-- --                                                    λ i → (B (transportRefl {A = a ≡ a} z i))) i p) ∙
-- --                                           sym (congComp2 (λ x → x p) (transportRefl A)
-- --                                                                  (funExt λ z → sym (transportRefl {A = Type ℓ} (A z)) ∙
-- --                                                                  (transportRefl (A z) ∙ cong (λ x → A x) (rUnit z) ∙
-- --                                                                  f z ∙
-- --                                                                  cong (λ x → B x) (sym (transportRefl z))) ∙
-- --                                                                  λ i → (B (transportRefl z i)))) ∙
-- --                                           invCanceller (cong (λ x → x p) (transportRefl A))
-- --                                                        (sym (transportRefl (A p)))
-- --                                                        (λ i → A (rUnit p i))
-- --                                                        (f p)
-- --                                                        (λ i → B (transportRefl p i))  ∙
-- --                                           assoc (λ i → transportRefl A i p)
-- --                                                 (λ i → A (rUnit p i))
-- --                                                 (f p) ∙
-- --                                           (λ k → ((λ i → transportRefl A i p) ∙ (λ i → A (rUnit p i))) ∙ f p) ∙
-- --                                           (λ k → (transpLemma2 {A = A} p k ∙ (cong (λ x → A x) (rUnit p))) ∙ f p ) ∙
-- --                                           (λ k → ((assoc (transportRefl (A (subst (_≡_ a) (λ i → a) p)))
-- --                                                          (cong (λ x → A x) (transportRefl p))
-- --                                                          (cong (λ x → A x) (rUnit p))) (~ k)) ∙
-- --                                                   f p) ∙
-- --                                           (λ k → ((transportRefl (A (subst (_≡_ a) (λ i → a) p)) ∙ congComp2 (λ x → A x) (transportRefl p) (rUnit p) k)  ∙ f p)) ∙
-- --                                           (λ k → (transportRefl (A (subst (_≡_ a) (λ i → a) p)) ∙
-- --                                                  (λ i → A ((transportRefl p ∙ rUnit p) i))) ∙
-- --                                                  f p) ∙
-- --                                           (λ k → (transportRefl (A (subst (_≡_ a) (λ i → a) p)) ∙ (λ i → A (pairLemma3*Refl p (~ k) i))) ∙ f p) ∙
-- --                                           λ k → (transportRefl (A (subst (_≡_ a) (λ i → a) p)) ∙ (λ i → A (pairLemma3Id p (λ i₁ → a ) (~ k)  i))) ∙ f p

-- --      where
-- --      transpLemma2 : ∀ {ℓ ℓ'} {X : Type ℓ} {x : X} {A : x ≡ x → Type ℓ'} (p : x ≡ x) → (λ i → transportRefl A i p)  ≡ (transportRefl (A (transport (λ i → x ≡ x)  p)) ∙ (λ i → A ((transportRefl p) i)))
-- --      transpLemma2 {ℓ' = ℓ'}{x = x} {A = A} p j = hcomp (λ k → λ{(j = i0) → (sym (lUnit (λ i → transportRefl (A ((transportRefl p) i)) i))) k
-- --                                                              ; (j = i1) → (transportRefl (A (transport (λ i → x ≡ x)  p)) ∙
-- --                                                                           (λ i → A ((transportRefl p) i)))})
-- --                                                      ((λ i → transportRefl (A (transport (λ i → x ≡ x) p )) (i ∧ j)) ∙
-- --                                                      (λ i → transportRefl (A ((transportRefl p) i)) (i ∨ j)))


-- --      invCanceller : ∀ {ℓ} {A : Type ℓ} {a b c d e f : A} (p : a ≡ b) (q : b ≡ c) (r : b ≡ d) (s : d ≡ e) (t : f ≡ e) →
-- --                     p ∙ q ∙ (sym q ∙ r ∙ s ∙ sym t) ∙ t ≡ p ∙ r ∙ s
-- --      invCanceller {a = a} {b = b} {c = c} {d = d} {e = e} {f = f}  = 
-- --                    J (λ b p → (q : b ≡ c) (r : b ≡ d) (s : d ≡ e) (t : f ≡ e) →
-- --                                p ∙ q ∙ (sym q ∙ r ∙ s ∙ sym t) ∙ t ≡ p ∙ r ∙ s)
-- --                                (J (λ c q → (r : a ≡ d) (s : d ≡ e) (t : f ≡ e) →
-- --                                            refl ∙ q ∙ ((λ i → q (~ i)) ∙ r ∙ s ∙ (λ i → t (~ i))) ∙ t ≡ refl ∙ r ∙ s)
-- --                                    (J (λ d r → (s : d ≡ e) (t : f ≡ e) →
-- --                                                (λ _ → a) ∙ (λ _ → a) ∙ ((λ _ → a) ∙ r ∙ s ∙ (λ i → t (~ i))) ∙ t  ≡ (λ _ → a) ∙ r ∙ s)
-- --                                       (J (λ e s → (t : f ≡ e) →
-- --                                                   (λ _ → a) ∙ (λ _ → a) ∙ ((λ _ → a) ∙ (λ _ → a) ∙ s ∙ (λ i → t (~ i))) ∙ t  ≡ (λ _ → a) ∙ (λ _ → a) ∙ s)
-- --                                          λ t → sym (lUnit ((λ _ → a) ∙ ((λ _ → a) ∙ (λ _ → a) ∙ refl ∙ (λ i → t (~ i))) ∙ t)) ∙
-- --                                                sym (lUnit (((λ _ → a) ∙ (λ _ → a) ∙ refl ∙ (λ i → t (~ i))) ∙ t)) ∙
-- --                                                (λ k → (lUnit (lUnit (lUnit (sym t) (~ k)) (~ k)) (~ k)) ∙ t) ∙
-- --                                                lCancel t ∙
-- --                                                λ k → lUnit (lUnit refl k) k)))



-- -- {- given things compue properly, we transform the inner transport as follows -}
-- -- test : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
-- --        (RlFun2 a x1 n iscon (merid x1)) (transport (λ i → cong (λ p₁ → ∥ fiber (λ y₁ → σ y₁ {a}) p₁ ∥ ℕ→ℕ₋₂ (n + n)) (pairLemma3 (merid x1) (sym (merid x1))) i)
-- --                                                   (transport (λ i → (transportRefl (∥ fiber (λ y₁ → σ y₁ {a})
-- --                                                                     (subst (_≡_ north) (sym (merid x1)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)))i)
-- --                                                    ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣))
-- --         ≡ ∣ x1 , refl ∣
-- -- test n a x1 iscon = (RlFun2 a x1 n iscon (merid x1)) (outer (inner guy)) ≡⟨ (λ j → (RlFun2 a x1 n iscon (merid x1)) (outer (innerTransp j))) ⟩
-- --                     (RlFun2 a x1 n iscon (merid x1)) (outer guy) ≡⟨ (λ j → (RlFun2 a x1 n iscon (merid x1)) (outerTransp j)) ⟩
-- --                     (RlFun2 a x1 n iscon (merid x1)) guy2 ≡⟨ refl ⟩
-- --                     sufMap2 n x1 a a iscon (merid x1) (rCancel (merid a) ∙ sym (rCancel (merid x1))) ≡⟨ cong (λ x → x (rCancel (merid a) ∙ sym (rCancel (merid x1))))
-- --                                                                                                              (sufMap2Id n a x1 iscon) ⟩
-- --                     ∣ x1 , switcher (merid a) (merid x1) (merid x1) (rCancel (merid a) ∙ sym (rCancel (merid x1))) ∣ ≡⟨ (λ j → ∣ x1 , switcherLemma (merid a) (merid x1) j ∣) ⟩
-- --                     ∣ x1 , refl ∣ ∎
-- --   where
-- --   switcherLemma : ∀ {ℓ} {A : Type ℓ} {a b c : A} (p : a ≡ b) (q : a ≡ c) → switcher p q q (rCancel p ∙ (sym (rCancel q))) ≡ refl  
-- --   switcherLemma {A = A} {a = a} {c = c} = J (λ b p → (q : a ≡ c) → switcher p q q (rCancel p ∙ (sym (rCancel q))) ≡ refl)
-- --                                             (J (λ c q → switcher refl q q (rCancel refl ∙ (sym (rCancel q))) ≡ refl)
-- --                                                 ((λ j → switcher refl refl refl (rCancel (rCancel refl) j )) ∙
-- --                                                  cong (λ x → x refl) (switcherRefl) ∙
-- --                                                  (λ j → lUnit refl ∙
-- --                                                         cong (λ x → x ∙ refl)
-- --                                                         (lUnit refl ∙ (lUnit (sym (lUnit (sym refl))) (~ j))) ∙
-- --                                                         lCancel refl) ∙
-- --                                                  (λ j → lUnit refl ∙
-- --                                                         cong (λ x → x ∙ refl)
-- --                                                         (rCancel (lUnit refl) j ) ∙
-- --                                                         lCancel refl) ∙
-- --                                                  (λ j → lUnit refl ∙
-- --                                                         lUnit (lCancel refl) (~ j)) ∙
-- --                                                  (λ j → rCancel (lUnit refl) j)))
-- --         where
-- --         helper2 : cong (λ x → x ∙ refl) (refl {x = (λ _ → a)})  ≡ refl
-- --         helper2 = refl
-- --   guy : transport (λ _ → Type _) (∥ fiber (λ y₁ → σ y₁ {a}) (subst (_≡_ north) (λ i → merid x1 (~ i)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n))
-- --   guy = ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣

-- --   guy2 : ∥ fiber (λ y → σ y) (merid x1 ∙ sym (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)
-- --   guy2 = ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∣
  
-- --   inner : transport (λ _ → Type _) (∥ fiber (λ y₁ → σ y₁ {a}) (subst (_≡_ north) (λ i → merid x1 (~ i)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)) →
-- --           ∥ fiber (λ y₁ → σ y₁ {a}) (subst (_≡_ north) (λ i → merid x1 (~ i)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)
-- --   inner = transport (λ i → (transportRefl (∥ fiber (λ y₁ → σ y₁ {a}) (subst (_≡_ north) (sym (merid x1)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)))i)
  
-- --   outer : transport (λ _ → Type _) (∥ fiber (λ y₁ → σ y₁ {a}) (subst (_≡_ north) (λ i → merid x1 (~ i)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)) →
-- --           ∥ fiber (λ y → σ y) (merid x1 ∙ sym (merid x1)) ∥ ℕ→ℕ₋₂ (n + n)
-- --   outer = transport (λ i → cong (λ p₁ → ∥ fiber (λ y₁ → σ y₁ {a}) p₁ ∥ ℕ→ℕ₋₂ (n + n)) (pairLemma3 (merid x1) (sym (merid x1))) i)
  
-- --   innerTransp : inner guy ≡ guy
-- --   innerTransp =
-- --      (λ j → (transport (λ i → (transportRefl (∥ fiber (λ y₁ → σ y₁ {a}) (subst (_≡_ north) (sym (merid x1)) (merid x1)) ∥ ℕ→ℕ₋₂ (n + n))) (i ∨ j))  guy ))
-- --                                                                     ∙  transportRefl guy
-- --   outerTransp : outer guy ≡ guy2
-- --   outerTransp = (λ j →  transport (λ i → cong (λ p₁ → ∥ fiber (λ y₁ → σ y₁ {a}) p₁ ∥ ℕ→ℕ₋₂ (n + n)) (pairLemma3 (merid x1) (sym (merid x1))) i)
-- --                                   ∣ a , rUnit (rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1)))) j  ∣  ) ∙
-- --                 (λ j → transport (λ i → cong (λ p₁ → ∥ fiber (λ y₁ → σ y₁ {a}) p₁ ∥ ℕ→ℕ₋₂ (n + n)) (pairLemma3 (merid x1) (sym (merid x1))) (i ∨ j))
-- --                        ∣ a , (rCancel (merid a) ∙
-- --                              sym (rCancel (merid x1)) ∙
-- --                              sym (pairLemma3 (merid x1) (sym (merid x1)))) ∙
-- --                              (λ i → (pairLemma3 (merid x1) (sym (merid x1))) (i ∧ j)) ∣) ∙
-- --                 (λ j → transportRefl (∣ a , (rCancel (merid a) ∙
-- --                                             sym (rCancel (merid x1)) ∙
-- --                                             sym (pairLemma3 (merid x1) (sym (merid x1)))) ∙
-- --                                             (pairLemma3 (merid x1) (sym (merid x1))) ∣) j) ∙
-- --                 (λ j → ∣ a , assoc (rCancel (merid a))
-- --                                    (sym (rCancel (merid x1)))
-- --                                    (sym (pairLemma3 (merid x1) (sym (merid x1)))) j
-- --                              ∙ (pairLemma3 (merid x1) (sym (merid x1))) ∣ ) ∙
-- --                 (λ j → ∣ a , assoc ((rCancel (merid a)) ∙ (sym (rCancel (merid x1))))
-- --                                    (sym (pairLemma3 (merid x1) (sym (merid x1))))
-- --                                    (pairLemma3 (merid x1) (sym (merid x1))) (~ j) ∣) ∙
-- --                 (λ j → ∣ a , ((rCancel (merid a)) ∙ (sym (rCancel (merid x1)))) ∙ (lCancel (pairLemma3 (merid x1) (sym (merid x1))) j)  ∣) ∙
-- --                 λ j → ∣ a , rUnit ((rCancel (merid a)) ∙ (sym (rCancel (merid x1)))) (~ j) ∣
