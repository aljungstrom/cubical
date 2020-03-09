{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Freudenthal.Prelim where


-- open import Cubical.ZCohomology.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.HITs.Truncation

open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

is-_-Truncated : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
                 (n : ℕ₋₂) → (f : A → B) → Type (ℓ-max ℓ ℓ')
is-_-Truncated {A = A} {B = B} n f = (b : B) → isOfHLevel (2+ n) (fiber f b)

_-_ : ℕ → ℕ → ℕ
zero - m = zero
suc n - zero = suc n
suc n - suc m = n - m


invPathCancel : {a b : A} → (p : a ≡ b) → p ∙ (sym p) ≡ refl
invPathCancel {a = a} {b = b} p = J {x = a} (λ y p → p ∙ (sym p) ≡ refl ) (sym (lUnit refl)) p
invPathCancel2 : {a b : A} → (p : a ≡ b) →  (sym p) ∙ p ≡ refl
invPathCancel2 {a = a} {b = b} p = J {x = a} (λ y p → (sym p) ∙ p ≡ refl ) (sym (lUnit refl)) p

cancelReflMid : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) (q : b ≡ a) → p ∙ refl ∙ q ≡ p ∙ q
cancelReflMid {ℓ = ℓ}{A = A} {a = a} {b = b} p q = J {ℓ} {A} {a} {ℓ} (λ b p → ((q : b ≡ a) →  p ∙ refl ∙ q ≡ p ∙ q)) (λ r → sym (lUnit (refl  ∙ r ))) {b} p q

pmId : (n : ℕ) → suc₋₂ (pred₋₂ (ℕ→ℕ₋₂ n)) ≡ (ℕ→ℕ₋₂ n)
pmId zero = refl
pmId (suc n) = refl

minusId : (n : ℕ) → n - n ≡ 0
minusId zero = refl
minusId (suc n) = minusId n


inducedFun : ∀{ℓ''} {k : ℕ₋₂}
             (f : A → B) →
             (P : (B → HLevel ℓ'' (2+ k))) →
             (((b : B) → fst (P b)) → (a : A) → fst (P (f a)) )
inducedFun  f P  = λ g a → g (f a)

-assocHelp : {a b : ℕ} → ((a + b) - b) ≡ a
-assocHelp {zero} {zero} = refl
-assocHelp {zero} {suc b} = -assocHelp {zero} {b}
-assocHelp {suc a} {zero} i = suc (+-zero a i)
-assocHelp {suc a} {suc b} = (λ i → ((+-suc a b i) - b)) ∙ (λ i → ((suc (+-comm a b i)) - b)) ∙
                             (λ i → (+-suc b a (~ i)) - b) ∙ ((λ i → ((+-comm b (suc a) i) - b))) ∙
                             -assocHelp {suc a} {b}


conTyp→conTyp2 : ∀ {ℓ} (n : ℕ₋₂) (A : Type ℓ) → is- n -ConnectedType A → is- n -ConnectedType2 A
conTyp→conTyp2 n A iscon = λ b → transport (λ i → isContr (∥ helper b i ∥ n)) iscon  where
  helper : (b : Unit) → A ≡ fiber (λ (x : A) → tt) b
  helper tt = isoToPath (iso (λ x → x , refl) (λ x → fst x) (λ b i → (refl {x = fst b} i) , ((isOfHLevelSuc 1 (isPropUnit) tt tt (snd b) refl) i)) λ a → refl)




canceller : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (p q : a ≡ b) (r : b ≡ c) → p ∙ r ≡ q ∙ r → p ≡ q
canceller {ℓ} {A} {a} {b} {c} = J {ℓ} {A} {a} (λ b p → ((q : a ≡ b) (r : b ≡ c) → p ∙ r ≡ q ∙ r → p ≡ q))
                                λ q → J {ℓ} {A} {a} (λ c r → (refl ∙ r ≡ q ∙ r → refl ≡ q)) λ id → rUnit refl ∙ id ∙ sym (rUnit q)   
-- rUnit p ∙ ((λ j → (p ∙ (rCancel r (~ j)))) ∙ assoc p r (sym r)) ∙ (cong (λ x → x ∙ (sym r)) id) ∙ sym (assoc q r (sym r)) ∙ (λ j → q ∙ (rCancel r j)) ∙ sym (rUnit q

switcher : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (p : a ≡ b) (q r : a ≡ c) → p ∙ (sym p) ≡ q ∙ (sym r) → r ≡ q
switcher {ℓ} {A} {a} {b} {c} = J {ℓ} {A} {a} (λ b p → ((q r : a ≡ c) → p ∙ (sym p) ≡ q ∙ (sym r) → r ≡ q))
                                 (J {ℓ} {A} {a} (λ c q → (r : a ≡ c) → refl ∙ (sym refl) ≡ q ∙ (sym r) → r ≡ q) λ r id → (lUnit r) ∙ cong (λ x → x ∙ r) ((rUnit (refl) ∙ id ∙ (sym (lUnit (sym r)))))  ∙ (lCancel r))
                                 -- ((λ j → (λ i → (lUnit (sym r) j) (~ i) ))) ∙ cong (λ x → sym x) (sym id) ∙ ((λ j → (λ i → (sym (rUnit (refl {x = a})) j) (~ i) ))))

switcherCancellerId : ∀ {ℓ} {A : Type ℓ} {a : A} (id : (refl {x = a}) ∙ refl ≡ refl ∙ refl) → canceller (refl {x = a}) refl refl id ≡ switcher refl refl refl id
switcherCancellerId id = (λ i → (cancellerRefl i) id) ∙ sym (finalReflPath id) ∙ λ i → (switcherRefl (~ i)) id
  where
  cancellerRefl : ∀ {ℓ} {A : Type ℓ} {a : A} → canceller {a = a} {b = a} {c = a} refl refl refl ≡ λ id → rUnit refl ∙ id ∙ sym (rUnit refl)
  cancellerRefl {ℓ} {A} {a} = (cong (λ x → x refl refl) (cancellerRefl1 {ℓ} {A} {a} {a} )) ∙ JRefl (λ c r → refl ∙ r ≡ (λ _ → a) ∙ r → refl ≡ (λ _ → a)) (λ id → rUnit refl ∙ id ∙ sym (rUnit (λ _ → a))) where
    cancellerRefl1 : ∀ {ℓ} {A : Type ℓ} {a c : A} → canceller {a = a} {b = a} {c = c} refl ≡ λ q → J {ℓ} {A} {a} (λ c r → (refl ∙ r ≡ q ∙ r → refl ≡ q)) λ id → rUnit refl ∙ id ∙ sym (rUnit q)
    cancellerRefl1 {ℓ} {A} {a} {c} = JRefl {ℓ} {A} {a} (λ b p → ((q : a ≡ b) (r : b ≡ c) → p ∙ r ≡ q ∙ r → p ≡ q)) (λ q → J {ℓ} {A} {a} (λ c r → (refl ∙ r ≡ q ∙ r → refl ≡ q)) λ id → rUnit refl ∙ id ∙ sym (rUnit q))

  switcherRefl : ∀ {ℓ} {A : Type ℓ} {a : A} → switcher (refl {x = a}) refl refl ≡ λ id → ((lUnit (refl {x = a})) ∙ cong (λ x → x ∙ refl) ((rUnit (refl {x = a}) ∙ id ∙ (sym (lUnit (sym refl))))) ∙ (lCancel refl))
  switcherRefl {ℓ} {A} {a} = cong (λ x → x refl refl) (JRefl {ℓ} {A} {a} ((λ b p → ((q r : a ≡ a) → p ∙ (sym p) ≡ q ∙ (sym r) → r ≡ q))) (J {ℓ} {A} {a} (λ c q → (r : a ≡ c) → refl ∙ (sym refl) ≡ q ∙ (sym r) → r ≡ q) λ r id → (lUnit r) ∙ cong (λ x → x ∙ r) ((rUnit (refl) ∙ id ∙ (sym (lUnit (sym r)))))  ∙ (lCancel r))) ∙
               cong (λ x → x refl) (JRefl {ℓ} {A} {a} (λ c q → (r : a ≡ c) → (λ _ → a) ∙ (λ i → a) ≡ q ∙ (λ i → r (~ i)) → r ≡ q) (λ r id → lUnit r ∙ (λ i → (rUnit (λ _ → a) ∙ id ∙ (λ i₁ → lUnit (λ i₂ → r (~ i₂)) (~ i₁))) i ∙ r) ∙ lCancel r))

  finalReflPath : {a : A} → (id : refl ∙ refl ≡ refl ∙ refl ) → ((lUnit (refl {x = a})) ∙ cong (λ x → x ∙ refl) ((rUnit (refl {x = a}) ∙ id ∙ (sym (lUnit (sym refl))))) ∙ (lCancel refl)) ≡ (rUnit (refl {x = a}) ∙ id ∙ (sym (lUnit (sym refl))))
  finalReflPath {a = a} id j = hcomp (λ k → λ{(j = i0) → refl {x = (lUnit (refl {x = a}))
                                                              ∙ cong (λ x → x ∙ refl) ((rUnit (refl {x = a}) ∙ id
                                                              ∙ (sym (lUnit (sym refl))))) ∙ (lCancel refl)} k
                                     ; (j = i1) → ((sym (lUnit ((cong (λ x → x)  (rUnit (refl {x = a}) ∙ id ∙ (sym (lUnit (sym refl))))) ∙ refl)))
                                                  ∙ (sym (rUnit ((cong (λ x → x)  (rUnit (refl {x = a}) ∙ id ∙ (sym (lUnit (sym refl))))))))) k})
                             ((λ i → (lUnit (refl {x = a})) (i ∧ ~ j) ) ∙ (cong (λ x → (sym (rUnit x)) j)  (rUnit (refl {x = a})
                                                                        ∙ id ∙ (sym (lUnit (sym refl))))) ∙ (λ i → (lCancel refl) (i ∨ j) ))




Lemma296b : ∀{ℓ ℓ' ℓ''} {X : Type ℓ} {x y : X} {A : X → Type ℓ'} {B : X → Type ℓ''}
           (p : x ≡ y)
           (f : (A x) → (B x))
           (g : (A y) → (B y)) →
           (transport (λ i → (A (p i)) → (B (p i))) f ≡ g) ≡ ((a : A y) → transport (λ i → B (p (~ i) )) (g a) ≡ f (transport (λ i → A (p (~ i))) a))
Lemma296b {ℓ = ℓ} {X = X} {x = x} {y = y} {A = A} {B = B} = J {ℓ} {X} {x} (λ y p → (f : (A x) → (B x)) (g : (A y) → (B y)) →
                                                                     (transport (λ i → (A (p i)) → (B (p i))) f ≡ g) ≡
                                                                          ((a : A y) → transport (λ i → B (p (~ i))) (g a) ≡ f (transport (λ i → A (p (~ i))) a)))
                                                                     λ f g → transport (λ i → helper1 f g (~ i)) (helper2 f g)
  where
  helper1 : (f : (A x) → (B x)) (g : (A x) → (B x)) →
            ((transport (λ i → A (refl {x = x} i) → B (refl {x = x} i)) f ≡ g) ≡ ((a : A x) → transport (λ i → B (refl {x = x} (~ i))) (g a) ≡ f (transport (λ i → A (refl {x = x} (~ i))) a)))
           ≡ ((f ≡ g) ≡ ((a : A x) → g a ≡ f a))
  helper1 f g i = ((transportRefl f i ≡ g) ≡ ((a : A x) → transportRefl (g a) i ≡ f (transportRefl a i)))

  helper2 : (f : (A x) → (B x)) (g : (A x) → (B x)) → ((f ≡ g) ≡ ((a : A x) → g a ≡ f a))
  helper2 f g =  isoToPath (iso (λ p a → sym (funExt⁻ p a)) (λ p → sym (funExt p) ) (λ x → refl) λ x → refl)

Lemma296 : ∀{ℓ ℓ' ℓ''} {X : Type ℓ} {x y : X} {A : X → Type ℓ'} {B : X → Type ℓ''}
           (p : x ≡ y)
           (f : (A x) → (B x))
           (g : (A y) → (B y)) →
           (transport (λ i → (A (p i)) → (B (p i))) f ≡ g) ≡ ((a : A x) → transport (λ i → B (p i)) (f a) ≡ g (transport (λ i → A (p i)) a))
Lemma296 {ℓ = ℓ} {X = X} {x = x} {y = y} {A = A} {B = B} = J {ℓ} {X} {x}
                                                            (λ y p → (f : (A x) → (B x)) (g : (A y) → (B y)) →
                                                                     (transport (λ i → (A (p i)) → (B (p i))) f ≡ g) ≡
                                                                          ((a : A x) → transport (λ i → B (p i)) (f a) ≡ g (transport (λ i → A (p i)) a)))
                                                            (λ f g → transport (λ i → reflTransport f g (~ i)) (reflCase f g))
  where
  reflTransport : (f g : A x → B x) → ((transport (λ i → A (refl {x = x} i) → B (refl {x = x} i)) f ≡ g) ≡ ((a : A x) → transport (λ i → B (refl {x = x} i)) (f a) ≡ g (transport (λ i → A (refl {x = x} i)) a))) ≡ ((f ≡ g) ≡ ((a : A x) → f a ≡ g a))
  reflTransport f g j = (transportRefl f j ≡ g) ≡ ((a : A x) → transportRefl (f a) j ≡ g (transportRefl a j))

  reflCase : (f g : A x → B x) → ((f ≡ g) ≡ ((a : A x) → f a ≡ g a))
  reflCase f g = isoToPath (iso (λ p → funExt⁻ p) (λ p → funExt p) (λ x → refl) λ x → refl) 

