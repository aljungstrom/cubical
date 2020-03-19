{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.FreudenthalFix.Prelim where


-- open import Cubical.ZCohomology.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
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

canceller : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (r : b ≡ c) (p q : a ≡ b) → p ∙ r ≡ q ∙ r → p ≡ q
canceller {ℓ} {A} {a} {b} {c} = J {ℓ} {A} {b} (λ c r → ((p q : a ≡ b) → p ∙ r ≡ q ∙ r → p ≡ q)) λ p q id → (rUnit p) ∙ id ∙ sym (rUnit q)

cancellerReflCase : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p q : a ≡ b) → canceller refl p q ≡ λ id → (rUnit p) ∙ id ∙ sym (rUnit q)
cancellerReflCase {a = a} {b = b} p q = cong (λ x → x p q) (JRefl (λ c r → ((p q : a ≡ b) → p ∙ r ≡ q ∙ r → p ≡ q)) λ p q id → (rUnit p) ∙ id ∙ sym (rUnit q)) 

cancellerInv : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (r : b ≡ c) (p q : a ≡ b) → (p ≡ q) → p ∙ r ≡ q ∙ r
cancellerInv {a = a} {b = b} = J (λ c r → (p q : a ≡ b) → (p ≡ q) → p ∙ r ≡ q ∙ r) λ p q id → sym (rUnit p) ∙ id ∙ rUnit q

cancellerInvReflCase : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p q : a ≡ b) → cancellerInv refl p q ≡ λ id → sym (rUnit p) ∙ id ∙ rUnit q
cancellerInvReflCase {a = a} {b = b} p q = cong (λ x → x p q) (JRefl (λ c r → (p q : a ≡ b) → (p ≡ q) → p ∙ r ≡ q ∙ r) λ p q id → sym (rUnit p) ∙ id ∙ rUnit q) 

cancellerSection :  ∀ {ℓ} {A : Type ℓ} {a b c : A} → (r : b ≡ c) (p q : a ≡ b) → section (canceller r p q) (cancellerInv r p q) 
cancellerSection {a = a} {b = b} {c = c} = J (λ c r → (p q : a ≡ b) → section (canceller r p q) (cancellerInv r p q) ) λ p q → transport (λ i → section (cancellerReflCase p q (~ i)) (cancellerInvReflCase p q (~ i))) (λ b → assoc (rUnit p) ((λ i → rUnit p (~ i)) ∙ b ∙ rUnit q) (λ i → rUnit q (~ i)) ∙
                          (λ i → ((assoc (rUnit p) (sym (rUnit p)) (b ∙ rUnit q)) i) ∙ (λ i → rUnit q (~ i))) ∙
                          (λ i → ((rCancel (rUnit p) i) ∙ (b ∙ rUnit q)) ∙ (sym (rUnit q))) ∙
                          (λ i → lUnit (b ∙ rUnit q) (~ i) ∙ (sym (rUnit q))) ∙
                          (sym (assoc b (rUnit q) (sym (rUnit q)))) ∙
                          (λ i → b ∙ (rCancel (rUnit q) i)) ∙
                          sym (rUnit b))

cancellerRetract :  ∀ {ℓ} {A : Type ℓ} {a b c : A} → (r : b ≡ c) (p q : a ≡ b) → retract (canceller r p q) (cancellerInv r p q) 
cancellerRetract {a = a} {b = b} {c = c} = J (λ c r → (p q : a ≡ b) → retract (canceller r p q) (cancellerInv r p q) ) λ p q → transport (λ i → retract (cancellerReflCase p q (~ i)) (cancellerInvReflCase p q (~ i))) λ b → assoc (sym (rUnit p)) ((λ i → rUnit p (i)) ∙ b ∙ (sym (rUnit q))) (rUnit q) ∙
                          (λ i → ((assoc (sym (rUnit p)) (rUnit p) (b ∙ sym (rUnit q))) i) ∙ (rUnit q)) ∙
                          (λ i → ((lCancel (rUnit p) i) ∙ (b ∙ sym (rUnit q))) ∙ ((rUnit q))) ∙
                          (λ i → (lUnit (b ∙ sym (rUnit q)) (~ i)) ∙ (rUnit q)) ∙
                          (sym (assoc b (sym (rUnit q)) (rUnit q))) ∙
                          (λ i → b ∙ (rCancel (sym (rUnit q)) i)) ∙
                          sym (rUnit b)
  

cancellerIsEquiv : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (r : b ≡ c) (p q : a ≡ b) → isEquiv (canceller r p q)
cancellerIsEquiv {ℓ} {A} {a} {b} {c} = J {ℓ} {A} {b} (λ c r → ((p q : a ≡ b) → isEquiv (canceller r p q))) λ p q → transport (λ i → isEquiv (cancellerHelp p q (~ i))) (helper p q)
  where
  helper : (p q  : a ≡ b) → isEquiv (λ id → ((rUnit p) ∙ id ∙ sym (rUnit q)))
  helper p q = isoToEquiv (iso ((λ id → ((rUnit p) ∙ id ∙ sym (rUnit q)))) (λ id → sym (rUnit p) ∙ id ∙ rUnit q)
                          ((λ b → assoc (rUnit p) ((λ i → rUnit p (~ i)) ∙ b ∙ rUnit q) (λ i → rUnit q (~ i)) ∙
                          (λ i → ((assoc (rUnit p) (sym (rUnit p)) (b ∙ rUnit q)) i) ∙ (λ i → rUnit q (~ i))) ∙
                          (λ i → ((rCancel (rUnit p) i) ∙ (b ∙ rUnit q)) ∙ (sym (rUnit q))) ∙
                          (λ i → lUnit (b ∙ rUnit q) (~ i) ∙ (sym (rUnit q))) ∙
                          (sym (assoc b (rUnit q) (sym (rUnit q)))) ∙
                          (λ i → b ∙ (rCancel (rUnit q) i)) ∙
                          sym (rUnit b)))
                          λ b → assoc (sym (rUnit p)) ((λ i → rUnit p (i)) ∙ b ∙ (sym (rUnit q))) (rUnit q) ∙
                          (λ i → ((assoc (sym (rUnit p)) (rUnit p) (b ∙ sym (rUnit q))) i) ∙ (rUnit q)) ∙
                          (λ i → ((lCancel (rUnit p) i) ∙ (b ∙ sym (rUnit q))) ∙ ((rUnit q))) ∙
                          (λ i → (lUnit (b ∙ sym (rUnit q)) (~ i)) ∙ (rUnit q)) ∙
                          (sym (assoc b (sym (rUnit q)) (rUnit q))) ∙
                          (λ i → b ∙ (rCancel (sym (rUnit q)) i)) ∙
                          sym (rUnit b)) .snd

  cancellerHelp : (p q : a ≡ b) → canceller refl p q ≡ λ id → (rUnit p) ∙ id ∙ sym (rUnit q)
  cancellerHelp  p q = cong (λ x → x p q) (JRefl (λ c r → ((p q : a ≡ b) → p ∙ r ≡ q ∙ r → p ≡ q)) λ p q id → (rUnit p) ∙ id ∙ sym (rUnit q))


-- rUnit p ∙ ((λ j → (p ∙ (rCancel r (~ j)))) ∙ assoc p r (sym r)) ∙ (cong (λ x → x ∙ (sym r)) id) ∙ sym (assoc q r (sym r)) ∙ (λ j → q ∙ (rCancel r j)) ∙ sym (rUnit q


switcher : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (p : a ≡ b) (q r : a ≡ c) → p ∙ (sym p) ≡ q ∙ (sym r) → r ≡ q
switcher {ℓ} {A} {a} {b} {c} = J {ℓ} {A} {a} (λ b p → ((q r : a ≡ c) → p ∙ (sym p) ≡ q ∙ (sym r) → r ≡ q))
                                 (J {ℓ} {A} {a} (λ c q → (r : a ≡ c) → refl ∙ (sym refl) ≡ q ∙ (sym r) → r ≡ q) λ r id → (lUnit r) ∙ cong (λ x → x ∙ r) ((rUnit (refl) ∙ id ∙ (sym (lUnit (sym r)))))  ∙ (lCancel r))
                                 -- ((λ j → (λ i → (lUnit (sym r) j) (~ i) ))) ∙ cong (λ x → sym x) (sym id) ∙ ((λ j → (λ i → (sym (rUnit (refl {x = a})) j) (~ i) ))))

switcherCancellerId : ∀ {ℓ} {A : Type ℓ} {a : A} (id : (refl {x = a}) ∙ refl ≡ refl ∙ refl) → canceller (refl {x = a}) refl refl id ≡ switcher refl refl refl id
switcherCancellerId id = (λ i → (cancellerRefl i) id) ∙ sym (finalReflPath id)  ∙ λ i → (switcherRefl (~ i)) id
  where
  cancellerRefl : ∀ {ℓ} {A : Type ℓ} {a : A} → canceller {a = a} {b = a} {c = a} refl refl refl ≡ λ id → rUnit refl ∙ id ∙ sym (rUnit refl)
  cancellerRefl {ℓ} {A} {a} = cong (λ x → x refl refl) (JRefl (λ c r → (p q : a ≡ a) → p ∙ r ≡ q ∙ r → p ≡ q) λ p q id → rUnit p ∙ id ∙ sym (rUnit q))

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


switcherCancellerIdGeneral : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p q : a ≡ b) → (p ≡ q) → (P : p ∙ (sym p) ≡ q ∙ (sym p)) → canceller (sym p) p q  P ≡ switcher p q p P
switcherCancellerIdGeneral {ℓ} {A} {a} {b} p q = J {ℓ} {a ≡ b} {p} (λ q _ → (P : p ∙ (sym p) ≡ q ∙ (sym p)) → canceller (sym p) p q  P ≡ switcher p q p P) (J {ℓ} {A} {a} (λ b p → (P : p ∙ (sym p) ≡ p ∙ (sym p)) → canceller (sym p) p p  P ≡ switcher p p p P) (λ P → switcherCancellerId P) p)


symTypeId : {a b : A} → (a ≡ b) ≡ (b ≡ a)
symTypeId {A = A} {a = a} {b = b} = isoToPath (iso sym sym (λ x → refl) λ x → refl)


Lemma296b2 : ∀{ℓ ℓ' ℓ''} {X : Type ℓ} {x y : X} {A : X → Type ℓ'} {B : X → Type ℓ''}
           (p : x ≡ y)
           (f : (A x) → (B x))
           (g : (A y) → (B y)) →
           (transport (λ i → (A (p i)) → (B (p i))) f ≡ g) ≡ ((a : A y) → transport (λ i → B (p (~ i) )) (g a) ≡ f (transport (λ i → A (p (~ i))) a))
Lemma296b2 {ℓ = ℓ} {X = X} {x = x} {y = y} {A = A} {B = B} = J {ℓ} {X} {x} (λ y p → (f : (A x) → (B x)) (g : (A y) → (B y)) →
                                                                     (transport (λ i → (A (p i)) → (B (p i))) f ≡ g) ≡
                                                                          ((a : A y) → transport (λ i → B (p (~ i))) (g a) ≡ f (transport (λ i → A (p (~ i))) a)))
                                                                          λ f g → (λ i → ((transportRefl f i) ≡ g) ) ∙ symTypeId ∙ isoToPath (iso funExt⁻  funExt (λ x → refl) λ x → refl) ∙ λ j → ((a : A x) → (transportRefl (g a) (~ j) ≡ f (transportRefl a  (~ j))))


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








