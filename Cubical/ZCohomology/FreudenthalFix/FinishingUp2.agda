{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.FreudenthalFix.FinishingUp2 where


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.FreudenthalFix.Prelim
open import Cubical.ZCohomology.FreudenthalFix.Code
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

{-
transpRCancel : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {a b : A} (p : a ≡ b) (x : B b) → subst B p (subst B (sym p) x) ≡ x 
transpRCancel {A = A} {B = B} {a} = J (λ b p → (x : B b) → subst B p (subst B (sym p) x) ≡ x  ) λ x → transportRefl ((subst B (λ i → refl (~ i)) x)) ∙ transportRefl x

 transpRCancelRefl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {a : A} (x : B a) → transpRCancel {B = B} refl x ≡ transportRefl ((subst B (λ i → refl (~ i)) x)) ∙ transportRefl x x) 
transpRCancelRefl {B = B} {a = a} x = cong (λ y → y x) (JRefl (λ a p → (x : B a) → subst B p (subst B (sym p) x) ≡ x  ) λ x → transportRefl ((subst B (λ i → refl (~ i)) x)) ∙ transportRefl  -}

transportJ : {!!}
transportJ = {!!}

transpRCancel : (p : A ≡ B) (b : B) → transport p (transport⁻ p b) ≡ b
transpRCancel {A = A} = J (λ B p → (b : B) → transport p (transport⁻ p b) ≡ b) λ b → transportRefl (transport refl b) ∙ transportRefl b

transpRCancelRefl : (a : A) → transpRCancel refl a ≡ transportRefl (transport refl a) ∙ transportRefl a
transpRCancelRefl {A = A} a = cong (λ x → x a) (JRefl (λ A p → (a : A) → transport p (transport⁻ p a) ≡ a) λ b → transportRefl (transport refl b) ∙ transportRefl b)


Lemma294 : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} {x1 x2 : X} (p : x1 ≡ x2) (f : A (x1) → B (x1)) → subst (λ x → (A x) → (B x)) p f ≡ λ x → subst B p (f (subst A (sym p) x) ) 
Lemma294 {A = A} {B = B} {x1 = x1} = J (λ x2 p → (f : A (x1) → B (x1)) → subst (λ x → (A x) → (B x)) p f ≡ λ x → subst B p (f (subst A (sym p) x) ) ) λ f → refl

happly : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} (f g : (x : A) → B x) → (f ≡ g) → ((x : A) → f x ≡ g x )
happly {A = A} {B = B} f g = J (λ (g : (x : A) → B x) p  → ((x : A) → f x ≡ g x )) (λ _ → refl) {g} 



pairLemma2 : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → transport (λ i → a ≡ p i) refl ≡ p
pairLemma2 {ℓ} {A} {a} = J (λ b p →  transport (λ i → a ≡ p i) refl ≡ p) (transportRefl refl)

pairLemma2Refl : ∀ {ℓ} {A : Type ℓ} {a : A} → pairLemma2 (refl {x = a}) ≡ (transportRefl refl)
pairLemma2Refl {ℓ} {A} {a} = JRefl (λ b p →  transport (λ i → a ≡ p i) refl ≡ p) (transportRefl refl)

pairLemma3 : ∀ {ℓ} {A : Type ℓ} {a1 b : A} (p : a1 ≡ b) (q : b ≡ a1) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q
pairLemma3 {a1 = a1} = J (λ b p → (q : b ≡ a1) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q) λ q → pairLemma2 q ∙ lUnit q

pairLemma3Refl : ∀ {ℓ} {A : Type ℓ} {a1 : A} (q : a1 ≡ a1) → pairLemma3 (λ _ → a1) q ≡ pairLemma2 q ∙ lUnit q
pairLemma3Refl {a1 = a1} q = cong (λ x → x q) (JRefl (λ b p → (q : b ≡ a1) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q) λ q → pairLemma2 q ∙ lUnit q)

pairLemma3ReflRefl : {a1 : A} → pairLemma3 (λ _ → a1) (λ _ → a1) ≡ (transportRefl refl) ∙ lUnit refl
pairLemma3ReflRefl = pairLemma3Refl refl ∙ λ i → pairLemma2Refl i ∙ lUnit refl

substComposite-∙ : ∀ {ℓ ℓ′} {A : Type ℓ} → (B : A → Type ℓ′)
                     → {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : B x)
                     → subst B (p ∙ q) u ≡ subst B q (subst B p u)
substComposite-∙ {A = A} B p q u = transport (λ i → subst B (□≡∙ p q i) u ≡ subst B q (subst B p u)) (substComposite-□ B p q u)

pair⁼ : ∀ {ℓ'} {B : A → Type ℓ'} {x y : Σ A (λ a → B a)} → (p : fst x ≡ fst y) → transport (λ i → B (p i)) (snd x) ≡ (snd y) → x ≡ y 
pair⁼ {B = B}{x = x1 , x2} {y = y1 , y2} p = J (λ y1 p → ((y2 : B y1) → (transport (λ i → B (p i)) x2 ≡ y2) → (x1 , x2) ≡ (y1 , y2))) (λ y2 p2 i → refl {x = x1} i , ((sym (transportRefl x2)) ∙ p2) i) p y2




abstract
  pair⁼'' : ∀ {ℓ'} {B : A → Type ℓ'} {x y : Σ A (λ a → B a)} → (p : fst x ≡ fst y) → transport (λ i → B (p i)) (snd x) ≡ (snd y) → x ≡ y 
  pair⁼'' {B = B}{x = x1 , x2} {y = y1 , y2} p = J (λ y1 p → ((y2 : B y1) → (transport (λ i → B (p i)) x2 ≡ y2) → (x1 , x2) ≡ (y1 , y2))) (λ y2 p2 i → refl {x = x1} i , ((sym (transportRefl x2)) ∙ p2) i) p y2

  pairId : ∀ {ℓ'} {B : A → Type ℓ'} {x y : Σ A (λ a → B a)} → (pair⁼'' {x = x} {y = y}) ≡ (pair⁼ {x = x} {y = y})
  pairId = refl

  functTransp2 : ∀ {ℓ ℓ'} {A : Type ℓ} {a1 b : A} {C : Σ A (λ b → a1 ≡ b) → Type ℓ' } (p : a1 ≡ b) (q : b ≡ a1) → transport (λ i → C (pair⁼'' (p ∙ q) (pairLemma2 (p ∙ q)) i) ) ≡ λ x → transport (λ i → C (pair⁼'' q ((pairLemma3 p q)) i)) (transport (λ i → C (pair⁼'' p (pairLemma2 p) i)) x)
  functTransp2 {ℓ} {ℓ'} {A = A} {a1 = a1} {b = b} {C = C} = J (λ b p → (q : b ≡ a1) → transport (λ i → C (pair⁼'' {B = λ a → a1 ≡ a} {x = (a1 , refl {x = a1})} (p ∙ q) (pairLemma2 (p ∙ q)) i) ) ≡ λ x → transport (λ i → C (pair⁼'' q ((pairLemma3 p q)) i)) (transport (λ i → C (pair⁼'' p (pairLemma2 p) i)) x))
                                λ q → (λ j → subst C (hej a1 q (~ j))) ∙ (λ j → subst C (pair⁼'' (λ _ → a1) (pairLemma2 (λ _ → a1)) ∙ pair⁼'' q (pairLemmaId q (~ j)))) ∙ funExt λ x → (substComposite-∙ C (pair⁼'' refl (pairLemma2 refl)) (pair⁼'' q (pairLemma3 refl q)) x)
           where
             pairLemmaId : (q : a1 ≡ a1) → (pairLemma3 (λ _ → a1) q) ≡ ((pairLemma2 q) ∙ lUnit q)
             pairLemmaId q = cong (λ f → f q) (JRefl (λ b p → (q : b ≡ a1) → transport (λ i₁ → a1 ≡ q i₁) p ≡ p ∙ q) λ q → pairLemma2 q ∙ lUnit q)

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
            

Lemma8610fun : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a2) → C a1 (subst B (sym p) b) → C a2 b
Lemma8610fun {ℓ} {ℓ'} {ℓ''} {A = A} {a1 = a1 } {a2 = a2} {B = B} C p b  = transport (λ i → idHelper i ) 
  where
  idHelper : C a1 (subst B (sym p) b) ≡ C a2 b
  idHelper = (sym (cong (λ x → x b) (Lemma294 {A = B} {B = λ _ → Type ℓ''} p (C a1)))) ∙ happly (subst (λ x → B x → Type ℓ'') p (C a1)) (C a2) (fromPathP λ j → C (p j)) b

Lemma8610 : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a2)  → transport ((λ i → uncurry C (pair⁼ p (transportTransport⁻ (λ i → B (p i)) b) i) )) ≡ Lemma8610fun C p b  
Lemma8610 {ℓ} {ℓ'} {ℓ''} {A = A} {a1 = a1} {B = B} C = J (λ a2 p → (b : B a2)  → transport ((λ i → uncurry C (pair⁼ p (transportTransport⁻ (λ i → B (p i)) b) i) )) ≡ Lemma8610fun C p b ) λ b → funExt λ x → {!!} ∙ sym (cong (λ f → f x) (helper b))
  where
  helper : (b : B a1) → Lemma8610fun C refl b ≡ λ x → transport (λ i → C a1 (transportRefl b i)) x 
  helper b = {!!}

Lemma8610'' : ∀{ℓ ℓ''} {A : Type ℓ} {a1 a2 : A} (C : (a : A) → (a1 ≡ a → Type ℓ'')) (p b : a1 ≡ a2)  → transport ((λ i → uncurry C (pair⁼'' p (transportTransport⁻ (λ i → a1 ≡ (p i)) b ) i) )) ≡ transport (λ i → ((sym (cong (λ x → x b) (Lemma294 {A = (λ a → a1 ≡ a)} {B = λ _ → Type ℓ''} p (C a1)))) ∙ funExt⁻ (fromPathP λ j → C (p j)) b) i)
Lemma8610'' = {!Lemma294!}


c : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (y : (Susp A)) (p : north ≡ y) → code {a = a} n iscon y p
c n a iscon y p = transport (λ i → (uncurry (code {a = a} n iscon) (pair⁼ p (pairLemma2 p) i))) ∣ a , (rCancel (merid a)) ∣

c'' : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (y : (Susp A)) (p : north ≡ y) → code {a = a} n iscon y p
c'' n a iscon y p = transport (λ i → (uncurry (code {a = a} n iscon) (pair⁼'' p (pairLemma2 p) i))) ∣ a , (rCancel (merid a)) ∣

cId : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) (y : (Susp A)) (p : north ≡ y) → c n a iscon y p ≡ c'' n a iscon y p
cId n a iscon y p i = transport (λ j → (uncurry (code {a = a} n iscon) ((pairId (~ i)) p (pairLemma2 p) j))) ∣ a , (rCancel (merid a)) ∣

reflCase  : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → c n a iscon north (σ x1) ≡ ∣ x1 , refl ∣
reflCase {A = A} n a x1 iscon = c n a iscon north (σ x1) ≡⟨ cId n a iscon north (σ x1) ⟩
                        c'' n a iscon north (σ x1) ≡⟨ cong (λ x → x ∣ a , (rCancel (merid a)) ∣) (functTransp2 {C = (uncurry (code {a = a} n iscon))} (merid x1) (sym (merid a))) ⟩
                        transport (λ i → uncurry (code n iscon) (pair⁼'' {B = λ x → north ≡ x} (λ i₁ → merid a (~ i₁)) (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i)) (transport (λ i → uncurry (code n iscon) (pair⁼'' (merid x1) (pairLemma2 (merid x1)) i)) ∣ a , rCancel (merid a) ∣)
                        ≡⟨ (λ j → transport (λ i → uncurry (codeId {a = a} n iscon j) (pair⁼'' {B = λ x → north ≡ x} (λ i₁ → merid a (~ i₁)) (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i)) (transport (λ i → uncurry (codeId {a = a} n iscon j) (pair⁼'' (merid x1) (pairLemma2 (merid x1)) i)) ∣ a , rCancel (merid a) ∣)) ⟩
                        transport (λ i → uncurry (code' n iscon) (pair⁼'' {B = λ x → north ≡ x} (λ i₁ → merid a (~ i₁)) (pairLemma3 (merid x1) (λ i₁ → merid a (~ i₁))) i)) (transport (λ i → uncurry (code' {a = a} n iscon) (pair⁼'' (merid x1) (pairLemma2 (merid x1)) i)) ∣ a , rCancel (merid a) ∣)
                        ≡⟨ {!!} ⟩ {!!} ≡⟨ {!(pair⁼'' (merid x1) (pairLemma2 (merid x1)))!} ⟩ {!(pairLemma2 (merid x1))!}

{- transport (λ i → uncurry (code {a = a} n iscon) (pair⁼'' {B = λ x → north ≡ x} {x = south , merid x1} {y = north , _} (λ i₁ → merid a (~ i₁)) (pairLemma3 {a1 = north} {b = south} (merid x1) (λ i₁ → merid a (~ i₁))) i)) (transport (λ i → uncurry (code {a = a} n iscon) (pair⁼ {B = λ x → north ≡ x} {x = north , refl} {y = south , _} (merid x1) (pairLemma2 (merid x1)) i)) ∣ a , rCancel (merid a) ∣) -}

  where
  wowie : (transport (λ i → uncurry (code' {a = a} n iscon) (pair⁼'' (merid x1) (transpRCancel (λ i₁ → north ≡ merid x1 i₁) (merid x1)) i))) ∣ a , rCancel (merid a) ∙ sym (rCancel (merid x1)) ∙ sym (pairLemma3 (merid x1) (sym (merid x1))) ∣ ≡ transport (λ i → (uncurry (codeId {a = a} n iscon i1) (pair⁼'' (merid x1) (pairLemma2 (merid x1)) i))) ∣ a , rCancel (merid a) ∣
  wowie = {!!}
  wowie2 : (y : Susp A) → (p : north ≡ y) → (transport (λ i → uncurry (code' {a = a} n iscon) (pair⁼'' p (transpRCancel (λ i₁ → north ≡ p i₁) p) i))) ∣ a , rCancel (merid a) ∙ sym (rCancel p) ∙ sym (pairLemma3 p (sym p)) ∣ ≡ transport (λ i → (uncurry (code' {a = a} n iscon) (pair⁼'' p (pairLemma2 p) i))) ∣ a , rCancel (merid a) ∣
  wowie2 y = J (λ y p → (transport (λ i → uncurry (code' {a = a} n iscon) (pair⁼'' p (transpRCancel (λ i₁ → north ≡ p i₁) p) i))) ∣ a , rCancel (merid a) ∙ sym (rCancel p) ∙ sym (pairLemma3 p (sym p)) ∣ ≡ transport (λ i → (uncurry (code' {a = a} n iscon) (pair⁼'' p (pairLemma2 p) i))) ∣ a , rCancel (merid a) ∣)
                 ((transport (λ i → uncurry (code' n iscon) (pair⁼'' refl (transpRCancel (λ i₁ → north ≡ refl i₁) refl) i))) ∣ a , rCancel (merid a) ∙ (sym (rCancel refl)) ∙ (sym (pairLemma3 refl refl)) ∣ ≡⟨ (λ j → transport (λ i → uncurry (code' n iscon) (pair⁼'' refl (transpRCancelRefl refl j) i)) ∣ a , rCancel (merid a) ∙ (sym (rCancel refl)) ∙ (pairLemma3ReflRefl j) ∣) ⟩ {!!})

  helper : (transport (λ i → uncurry (code' {a = a} n iscon) (pair⁼'' {B = λ x → north ≡ x} {x = north , refl} {y = south , _} (merid x1) (pairLemma2 (merid x1)) i)) ∣ a , rCancel (merid a) ∣) ≡ ∣ x1 , {!!} ∣
  helper = (transport (λ i → uncurry (code' {a = a} n iscon) (pair⁼'' {B = λ x → north ≡ x} {x = north , refl} {y = south , _} (merid x1) (pairLemma2 (merid x1)) i)) ∣ a , rCancel (merid a) ∣) ≡⟨ {!cong (λ x → x ∣ a , rCancel (merid a) ∣) (Lemma8610'' (code n iscon) (merid x1) (merid x1)) !} ⟩  {!!}
  
  help2 : transport (λ i → uncurry ((code {a = a} n iscon)) (pair⁼'' {B = λ x → north ≡ x} {x = north , refl} {y = south , merid x1} (merid x1) ({!transpRCancel -- (λ i₁ → north ≡ merid x1 i₁) ∣ a , rCancel (merid a) ∣!}) i)) ≡ (transport (λ i → uncurry (code {a = a} n iscon) (pair⁼'' {B = λ x → north ≡ x} {x = north , refl} {y = south , _} (merid x1) (pairLemma2 (merid x1)) i)))
  help2 = {!!}
{-
  testComp : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → PathP (λ i → {!(transpRCancel (λ i₁ → a ≡ p i₁) p) !} ≡ {!(transpRCancel (λ i₁ → a ≡ p i₁) p)!}) (pairLemma2 p) (transpRCancel (λ i₁ → a ≡ p i₁) p)
  testComp {a = a}= J (λ b p → PathP {!!} (pairLemma2 p) (transpRCancel (λ i₁ → a ≡ p i₁) p)) (transport (λ i → PathP {!!} (pairLemma3Refl refl (~ i)) (transpRCancelRefl refl (~ i)) ) {!!})
     -}
{-

reflCase  : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → transport (λ i → (uncurry (code {a = a} n iscon) (pair⁼ (σ x1 {a}) (pairLemma2 (σ x1)) i))) ∣ a , (rCancel (merid a)) ∣ ≡ ∣ x1 , refl ∣
reflCase n a x1 iscon =   transport (λ i → (uncurry (code {a = a} n iscon)) (pair⁼ (σ x1 {a}) (pairLemma2 (σ x1)) i)) ∣ a , (rCancel (merid a)) ∣
                          ≡⟨ cong (λ x → x ∣ a , (rCancel (merid a)) ∣ ) (functTransp {C = (uncurry (code {a = a} n iscon))} (merid x1) (sym (merid a))) ⟩
                          {!!}
-}

{-
module test (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) where
  pairLemma2 : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → transport (λ i → a ≡ p i) refl ≡ p
  pairLemma2 {ℓ} {A} {a} = J (λ b p →  transport (λ i → a ≡ p i) refl ≡ p) (transportRefl refl)

  c : (y : (Susp A)) (p : north ≡ y) → code {a = a} n iscon y p
  c y p = transport (λ i → (uncurry (code {a = a} n iscon) (pair⁼ p (pairLemma2 p) i))) ∣ a , (rCancel (merid a)) ∣

  reflCase2 : (x1 : A) → c north (σ x1) ≡ ∣ x1 , refl ∣
  reflCase2 x1 = {!!} ≡⟨ {!!} ⟩ {!!}

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
-}

Thm864 : (n : ℕ) (a : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) {y : Susp A} → (p : north ≡ y) → isContr (code {a = a} n iscon y p)
Thm864 {ℓ} {A} n a iscon =  J {ℓ} {Susp A} {north} (λ y p → (isContr (code {a = a} n iscon y p))) (∣ a , (rCancel _) ∣ , (λ y → {!!}))  where
  
{-
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
  -}

Freudenthal : (n : ℕ) (A : Pointed ℓ) → is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A) → ∥ typ A ∥ (ℕ→ℕ₋₂ (n + n)) ≡ ∥ typ (Ω (Susp (typ A) , north)) ∥ ((ℕ→ℕ₋₂ (n + n)))
Freudenthal n A isCon = ua ({!!} , {!Lemma757i→ii ? ? ? ?!})
