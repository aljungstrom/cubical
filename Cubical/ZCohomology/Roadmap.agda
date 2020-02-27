{-# OPTIONS --cubical #-}
module Cubical.ZCohomology.Roadmap where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Prelude renaming (funExt to λ≃ ; cong to ap)
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
open import Cubical.Data.Int
open import Cubical.Data.Nat
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

data WrapPath (A : Type ℓ) (outs : A) (ins : A) : Type ℓ where
       wrap : (wrapper : outs ≡ ins) (middle : ins ≡ ins) → WrapPath A outs ins

unwrap : {outs ins : A} → WrapPath A outs ins → outs ≡ outs
unwrap (wrap wrapper middle) = wrapper ∙ middle ∙ sym wrapper

inside : {outs ins : A} → WrapPath A outs ins → ins ≡ ins
inside (wrap _ middle) = middle

adjust : {outs ins : A} → (outs ≡ ins → ins ≡ ins → outs ≡ outs)
adjust w m = unwrap (wrap w m)

cancelReflMid : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) (q : b ≡ a) → p ∙ refl ∙ q ≡ p ∙ q
cancelReflMid {ℓ = ℓ}{A = A} {a = a} {b = b} p q = J {ℓ} {A} {a} {ℓ} (λ b p → ((q : b ≡ a) →  p ∙ refl ∙ q ≡ p ∙ q)) (λ r → sym (lUnit (refl  ∙ r ))) {b} p q

ap-o : ∀ {ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}  (g : B → C) (f : A → B)
            {M N : A} (α : N ≡ M) → ap (λ x → g (f x)) α ≡ ap g (ap f α)
ap-o {ℓ} {ℓ'} {ℓ''} {A} {B} {C} g f {M} {N}  = J {ℓ} {A} {N} {ℓ''} (λ x p → ap (λ x → g (f x)) p ≡ ap g (ap f p)) refl {M}

ap≃ : {B : A → Type ℓ'} {f g : (x : A) → B x} 
        → f ≡ g → {x : A} →  (g x) ≡ (f x)
ap≃ α {x} = sym (ap (\ f → f x) α)

abstract
  adj : {outs ins : A} → (outs ≡ ins → ins ≡ ins → outs ≡ outs)
  adj w m = unwrap (wrap w m)

  adj-def : {outs ins : A} → (w : outs ≡ ins) → (m : ins ≡ ins) → adj w m ≡ adjust w m
  adj-def w m = refl

  adj-∙ : {A : Type ℓ} {outs mids ins : A} → (w : outs ≡ mids) (w' : mids ≡ ins) (m : ins ≡ ins) → adj w (adj w' m) ≡ adj (w ∙ w') m
  adj-∙  {ℓ} {A} {outs} {mids} {ins} = J {ℓ} {A} {outs} {ℓ}
                                         (λ x w → ((w' : x ≡ ins) (m : ins ≡ ins) → adj w (adj w' m) ≡ adj (w ∙ w') m))
                                         (J {ℓ} {A} {outs} {ℓ} (λ x w' → (m : x ≡ x) → adj refl (adj w' m) ≡ adj (refl ∙ w') m )
                                            λ m →  (sym (lUnit ((adj refl m) ∙ refl))) ∙ sym (rUnit (adj (λ _ → outs) m)) ∙ λ i → adj (rUnit (refl) i ) m )
                                            
  ignore-wrappers : {a : A} {ins out : a ≡ a} 
          → (w w' : WrapPath (a ≡ a) out ins)
          → inside w ≡ inside w'  
          → unwrap w ≡ unwrap w'
  ignore-wrappers {A} {a} (wrap w1 m1) (wrap w2 m2) α =
                   w1 ∙ m1 ∙ (sym w1) ≡⟨ ap (λ x → w1 ∙ x ∙ (sym w1)) α  ⟩
                   w1 ∙ m2 ∙ (sym w1) ≡⟨ {!!} ⟩
                   w2 ∙ m2 ∙ (sym w2) ∎
  
  adj-eq : {a : A} {ins outs : a ≡ a} 
          → (wrapper : outs ≡ ins) (middle : ins ≡ ins)
          → (wrapper' : outs ≡ ins) (middle' : ins ≡ ins)
          → middle ≡ middle'
          → adj wrapper middle ≡ adj wrapper' middle'
  adj-eq wrapper middle wrapper' middle' α = ignore-wrappers (wrap wrapper middle) (wrap wrapper' middle') α 
  
  adj-bind : {outs mid ins : A} {w : outs ≡ mid} {w' : mid ≡ ins } {m : ins ≡ ins} {α : _}
            → α ≡ (adj w' m)
            → adj w α ≡ adj (w ∙ w') m
  adj-bind β = ap (adj _) β ∙ (adj-∙ _ _ _)

  adj-id : {a : A} (α : a ≡ a) → α ≡ adj refl α
  adj-id α = (lUnit α) ∙ rUnit (refl ∙ α) ∙ sym (assoc refl α refl)

  adj-id2 : {a : A} (α : a ≡ a) → α ≡ adj (sym refl) α
  adj-id2 α = (rUnit α) ∙ lUnit (α ∙ refl)
  {-
  adj-by-inv : {A : Type ℓ} {a b : A} {q : a ≡ a} {p : b ≡ a} → adj p q ≡ adj p (sym q)
  adj-by-inv {ℓ} {A} {a} {b} {q} {p} = {!!}
  -}

  ap-adj : {A : Type ℓ} {B : Type ℓ'} {a a1 : A} → (f : A → B) (α : a ≡ a) (q : a1 ≡ a ) → (ap f (adj q α)) ≡ adj (ap f q) (ap f α)
  ap-adj {ℓ = ℓ} {ℓ' = ℓ'} {A} {B} {a} {a1} f α q = ((J {ℓ} {A} {a} {ℓ'} (λ y p → (ap f (adj (sym p) α)) ≡ adj (ap f (sym p)) (ap f α)) (((sym (ap (ap f) (adj-id2 α))) ∙ adj-id (λ i → f (α i))) ∙ adj-def refl (ap f α))) (sym q))

  ap-by-equals : {A : Type ℓ} {B : Type ℓ'} {f g : A → B}
                (α : (x : _) → f x ≡ g x) 
              → {M N : A} (β : N ≡ M)
              → (ap f β ≡ (α N) ∙ ap g β ∙ sym (α M) )
  ap-by-equals {ℓ} {ℓ'} {A} {B} {f} {g} α {M} {N} = J {ℓ} {A} {N} {ℓ'} (λ x p → (ap f p ≡ (α N) ∙ ap g p ∙ sym (α x) )) (sym (cancelReflMid (α N) (λ i → α N (~ i)) ∙ rCancel (α N)))

  ap-loop-by-equals  : {A : Type ℓ} {B : Type ℓ'} {f g : A → B}
                        (α : (x : _) → f x ≡ g x) 
                      → {M : A} (β : M ≡ M)
                      → (ap f β ≡ adj (α M) (ap g β))
  ap-loop-by-equals {f = f} {g = g} α {M = M} β = ((ap-by-equals α β) ∙ assoc (α M) (cong (λ z → g z) β) (sym (α M)) ∙ (sym (assoc (α _) (ap g β) (sym (α _)))))

  adj-eq-loop : {a : A} (n : ℕ) {ins outs : typ ((Ω^ (suc n)) (A , a))} 
          → (wrapper : outs ≡ ins) (middle : ins ≡ ins)
          → (wrapper' : outs ≡ ins) (middle' : ins ≡ ins)
          → middle ≡ middle'  
          → adj wrapper middle ≡ adj wrapper' middle'
  adj-eq-loop zero w m w' m' α = adj-eq w m w' m' α
  adj-eq-loop (suc n) w m w' m' α = adj-eq w m w' m' α

  adj-ap≃ : {B : A → Type ℓ'} {x : A} {f g : (x : A) → B x}
              (α : f ≡ f) (q : f ≡ g)
            → adj (ap≃ q{x}) (ap≃ α {x}) ≡ ap≃ (adj (sym q) α) {x}
  adj-ap≃ {x = x} α id = {!!}

  adj-ap≃-pointwise : {B : A → Type ℓ'} {x : A} {f g : (x : A) → B x}
              (α : f ≡ f) (q : (x : A) → (g x) ≡ (f x))
            → adj (q x) (ap≃ α {x}) ≡ ap≃ (adj (λ≃ q) α) {x}
  adj-ap≃-pointwise {x = x} α q = adj-ap≃ α (sym (λ≃ q)) -- adj-ap≃ α (λ≃ q) ∘ ap (λ y → adj y (ap≃ α)) (! (Π≃β q)

  wrapInv : {A : Type ℓ} {a b : A} (p : a ≡ a) (q : b ≡ a) → (adj q p) ≡ sym (adj q (sym p))
  wrapInv {ℓ = ℓ} {A = A} {a} {b} p q = Jright {ℓ} {A} {a} (λ x r → (adj r p) ≡ sym (adj r (sym p))) ((sym (lUnit (p ∙ refl))) ∙ sym ((rUnit) p) ∙ sym ((λ k i → ((sym (lUnit ((sym p) ∙ refl))) k ) (~ i)) ∙ (λ k i → ((sym (rUnit (sym p))) k) (~ i)) ∙ sym (symInvo p))) q






ap-id : {M N : A} (α : M ≡ N)
        → (ap (λ x → x) α) ≡ α
ap-id j = refl  

ap^ : (n : ℕ) (f : A → B) → {base : A} → typ ((Ω^ (suc n)) (A , base)) → typ ((Ω^ (suc n)) (B , f base))
ap^-id : (n : ℕ) (f : A → B) {base : A} → pt ((Ω^ (suc n)) (B , f base)) ≡ ap^ n f (pt ((Ω^ (suc n)) (A , base)))

ap^ zero f x = ap f x
ap^ (suc n) f x = adjust (ap^-id n f) (ap (ap^ n f) x)

ap^-id zero f = refl
ap^-id (suc n) f = sym (cancelReflMid (ap^-id n f) (sym (ap^-id n f)) ∙  (rCancel (ap^-id n f)))

λl : (n : ℕ) {f : A → B} → ((x : A) → typ ((Ω^ (suc n)) (B , (f x)))) → (typ ((Ω^ (suc n)) ((A → B) , f)))
λl-id : (n : ℕ) {f : A → B} → refl ≡ λl n {f} (λ x → refl)

λl zero {f} a = λ≃ a
λl (suc n) {f} a = adjust (λl-id n) (ap (λl n) (λ≃ a))

λl-id zero {f} = refl
λl-id (suc n) {f} = sym (cancelReflMid (λl-id n) (sym ((λl-id n))) ∙ rCancel (λl-id n))

apl : (n : ℕ) {f : A → B} → (typ ((Ω^ (suc n)) ((A → B) , f))) → ((x : A) → typ ((Ω^ (suc n)) (B , (f x))))
apl n {f} a x = ap^ n (λ f → f x) a

β : (n : ℕ) {f : A → B} (a : ((x : A) → typ ((Ω^ (suc n)) (B , (f x))))) →
    apl n (λl n a) ≡ a
β zero a = refl
β (suc n) {f} a  = λ≃ λ x → adjust (ap^-id n (λ f → f x)) (ap (λ f → apl n f x) (adjust (λl-id n) (ap (λl n) (λ≃ a))))
                                           ≡⟨ ap (λ y → adjust (ap^-id n (λ f' → f' x) {f}) (ap (ap^ n (λ f' → f' x)) y)) (sym (adj-def (λl-id n) _)) ⟩
                      adjust (ap^-id n (λ f → f x){f}) (ap (λ f → apl n f x) (adj _ (ap (λl n) (λ≃ a)))) ≡⟨ sym (adj-def (ap^-id n (λ f → f x)) _)⟩
                      adj _ (ap (λ f → apl n f x) (adj _ (ap (λl n) (λ≃ a)))) ≡⟨ adj-bind (ap-adj (λ f' → apl n f' x) _ _) ⟩
                      adj _ (ap (λ f → apl n f x) (ap (λl n) (λ≃ a))) ≡⟨ ap (adj _) (sym (ap-o (\ f -> apl n f x) (λl n) _)) ⟩
                      adj _ (ap (λ f → apl n (λl n f) x) (λ≃ a)) ≡⟨ adj-bind (ap-loop-by-equals {f = λ f → apl n (λl n f) x} {g = λ f → f x} (λ f → ap≃ (sym (β n f))) _)  ⟩
                      adj _ (ap (λ f → f x) (λ≃ a)) ≡⟨ ap (adj _) (refl)  ⟩
                      adj _ (a x) ≡⟨ adj-eq-loop n _ _ _ _ refl ⟩
                      adj refl (a x) ≡⟨ sym (adj-id _) ⟩
                      a x ∎

Π≃η : {A : Type ℓ} {B : A -> Type ℓ'} {f g : (x : A) -> B x} 
         → (α : f ≡ g)
         → sym α ≡ λ≃ (λ x → (ap≃ (α)) {x})
Π≃η {ℓ = ℓ} {ℓ' = ℓ'} {A = A} {B = B} {f} {g} = J {ℓ-max ℓ ℓ'} {(x : A) -> B x} {f} (λ x p → sym p ≡ λ≃ (λ x → (ap≃ p) {x})) refl 

η : (n : ℕ) {f : A → B} (a : _) → (λl n  {f} (apl n a)) ≡ a
η zero {f} a = refl
η {A = A} (suc n)  {f = f}  a =
                adjust (λl-id n) (ap (λl n) (λ≃ (λ x → adjust (ap^-id n (\ f -> f x){f}) (ap (λ f → apl n f x) a)))) ≡⟨ ap (λ α → adjust (λl-id n) (ap (λl n) (λ≃ α))) (λ≃ (λ α → sym (adj-def _ _))) ⟩
                adjust (λl-id n) (ap (λl n) (λ≃ (λ x → adj (ap^-id n (\ f -> f x){f}) (ap (λ f → apl n f x) a)))) ≡⟨ sym (adj-def _ _) ⟩
                adj (λl-id n) (ap (λl n) (λ≃ (λ x → adj _ (ap (λ f → apl n f x) a)))) ≡⟨ refl ⟩
                adj _ (ap (λl n) (λ≃ (λ x → adj _ (ap (λ f → apl n f x) a)))) ≡⟨ refl ⟩ 
                adj _ (ap (λl n) (λ≃ (λ x → adj _ (ap ((λ f → f x) ∘ (apl n)) a)))) ≡⟨  ap (adj _) (ap (λ y → ap (λl n) (λ≃ y)) (λ≃ (\ x -> ap (adj _) (ap-o (λ a' → a' x) (apl n) a))))  ⟩ 
                adj _ (ap (λl n) (λ≃ (λ x → adj _ (ap≃ (ap (apl n) (sym a))))))     ≡⟨  ap (adj _) (ap (λ α → ap (λl n) (λ≃ α)) (λ≃ (λ x → adj-ap≃-pointwise {x = x} (ap (apl n) (sym a)) (λ x → ap^-id n (\f -> f x) {f}))))  ⟩
                adj _ (ap (λl n) (λ≃ (λ x → ap≃ (adj _ (ap (apl n) (sym a))) {x}))) ≡⟨ ap (adj (λl-id n) ∘ ap (λl n)) (sym (wrapInv _ _ ∙ (Π≃η (λ i →
         adj (λ≃ (λ x₁ → ap^-id n (λ f₁ → f₁ x₁))) (λ i₁ → apl n (a (~ i₁))) i))) ) ⟩
                adj _ (ap (λl n) (adj (λ≃ (λ x₁ → ap^-id n (λ f₁ → f₁ x₁))) (ap (apl n) (a)))) ≡⟨  adj-bind (ap-adj (λl n) _ _)  ⟩
                adj _ (ap (λl n) (ap (apl n) a)) ≡⟨ ap (adj _) (sym (ap-o (λl n) (apl n) a)) ⟩
                adj _ (ap ((λl n) ∘ (apl n)) a) ≡⟨  adj-bind (ap-loop-by-equals {f = (λl n) ∘ (apl n)} {g = λ x → x} (λ x →  (η n x)) a)  ⟩
                adj _ (ap (λ x → x) a) ≡⟨ ap (adj _) (ap-id a) ⟩
                adj _ a ≡⟨ adj-eq-loop n _ _ _ _ refl ⟩
                adj refl a ≡⟨ sym (adj-id _) ⟩
                a ∎ where
                  

FunLoopSpace : (n : ℕ) {f : A → B} → (typ ((Ω^ (n)) ((A → B) , f))) ≡ ((x : A) → typ ((Ω^ (n)) (B , (f x))))
FunLoopSpace zero = refl
FunLoopSpace (suc n) = isoToPath (iso (apl n ) (λl n) (β n) (η n))




-- ≡⟨ ⟩




{-

funLr : (n : ℕ) {f : A → B} → (typ ((Ω^ (suc n)) ((A → B) , f))) → ((x : A) → typ ((Ω^ (suc n)) (B , (f x))))
LrId : (n : ℕ) {f : A → B} → funLr n {f} refl ≡ λ x → refl
funLr zero = funExt⁻
funLr (suc n) {f = f} p x = adjust (cong (λ y → y x) (sym (LrId n {f}))) (((funExt⁻ (cong (λ x → funLr n x) p) x)))
LrId zero = refl
LrId (suc n) {f} =  funExt λ x → (cancelReflMid ((λ i → LrId n (~ i) x) ) (λ i → LrId n {f} i x)) ∙ rCancel (λ i → LrId n (~ i) x)

funRl : (n : ℕ) {f : A → B} → ((x : A) → typ ((Ω^ (suc n)) (B , (f x)))) → (typ ((Ω^ (suc n)) ((A → B) , f)))
RlId : (n : ℕ) {f : A → B} → funRl n {f} (λ x → refl) ≡ refl
funRl zero = funExt
funRl (suc n) p = adjust (sym (RlId n)) (cong (funRl n) (funExt p))
RlId zero = refl
RlId (suc n) = cancelReflMid (λ i → RlId n  (~ i)) (RlId n) ∙ rCancel (λ i → RlId n (~ i))  

-}

-------------------


φ : (a : A) → A → (north {A = A} ≡ north {A = A})
φ x = (λ a → ((merid  a) ∙ sym ((merid x))))

φ* : (A : Pointed ℓ) → A →* Ω ((Susp (typ A)) , north)
φ* A = (φ (pt A)) , rCancel (merid (pt A))

σ : (n : ℕ) → (typ (coHomK-ptd n)) → (typ (Ω (coHomK-ptd (suc n))))
σ zero k = looper k  ( cong {B = λ _ → (∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1)}
                     (λ x → ∣ x ∣)
                     ((merid north) ∙ (sym (merid south))) ) where
                     
  looper : ∀ {ℓ} → {A : Type ℓ} → {a : A} → (n : Int) → (a ≡ a) → (a ≡ a) -- defining loopⁿ
  looper {A = A} {a = a} (pos zero) p = refl
  looper {A = A} {a = a} (pos (suc n)) p = (looper (pos n) p) ∙ p
  looper {A = A} {a = a} (negsuc zero) p = sym p
  looper {A = A} {a = a} (negsuc (suc n)) p = (sym p) ∙ (looper (negsuc n) p)
  
σ (suc n) x = rec {B = typ (Ω ((∥ S₊ (suc (suc n)) ∥ ℕ→ℕ₋₂ (suc (suc n))) , ∣ north ∣))}
              (test n isOfHLeveln+3)
              (λ y → cong
                     {B = λ _ → Null (S (Cubical.Data.NatMinusTwo.Base.1+ ℕ→ℕ₋₂ (suc (suc n)))) (S₊ (suc (suc n)))}
                     (λ z → ∣ z ∣)
                     (φ north y))
              x
              where

              {- The following trivial but technical lemmas are needed to circumvent computational problems with the
                 transitions between ℕ, ℕ₋₁ and ℕ₋₂, causing problems in using isOfHLevel∥∥ to show that ΩKₙ₊₁ is 
                 n-truncated -}

              test : (m : ℕ) →
                     isOfHLevel (suc (suc (suc m)))
                                (fst (Ω ((∥ S₊ (suc (suc n)) ∥ ℕ→ℕ₋₂ (suc (suc n))) , ∣ north ∣))) →
                     isOfHLevel (suc (suc (Cubical.Data.NatMinusOne.Base.1+
                                          (Cubical.Data.NatMinusTwo.Base.1+
                                            (Cubical.Data.NatMinusTwo.Base.-1+
                                              (Cubical.Data.NatMinusOne.Base.-1+ (suc m)))))))
                                                (fst (Ω ((∥ S₊ (suc (suc n)) ∥ ℕ→ℕ₋₂ (suc (suc n))) , ∣ north ∣)))
              test m K = transp (λ i → isOfHLevel (testhelp m i)
                                ((fst (Ω ((∥ S₊ (suc (suc n)) ∥ ℕ→ℕ₋₂ (suc (suc n))) , ∣ north ∣)))))
                                i0
                                K
                                where

                                testhelp : (k : ℕ) → _≡_ {A = ℕ}
                                                         (suc (suc (suc k)))
                                                         ((suc (suc (Cubical.Data.NatMinusOne.Base.1+
                                                                    (Cubical.Data.NatMinusTwo.Base.1+
                                                                      (Cubical.Data.NatMinusTwo.Base.-1+
                                                                        (Cubical.Data.NatMinusOne.Base.-1+
                                                                          (suc k)))))))) 
                                testhelp zero = refl
                                testhelp (suc k) = cong (λ x → (suc x)) (testhelp k)

              isOfHLeveln+3 : isOfHLevel (suc (suc (suc n)))
                                         (fst (Ω ((∥ S₊ (suc (suc n)) ∥ ℕ→ℕ₋₂ (suc (suc n))) , ∣ north ∣)))
              isOfHLeveln+3 x y =  (another (isOfHLevel∥∥ (ℕ→ℕ₋₂ (suc (suc n))))) ∣ north ∣ ∣ north ∣ x y
                where
         
                another : (isOfHLevel (suc (suc (suc (Cubical.Data.NatMinusOne.Base.1+
                                                     (Cubical.Data.NatMinusTwo.Base.1+
                                                       (Cubical.Data.NatMinusTwo.Base.-1+
                                                         (Cubical.Data.NatMinusOne.Base.-1+
                                                           (suc n))))))))
                                      (∥ S₊ (suc (suc n)) ∥ ℕ→ℕ₋₂ (suc (suc n)))) →
                           isOfHLevel (suc (suc (suc (suc n)))) (∥ S₊ (suc (suc n)) ∥ ℕ→ℕ₋₂ (suc (suc n))) 
                another K = transp (λ i → isOfHLevel ((helper100 n) i)
                                   ((∥ S₊ (suc (suc n)) ∥ ℕ→ℕ₋₂ (suc (suc n)))))
                                   i0
                                   K
                                   where
                            
                                   helper100 : (m : ℕ) →  _≡_ {A = ℕ}
                                                              (suc (suc (suc (Cubical.Data.NatMinusOne.Base.1+
                                                                             (Cubical.Data.NatMinusTwo.Base.1+
                                                                               (Cubical.Data.NatMinusTwo.Base.-1+
                                                                                 (Cubical.Data.NatMinusOne.Base.-1+
                                                                                   (suc m))))))))
                                                              (suc (suc (suc (suc m))))
                                   helper100 zero = refl
                                   helper100 (suc m) = cong (λ x → (suc x)) (helper100 m)


postulate
 Kn≡ΩKn+1 : (n : ℕ) → coHomK n ≡ typ (Ω (coHomK-ptd (suc n)))

0* : {n : ℕ} → coHomK n
0* {zero} = pt (coHomK-ptd zero)
0* {suc n} = pt (coHomK-ptd (suc n))

postulate
    _+̂'_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
    -̂' : {n : ℕ} → coHomK n → coHomK n
    +̂'rUnit : {n : ℕ} (x : coHomK n) → x +̂' 0* ≡ x
    +̂'lUnit : {n : ℕ} (x : coHomK n) → 0* +̂' x ≡ x
    +̂'rinv : {n : ℕ} (x : coHomK n) → x +̂' (-̂' x) ≡ 0*
    +̂'linv : {n : ℕ} (x : coHomK n) → (-̂' x) +̂' x ≡ 0*
    +̂'assoc : {n : ℕ} (x y z : coHomK n) → (x +̂' y) +̂' z ≡ x +̂' (y +̂' z)
    +̂'comm : {n : ℕ} (x y : coHomK n) → x +̂' y ≡ y +̂' x

_+̂_ : {n : ℕ} → coHom n A  → coHom n A → coHom n A
_+̂_ {A = A} {n = n}  = elimSetTrunc2 {B = λ _ _ → coHom n A}
                                     (λ _ _ → setTruncIsSet )
                                     λ a b → ∣ (λ x → (a x) +̂' (b x)) ∣₀

-̂_ : {n : ℕ} → coHom n A  → coHom n A
-̂_ {A = A} {n = n} = elimSetTrunc {B = λ _ → coHom n A} (λ _ → setTruncIsSet) λ a → ∣ (λ x → -̂' (a x)) ∣₀ 

0̂ : {n : ℕ} → coHom n A
0̂ {n = n} = ∣ (λ _ → 0*) ∣₀

0̂R : {A : Pointed ℓ} {n : ℕ} → coHomRed n A
0̂R {n = zero} = ∣ (λ _ → 0*) , refl ∣₀
0̂R {n = suc n} = ∣ (λ _ → 0*) , refl ∣₀

_* :  {n : ℕ} (f : B → A) → coHom n A  → coHom n B
_* {B = B} {A = A} {n = n} f = elimSetTrunc {B = λ _ → coHom n B}
                                            (λ _ → setTruncIsSet)
                                            λ β → ∣ (λ x → (β (f x))) ∣₀

_*-Red :  {n : ℕ} {A : Pointed ℓ} {B : Pointed ℓ'} (f : B →* A) → coHomRed n A  → coHomRed n B
_*-Red {n = n}  {A = A} {B = B}  f = elimSetTrunc {B = λ _ → coHomRed n B}
                                            (λ _ → setTruncIsSet)
                                            λ β → ∣ (λ x → fst β (fst f x)) , (λ i → (fst β (snd f i))) ∙ snd β ∣₀



module Mayer-Vietoris where
  inj : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
         {f : C → (typ A)} {g : C → B} →
         coHomRed n ((Pushout f g) , inl (pt A)) → coHomRed n A × coHom n B
  inj {A = A} {B = B} {C = C} {n = zero} {f = f} {g = g} = elimSetTrunc (λ _ → hLevelProd (suc (suc zero)) setTruncIsSet setTruncIsSet) λ d → ((_*-Red) {n = zero} inl' ) ∣ d ∣₀ ,  (inr *) ∣ fst d ∣₀  
    module MV-help where
      inl' : A →* ((Pushout f g) , inl (pt A))
      inl' = inl , refl
  inj {A = A} {B = B} {C = C} {n = suc n} {f = f} {g = g} = elimSetTrunc (λ _ → hLevelProd (suc (suc zero)) setTruncIsSet setTruncIsSet) λ d → ((_*-Red) {n = (suc n)} MV-help.inl' ) ∣ d ∣₀ ,  (inr *) ∣ fst d ∣₀

  Δfun : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
         {f : C → (typ A)} {g : C → B} →
         (coHomRed n A) × (coHom n B) →  coHom n C
  Δfun {A = A} {B = B} {n = zero} {f = f} {g = g} (a , b) = elimSetTrunc (λ _ → setTruncIsSet) (λ d → (f *) ∣ fst d ∣₀) a
                                                                    +̂
                                                                    (-̂ elimSetTrunc (λ _ → setTruncIsSet) (λ d → (g *) ∣ d ∣₀) b) 
  Δfun {A = A} {B = B} {n = suc n} {f = f} {g = g} (a , b) = elimSetTrunc (λ _ → setTruncIsSet) (λ d → (f *) ∣ fst d ∣₀) a
                                                                    +̂
                                                                    (-̂ elimSetTrunc (λ _ → setTruncIsSet) (λ d → (g *) ∣ d ∣₀) b)

  d-fun : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
         {f : C → (typ A)} {g : C → B} →
         coHom n C → coHomRed (suc n) (Pushout f g , inl (pt A))
  d-fun {A = A} {B = B} {C = C} {n = n} {f = f} {g = g} = elimSetTrunc (λ _ → setTruncIsSet) λ γ → ∣ (d̃-fun γ) ∣₀
    where 
    d̃-fun : (C → (coHomK n)) → typ ((Pushout f g , inl (pt A)) →* coHomK-ptd (suc n) *)
    d̃-fun fun = d̃' , refl
      where
      d̃' : Pushout f g → coHomK (suc n)
      d̃' (inl x) = 0*
      d̃' (inr x) = 0*
      d̃' (push a i) = (transport (λ i → Kn≡ΩKn+1 n i) (fun a)) i

{-
  ker-d : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
         {f : C → (typ A)} {g : C → B} → Type (ℓ-max (ℓ-max ℓ'' ℓ) ℓ')
  ker-d {A = A} {B = B} {C = C} {n = n} {f = f} {g = g} = Σ (coHom n C) (λ x → (d-fun {A = A} {f = f} {g = g} x) ≡ 0̂R {n = (suc n)})

  ker-Δ : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
         {f : C → (typ A)} {g : C → B} → Type (ℓ-max (ℓ-max ℓ'' ℓ) ℓ')
  ker-Δ {A = A} {B = B} {C = C} {n = n} {f = f} {g = g} = Σ ((coHomRed n A) × (coHom n B)) (λ x → (Δfun {A = A} {f = f} {g = g} x) ≡ 0̂)

  im-i : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
         {f : C → (typ A)} {g : C → B} → Type (ℓ-max (ℓ-max ℓ'' ℓ) ℓ')
  im-i {A = A} {B = B} {C = C} {n = n} {f = f} {g = g} = Σ (coHomRed n A × coHom n B) λ y → Σ (coHomRed n ((Pushout f g) , inl (pt A))) λ x → inj x ≡ y

  im-d : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
         {f : C → (typ A)} {g : C → B} → Type (ℓ-max (ℓ-max ℓ'' ℓ) ℓ')
  im-d {A = A} {B = B} {C = C} {n = n} {f = f} {g = g} = Σ (coHomRed (suc n) (Pushout f g , inl (pt A))) λ y → Σ (coHom n C) λ x → d-fun x ≡ y

  im-Δ : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
         {f : C → (typ A)} {g : C → B} → Type (ℓ-max (ℓ-max ℓ'' ℓ) ℓ')
  im-Δ {A = A} {B = B} {C = C} {n = n} {f = f} {g = g} = Σ (coHom n C) λ y → Σ ((coHomRed n A) × (coHom n B)) λ x → Δfun {f = f} {g = g} x ≡ y
-}

  Im-d⊂Ker-i : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
                {f : C → (typ A)} {g : C → B} →
                (y : (coHomRed (suc n) (Pushout f g , inl (pt A)))) →
                Σ (coHom n C) (λ x → d-fun x ≡ y) →
                inj {n = (suc n)} y ≡ (0̂R {n = (suc n)} , 0̂)
  Im-d⊂Ker-i {n = n} y (x , pf) = {!(sym (cong (inj {n = (suc n)}) pf))!}


  Ker-i⊂Im-d : ∀{ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'} {C : Type ℓ''} {n : ℕ}
                {f : C → (typ A)} {g : C → B} →
                (y : (coHomRed (suc n) (Pushout f g , inl (pt A)))) →
                Σ (coHom n C) (λ x → d-fun x ≡ y) →
                inj {n = (suc n)} y ≡ (0̂R {n = (suc n)} , 0̂)
  Ker-i⊂Im-d = {!!}
