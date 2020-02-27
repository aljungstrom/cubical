{-# OPTIONS --cubical #-}
module Cubical.ZCohomology.loopSpaceProof where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.HITs.S1
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

  adj-ap≃ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x : A} {f g : (x : A) → B x}
              (α : f ≡ f) (q : f ≡ g)
            → adj (ap≃ q{x}) (ap≃ α {x}) ≡ ap≃ (adj (sym q) α) {x}
  adj-ap≃ {ℓ} {ℓ'} {A} {B} {x} {f} {g} α q = J {ℓ-max ℓ ℓ'} {(x : A) → B x} {f} (λ x p → adj (ap≃ p ) (ap≃ α ) ≡ ap≃ (adj (sym p) α)) (sym (lUnit ((λ i → (α (~ i) x)) ∙ refl))  ∙  sym (rUnit (λ i → α (~ i) x)) ∙ sym ((λ k i → (sym (lUnit (α ∙ refl) ) k) (~ i) x) ∙ (λ k i → (sym (rUnit α) k) (~ i) x))) q 

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

β-fun : (n : ℕ) {f : A → B} (a : ((x : A) → typ ((Ω^ (suc n)) (B , (f x))))) →
    apl n (λl n a) ≡ a
β-fun zero a = refl
β-fun (suc n) {f} a  = λ≃ λ x → adjust (ap^-id n (λ f → f x)) (ap (λ f → apl n f x) (adjust (λl-id n) (ap (λl n) (λ≃ a))))
                                           ≡⟨ ap (λ y → adjust (ap^-id n (λ f' → f' x) {f}) (ap (ap^ n (λ f' → f' x)) y)) (sym (adj-def (λl-id n) _)) ⟩
                      adjust (ap^-id n (λ f → f x){f}) (ap (λ f → apl n f x) (adj _ (ap (λl n) (λ≃ a)))) ≡⟨ sym (adj-def (ap^-id n (λ f → f x)) _)⟩
                      adj _ (ap (λ f → apl n f x) (adj _ (ap (λl n) (λ≃ a)))) ≡⟨ adj-bind (ap-adj (λ f' → apl n f' x) _ _) ⟩
                      adj _ (ap (λ f → apl n f x) (ap (λl n) (λ≃ a))) ≡⟨ ap (adj _) (sym (ap-o (\ f -> apl n f x) (λl n) _)) ⟩
                      adj _ (ap (λ f → apl n (λl n f) x) (λ≃ a)) ≡⟨ adj-bind (ap-loop-by-equals {f = λ f → apl n (λl n f) x} {g = λ f → f x} (λ f → ap≃ (sym (β-fun n f))) _)  ⟩
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
FunLoopSpace (suc n) = isoToPath (iso (apl n ) (λl n) (β-fun n) (η n))

record IsEquiv {A B : Type ℓ} (f : A → B) : Type ℓ where
  constructor isequiv
  field
     g : B → A
     α : (x : A) → (g (f x)) ≡ x
     β : (y : B) → (f (g y)) ≡ y
     γ : (x : A) → (β (f x)) ≡ (ap f (α x)) -- coherence condition necessary for higher spaces
     -- also satifies:
     -- (y : B) →  Path (α (g y)) (ap g (β y));
     -- this is just γ with f<→g and α<→β, so we'll prove this in
     -- the process of defining !-equiv below

record IsHEquiv {A B : Type ℓ} (f : A → B) : Type ℓ where
  constructor ishequiv
  field
     g : B → A
     α : (x : A) → (g (f x)) ≡ x
     β : (y : B) → (f (g y)) ≡ y

HEquiv : Type ℓ → Type ℓ → Type ℓ
HEquiv A B = Σ (A → B) λ f → IsHEquiv f

hequiv : {A B : Type ℓ}
         (f : A → B)
         (g : B → A)
         (α : (x : A) → (g (f x)) ≡ x)
         (β : (y : B) → (f (g y)) ≡ y)
         → HEquiv A B
hequiv f g α β = f , ishequiv g α β

Equiv : Type ℓ -> Type ℓ -> Type ℓ
Equiv A B = Σ (A → B) λ f → IsEquiv f

equiv : {A B : Type ℓ}
     (f : A → B)
     (g : B → A)
     (α : (x : A) → (g (f x)) ≡ x)
     (β : (y : B) → (f (g y)) ≡ y)
     (γ : (x : A) → (β (f x)) ≡ (ap f (α x)))
   → Equiv A B
equiv f g α β γ = f , isequiv g α β γ

infixr 30 _∘'_

_∘'_  : {M N P : A} → N ≡ P → M ≡ N → M ≡ P
β ∘' γ = γ ∙ β

move-right-right-! :  {A : Type ℓ} {M N P : A}
                       (β : N ≡ P) (α : N ≡ M) (γ : M ≡ P)
                    → (β ∘' sym α) ≡ γ
                    →  β ≡ (γ ∘' α)
move-right-right-! = {!!}

move-right :  {A : Type ℓ} {M N P : A}
               (β : N ≡ P) (α : M ≡ N) (γ : M ≡ P)
            → (β ∘' α) ≡ γ
            →  α ≡ (sym β ∘' γ) 
move-right = {!!}

-- η (g (f x)) ≡ ((λ i → cong (λ x₁ → x₁) (η x) (~ i)) ∙ η x) ∙ (λ i → g (f (η x i)))
-- need to show (sym (((λ i → cong (λ x₁ → x₁) (η x) (~ i)) ∙ η x))) ∙  η (g (f x)) ≡ (λ i → g (f (η x i)))
-- ie :  ((η x) ∙ η x)) ∙  η (g (f x)) ≡ (λ i → g (f (η x i)))



!-inv-l  :  {M N : A} (α : M ≡ N) 
            → ((sym α) ∘' α) ≡ refl
!-inv-l id = rCancel id



transport-Path : ∀{ℓ} {Γ A : Type ℓ} (f g : Γ → A) {M N : Γ} (p : M ≡ N) → (p' : _) → (transport (λ i → f (p i) ≡ g (p i)) p' ) ≡ (((ap g p) ∘' p') ∘' (sym (ap f p)))
transport-Path {ℓ = ℓ} {Γ = Γ} {A = A} f g {M = M} {N = N}  = J {ℓ} {Γ} {M} (λ x p → (p' : _) → (transport (λ i → f (p i) ≡ g (p i)) p' ) ≡ (((ap g p) ∘' p') ∘' (sym (ap f p)))) λ p' → transportRefl p' ∙ (lUnit (((λ i → g (refl i)) ∘' p')) ∘' rUnit p')   

inverses-natural : {A B : Type ℓ} (f : A → B) (g : B → A) (η : (x : A) → (g (f x)) ≡ x)
                      {x : A} →  (η (g (f x))) ≡ (ap (g ∘ f) (η x))
inverses-natural {A} {B} f g η {x} = (sym (rUnit _) ∘' ap (λ y → y ∘' ap (λ x' → g (f x')) (η x)) (rCancel (η x))  ) ∘' (ap (λ a → (sym a ∘' η x) ∘' ap (g ∘ f) (η x)) (ap-id (η x)) ∘' move-right-right-! ((η (g (f x))) ) ((ap (λ x' → g (f x'))) (η x) ) _ (move-right ((ap (λ x' → x') (η x))) ((η (g (f x)) ∘' sym (ap (λ x' → g (f x')) (η x)))) _ (((fromPathP (cong η (η x)))  ∘' sym (transport-Path (g ∘ f) (λ x' → x') (η x) (η (g (f x))))) ∘' sym (assoc _ _ _))))

improve : {A B : Type ℓ} → HEquiv A B → Equiv A B
improve (f , ishequiv g η ξ) =
  equiv f g
        η
        ((λ x → ξ x ∘' ap f (η (g x)) ∘' ap (f ∘ g) (sym (ξ x))))
        coh where
  abstract
    coh : (x : _) → ξ (f x) ∘' ap f (η (g (f x))) ∘' ap (f ∘ g) (sym (ξ (f x))) ≡ ap f (η x)
    coh x = ξ (f x) ∘' ap f (η (g (f x))) ∘' ap (f ∘ g) (sym (ξ (f x))) ≡⟨ ap (λ a → ξ (f x) ∘' ap f a ∘' ap (f ∘ g) (sym (ξ (f x)))) (inverses-natural f g η)  ⟩
            ξ (f x) ∘' ap f (ap (g ∘ f) (η x)) ∘' ap (f ∘ g) (sym (ξ (f x))) ≡⟨ ap (λ a → ξ (f x) ∘' a ∘' ap (f ∘ g) (sym (ξ (f x)))) (ap-o (f ∘ g) f (η x) ∘' sym (ap-o f (g ∘ f) (η x)))   ⟩
            ξ (f x) ∘' ap (f ∘ g) (ap f (η x)) ∘' ap (f ∘ g) (sym (ξ (f x))) ≡⟨ {!ap (λ a → ξ (f x) ∘ a ∘ ap (f o g) (! (ξ (f x)))) (ap (λ a → ! (ξ (f x)) ∘ ap f (η x) ∘ a) (!-invol (ξ (f (g (f x))))) ∘ ap-by-id (λ x' → ! (ξ x')) (ap f (η x)))!} ⟩
            ξ (f x) ∘' (sym (ξ (f x)) ∘' (ap f (η x)) ∘' ξ (f (g (f x)))) ∘' ap (f ∘ g) (sym (ξ (f x))) ≡⟨ (λ i → ξ (f x) ∘' {!sym (assoc ? ? ?) i!}) ⟩
            ξ (f x) ∘' sym (ξ (f x)) ∘' (ap f (η x)) ∘' ξ (f (g (f x))) ∘' ap (f ∘ g) (sym (ξ (f x))) ≡⟨ {!!-inv-r-front (ξ (f x)) (ap f (η x) ∘ ξ (f (g (f x))) ∘ ap (f o g) (! (ξ (f x))))!} ⟩
            {!!} ≡⟨ {!!} ⟩
            {!!} ≡⟨ {!!} ⟩
            {!!}
-- 


-- hcomp (λ z → λ{ (j = i0) → refl {x = {!g (f (g (f x)))!} } z ; (j = i1) → η (η x (i ∨ z)) (~ i ∧ (~ z))}) ?
{- j → ((η (η x (i ∧ j)) (j ∧ ~ i))))
ap (λ a → (! a ∘ η x) ∘ ap (g o f) (η x)) (ap-id (η x)) ∘
   move-right-right-! (η (g (f x))) (ap (λ x' → g (f x')) (η x)) _
     (move-right (ap (λ x' → x') (η x)) (η (g (f x)) ∘ ! (ap (λ x' → g (f x')) (η x))) _
       (apd η (η x) ∘ ! (transport-Path (g o f) (λ x' → x') (η x) (η (g (f x))))))
-}

{-
path : ∀ n → 
              ((x : A) → Loop n (B x) (f x))
            ≃ (Loop n ((x : A) -> B x) f)
path n = ua (eqv n) 

ext : ∀ n → (α α' : Loop n ((x : A) → B x) f) (p : (x : A) → apl n α x ≃ apl n α' x) → α ≃ α'
ext n α α' p = η n α' ∘ ap (λl n) (λ≃ p) ∘ ! (η n α)
-}
