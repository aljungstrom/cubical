{-# OPTIONS --cubical #-}

module Cubical.Issue6198a where

open import Agda.Primitive
  using ( Level ; Set )
  renaming ( lzero to ℓ-zero )
open import Agda.Builtin.Bool
  using ( Bool ; true ; false )
open import Agda.Builtin.Sigma
  using ( Σ ; fst ; snd ; _,_ )
open import Agda.Builtin.Unit
  using ( ⊤ )

open import Agda.Primitive.Cubical
  using ( PathP ; I ; i0 ; i1 ; Partial )
  renaming ( primHComp to hcomp ; primTransp to transp
           ; primINeg to ~_ ; primIMax to _∨_ ; primIMin to _∧_
           )
open import Agda.Builtin.Cubical.Path
  using ( _≡_ )
open import Agda.Builtin.Cubical.Glue
  using ( primGlue )
open import Agda.Builtin.Cubical.Glue
  using ( isEquiv ; equiv-proof ; _≃_ )

-- Stuff copied from the Cubical library:

refl : ∀ {ℓ} {A : Set ℓ} {x : A} → x ≡ x
refl {x = x} _ = x

Path : ∀ {ℓ} (A : Set ℓ) (x y : A) → Set ℓ
Path A x y = x ≡ y

data S¹ : Set where
  base : S¹
  loop : base ≡ base

rotLoop : (a : S¹) → a ≡ a
rotLoop base       = loop
rotLoop (loop i) j =
  hcomp (λ k → λ { (i = i0) → loop (j ∨ ~ k)
                 ; (i = i1) → loop (j ∧ k)
                 ; (j = i0) → loop (i ∨ ~ k)
                 ; (j = i1) → loop (i ∧ k)}) base

variable
  ℓ ℓ' : Level
  A : Set ℓ
  B : Set ℓ'

fiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set _
fiber {A = A} f y = Σ A \ x → f x ≡ y

strictContrFibers : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} (g : B → A) (b : B)
  → Σ (fiber f (f (g b))) λ t →
    ((t' : fiber f b) → Path (fiber f (f (g b))) t (g (f (t' .fst)) , λ i → f (g (t' .snd i))))
strictContrFibers {f = f} g b .fst = (g b , refl)
strictContrFibers {f = f} g b .snd (a , p) i = (g (p (~ i)) , λ j → f (g (p (~ i ∨ j))))

idfun : ∀ {ℓ} (A : Set ℓ) → A → A
idfun _ x = x

idIsEquiv : ∀ {ℓ} (A : Set ℓ) → isEquiv (idfun A)
idIsEquiv A .equiv-proof = strictContrFibers (idfun A)

idEquiv : ∀ {ℓ} (A : Set ℓ) → A ≃ A
idEquiv A .fst = idfun A
idEquiv A .snd = idIsEquiv A

not : Bool → Bool
not false = true
not true = false

notNot : (x : Bool) → not (not x) ≡ x
notNot false = refl
notNot true = refl

-- this postulate doesn't seem to be computationally relevant?
postulate
  POSTULATE-notInv2 : (y : Bool) → (u : Σ Bool (λ x → not x ≡ y)) → (not y , notNot y) ≡ u

notEquiv : Bool ≃ Bool
fst notEquiv = not
fst (fst (equiv-proof (snd notEquiv) y)) = not y
snd (fst (equiv-proof (snd notEquiv) y)) = notNot y
snd (equiv-proof (snd notEquiv) y) = POSTULATE-notInv2 y

notPath : Bool ≡ Bool
notPath i = primGlue Bool (λ _ → Bool) λ { (i = i0) → notEquiv ; (i = i1) → idEquiv Bool }

doubleCover : S¹ → Set
doubleCover base = Bool
doubleCover (loop i) = notPath i

winding : Path S¹ base base → Bool
winding p = transp (λ i → doubleCover (p i)) i0 false



-- Example starts here:

-- these postulates don't seem to be computationally relevant?
postulate
  POSTULATE-rotInv1 : {A : Set} (h : (x : A) → x ≡ x) (y : A) → PathP (λ i → h (h y (~ i)) i ≡ y) refl refl
  POSTULATE-rotInv2 : {A : Set} (h : (x : A) → x ≡ x) (y : A) → PathP (λ i → (u : Σ A (λ x → h x i ≡ y)) → (h y (~ i) , POSTULATE-rotInv1 h y i) ≡ u) (snd (equiv-proof (idIsEquiv A) y)) (snd (equiv-proof (idIsEquiv A) y))

rotIsEquiv : {A : Set} (h : (x : A) → x ≡ x) → PathP (λ i → isEquiv λ x → h x i) (idIsEquiv A) (idIsEquiv A)
fst (fst (equiv-proof (rotIsEquiv h i) y)) = h y (~ i) -- hmm, is it actually possible to get this exactly? does it matter?
snd (fst (equiv-proof (rotIsEquiv h i) y)) = POSTULATE-rotInv1 h y i
snd (equiv-proof (rotIsEquiv h i) y) = POSTULATE-rotInv2 h y i

globalSys : {A : Set ℓ-zero} (h : (x : A) → x ≡ x) (i j : I) → Partial (~ i ∨ i ∨ ~ j ∨ j) (Σ (Set ℓ-zero) (λ T → T ≃ A))
globalSys {A} h i j (i = i0) = A , idEquiv A
globalSys {A} h i j (i = i1) = A , idEquiv A
globalSys {A} h i j (j = i0) = A , ((λ x → h x i) , rotIsEquiv h i)
globalSys {A} h i j (j = i1) = A , idEquiv A

global : ∀ {A : Set ℓ-zero} → ((x : A) → x ≡ x) → Path (A ≡ A) refl refl
global {A = A} h i j = primGlue A (λ o → globalSys h i j o .fst) (λ o → globalSys h i j o .snd)

data JS¹ : Set where
  base : JS¹
  loops : (x : JS¹) → x ≡ x

-- should use J₃S¹ but J₂S¹ seems good enough for the computation
data J₂S¹ : Set where
  base : J₂S¹
  loop : base ≡ base
  funk : PathP (λ i → loop i ≡ loop i) loop loop

-- should 2-truncate to avoid this postulate, but it doesn't seem to
-- be computationally relevant
postulate
  POSTULATE-funky-whoa : PathP (λ i → PathP (λ j → PathP (λ k → J₂S¹) (funk i j) (funk i j)) (λ k → funk i k) (λ k → funk i k)) (λ j k → funk j k) (λ j k → funk j k)

data S² : Set where
  base : S²
  surf : Path (Path S² base base) refl refl

LoopS² : S² → Set
LoopS² base = JS¹
LoopS² (surf i j) = global loops i j

f1 : Path S² base base → JS¹
f1 p = transp (λ i → LoopS² (p i)) i0 base

funky : (x : J₂S¹) → x ≡ x
funky base = loop
funky (loop i) = funk i
funky (funk i j) = POSTULATE-funky-whoa i j

f2 : JS¹ → J₂S¹
f2 base = base
f2 (loops x i) = funky (f2 x) i

f3 : J₂S¹ → S²
f3 base = base
f3 (loop i) = base
f3 (funk i j) = surf i j

annoying : Path S² base base
annoying i = f3 (f2 (f1 (surf i)))

Hopf : S² → Set
Hopf base = S¹
Hopf (surf i j) = global rotLoop i j

f4 : annoying ≡ annoying → Bool
f4 p = winding (λ i → transp (λ j → Hopf (p i j)) i0 base)

thingSys : (j a b : I) → I → Partial (~ j ∨ j ∨ ~ a ∨ a ∨ ~ b ∨ b) S²
thingSys j a b i (j = i0) = surf a b
thingSys j a b i (j = i1) = surf a b
-- thingSys j a b i (a = i0) = surf i j
-- thingSys j a b i (a = i1) = surf i j
-- thingSys j a b i (b = i0) = surf i j
-- thingSys j a b i (b = i1) = surf i j
-- not the thing but still breaks canonicity:
thingSys j a b i (a = i0) = base
thingSys j a b i (a = i1) = base
thingSys j a b i (b = i0) = base
thingSys j a b i (b = i1) = base

thing : surf ≡ surf
thing j a b = hcomp (thingSys j a b) (surf a b)

b : Bool
b = f4 (λ i j → f3 (f2 (f1 (thing i j))))

-- test : b ≡ false
-- test = refl
