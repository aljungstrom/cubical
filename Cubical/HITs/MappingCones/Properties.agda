{-# OPTIONS --safe #-}

module Cubical.HITs.MappingCones.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.HITs.Pushout

open import Cubical.HITs.MappingCones.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

PushoutUnit-iso-Cone : ∀ {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → Iso (Pushout (const tt) f) (Cone f)
Iso.fun (PushoutUnit-iso-Cone f) (inl tt)   = hub
Iso.fun (PushoutUnit-iso-Cone f) (inr x)    = inj x
Iso.fun (PushoutUnit-iso-Cone f) (push x i) = spoke x i
Iso.inv (PushoutUnit-iso-Cone f) (inj x)     = inr x
Iso.inv (PushoutUnit-iso-Cone f) hub         = inl tt
Iso.inv (PushoutUnit-iso-Cone f) (spoke x i) = push x i
Iso.rightInv (PushoutUnit-iso-Cone f) (inj x)     = refl
Iso.rightInv (PushoutUnit-iso-Cone f) hub         = refl
Iso.rightInv (PushoutUnit-iso-Cone f) (spoke x i) = refl
Iso.leftInv (PushoutUnit-iso-Cone f) (inl tt)   = refl
Iso.leftInv (PushoutUnit-iso-Cone f) (inr x)    = refl
Iso.leftInv (PushoutUnit-iso-Cone f) (push x i) = refl

PushoutUnit≡Cone : ∀ {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → Pushout (const tt) f ≡ Cone f
PushoutUnit≡Cone f = isoToPath (PushoutUnit-iso-Cone f)

ConesUnit-iso-Cone : ∀ {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → Iso (Cones Unit (λ { tt → f })) (Cone f)
Iso.fun (ConesUnit-iso-Cone f) (inj x)        = inj x
Iso.fun (ConesUnit-iso-Cone f) (hub tt)       = hub
Iso.fun (ConesUnit-iso-Cone f) (spoke tt x i) = spoke x i
Iso.inv (ConesUnit-iso-Cone f) (inj x)     = inj x
Iso.inv (ConesUnit-iso-Cone f) hub         = hub tt
Iso.inv (ConesUnit-iso-Cone f) (spoke x i) = spoke tt x i
Iso.rightInv (ConesUnit-iso-Cone f) (inj x)     = refl
Iso.rightInv (ConesUnit-iso-Cone f) hub         = refl
Iso.rightInv (ConesUnit-iso-Cone f) (spoke x i) = refl
Iso.leftInv (ConesUnit-iso-Cone f) (inj x) = refl
Iso.leftInv (ConesUnit-iso-Cone f) (hub x) = refl
Iso.leftInv (ConesUnit-iso-Cone f) (spoke a x i) = refl

ConesUnit≡Cone : ∀ {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → (Cones Unit (λ { tt → f })) ≡ (Cone f)
ConesUnit≡Cone f = isoToPath (ConesUnit-iso-Cone f)

open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.Data.Unit

module _ {ℓ ℓ' ℓ'' ℓ'''} {W : Type ℓ} {X : Type ℓ'} {Y : Pointed ℓ''} {Z : Pointed ℓ'''}
         (f : W → X) (g : X → typ Y) (h' : Y →∙ Z)
         (gf : (λ _ → pt Y) ≡ g ∘ f) (hg : fst h' ∘ g ≡ λ _ → pt Z)
         where
         h = fst h'

         Tod : Susp W → typ Z
         Tod north = pt Z
         Tod south = pt Z
         Tod (merid a i) =
           (sym (snd h') ∙∙ cong h (funExt⁻ gf a) ∙∙ funExt⁻ hg (f a)) i

         Tod∙ : Susp∙ W →∙ Z
         fst Tod∙ = Tod
         snd Tod∙ = refl

open import Cubical.HITs.PropositionalTruncation as pTrunc
open import Cubical.HITs.SetTruncation as sTrunc
open import Cubical.HITs.Sn
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Homotopy.Group.Base

⟨_,_,_⟩ : ∀ {ℓ ℓ' ℓ'' ℓ'''} {W : Type ℓ} {X : Type ℓ'} {Y : Pointed ℓ''} {Z : Pointed ℓ'''}
         (f : W → X) (g : X → typ Y) (h : Y →∙ Z)
         → Type _
⟨_,_,_⟩ {W = W} {X = X} {Y = Y} {Z = Z} f g h =
  ∥ (Σ[ F ∈ (Susp∙ W →∙ Z) ]
    ∃[ p,q ∈ ((λ _ → pt Y) ≡ g ∘ f) × (fst h ∘ g ≡ (λ _ → pt Z)) ]
      F ≡ Tod∙ f g h (fst p,q) (snd p,q)) ∥₂


Toda↪π : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Pointed ℓ'} {Z : Pointed ℓ''} (n : ℕ)
       → {f : S₊ (suc n) → X} {g : X → typ Y} {h : Y →∙ Z}
       → ⟨ f , g , h ⟩
       → π' (suc (suc n)) Z
Toda↪π _ = sTrunc.map fst

open import Cubical.Foundations.HLevels

Toda↪πInjective : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Pointed ℓ'} {Z : Pointed ℓ''} (n : ℕ)
       → {f : S₊ (suc n) → X} {g : X → typ Y} {h : Y →∙ Z}
       → (x y : ⟨ f , g , h ⟩)
       → Toda↪π n x ≡ Toda↪π n y
       → x ≡ y
Toda↪πInjective n =
  sTrunc.elim2 (λ _ _ → isSetΠ λ _ → isOfHLevelPath 2 squash₂ _ _)
    λ f g p
      → pTrunc.rec (squash₂ _ _)
        (λ p → cong ∣_∣₂ (ΣPathP (p , isProp→PathP (λ _ → squash₁) _ _)))
        (Iso.fun PathIdTrunc₀Iso p)

open import Cubical.HITs.Join
open import Cubical.HITs.S1 renaming (_·_ to _*_)

TodaConst : join S¹ S¹ → join S¹ S¹ → S₊ 3
TodaConst (inl x) y = north
TodaConst (inr x) y = north
TodaConst (push a b i) (inl x) = toSusp (S₊∙ 2) north i 
TodaConst (push a b i) (inr x) = toSusp (S₊∙ 2) north i
TodaConst (push a b i) (push c d j) =
  toSusp (S₊∙ 2) ((toSusp (S₊∙ 1) (a * c) ∙ sym (toSusp (S₊∙ 1) (b * d))) j) i

open import Cubical.HITs.SmashProduct
open import Cubical.Foundations.GroupoidLaws

TotaConstInv : Smash (join S¹ S¹ , inl base) (join S¹ S¹ , inl base)
             → S₊ 3
TotaConstInv basel = north
TotaConstInv baser = north
TotaConstInv (proj x y) = TodaConst x y
TotaConstInv (gluel (inl x) i) = north
TotaConstInv (gluel (inr x) i) = north
TotaConstInv (gluel (push a b j) i) = rCancel (merid north) i j
TotaConstInv (gluer b i) = north



_·j_ : join S¹ S¹ → join S¹ S¹ → join S¹ S¹
inl x ·j y = inl base
inr x ·j y = inl base
push a b i ·j inl x = inl base
push a b i ·j inr x = inl base
push a b i ·j push a₁ b₁ i₁ = {!!}

n : S₊ 3 → S₊ 3
n north = north
n south = north
n (merid a i) = toSusp (S₊∙ 2) a i

_++_ : S₊ 3 → S₊ 3 → S₊ 3
north ++ y = n y
south ++ y = n y
merid a i ++ north = toSusp (S₊∙ 2) a i
merid a i ++ south = toSusp (S₊∙ 2) a i
merid a i ++ merid b j = {!!}
open import Cubical.HITs.Truncation as Trunc
S³t = hLevelTrunc 6 (S₊ 3)
0S : S³t
0S = ∣ north ∣ₕ

hLev : isOfHLevel 6 S³t
hLev = isOfHLevelTrunc 6

hLevp : {x y : S³t} → isOfHLevel 6 (x ≡ y) 
hLevp = isOfHLevelPath 6 (isOfHLevelTrunc 6) _ _

_+3_ : S³t → S³t → S³t
_+3_ =
  Trunc.rec2 (isOfHLevelTrunc 6)
    (wedgeconFun 2 2
      (λ _ _ → isOfHLevelTrunc 6)
      ∣_∣ₕ
      ∣_∣ₕ
      refl)

+3-rUnit : (x : S³t) → x +3 0S ≡ x
+3-rUnit =
  Trunc.elim (λ _ → hLevp)
    λ a → wedgeconRight 2 2
      (λ _ _ → isOfHLevelTrunc 6)
      ∣_∣ₕ
      ∣_∣ₕ
      refl a

3- : S³t → S³t
3- = Trunc.map
  λ { north → north ; south → north ; (merid a i) → toSusp (S₊∙ 2) a (~ i)}

+3-lUnit : (x : S³t) → 0S +3 x ≡ x
+3-lUnit = Trunc.elim (λ _ → hLevp) λ _ → refl

+3-assoc : (x y z : S³t) → (x +3 y) +3 z ≡ (x +3 (y +3 z))
+3-assoc =
  Trunc.elim3 (λ _ _ _ → hLevp)
    (wedgeconFun 2 2
      (λ _ _ → isOfHLevelΠ 6 λ _ → hLevp)
      (λ x c → sym (+3-lUnit ((∣ x ∣ +3 ∣ c ∣))))
      (λ x c → cong (_+3 ∣ c ∣ₕ) (+3-rUnit ∣ x ∣ₕ))
      refl)

+3-rCancel : (x : S³t) → (x +3 3- x) ≡ 0S
+3-rCancel =
  Trunc.elim (λ _ → hLevp)
    λ { north → refl
      ; south → refl
      ; (merid a i) j → help a j i}
  where
  help : (a : S₊ 2) → cong₂ (λ x y → ∣ x ∣ₕ +3 3- ∣ y ∣ₕ) (merid a) (merid a) ≡ refl
  help a = cong₂Funct (λ x y → ∣ x ∣ₕ +3 3- ∣ y ∣ₕ) (merid a) (merid a)
         ∙ (λ i → cong (λ x → ∣ x ∣ +3 3- ∣ north ∣) (merid a) ∙
                   cong (λ y → ∣ merid north (~ i) ∣ +3 3- ∣ y ∣) (merid a))
         ∙ (λ i → cong (λ x → +3-rUnit ∣ x ∣ i) (merid a)
                 ∙ compPath-filler' (sym (+3-rUnit ∣ south ∣))
                     (cong ∣_∣ₕ (sym (toSusp (S₊∙ 2) a))) i)
         ∙ {!!}
         ∙ {!!}

+3-comm : (x y : S³t) → x +3 y ≡ y +3 x
+3-comm = 
  Trunc.elim2 (λ _ _ → hLevp)
    (wedgeconFun 2 2 (λ _ _ → hLevp)
      (λ _ → sym (+3-rUnit _))
      (λ _ → +3-rUnit _)
      refl)

+3-lCancel : (x : S³t) → (3- x +3 x) ≡ 0S
+3-lCancel x = +3-comm (3- x) x ∙ +3-rCancel x

S³tIso : (x : S₊ 3) → Iso S³t S³t
Iso.fun (S³tIso x) = ∣ x ∣ₕ +3_
Iso.inv (S³tIso x) y = (3- ∣ x ∣ₕ) +3 y
Iso.rightInv (S³tIso x) y =
  sym (+3-assoc ∣ x ∣ₕ (3- ∣ x ∣ₕ) y)
  ∙ cong (_+3 y) (+3-rCancel ∣ x ∣ₕ)
  ∙ +3-lUnit y
Iso.leftInv (S³tIso x) y =
  sym (+3-assoc (3- ∣ x ∣ₕ) ∣ x ∣ₕ y)
  ∙ cong (_+3 y) (+3-lCancel ∣ x ∣ₕ)
  ∙ +3-lUnit y


{-

assume Ση trivial

S⁵ → S⁴ → S⁴ -η→ S³

gives map S⁶→S³

   η     l          ⌣
S³ → S² → S² × S¹ → S³

-}

_+S³'_ : join S¹ S¹ → join S¹ S¹ → S₊ 3
inl x +S³' inl y = north
inl x +S³' inr y = north
inl x +S³' push a b i = toSusp (S₊∙ 2) (S¹×S¹→S² a (b * x)) i
inr x +S³' inl y = north
inr x +S³' inr y = north
inr x +S³' push a b i = toSusp (S₊∙ 2) (S¹×S¹→S² (a * x) b) i
push a b i +S³' inl x = toSusp (S₊∙ 2) (S¹×S¹→S² (a * x) (b * x)) i
push a b i +S³' inr x = toSusp (S₊∙ 2) (S¹×S¹→S² (a * x) (b * x)) i
push a b i +S³' push c d j =
  {!toSusp (S₊∙ 2) (S¹×S¹→S² (a * b) (b * c)) i!}
  where
  help : ∀ {ℓ} {A : Type ℓ} {x : A} (p p' q q' : x ≡ x)
         → p ≡ p' → q ≡ q' → Square p q p' q'
  help p p' q q' =
    J (λ p' _ → q ≡ q' → Square p q p' q')
      (J (λ q' _ → Square p q p q')
        {!!})

_+S³_ : join S¹ S¹ → join S¹ S¹ → S₊ 3
inl x +S³ y = Iso.fun (IsoSphereJoin 1 1) y
inr x +S³ y = Iso.fun (IsoSphereJoin 1 1) y
push a b i +S³ inl x = toSusp (S₊∙ 2) (S¹×S¹→S² (a * x) b) i
push a b i +S³ inr x = (sym (merid north) ∙ merid (S¹×S¹→S² a (b * x))) i
push a b i +S³ push c d j = {!!}

open import Cubical.Homotopy.Loopspace
module _ (A : Pointed₀) where
  test : (join S¹ S¹ , inl base) →∙ A → Σ[ f ∈ (S¹ × S¹ → typ (Ω A)) ] ((x : _) → f (x , base) ≡ refl) × ((y : _) → f (base , y) ≡ refl)
  fst (test f) (x , y) = sym (snd f) ∙∙ (cong (fst f) (push base base) ∙ (cong (fst f) (sym (push x base)) ∙∙ cong (fst f) (push x y) ∙∙ cong (fst f) (sym (push base y)))) ∙∙ snd f
  fst (snd (test f)) = {!refl!}
  snd (snd (test f)) = {!!}
