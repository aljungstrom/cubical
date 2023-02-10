{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.Group.SmashGroup where

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

open import Cubical.Functions.Morphism

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as T
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.S3

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Unit

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open Iso
open IsGroup
open IsSemigroup
open IsMonoid
open GroupStr

private
  variable
    ℓ ℓ' : Level

open import Cubical.HITs.SmashProduct

Susp→∙Grp : (A : Pointed ℓ) (B : Pointed ℓ') → Group _
fst (Susp→∙Grp A B) = ∥ [Σ A ∶ B ] ∥₂
1g (snd (Susp→∙Grp A B)) = ∣ 0Σ+ ∣₂
GroupStr._·_ (snd (Susp→∙Grp A B)) = ST.rec2 squash₂ λ f g → ∣ f Σ+ g ∣₂
inv (snd (Susp→∙Grp A B)) = ST.map (Σ-_)
is-set (isSemigroup (isMonoid (isGroup (snd (Susp→∙Grp A B))))) = squash₂
·Assoc (isSemigroup (isMonoid (isGroup (snd (Susp→∙Grp A B))))) =
  ST.elim3 (λ _ _ _ → isSetPathImplicit) λ f g h → cong ∣_∣₂ (assoc-Σ+ f g h)
·IdR (isMonoid (isGroup (snd (Susp→∙Grp A B)))) =
  ST.elim (λ _ → isSetPathImplicit) λ f i → ∣ rUnit-Σ+ f i ∣₂
·IdL (isMonoid (isGroup (snd (Susp→∙Grp A B)))) =
  ST.elim (λ _ → isSetPathImplicit) λ f i → ∣ lUnit-Σ+ f i ∣₂
·InvR (isGroup (snd (Susp→∙Grp A B))) =
  ST.elim (λ _ → isSetPathImplicit) λ f i → ∣ rCancel-Σ+ f i ∣₂
·InvL (isGroup (snd (Susp→∙Grp A B))) =
  ST.elim (λ _ → isSetPathImplicit) λ f i → ∣ lCancel-Σ+ f i ∣₂

⋀π : (n m : ℕ) (A : Pointed ℓ) → Type ℓ
⋀π n m A = ∥ [Σ S₊∙ n ⋀∙ S₊∙ m ∶ A ] ∥₂

⋀πGr : (n m : ℕ) (A : Pointed ℓ) → Group ℓ
⋀πGr n m A = Susp→∙Grp (S₊∙ n ⋀∙ S₊∙ m) A

module _ {n m : ℕ} {A : Pointed ℓ} where
  _⋀π+_ : ⋀π n m A → ⋀π n m A → ⋀π n m A
  _⋀π+_ = GroupStr._·_ (snd (⋀πGr n m A))

  ⋀π-_ : ⋀π n m A → ⋀π n m A
  ⋀π-_ = GroupStr.inv (snd (⋀πGr n m A))

  _⋀π-_ : ⋀π n m A → ⋀π n m A → ⋀π n m A
  f ⋀π- g = f ⋀π+ (⋀π- g)


Susp⋀Sphere→∙Sphere : (n m : ℕ) → Susp∙ (S₊∙ n ⋀ S₊∙ m) →∙ S₊∙ (suc (n + m))
fst (Susp⋀Sphere→∙Sphere n m) =
  Iso.inv (IsoSucSphereSusp (n + m)) ∘ suspFun (Iso.fun (SphereSmashIso n m))
snd (Susp⋀Sphere→∙Sphere n m) = IsoSucSphereSusp∙ (n + m)

IsoSusp⋀SphereSphere : (n m : ℕ) → Iso (Susp (S₊∙ n ⋀ S₊∙ m)) (S₊ (suc (n + m)))
IsoSusp⋀SphereSphere n m =
  compIso (congSuspIso (SphereSmashIso n m)) (invIso (IsoSucSphereSusp (n + m)))

Susp⋀Sphere≃∙Sphere : (n m : ℕ) → (Susp∙ (S₊∙ n ⋀ S₊∙ m)) ≃∙ (S₊∙ (suc (n + m)))
fst (Susp⋀Sphere≃∙Sphere n m) = isoToEquiv (IsoSusp⋀SphereSphere n m)
snd (Susp⋀Sphere≃∙Sphere n m) = Susp⋀Sphere→∙Sphere n m .snd

invSusp⋀Sphere≃∙Sphere∙ : (n m : ℕ) → S₊∙ (suc (n + m)) →∙ Susp∙ (S₊∙ n ⋀ S₊∙ m)
fst (invSusp⋀Sphere≃∙Sphere∙ n m) = Iso.inv (IsoSusp⋀SphereSphere n m)
snd (invSusp⋀Sphere≃∙Sphere∙ zero zero) = refl
snd (invSusp⋀Sphere≃∙Sphere∙ zero (suc m)) = refl
snd (invSusp⋀Sphere≃∙Sphere∙ (suc n) m) = refl

Sphere≃∙Susp⋀Sphere : (n m : ℕ) → S₊∙ (suc (n + m)) ≃∙ Susp∙ (S₊∙ n ⋀ S₊∙ m)
fst (Sphere≃∙Susp⋀Sphere n m) = isoToEquiv (invIso (IsoSusp⋀SphereSphere n m))
snd (Sphere≃∙Susp⋀Sphere n m) = invSusp⋀Sphere≃∙Sphere∙ n m .snd



π'→⋀π : (n m : ℕ) (A : Pointed ℓ) → π' (suc (n + m)) A → ⋀π n m A
π'→⋀π n m A = ST.map λ f → f ∘∙ Susp⋀Sphere→∙Sphere n m

π'-⋀π-Iso : (n m : ℕ) {A : Pointed ℓ}
  → Iso (⋀π n m A) (π' (suc (n + m)) A)
π'-⋀π-Iso n m = setTruncIso (post∘∙equiv (Susp⋀Sphere≃∙Sphere n m))

π'-⋀π-Iso' : (n m : ℕ) {A : Pointed ℓ}
  → (π' (suc (n + m)) A) → (⋀π n m A)
π'-⋀π-Iso' n m {A} = ST.map λ f
  → (λ x → fst f (Iso.fun (IsoSusp⋀SphereSphere n m) x))
   , (cong (fst f) (IsoSucSphereSusp∙ (n + m)) ∙ snd f)

π'-⋀π-Iso'← : (n m : ℕ) {A : Pointed ℓ} → (⋀π n m A) → (π' (suc (n + m)) A)
π'-⋀π-Iso'← n m {A} =
  ST.map λ f → (λ x → fst f (Iso.inv (IsoSusp⋀SphereSphere n m) x))
    , cong (fst f) (lem n m) ∙ snd f
  where
  lem : (n m : ℕ) → inv (IsoSusp⋀SphereSphere n m) (pt (S₊∙ (suc (n + m)))) ≡ north
  lem zero zero = refl
  lem zero (suc m) = refl
  lem (suc n) m = refl
-- post∘∙equiv'

π'-⋀π-Iso** : (n m : ℕ) {A : Pointed ℓ} → Iso (⋀π n m A) (π' (suc (n + m)) A)
fun (π'-⋀π-Iso** n m {A = A}) = π'-⋀π-Iso'← n m
inv (π'-⋀π-Iso** n m {A = A}) = π'-⋀π-Iso' n m
rightInv (π'-⋀π-Iso** zero zero {A = A}) =
  ST.elim (λ _ → isSetPathImplicit) λ f
    → cong ∣_∣₂ (ΣPathP ((funExt (λ x → cong (fst f) (Iso.rightInv (IsoSusp⋀SphereSphere zero zero) x)))
      , {!!}))
rightInv (π'-⋀π-Iso** zero (suc m) {A = A}) =
  ST.elim (λ _ → isSetPathImplicit) λ f → cong ∣_∣₂ (ΣPathP ({!!} , {!!}))
rightInv (π'-⋀π-Iso** (suc n) m {A = A}) =
  ST.elim (λ _ → isSetPathImplicit) λ f → cong ∣_∣₂ (ΣPathP ({!!} , {!!}))
leftInv (π'-⋀π-Iso** n m {A = A}) = {!!}

π'-⋀π-Iso*raw : (n m : ℕ) {A : Pointed ℓ}
  → Iso (S₊∙ (suc (n + m)) →∙ A) [Σ S₊∙ n ⋀∙ S₊∙ m ∶ A ]
π'-⋀π-Iso*raw n m = 
  post∘∙equiv'
    ((isoToEquiv (IsoSusp⋀SphereSphere n m))
    , IsoSucSphereSusp∙ (n + m))

π'-⋀π-Iso* : (n m : ℕ) {A : Pointed ℓ}
  → Iso (π' (suc (n + m)) A) (⋀π n m A)
π'-⋀π-Iso* n m {A} =
  setTruncIso (π'-⋀π-Iso*raw n m)

open import Cubical.HITs.Pushout
helplem : (n m : ℕ) {A : Pointed ℓ} (f : S₊∙ (suc (n + m)) →∙ A)
  → (x : _) (y : _) → (mkLoopΣfun (fun (π'-⋀π-Iso*raw n m) f) .fst (inr (x , y)))
                      ≡ wrap {!!} {!cong (fst f , )!}
helplem = {!!}

π'-⋀π-isHom : (n m : ℕ) {A : Pointed ℓ} (f g : π' (suc (n + m)) A)
  → Iso.fun (π'-⋀π-Iso* n m) (·π' _ f g)
  ≡ Iso.fun (π'-⋀π-Iso* n m) f ⋀π+ Iso.fun (π'-⋀π-Iso* n m) g
π'-⋀π-isHom zero zero {A} = ST.elim2 (λ _ _ → isSetPathImplicit)
  λ f g → cong ∣_∣₂ (ΣPathP ((funExt λ { north → refl
                                       ; south → refl
                                       ; (merid a i) j → f₁≡f₂ f g j .fst a i})
                  , sym (rUnit refl)))
  where
  module _ (f g : S₊∙ 1 →∙ A) where
    f₁ f₂ : (S₊∙ zero ⋀∙ S₊∙ zero →∙ Ω A)
    f₁ = (λ a → cong (fst (∙Π f g) ∘ IsoSusp⋀SphereSphere zero zero .fun) (merid a)) , refl
    f₂ = (λ a → cong (fst (fun (π'-⋀π-Iso*raw zero zero) f Σ+ fun (π'-⋀π-Iso*raw zero zero) g)) (merid a))
       , cong₂ _∙_ (mkLoopΣfun (fun (π'-⋀π-Iso*raw zero zero) f) .snd)
                   (mkLoopΣfun (fun (π'-⋀π-Iso*raw zero zero) g) .snd)
                   ∙ sym (rUnit refl)

    f₁≡f₂ : f₁ ≡ f₂
    f₁≡f₂ = ⋀→∙Homogeneous≡ (isHomogeneousPath _ _)
             λ x y → {!!}
                    ∙ cong₂ _∙_ {!!} {!!} -- cong₂ _∙_ (λ _ → mkLoopΣfun {!snd f!} .fst {!!}) {!!}

π'-⋀π-isHom zero (suc m) {A} = {!!}
π'-⋀π-isHom (suc n) m {A} = {!!}
