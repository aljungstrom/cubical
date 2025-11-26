module Cubical.Foundations.Pointed.Family where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties
open import Cubical.Structures.Pointed

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

open import Cubical.Homotopy.Loopspace

Ω' : Pointed ℓ → Pointed ℓ
Ω' (A , x) .fst = Σ[ a ∈ A ] ((a ≡ x) × (a ≡ a))
Ω' (A , x) .snd = (x , (refl , refl))

-- Ω'' : Pointed ℓ → Pointed ℓ
-- Ω'' (A , x) .fst = Σ[ a ∈ A ] (Σ[ a' ∈ A ] ((a ≡ a') × (a' ≡ x) × (a ≡ a)))
-- Ω'' (A , x) .snd = (x , (x , refl , refl , refl))

-- Ω''→ : {A : Pointed ℓ} {B : Pointed ℓ'}
--   → A →∙ B → Ω'' A →∙ Ω'' B
-- Ω''→ {A = A} f .fst (x , y , p , q , r) = (fst f x) , (fst f y , (cong (fst f) p , {!!} , {!!}))
-- Ω''→ f .snd = {!!}

-- Ω'→ : {A : Pointed ℓ} {B : Pointed ℓ'}
--   → A →∙ B → Ω' A →∙ Ω' B
-- Ω'→ f .fst (x , p , q) .fst = fst f x
-- Ω'→ f .fst (x , p , q) .snd .fst = cong (fst f) p ∙ snd f
-- Ω'→ f .fst (x , p , q) .snd .snd = cong (fst f) q
-- Ω'→ f .snd = ΣPathP ((snd f) , (ΣPathP ((sym (lUnit (snd f)) ◁ λ i j → snd f (i ∨ j)) , (λ j i → snd f j))))

--------------------------

PointedFam : (ℓ : Level) → Type (ℓ-suc ℓ)
PointedFam ℓ = Σ[ A ∈ Type ℓ ] Σ[ P ∈ (A → Type ℓ) ] (isContr (Σ A P))

ty : ∀ {ℓ} (A : PointedFam ℓ) → Type ℓ
ty A = fst A

ptFam : ∀ {ℓ} (A : PointedFam ℓ) → ty A → Type ℓ
ptFam A = fst (snd A)

pt' : ∀ {ℓ} (A : PointedFam ℓ) → ty A
pt' A = fst (fst (snd (snd A)))

_→∙ᶠ_ : PointedFam ℓ → PointedFam ℓ' → Type (ℓ-max ℓ ℓ')
A →∙ᶠ B = (x : fst A) → Σ[ b ∈ ty B ] (ptFam A x → ptFam B b)

PointedFam→Pointed : PointedFam ℓ → Pointed ℓ
PointedFam→Pointed A .fst = fst A
PointedFam→Pointed A .snd = fst (fst (snd (snd A)))

Pointed→PointedFam : Pointed ℓ → PointedFam ℓ
Pointed→PointedFam A .fst = fst A
Pointed→PointedFam A .snd .fst x = pt A ≡ x
Pointed→PointedFam A .snd .snd = isContrSingl _

Pointed→PointedFam→Pointed : ∀ {ℓ} → (A : Pointed ℓ)
  → PointedFam→Pointed (Pointed→PointedFam A) ≡ A
Pointed→PointedFam→Pointed A = refl

open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels


PointedFam→Pointed→PointedFam≃ : (A : PointedFam ℓ) (x : fst A)
  → Iso (pt' A ≡ x) (fst (snd A) x)
PointedFam→Pointed→PointedFam≃ A x .Iso.fun p =
  subst (fst (snd A)) p (snd (snd (snd A) .fst))
PointedFam→Pointed→PointedFam≃ A x .Iso.inv t =
  cong fst (snd (snd A) .snd (x , t))
PointedFam→Pointed→PointedFam≃ A x .Iso.rightInv b = fromPathP (cong snd (snd (snd (snd A)) (_ , b)))
PointedFam→Pointed→PointedFam≃ A x .Iso.leftInv p i j =
  fst (isProp→isSet (isContr→isProp (snd (snd A))) _ _ (snd (snd A) .snd
          (x , subst (fst (snd A)) p (snd (snd (snd A) .fst))))
          (λ i₁ → (p i₁) , transp (λ i → fst (snd A) (p (i ∧ i₁))) (~ i₁)
          (snd (snd A) .fst .snd)) i j)

PointedFam→Pointed→PointedFam : ∀ {ℓ} → (A : PointedFam ℓ)
  → Pointed→PointedFam (PointedFam→Pointed A) ≡ A
PointedFam→Pointed→PointedFam A = ΣPathP (refl
  , ΣPathP ((funExt λ x → isoToPath (PointedFam→Pointed→PointedFam≃ A x))
  , isProp→PathP (λ _ → isPropIsContr) _ _))

Iso-PointedFam-Pointed : Iso (PointedFam ℓ) (Pointed ℓ)
Iso-PointedFam-Pointed .Iso.fun = PointedFam→Pointed
Iso-PointedFam-Pointed .Iso.inv = Pointed→PointedFam
Iso-PointedFam-Pointed .Iso.rightInv = Pointed→PointedFam→Pointed
Iso-PointedFam-Pointed .Iso.leftInv = PointedFam→Pointed→PointedFam

Iso-PointedFam-Pointed-pres→∙ : {A : Pointed ℓ} {B : Pointed ℓ'}
  → Iso (A →∙ B) (Pointed→PointedFam A →∙ᶠ Pointed→PointedFam B)
Iso-PointedFam-Pointed-pres→∙ .Iso.fun f x .fst = fst f x
Iso-PointedFam-Pointed-pres→∙ .Iso.fun f x .snd t = sym (snd f) ∙ cong (fst f) t
Iso-PointedFam-Pointed-pres→∙ .Iso.inv f .fst x = fst (f x)
Iso-PointedFam-Pointed-pres→∙ {A = A} .Iso.inv f .snd = sym (f (pt A) .snd refl)
Iso-PointedFam-Pointed-pres→∙ .Iso.rightInv f i x .fst = fst (f x)
Iso-PointedFam-Pointed-pres→∙ .Iso.rightInv f i x .snd p =
  ((λ i → f (p i) .snd (λ j → p (i ∧ j)) ∙ λ j → fst (f (p (i ∨ j))))
  ∙ sym (rUnit (f x .snd p))) i
Iso-PointedFam-Pointed-pres→∙ .Iso.leftInv f = ΣPathP (refl
  , cong sym (sym (rUnit (sym (snd f)))))


ΩFam : ∀ {ℓ} → PointedFam ℓ → PointedFam ℓ
ΩFam A .fst = {!pt A' ≡ pt' A!}
ΩFam A .snd .fst x = {!x!}
ΩFam A .snd .snd = {!!}

Iso-PointedFam-Pointed-presComp→∙ : {!!}
Iso-PointedFam-Pointed-presComp→∙ = {!
Ω* : PointedGen ℓ → PointedGen ℓ
Ω* (B , P) .fst = Σ[ x ∈ B ] P x × (x ≡ x)
Ω* (B , P) .snd (b , p , q) = refl ≡ q!}

_→∙ᶠ_∙ : PointedFam ℓ → PointedFam ℓ' → PointedFam (ℓ-max ℓ ℓ')
(A →∙ᶠ B ∙) .fst = A →∙ᶠ B
(A →∙ᶠ B ∙) .snd .fst F = (x : ty A) (b : typ B) (p : ptFam B b)
  → Σ[ x ∈ ty A ] (Path {!!} {!!} {!!}) -- Σ[ A ∈ {!F x!} ] {!!} --- Σ[ p ∈ fiber f b ] Σ[ a ∈ {!fiber f!} ] {!f!}
(A →∙ᶠ B ∙) .snd .snd = {!!}
