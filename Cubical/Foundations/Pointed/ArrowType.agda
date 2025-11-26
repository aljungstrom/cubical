module Cubical.Foundations.Pointed.ArrowType where

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


AoA : Σ[ B ∈ Type ℓ ] Σ[ T ∈ Type ℓ ] (T → B) → Σ[ B ∈ Type ℓ ] Σ[ T ∈ Type ℓ ] (T → B)
AoA (B , T , f) .fst = Σ[ x ∈ T ] (f x ≡ f x)
AoA (B , T , f) .snd .fst = T
AoA (B , T , f) .snd .snd t = t , refl


Qt : (B : Type ℓ) → Iso ((B → Type ℓ)) (Σ[ T ∈ Type ℓ ] (T → B))
Qt B .Iso.fun P = Σ _ P , fst
Qt B .Iso.inv (T , f) x = fiber f x
Qt B .Iso.rightInv (T , f) = {!!}
-- ΣPathP (isoToPath (iso {!!} {!!} {!!} {!!}) , {!!})
Qt B .Iso.leftInv = {!!}

PointedGen : (ℓ : Level) → Type _
PointedGen ℓ = Σ[ B ∈ Type ℓ ] (B → Type ℓ)

PointedGenHom : ∀ {ℓ} → PointedGen ℓ → PointedGen ℓ' → Type _
PointedGenHom (B , P) (B' , P') =
  Σ[ f ∈ (B → B') ]
    ((x : B) → P x → P' (f x))

compPointedGenHom : ∀ {ℓ ℓ' ℓ''} {A : PointedGen ℓ}
  {B : PointedGen ℓ'} {C : PointedGen ℓ''}
  → PointedGenHom A B → PointedGenHom B C
  → PointedGenHom A C
compPointedGenHom (f , p) (g , q) .fst x = g (f x)
compPointedGenHom (f , p) (g , q) .snd x a = q (f x) (p x a)

compPointedGenAssoc : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : PointedGen ℓ}
  {B : PointedGen ℓ'} {C : PointedGen ℓ''} {D : PointedGen ℓ'''}
  (f : PointedGenHom A B) (g : PointedGenHom B C) (h : PointedGenHom C D)
  → compPointedGenHom {A = A} {B} {D} f (compPointedGenHom {A = B} {C} {D} g h)
  ≡ compPointedGenHom {A = A} {C} {D} (compPointedGenHom {A = A} {B} {C} f g) h
compPointedGenAssoc f g h = refl

Pointed→ : Pointed ℓ → PointedGen ℓ
Pointed→ A .fst = fst A
Pointed→ A .snd a = snd A ≡ a

HomEq : ∀ {ℓ} (A B : Pointed ℓ)
  → Iso (A →∙ B) (PointedGenHom (Pointed→ A) (Pointed→ B))
HomEq A B .Iso.fun (f , p) .fst = f
HomEq A B .Iso.fun (f , p) .snd x q = sym p ∙ cong f q
HomEq A B .Iso.inv (f , q) .fst = f
HomEq A B .Iso.inv (f , q) .snd = sym (q (pt A) refl)
HomEq A B .Iso.rightInv (f , p) = ΣPathP (refl , funExt λ x → funExt
  (J (λ x q → (λ i → p (pt A) (λ _ → snd A) i) ∙ (λ i → f (q i))
             ≡ p x q)
    (sym (rUnit _))))
HomEq A B .Iso.leftInv (f , p) = ΣPathP (refl , cong sym (sym (rUnit (sym p))))

Ω* : PointedGen ℓ → PointedGen ℓ
Ω* (B , P) .fst = Σ[ x ∈ B ] P x × (x ≡ x)
Ω* (B , P) .snd (b , p , q) = refl ≡ q

Ω*→ : ∀ {ℓ ℓ'} {A : PointedGen ℓ} {B : PointedGen ℓ'}
  → PointedGenHom A B
  → PointedGenHom (Ω* A) (Ω* B)
Ω*→ (f , p) .fst (t , s , q) = (f t) , (p t s , cong f q)
Ω*→ (f , p) .snd (t , q) r = cong (cong f) r

open import Cubical.Homotopy.Loopspace
Iso-Ω*-Ω : ∀ {ℓ} (A : Pointed ℓ) → Iso (Ω* (Pointed→ A) .fst) (Pointed→ (Ω A) .fst)
Iso-Ω*-Ω A .Iso.fun (_ , q , p) = q ∙∙ p ∙∙ sym q
Iso-Ω*-Ω A .Iso.inv p = (pt A) , (refl , p)
Iso-Ω*-Ω A .Iso.rightInv p = sym (rUnit p)
Iso-Ω*-Ω A .Iso.leftInv (_ , q , p) =
  ΣPathP (q , ΣPathP ((λ i j → q (i ∧ j))
    , symP (doubleCompPath-filler q p (sym q))))

Ω*≡Ω : ∀ {ℓ} (A : Pointed ℓ) → Pointed→ (Ω A) ≡ Ω* (Pointed→ A)
Ω*≡Ω A = ΣPathP (isoToPath (invIso (Iso-Ω*-Ω A)) , {!Ω* (Pointed→ A) .snd!})


PointedGenHomΩ : ∀ {ℓ} {B : Pointed ℓ} → PointedGenHom (Ω* (Pointed→ B)) (Pointed→ (Ω B))
PointedGenHomΩ {B = B} .fst (b , p , q) = p ∙∙ q ∙∙ sym p
PointedGenHomΩ {B = B} .snd (b , p , q) r =
  sym (∙∙lCancel (sym p)) ∙ cong (p ∙∙_∙∙ sym p) r

PointedGenHomΩ← : ∀ {ℓ} {B : Pointed ℓ} → PointedGenHom (Pointed→ (Ω B)) (Ω* (Pointed→ B))
PointedGenHomΩ← {B = B} .fst p = (pt B) , (refl , p)
PointedGenHomΩ← {B = B} .snd _ q = q

ΩPres* : ∀ {ℓ} (A B : Pointed ℓ) (f : A →∙ B)
  →  Ω*→ (Iso.fun (HomEq A B) f)
    ≡ compPointedGenHom {B = Pointed→ (Ω B)} {C = Ω* (Pointed→ B)}
        (compPointedGenHom {B =  Pointed→ (Ω A)} {C =  Pointed→ (Ω B)}
          PointedGenHomΩ
          (Iso.fun (HomEq (Ω A) (Ω B)) (Ω→ f)))
        PointedGenHomΩ←
ΩPres* A B f =
  ΣPathP ((funExt λ {(x , p , q) → ΣPathP (cong (fst f) (sym p) ∙ snd f
  , {!p!})})
        , {!!})

ΩPres : ∀ {ℓ} (A B : Pointed ℓ) (f : A →∙ B)
  →  compPointedGenHom {B = Ω* (Pointed→ B)} {C = Pointed→ (Ω B)}
        (compPointedGenHom {C = Ω* (Pointed→ B)}
          PointedGenHomΩ←
          (Ω*→ (Iso.fun (HomEq A B) f)))
        PointedGenHomΩ
    ≡ (Iso.fun (HomEq (Ω A) (Ω B)) (Ω→ f))
ΩPres A B f = ΣPathP
  ((funExt (λ q → {!!}))
  , {!!})

ArrowType : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
ArrowType ℓ ℓ' = Σ[ A ∈ Type ℓ ] Σ[ B ∈ (A → Type ℓ') ] ((x : A) → B x)

ArrowType' : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
ArrowType' ℓ ℓ' = {!!}
-- Σ[ B ∈ (Type ℓ → Type ℓ') ] {!!}

-- ArrowTypeHom : ArrowType ℓ ℓ' → ArrowType ℓ'' ℓ'''
--   → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ'''))
-- ArrowTypeHom (A , B , f) (A' , B' , f') =
--   Σ[ F ∈ (A → A') ]
--     Σ[ G ∈ ({x : A} → B x → B' (F x)) ]
--       ((x : _) → G (f x) ≡ f' (F x))

-- compArrowTypeHom : ∀ {ℓ'''' ℓ'''''} {X : ArrowType ℓ ℓ'}
--   {Y : ArrowType ℓ'' ℓ'''} {Z : ArrowType ℓ'''' ℓ'''''}
--   → ArrowTypeHom X Y
--   → ArrowTypeHom Y Z
--   → ArrowTypeHom X Z
-- compArrowTypeHom (F , G , P) (F' , G' , P') .fst = F' ∘ F
-- compArrowTypeHom (F , G , P) (F' , G' , P') .snd .fst x = G' (G x)
-- compArrowTypeHom (F , G , P) (F' , G' , P') .snd .snd x = {!P' !}


-- ArrowTypeHomAssoc : ∀ {ℓ'''' ℓ'''''}
--   (f : ArrowType ℓ ℓ') (g : ArrowType ℓ'' ℓ''')
--   (h : ArrowType ℓ'''' ℓ''''')
--   → {!!}
-- ArrowTypeHomAssoc (A , B , f) (A' , B' , f') (A'' , B'' , f'') = {!!}
