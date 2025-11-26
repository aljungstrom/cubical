{-
  This uses ideas from Floris van Doorn's phd thesis and the code in
  https://github.com/cmu-phil/Spectral/blob/master/spectrum/basic.hlean
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Homotopy.Prespectrum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Data.Unit.Pointed

open import Cubical.Structures.Successor

open import Cubical.Data.Nat
open import Cubical.Data.Int

open import Cubical.HITs.Susp

open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ ℓ' : Level

record GenericPrespectrum (S : SuccStr ℓ) (ℓ' : Level) : Type (ℓ-max (ℓ-suc ℓ') ℓ) where
  open SuccStr S
  field
    space : Index → Pointed ℓ'
    map : (i : Index) → (space i →∙ Ω (space (succ i)))

record GenericPrespectrum' (S : SuccStr ℓ) (ℓ' : Level) : Type (ℓ-max (ℓ-suc ℓ') ℓ) where
  open SuccStr S
  field
    space' : Index → Pointed ℓ'
    map' : (i : Index) → (Susp∙ (fst (space' i)) →∙ space' (succ i))

-- private
--   open import Cubical.Foundations.Function
--   open import Cubical.Data.Sigma
--   module _ {S : SuccStr ℓ} where
--     open SuccStr S
--     open GenericPrespectrum'
--     GenericPrespectrumMap' : ∀ {ℓ' ℓ''}
--       (X : GenericPrespectrum' S ℓ') (Y : GenericPrespectrum' S ℓ'')
--       → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
--     GenericPrespectrumMap' X Y =
--       Σ[ f ∈ ((i : Index) → space' X i →∙ space' Y i) ]
--        (((i : Index) →
--          Σ[ coh ∈ ((x : _) → fst (f (succ i)) (fst (map' X i) x)
--                             ≡ fst (map' Y i) (suspFun (fst (f i)) x)) ]
--           Square (coh north) (snd (f (succ i)))
--                  (cong (fst (f (succ i))) (snd (map' X i))) (snd (map' Y i))))

--     compGenericPrespectrumMap' : ∀ {ℓ' ℓ''}
--       (X : GenericPrespectrum' S ℓ') (Y : GenericPrespectrum' S ℓ'')
--       → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
--     compGenericPrespectrumMap' X Y =
--       Σ[ f ∈ ((i : Index) → space' X i →∙ space' Y i) ]
--        (((i : Index) →
--          Σ[ coh ∈ ((x : _) → fst (f (succ i)) (fst (map' X i) x)
--                             ≡ fst (map' Y i) (suspFun (fst (f i)) x)) ]
--           Square (coh north) (snd (f (succ i)))
--                  (cong (fst (f (succ i))) (snd (map' X i))) (snd (map' Y i))))

--     GenericPrespectrumMap : ∀ {ℓ' ℓ''}
--       (X : GenericPrespectrum' S ℓ') (Y : GenericPrespectrum' S ℓ'')
--       → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
--     GenericPrespectrumMap X Y =
--       Σ[ f ∈ ((i : Index) → space' X i →∙ space' Y i) ]
--        ((i : Index) → Path (Susp∙ _ →∙ space' Y (succ i))
--                             (f (succ i) ∘∙ map' X i)
--                             (fst (map' Y i) ∘ suspFun (fst (f i)) , snd (map' Y i)))

    -- private
    --   compGenericPrespectrumMap' : ∀ {ℓ' ℓ'' ℓ'''} {X : GenericPrespectrum' S ℓ'}
    --     {Y : GenericPrespectrum' S ℓ''} {Z : GenericPrespectrum' S ℓ'''}
    --     → (f : GenericPrespectrumMap X Y) (g : GenericPrespectrumMap Y Z)
    --     → GenericPrespectrumMap X Z
    --   compGenericPrespectrumMap' {X = X} {Y} {Z} f g .fst i = fst g i ∘∙ fst f i
    --   compGenericPrespectrumMap' {X = X} {Y} {Z} f g .snd i =
    --     ΣPathP (funExt (λ { north → cong (fst g (succ i) .fst) (funExt⁻ (cong fst (snd f i)) north)
    --                                ∙ funExt⁻ (cong fst (snd g i)) north
    --                      ; south → cong (fst g (succ i) .fst) (funExt⁻ (cong fst (snd f i)) south)
    --                                ∙ funExt⁻ (cong fst (snd g i)) south
    --                      ; (merid a k) j → (cong (fst g (succ i) .fst) (funExt⁻ (cong fst (snd f i)) (merid a k))
    --                                       ∙ funExt⁻ (cong fst (snd g i)) (merid (fst (f .fst i) a) k)) j})
    --           , ({!compPath-filler' (λ i₁ →
    --      fst g (succ i) .fst (fst f (succ i) .fst (map' X i .snd i₁)))
    --   ∙
    --   (λ i₁ → fst g (succ i) .fst (fst f (succ i) .snd i₁)) ∙
    --   fst g (succ i) .snd!} ◁ ({!cong snd (snd g i)!} ▷ {!snd (map' Z i)!})))


Prespectrum = GenericPrespectrum ℤ+

Unit∙→ΩUnit∙ : {ℓ : Level} → (Unit∙ {ℓ = ℓ}) →∙ Ω (Unit∙ {ℓ = ℓ})
Unit∙→ΩUnit∙ = (λ {tt* → refl}) , refl

makeℤPrespectrum : (space : ℕ → Pointed ℓ)
                  (map : (i : ℕ) → (space i) →∙ Ω (space (suc i)))
                → Prespectrum ℓ
GenericPrespectrum.space (makeℤPrespectrum space map) (pos n) = space n
GenericPrespectrum.space (makeℤPrespectrum space map) (negsuc n) = Unit∙
GenericPrespectrum.map (makeℤPrespectrum space map) (pos n) = map n
GenericPrespectrum.map (makeℤPrespectrum space map) (negsuc zero) = (λ {tt* → refl}) , refl
GenericPrespectrum.map (makeℤPrespectrum space map) (negsuc (suc n)) = Unit∙→ΩUnit∙

SuspensionPrespectrum : Pointed ℓ → Prespectrum ℓ
SuspensionPrespectrum A = makeℤPrespectrum space map
          where
            space : ℕ → Pointed _
            space zero = A
            space (suc n) = Susp∙ (typ (space n))

            map : (n : ℕ) → _
            map n = toSuspPointed (space n)

asd = Ω→∘∙

module _ {S : SuccStr ℓ} where
  open SuccStr S
  open GenericPrespectrum
  GenericPrespectrumMap : ∀ {ℓ' ℓ''}
    (X : GenericPrespectrum S ℓ') (Y : GenericPrespectrum S ℓ'')
    → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  GenericPrespectrumMap X Y =
    Σ[ f ∈ ((i : Index) → space X i →∙ space Y i) ]
     ((i : Index) → (Ω→ (f (succ i)) ∘∙ map X i) ≡ (map Y i ∘∙ f i))

  private
    compGenericPrespectrumMap' : ∀ {ℓ' ℓ'' ℓ'''} {X : GenericPrespectrum S ℓ'}
      {Y : GenericPrespectrum S ℓ''} {Z : GenericPrespectrum S ℓ'''}
      → (f : GenericPrespectrumMap X Y) (g : GenericPrespectrumMap Y Z)
      → GenericPrespectrumMap X Z
    compGenericPrespectrumMap' {X = X} {Y} {Z} f g .fst i = fst g i ∘∙ fst f i
    compGenericPrespectrumMap' {X = X} {Y} {Z} f g .snd i =
        cong (_∘∙ map X i) (Ω→∘∙ (fst g (succ i)) (fst f (succ i)))
      ∙ ∘∙-assoc (Ω→ (fst g (succ i))) (Ω→ (fst f (succ i))) (map X i)
      ∙∙ cong (Ω→ (fst g (succ i)) ∘∙_) (snd f i)
      ∙∙ (sym (∘∙-assoc (Ω→ (fst g (succ i))) (map Y i) (f .fst i))
      ∙∙ cong (_∘∙ fst f i) (snd g i)
      ∙∙ ∘∙-assoc (map Z i) (fst g i) (fst f i))

    compGenericPrespectrumMapId : ∀ {ℓ' ℓ'' ℓ'''} {X : GenericPrespectrum S ℓ'}
      {Y : GenericPrespectrum S ℓ''} {Z : GenericPrespectrum S ℓ'''}
      → (f : GenericPrespectrumMap X Y) (g : GenericPrespectrumMap Y Z)
      → (i : Index)
        → cong fst (snd (compGenericPrespectrumMap' {X = X} {Y} {Z} f g) i)
         ≡ cong fst (cong (_∘∙ map X i) (Ω→∘∙ (fst g (succ i)) (fst f (succ i))))
         ∙∙ cong fst (cong (Ω→ (fst g (succ i)) ∘∙_) (snd f i))
         ∙∙ cong fst (cong (_∘∙ fst f i) (snd g i))
    compGenericPrespectrumMapId {X = X} {Y} {Z} f g i =
      cong-∙∙ fst _ _ _
      ∙ cong₃ _∙∙_∙∙_ (cong-∙ fst _ _ ∙ sym (rUnit _))
                      refl
                      (cong-∙∙ fst _ _ _ ∙ sym (rUnit _))

  open import Cubical.Data.Sigma
  open import Cubical.Foundations.Pointed.Homogeneous
  open import Cubical.Foundations.Path
  open import Cubical.Foundations.Function

  module _ {ℓ' ℓ''} {X : GenericPrespectrum S ℓ'}
    (Y : GenericPrespectrum S ℓ'')
    (f : GenericPrespectrumMap X Y) where
    strictifySpec : GenericPrespectrum S ℓ''
    strictifySpec .space i .fst = fst (space Y i)
    strictifySpec .space i .snd = fst f i .fst (space X i .snd)
    strictifySpec .map i .fst = Ω→ (idfun _ , sym (snd (fst f (succ i)))) .fst ∘ Y .map i .fst
    strictifySpec .map i .snd = cong (snd (fst f (succ i)) ∙∙_∙∙ sym (snd (fst f (succ i)))) (cong (Y .map i .fst) (fst f i .snd)) ∙ {!∙∙lCancel _!}

  compGenericPrespectrumMap : ∀ {ℓ' ℓ'' ℓ'''} {X : GenericPrespectrum S ℓ'}
    {Y : GenericPrespectrum S ℓ''} {Z : GenericPrespectrum S ℓ'''}
    → (f : GenericPrespectrumMap X Y) (g : GenericPrespectrumMap Y Z)
    → GenericPrespectrumMap X Z
  compGenericPrespectrumMap {X = X} {Y} {Z} f g .fst i = fst g i ∘∙ fst f i
  compGenericPrespectrumMap {X = X} {Y} {Z} f g .snd i j .fst =
           (cong fst (cong (_∘∙ map X i) (Ω→∘∙ (fst g (succ i)) (fst f (succ i))))
         ∙∙ cong fst (cong (Ω→ (fst g (succ i)) ∘∙_) (snd f i))
         ∙∙ cong fst (cong (_∘∙ fst f i) (snd g i))) j
  compGenericPrespectrumMap {X = X} {Y} {Z} f g .snd i j .snd k =
    ((λ  k j → compGenericPrespectrumMapId f g i (~ k) j (space X i .snd))
    ◁ flipSquare (cong snd (compGenericPrespectrumMap' f g .snd i))) k j

  GenericPrespectrumMap≡Lem : ∀ {ℓ' ℓ''}
    {X : GenericPrespectrum S ℓ'} {Y : GenericPrespectrum S ℓ''}
    {f g : GenericPrespectrumMap X Y}
    (h : (i : Index) → fst f i ≡ fst g i)
    (sq : (i : Index) → Square (cong fst (snd f i)) (cong fst (snd g i))
                                (λ j x → sym (h (succ i) j .snd)
                                       ∙∙ (λ k → fst (h (succ i) j) (map X i .fst x k))
                                       ∙∙ h (succ i) j .snd)
                                (funExt (λ x → cong (fst (map Y i))
                                  (funExt⁻ (cong fst (h i)) x))))
    → f ≡ g
  GenericPrespectrumMap≡Lem {f = f} {g} h sq =
    ΣPathP ((funExt h)
     , funExt λ ind → →∙HomogeneousSquare (isHomogeneousPath _ _)
       _ _ _ _ (flipSquare λ i j x → sq ind j i x))

  assocGenericPrespectrumMap : ∀ {ℓ' ℓ'' ℓ''' ℓ''''}
    {X : GenericPrespectrum S ℓ'} {Y : GenericPrespectrum S ℓ''}
    {Z : GenericPrespectrum S ℓ'''} {W : GenericPrespectrum S ℓ''''}
    (f : GenericPrespectrumMap X Y) (g : GenericPrespectrumMap Y Z)
    (h : GenericPrespectrumMap Z W)
    → compGenericPrespectrumMap {X = X} {Y = Y} {Z = W} f
        (compGenericPrespectrumMap {X = Y} {Y = Z} {Z = W} g h)
     ≡ compGenericPrespectrumMap {X = X} {Z} {W}
        (compGenericPrespectrumMap {X = X} {Y} {Z} f g) h
  assocGenericPrespectrumMap {X = X} {Y} {Z} {W = W} f g h = {!!}
    -- GenericPrespectrumMap≡Lem (λ i → ∘∙-assoc (fst h i) (fst g i) (fst f i))
    --   λ i → λ j k x →
    --     gen (fst (fst f i)) (fst (fst g i)) (fst (fst h i))
    --         (fst (fst f (succ i))) (fst (fst g (succ i))) (fst (fst h (succ i)))
    --      _ _ _ (snd (fst f i)) _ (snd (fst g i)) _ (snd (fst h i))
    --          _ (snd (fst f (succ i))) _ (snd (fst g (succ i))) _ (snd (fst h (succ i)))
    --      (map X i) (map Y i) (map Z i) (map W i)
    --      (λ x → funExt⁻ (cong fst (snd f i)) x)
    --      ((λ x → funExt⁻ (cong fst (snd g i)) x))
    --      ((λ x → funExt⁻ (cong fst (snd h i)) x)) x j k
    where
    gen : ∀ {ℓA ℓB ℓC ℓD} {ℓA' ℓB' ℓC' ℓD'} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} {D : Type ℓD}
      {A' : Type ℓA'} {B' : Type ℓB'} {C' : Type ℓC'} {D' : Type ℓD'}
      (f : A → B) (g : B → C) (h : C → D)
      (f' : A' → B') (g' : B' → C') (h' : C' → D')
      (a : A) (a' : A') (b : B) (fp : f a ≡ b) (c : C) (gp : g b ≡ c) (d : D) (hp : h c ≡ d)
      (b' : B') (fp' : f' a' ≡ b') (c' : C') (gp' : g' b' ≡ c') (d' : D') (hp' : h' c' ≡ d')
      (↑A : (A , a) →∙ Ω (A' , a')) (↑B : (B , b) →∙ Ω (B' , b'))
      (↑C : (C , c) →∙ Ω (C' , c')) (↑D : (D , d) →∙ Ω (D' , d'))
      (fid : (x : A) → (sym fp' ∙∙ cong f' (↑A .fst x) ∙∙ fp') ≡ ↑B .fst (f x))
      (gid : (x : B) → (sym gp' ∙∙ cong g' (↑B .fst x) ∙∙ gp') ≡ ↑C .fst (g x))
      (hid : (x : C) → (sym hp' ∙∙ cong h' (↑C .fst x) ∙∙ hp') ≡ ↑D .fst (h x))
      (x : A)
      → Square ((λ i → Ω→∘∙ ((h' , hp') ∘∙ (g' , gp') ) (f' , fp') i .fst (↑A .fst x))
             ∙∙ cong₃ _∙∙_∙∙_ refl (cong (cong (h' ∘ g')) (fid x)) refl
             ∙∙ ((λ i → Ω→∘∙ (h' , hp') (g' , gp') i .fst (↑B .fst (f x)))
             ∙∙ cong₃ _∙∙_∙∙_ refl (cong (cong h') (gid (f x))) refl
             ∙∙ hid (g (f x))))
               (((λ i → Ω→∘∙ ((h' , hp')) ( (g' , gp') ∘∙ (f' , fp')) i .fst (↑A .fst x))
             ∙∙ cong₃ _∙∙_∙∙_ refl (cong (cong h')
                    ((λ k → Ω→∘∙ (g' , gp') (f' , fp') k .fst (↑A .fst x))
                  ∙∙ cong₃ _∙∙_∙∙_ refl (cong (cong g') (fid x)) refl
                  ∙∙ gid (f x))) refl
             ∙∙ hid (g (f x))))
               (λ k → Ω→ (∘∙-assoc (h' , hp') (g' , gp') (f' , fp') k) .fst (↑A .fst x)) refl
    gen {A = A} {B = B} {C = C} f g h f' g' h' a a' = J> (J> (J> (J> (J> (J>
      λ ↑A ↑B ↑C ↑D → {!Ω→∘∙ (h' , refl) (g' , refl)!})))))
      {-
      transport (λ k →
      (fid : (x : A) → (rUnit (cong f' (↑A .fst x)) k) ≡ ↑B .fst (f x))
      (gid : (x : B) → (rUnit (cong g' (↑B .fst x)) k) ≡ ↑C .fst (g x))
      (hid : (x : C) → (rUnit (cong h' (↑C .fst x)) k) ≡ ↑D .fst (h x))
      (x : A) →
      Square ({!!}
           ∙∙ cong₃ _∙∙_∙∙_ refl (cong (cong (h' ∘ g')) (fid x)) refl -- (λ i → rUnit {!λ j → (h' ∘ g') (fid x j i)!} k)
           ∙∙ {!!})
             {!!}
             {!!}
             {!!})
        {!Square!})))))
-}
PrespectrumMap : ∀ {ℓ ℓ'} → Prespectrum ℓ → Prespectrum ℓ' → Type (ℓ-max ℓ ℓ')
PrespectrumMap X Y = GenericPrespectrumMap X Y
