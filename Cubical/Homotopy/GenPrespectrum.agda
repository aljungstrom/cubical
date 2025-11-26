{-
  This uses ideas from Floris van Doorn's phd thesis and the code in
  https://github.com/cmu-phil/Spectral/blob/master/spectrum/basic.hlean
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Homotopy.GenPrespectrum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.ArrowType2
open import Cubical.Data.Unit.Pointed

open import Cubical.Structures.Successor
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor


open import Cubical.Data.Nat
open import Cubical.Data.Int

open import Cubical.HITs.Susp

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓD ℓT : Level

-- open WildCat
open WildFunctor

-- Σ I A → Σ I B → Σ I C → Σ I D
{-
***********
***********
**A →  B**
**↓     ↓**
**C  → D**
***********
***********
-}

module _ {A B C : Type ℓ} (f : A → B) (r : A → C) where
  T : Type _
  T = Σ[ g ∈ (B → C) ] ((a : A) → g (f a) ≡ r a)

  AA : {!!}
  AA = {!!}

  S' : Type _
  S' = Σ[ h ∈ {!Σ A ?!} ] {!!}

module _ (C : WildCat ℓD ℓT) (Ω : WildFunctor C C) (S : SuccStr ℓ)  where
  open SuccStr S
  open WildCat C

  record GenericPrespectrum : Type (ℓ-max ℓ (ℓ-max ℓD ℓT)) where
    field
      space : Index → ob
      map : (i : Index) → Hom[ space i , F-ob Ω (space (succ i)) ]

  open GenericPrespectrum
  GenericPrespectrumMap :
    (X : GenericPrespectrum) (Y : GenericPrespectrum)
    → Type (ℓ-max ℓT ℓ)
  GenericPrespectrumMap X Y =
    Σ[ f ∈ ((i : Index) → Hom[ space X i , space Y i ]) ]
     ((i : Index) → f i ⋆⟨ C ⟩ map Y i ≡ map X i ⋆⟨ C ⟩ F-hom Ω (f (succ i)))

  compPrespectrumMap : {X Y Z : GenericPrespectrum}
    (f : GenericPrespectrumMap X Y) (g : GenericPrespectrumMap Y Z)
      → GenericPrespectrumMap X Z
  compPrespectrumMap (f , fc) (g , gc) .fst i = f i ⋆⟨ C ⟩ g i
  compPrespectrumMap {X = X} {Y} {Z} (f , fc) (g , gc) .snd i =
      (⋆Assoc (f i) (g i) (map Z i)
    ∙ cong (f i ⋆_) (gc i))
    ∙ (sym (⋆Assoc (f i) (map Y i) (Ω .F-hom (g (succ i)))) 
    ∙ cong (_⋆ Ω .F-hom (g (succ i))) (fc i))
    ∙ (⋆Assoc (map X i) (Ω .F-hom (f (succ i))) (Ω .F-hom (g (succ i)))
    ∙ cong (map X i ⋆_) (sym (F-seq Ω (f (succ i)) (g (succ i)))))

  idPrespectrumMap : {X : GenericPrespectrum}
    → GenericPrespectrumMap X X
  idPrespectrumMap .fst i = WildCat.id C
  idPrespectrumMap {X = X} .snd i =
      (WildCat.⋆IdL C (map X i)
    ∙ sym (WildCat.⋆IdR C (map X i)))
    ∙ cong (map X i ⋆_) (sym (F-id Ω))

module _ {ℓA : Level} (S : SuccStr ℓ) where
  open SuccStr S

  GenArrowPrespectrum = GenericPrespectrum (ArrowWildCat ℓA) ΩArrowFunctor S
  GenArrowPrespectrumMap = GenericPrespectrumMap (ArrowWildCat ℓA) ΩArrowFunctor S
  open WildCat

  compPrespectrumMap'Fst : {X Y Z : GenArrowPrespectrum}
    (f : GenArrowPrespectrumMap X Y) (g : GenArrowPrespectrumMap Y Z)
      → (i : Index) (x : GenericPrespectrum.space X i .fst)
      → Σ[ h ∈ GenericPrespectrum.space Z i .fst ]
          (GenericPrespectrum.space X i .snd x
        → GenericPrespectrum.space Z i .snd h)
  compPrespectrumMap'Fst f g i x .fst = fst (fst g i (fst (fst f i x)))
  compPrespectrumMap'Fst f g i x .snd a = snd (fst g i (fst f i x .fst)) ((snd (fst f i x) a))

  compPrespectrumMap' : {X Y Z : GenArrowPrespectrum}
    (f : GenArrowPrespectrumMap X Y) (g : GenArrowPrespectrumMap Y Z)
      → GenArrowPrespectrumMap X Z
  compPrespectrumMap' f g .fst i x = compPrespectrumMap'Fst f g i x
  compPrespectrumMap' f g .snd i =
       cong (compArrowHom (fst f i)) (snd g i)
     ∙ cong (λ p → compArrowHom p (ΩArrow→ (fst g (succ i)))) (snd f i) 

  idPrespectrumMap' : {X : GenArrowPrespectrum}
    → GenArrowPrespectrumMap X X
  idPrespectrumMap' .fst i x .fst = x
  idPrespectrumMap' .fst i x .snd a = a
  idPrespectrumMap' .snd i = refl

  GenArrowPrespectrumWildCat : WildCat (ℓ-max ℓ (ℓ-suc ℓA)) (ℓ-max ℓ ℓA)
  GenArrowPrespectrumWildCat .ob = GenArrowPrespectrum
  GenArrowPrespectrumWildCat .Hom[_,_] =
    GenericPrespectrumMap (ArrowWildCat ℓA) ΩArrowFunctor S
  GenArrowPrespectrumWildCat .WildCat.id = idPrespectrumMap'
  GenArrowPrespectrumWildCat ._⋆_ = compPrespectrumMap'
  GenArrowPrespectrumWildCat .⋆IdL f =
    ΣPathP (refl , (funExt (λ i → sym (rUnit (snd f i)))))
  GenArrowPrespectrumWildCat .⋆IdR f =
    ΣPathP (refl , (funExt (λ i → sym (lUnit (snd f i)))))
  GenArrowPrespectrumWildCat .⋆Assoc f g h =
    ΣPathP (refl , funExt λ i
    → cong₂ _∙_ refl (cong-∙ (λ P → compArrowHom P (ΩArrow→ (fst h (succ i))))
                      (λ i₁ x₁ → compArrowHom (fst f i) (snd g i i₁) x₁)
                       λ i₁ → compArrowHom (snd f i i₁)
                      (ΩArrow→ (fst g (succ i))))
     ∙ assoc _ _ _
     ∙ cong₂ _∙_ (sym (cong-∙ (compArrowHom (fst f i)) _ _)) refl)

  
  



  PentagonPrespectrum : pentagonHom GenArrowPrespectrumWildCat
  PentagonPrespectrum {a = a} {b} {c} {d} {e} f g h j =
    {!ΣSquareP ?!} -- {!snd f !} ◁ {!cong ΣPathP ?!}

-- record GenericPrespectrum' (S : SuccStr ℓ) (ℓ' : Level) : Type (ℓ-max (ℓ-suc ℓ') ℓ) where
--   open SuccStr S
--   field
--     space' : Index → Pointed ℓ'
--     map' : (i : Index) → (Susp∙ (fst (space' i)) →∙ space' (succ i))

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

--     private
--       compGenericPrespectrumMap' : ∀ {ℓ' ℓ'' ℓ'''} {X : GenericPrespectrum' S ℓ'}
--         {Y : GenericPrespectrum' S ℓ''} {Z : GenericPrespectrum' S ℓ'''}
--         → (f : GenericPrespectrumMap X Y) (g : GenericPrespectrumMap Y Z)
--         → GenericPrespectrumMap X Z
--       compGenericPrespectrumMap' {X = X} {Y} {Z} f g .fst i = fst g i ∘∙ fst f i
--       compGenericPrespectrumMap' {X = X} {Y} {Z} f g .snd i =
--         ΣPathP (funExt (λ { north → cong (fst g (succ i) .fst) (funExt⁻ (cong fst (snd f i)) north)
--                                    ∙ funExt⁻ (cong fst (snd g i)) north
--                          ; south → cong (fst g (succ i) .fst) (funExt⁻ (cong fst (snd f i)) south)
--                                    ∙ funExt⁻ (cong fst (snd g i)) south
--                          ; (merid a k) j → (cong (fst g (succ i) .fst) (funExt⁻ (cong fst (snd f i)) (merid a k))
--                                           ∙ funExt⁻ (cong fst (snd g i)) (merid (fst (f .fst i) a) k)) j})
--               , ({!compPath-filler' (λ i₁ →
--          fst g (succ i) .fst (fst f (succ i) .fst (map' X i .snd i₁)))
--       ∙
--       (λ i₁ → fst g (succ i) .fst (fst f (succ i) .snd i₁)) ∙
--       fst g (succ i) .snd!} ◁ ({!cong snd (snd g i)!} ▷ {!snd (map' Z i)!})))


-- -- Prespectrum = GenericPrespectrum ℤ+

-- -- Unit∙→ΩUnit∙ : {ℓ : Level} → (Unit∙ {ℓ = ℓ}) →∙ Ω (Unit∙ {ℓ = ℓ})
-- -- Unit∙→ΩUnit∙ = (λ {tt* → refl}) , refl

-- -- makeℤPrespectrum : (space : ℕ → Pointed ℓ)
-- --                   (map : (i : ℕ) → (space i) →∙ Ω (space (suc i)))
-- --                 → Prespectrum ℓ
-- -- GenericPrespectrum.space (makeℤPrespectrum space map) (pos n) = space n
-- -- GenericPrespectrum.space (makeℤPrespectrum space map) (negsuc n) = Unit∙
-- -- GenericPrespectrum.map (makeℤPrespectrum space map) (pos n) = map n
-- -- GenericPrespectrum.map (makeℤPrespectrum space map) (negsuc zero) = (λ {tt* → refl}) , refl
-- -- GenericPrespectrum.map (makeℤPrespectrum space map) (negsuc (suc n)) = Unit∙→ΩUnit∙

-- -- SuspensionPrespectrum : Pointed ℓ → Prespectrum ℓ
-- -- SuspensionPrespectrum A = makeℤPrespectrum space map
-- --           where
-- --             space : ℕ → Pointed _
-- --             space zero = A
-- --             space (suc n) = Susp∙ (typ (space n))

-- --             map : (n : ℕ) → _
-- --             map n = toSuspPointed (space n)

-- -- asd = Ω→∘∙

-- -- module _ {S : SuccStr ℓ} where
-- --   open SuccStr S
-- --   open GenericPrespectrum
-- --   GenericPrespectrumMap : ∀ {ℓ' ℓ''}
-- --     (X : GenericPrespectrum S ℓ') (Y : GenericPrespectrum S ℓ'')
-- --     → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
-- --   GenericPrespectrumMap X Y =
-- --     Σ[ f ∈ ((i : Index) → space X i →∙ space Y i) ]
-- --      ((i : Index) → (Ω→ (f (succ i)) ∘∙ map X i) ≡ (map Y i ∘∙ f i))

-- --   private
-- --     compGenericPrespectrumMap' : ∀ {ℓ' ℓ'' ℓ'''} {X : GenericPrespectrum S ℓ'}
-- --       {Y : GenericPrespectrum S ℓ''} {Z : GenericPrespectrum S ℓ'''}
-- --       → (f : GenericPrespectrumMap X Y) (g : GenericPrespectrumMap Y Z)
-- --       → GenericPrespectrumMap X Z
-- --     compGenericPrespectrumMap' {X = X} {Y} {Z} f g .fst i = fst g i ∘∙ fst f i
-- --     compGenericPrespectrumMap' {X = X} {Y} {Z} f g .snd i =
-- --         cong (_∘∙ map X i) (Ω→∘∙ (fst g (succ i)) (fst f (succ i)))
-- --       ∙ ∘∙-assoc (Ω→ (fst g (succ i))) (Ω→ (fst f (succ i))) (map X i)
-- --       ∙∙ cong (Ω→ (fst g (succ i)) ∘∙_) (snd f i)
-- --       ∙∙ (sym (∘∙-assoc (Ω→ (fst g (succ i))) (map Y i) (f .fst i))
-- --       ∙∙ cong (_∘∙ fst f i) (snd g i)
-- --       ∙∙ ∘∙-assoc (map Z i) (fst g i) (fst f i))

-- --     compGenericPrespectrumMapId : ∀ {ℓ' ℓ'' ℓ'''} {X : GenericPrespectrum S ℓ'}
-- --       {Y : GenericPrespectrum S ℓ''} {Z : GenericPrespectrum S ℓ'''}
-- --       → (f : GenericPrespectrumMap X Y) (g : GenericPrespectrumMap Y Z)
-- --       → (i : Index)
-- --         → cong fst (snd (compGenericPrespectrumMap' {X = X} {Y} {Z} f g) i)
-- --          ≡ cong fst (cong (_∘∙ map X i) (Ω→∘∙ (fst g (succ i)) (fst f (succ i))))
-- --          ∙∙ cong fst (cong (Ω→ (fst g (succ i)) ∘∙_) (snd f i))
-- --          ∙∙ cong fst (cong (_∘∙ fst f i) (snd g i))
-- --     compGenericPrespectrumMapId {X = X} {Y} {Z} f g i =
-- --       cong-∙∙ fst _ _ _
-- --       ∙ cong₃ _∙∙_∙∙_ (cong-∙ fst _ _ ∙ sym (rUnit _))
-- --                       refl
-- --                       (cong-∙∙ fst _ _ _ ∙ sym (rUnit _))

-- --   open import Cubical.Data.Sigma
-- --   open import Cubical.Foundations.Pointed.Homogeneous
-- --   open import Cubical.Foundations.Path
-- --   open import Cubical.Foundations.Function

-- --   module _ {ℓ' ℓ''} {X : GenericPrespectrum S ℓ'}
-- --     (Y : GenericPrespectrum S ℓ'')
-- --     (f : GenericPrespectrumMap X Y) where
-- --     strictifySpec : GenericPrespectrum S ℓ''
-- --     strictifySpec .space i .fst = fst (space Y i)
-- --     strictifySpec .space i .snd = fst f i .fst (space X i .snd)
-- --     strictifySpec .map i .fst = Ω→ (idfun _ , sym (snd (fst f (succ i)))) .fst ∘ Y .map i .fst
-- --     strictifySpec .map i .snd = cong (snd (fst f (succ i)) ∙∙_∙∙ sym (snd (fst f (succ i)))) (cong (Y .map i .fst) (fst f i .snd)) ∙ {!∙∙lCancel _!}

-- --   compGenericPrespectrumMap : ∀ {ℓ' ℓ'' ℓ'''} {X : GenericPrespectrum S ℓ'}
-- --     {Y : GenericPrespectrum S ℓ''} {Z : GenericPrespectrum S ℓ'''}
-- --     → (f : GenericPrespectrumMap X Y) (g : GenericPrespectrumMap Y Z)
-- --     → GenericPrespectrumMap X Z
-- --   compGenericPrespectrumMap {X = X} {Y} {Z} f g .fst i = fst g i ∘∙ fst f i
-- --   compGenericPrespectrumMap {X = X} {Y} {Z} f g .snd i j .fst =
-- --            (cong fst (cong (_∘∙ map X i) (Ω→∘∙ (fst g (succ i)) (fst f (succ i))))
-- --          ∙∙ cong fst (cong (Ω→ (fst g (succ i)) ∘∙_) (snd f i))
-- --          ∙∙ cong fst (cong (_∘∙ fst f i) (snd g i))) j
-- --   compGenericPrespectrumMap {X = X} {Y} {Z} f g .snd i j .snd k =
-- --     ((λ  k j → compGenericPrespectrumMapId f g i (~ k) j (space X i .snd))
-- --     ◁ flipSquare (cong snd (compGenericPrespectrumMap' f g .snd i))) k j

-- --   GenericPrespectrumMap≡Lem : ∀ {ℓ' ℓ''}
-- --     {X : GenericPrespectrum S ℓ'} {Y : GenericPrespectrum S ℓ''}
-- --     {f g : GenericPrespectrumMap X Y}
-- --     (h : (i : Index) → fst f i ≡ fst g i)
-- --     (sq : (i : Index) → Square (cong fst (snd f i)) (cong fst (snd g i))
-- --                                 (λ j x → sym (h (succ i) j .snd)
-- --                                        ∙∙ (λ k → fst (h (succ i) j) (map X i .fst x k))
-- --                                        ∙∙ h (succ i) j .snd)
-- --                                 (funExt (λ x → cong (fst (map Y i))
-- --                                   (funExt⁻ (cong fst (h i)) x))))
-- --     → f ≡ g
-- --   GenericPrespectrumMap≡Lem {f = f} {g} h sq =
-- --     ΣPathP ((funExt h)
-- --      , funExt λ ind → →∙HomogeneousSquare (isHomogeneousPath _ _)
-- --        _ _ _ _ (flipSquare λ i j x → sq ind j i x))
