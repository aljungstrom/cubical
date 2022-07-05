{-# OPTIONS --safe #-}

module Cubical.Categories.Closed where
open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Morphism

open import Cubical.Foundations.Pointed
open import Cubical.HITs.SmashProduct
-- open import Cubical.Categories.Category.Precategory
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.NaturalTransformation

open import Cubical.Data.Sigma renaming (_×_ to _×'_) 
open Functor
open Category

restrictₗ : 
  ∀ {ℓC ℓC' ℓD ℓD' ℓE ℓE'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  → Functor (C × D) E → (c : Category.ob C) → Functor D E
F-ob (restrictₗ F c) d = F-ob F (c , d)
F-hom (restrictₗ {C = C} F c) f = F-hom F (Category.id C , f)
F-id (restrictₗ {C = C} F c) = F-id F
F-seq (restrictₗ {C = C} F c) f g =
    cong (F-hom F) (ΣPathP (sym (⋆IdL C (Category.id C)) , refl))
  ∙ F-seq F (Category.id C , f) (Category.id C , g)

diagFunctor : 
  ∀ {ℓC ℓC' ℓD ℓD' ℓE ℓE'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  → Functor (C × D) E
  → Functor {!!} {!!}
diagFunctor = {!!}

open import Cubical.Data.Nat
data one : Type ℓ-zero where
  tt : one

open import Cubical.Core.Primitives
-- Agda.Prmitive.SSet ℓ-zero

data EqT {ℓ : Level} {A : Type ℓ} (x : A) : A → Type ℓ where
  ref : EqT x x   


Cub : ?
Cub = ?

CCC : ℕ → Type (ℓ-suc ℓ-zero)
CC↓ : (n : ℕ) → (p : CCC (suc n)) → CCC n 
CCC zero = Type ℓ-zero
CCC (suc n) = {!!}
CC↓ zero p = {!!}
CC↓ (suc n) p = {!!}


CC : (n : ℕ) → Type ℓ-zero
CC zero = one
CC (suc n) = {!!} -- CC-help
  where
  ceb : {!!} -- Partial {!!} {!!} → {!!}
  ceb = {!!}

-- constFunctor : ∀ {ℓC ℓC' ℓD ℓD'} (C : Category ℓC ℓC') (D : Category ℓD ℓD') (d : ob D)
--   → Functor C D
-- F-ob (constFunctor C D d) _ = d
-- F-hom (constFunctor C D d) _ = Category.id D
-- F-id (constFunctor C D d) = refl
-- F-seq (constFunctor C D d) _ _ = sym (⋆IdL D (Category.id D))

-- idFunctor : ∀ {ℓ ℓ'} → (C : Category ℓ ℓ') → Functor C C
-- Functor.F-ob (idFunctor C) x = x
-- Functor.F-hom (idFunctor C) x = x
-- Functor.F-id (idFunctor C) = refl
-- Functor.F-seq (idFunctor C) p q = refl

-- record ClosedPrecat ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
--   field
--     C : Category ℓ ℓ'
--     [_,_]' : Functor ((C ^op) × C) C
--     Unit : Category.ob C

--     i : NatIso (idFunctor C) (restrictₗ {C = C ^op} {D = C} {E = C} [_,_]' Unit)

--     j : NatTrans (constFunctor C C Unit) {!!} 


--   --   ob : Type ℓ
--   --   Hom[_,_] : ob → ob → Type ℓ'
--   --   id   : ∀ {x} → Hom[ x , x ]
--   --   _⋆_  : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ]) → Hom[ x , z ]
--   --   ⋆IdL : ∀ {x y} (f : Hom[ x , y ]) → id ⋆ f ≡ f
--   --   ⋆IdR : ∀ {x y} (f : Hom[ x , y ]) → f ⋆ id ≡ f
--   --   ⋆Assoc : ∀ {u v w x} (f : Hom[ u , v ]) (g : Hom[ v , w ]) (h : Hom[ w , x ]) → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)

--   -- -- composition: alternative to diagramatic order
--   -- _∘_ : ∀ {x y z} (g : Hom[ y , z ]) (f : Hom[ x , y ]) → Hom[ x , z ]
--   -- g ∘ f = f ⋆ g
