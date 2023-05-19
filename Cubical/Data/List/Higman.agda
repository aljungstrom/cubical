{-# OPTIONS --safe #-}
module Cubical.Data.List.Higman where

open import Agda.Builtin.List
open import Cubical.Core.Everything
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary
open import Cubical.Functions.Embedding
open import Cubical.HITs.SequentialColimit
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset


open import Cubical.Data.List.Base
open import Cubical.Data.Maybe
open import Cubical.Data.Sum
open import Cubical.Data.List.Properties

module _ {ℓ ℓ' : Level} {U : Type ℓ} (X B : ℙ U) (R : U → U → Type ℓ') where
  X* : Type _
  X* = Σ[ x ∈ U ] X x .fst

  data Cl : U → Type (ℓ-max ℓ ℓ') where
    ink : (x : X*) → B (fst x) .fst → Cl (fst x)
    cl : (x : X*) → ((y : X*) → R (fst x) (fst y) → Cl (fst y)) → Cl (fst x)

  Closure : U → hProp _
  fst (Closure u) = ∥ Cl u ∥₁
  snd (Closure u) = squash₁
  
module _ {ℓ ℓ' : Level} {U : Type ℓ}
  (X BX Y BY  : ℙ U) (R Q : U → U → Type ℓ)
  where
  -- _×h_ : ℙ U → ℙ U → ℙ (U × U)
  -- fst ((X ×h Y) (u , u')) = X u .fst × Y u' .fst
  -- snd ((X ×h Y) x) = isOfHLevel× 1 (snd (X _)) (snd (Y _))

  _×h_ : ℙ U → ℙ U → ℙ U
  fst ((X ×h Y) x) = X x .fst × Y x .fst
  snd ((X ×h Y) x) = isOfHLevel× 1 (snd (X _)) (snd (Y _))

  R* : U → U → Type _
  R* A B = Σ[ T ∈ U ] R A T × Q T B


  CL→ : (u : U) → Cl X BX R u → Cl Y BY Q u
    → Cl (X ×h Y) (BX ×h BY) R* u
  CL→ .(fst x) (ink x bx) (ink (.(fst x) , y) by) =
    ink (fst x , (x .snd) , y) (bx , by)
  CL→ .(fst x) (ink x bx) (cl (.(fst x) , y) F) =
    cl ((fst x) , x .snd , y) λ t r
    → CL→ (fst t)
        (ink (fst t , fst (snd t)) {!F ? ?!})
        (F (fst t , t .snd .snd)
          {!!})
    where
    hh : (x : _) → Cl Y BY Q (fst x) → BY (fst x) .fst
    hh x (ink (.(fst x) , snd₁) x₁) = x₁
    hh x (cl (.(fst x) , snd₁) x₁) = hh x (x₁ ((x .fst) , snd₁) {!!})
  {-
    cl (fst x , (x .snd) , y) λ {(a , xa , ya) (t , rt , qt)
      → CL→ a {!!} (F (a , ya) {!q!}) -- CL→ a ({!!}) (F (a , ya) {!qt!})
      } -}
  CL→ .(fst x) (cl x x₁) y = {!!}


--   R' : U × U → U × U' → Type _
--   R' (A , A') (B , B') = {!R A B!} -- R A B × Q A' B'


--   CL→' : (u : U) (u' : U') → Cl X BX R u → Cl Y BY Q u'
--     → Cl (X ×h Y) (BX ×h BY) R* (u , u')
--   CL→' .(fst u) u' (ink u t) = {!!}
--   CL→' .(fst x) u' (cl x x₁) y = {!!}

--   CL→ : (u : U) (u' : U') → Cl X BX R u → Cl Y BY Q u'
--     → Cl (X ×h Y) (BX ×h BY) R* (u , u')
--   CL→ .(fst u) .(fst u') (ink u bu) (ink u' bu') =
--     ink ((fst u , fst u') , (u .snd) , snd u') (bu , bu')
--   CL→ .(fst u) .(fst v) (ink u bu) (cl v t) =
--     cl ((u .fst , v .fst) , u .snd , v .snd)
--        λ { ((u1 , u2) , a , b) (r1 , r2)
--        → CL→ u1 u2 (ink (u1 , a) {!!}) (t (u2 , b) r2)}
--   CL→ .(fst x) u' (cl x x₁) b = {!!}
  


-- -- subtypeOf : ∀ {ℓ} → Type ℓ → Type (ℓ-suc ℓ)
-- -- subtypeOf {ℓ} A = Σ[ X ∈ Type ℓ ] (X ↪ A)

-- -- isOfHLevel-subtype : ∀ {ℓ} {A : Type ℓ} (X : subtypeOf A) (n : ℕ)
-- --   → isOfHLevel (suc n) A → isOfHLevel (suc n) (fst X) 
-- -- isOfHLevel-subtype X n hlev =
-- --   Embedding-into-hLevel→hLevel n (snd X) hlev

-- -- infList : ∀ {ℓ} → Type ℓ → Type ℓ
-- -- infList A = ℕ → A

-- -- shift-infList : ∀ {ℓ} {A : Type ℓ} → infList A → A → infList A
-- -- shift-infList x a zero = a
-- -- shift-infList x a (suc n) = x n

-- -- List→infList : ∀ {ℓ} {A : Type ℓ} → List A → Maybe (infList A)
-- -- List→infList [] = nothing
-- -- List→infList (x ∷ []) = just λ _ → x
-- -- List→infList (x ∷ x₁ ∷ x₂) = {!!}

-- -- AllList : ∀ {ℓ} → Type ℓ → Type ℓ
-- -- AllList A = List A ⊎ (ℕ → A)



-- -- module _ {ℓ : Level} (P : Type ℓ) (setP : isSet P) (X' : subtypeOf (List P))
-- --   where
-- --   X = fst X'

-- --   data barCompletion (B' : subtypeOf (List P)) : Type ℓ where
-- --     ins : fst B' → barCompletion B'
-- --     k : (l : List P) → ((b : P) → ∃[ lp ∈ fst B' ] ((b ∷ l)
-- --                                            ≡ B' .snd .fst lp))
-- --       → barCompletion B'
-- --     glueit : (b : fst B') (pf : _) → ins b ≡ k (snd B' .fst b) pf
-- --     trunc : isSet (barCompletion B')

-- --   barCompletion→Set : ∀ {ℓ} {B' : subtypeOf (List P)}
-- --     → {C : barCompletion B' → Type ℓ}
-- --     → ((x : _) → isSet (C x))
-- --     → (ins' : (b : fst B') → C (ins b))
-- --     → (k' : (l : _) (pf : _) → C (k l pf))
-- --     → ((l : _) (pf : _) → PathP (λ i → C (glueit l pf i)) (ins' l) (k' (snd B' .fst l) pf))
-- --     → (x : _) → C x
-- --   barCompletion→Set {B' = B , s} {C = C} st ins' k' gl (ins x) = ins' x
-- --   barCompletion→Set {B' = B , s} {C = C} st ins' k' gl (k l x) = k' l x
-- --   barCompletion→Set {B' = B , s} {C = C} st ins' k' gl (glueit b pf i) = gl b pf i
-- --   barCompletion→Set {B' = B , s} {C = C} st ins' k' gl (trunc x y p q i j) =
-- --     help i j
-- --     where
-- --     help : SquareP (λ i j → C (trunc x y p q i j))
-- --              (λ j → barCompletion→Set st ins' k' gl (p j))
-- --              (λ j → barCompletion→Set st ins' k' gl (q j))
-- --              refl
-- --              refl
-- --     help = toPathP (isOfHLevelPath' 0 (isOfHLevelPathP' 1 (st _) _ _) _ _ .fst)

-- --   barCompletion→Prop : ∀ {ℓ} {B' : subtypeOf (List P)}
-- --     → {C : barCompletion B' → Type ℓ}
-- --     → ((x : _) → isProp (C x))
-- --     → (ins' : (b : fst B') → C (ins b))
-- --     → (k' : (l : _) (pf : _) → C (k l pf))
-- --     → (x : _) → C x
-- --   barCompletion→Prop pr ins' k' =
-- --     barCompletion→Set (λ _ → isProp→isSet (pr _))
-- --       ins' k' λ _ _ → isProp→PathP (λ _ → pr _) _ _


-- --   barCompletion↪ : (B' : subtypeOf (List P)) → barCompletion B' ↪ List P
-- --   fst (barCompletion↪ B') = barCompletion→Set (λ _ → isOfHLevelList 0 setP)
-- --     (snd B' .fst)
-- --     (λ l _ → l)
-- --     λ _ _ → refl
-- --   snd (barCompletion↪ B') = barCompletion→Prop (λ _ → isPropΠ λ _ → isPropIsEquiv _)
-- --     (λ b → barCompletion→Prop (λ _ → isPropIsEquiv _)
-- --              (λ b' → propBiimpl→Equiv (trunc _ _) (isOfHLevelList 0 setP _ _) _ (λ p → cong ins (invEq (_ , B' .snd .snd _ _) p)) .snd)
-- --              λ l pf → propBiimpl→Equiv (trunc _ _) (isOfHLevelList 0 setP _ _) _ (λ q → J (λ l _ → (pf :  (b₁ : P) →
-- --       ∃-syntax (fst B') (λ lp → b₁ ∷ l ≡ B' .snd .fst lp)) → ins b ≡ k l pf) (λ _ → glueit b _) q pf) .snd)
-- --     {!!}
-- --   {- propBiimpl→Equiv (trunc _ _) (isOfHLevelList 0 setP _ _)
-- --     _ {!!} .snd
-- -- -}

-- --   se' : subtypeOf (List P) → ℕ → subtypeOf (List P)
-- --   se' B' zero = {!!} , {!!}
-- --   se' B' (suc n) = {!!}

-- --   se : subtypeOf (List P) → Sequence ℓ
-- --   Sequence.space (se B') zero = barCompletion B'
-- --   Sequence.space (se B') (suc n) = barCompletion {!!}
-- --   Sequence.map (se B') = {!!}


-- --   barComplSubtype : Type _
-- --   barComplSubtype = Lim→ {!!}
  
