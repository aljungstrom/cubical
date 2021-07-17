{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}

module Cubical.Algebra.Group.EilenbergMacLane.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec; elim to trElim)
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Empty
  renaming (rec to ⊥-rec)
open import Cubical.HITs.Truncation
  renaming (elim to trElim ; rec to trRec ; rec2 to trRec2)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.HITs.Susp
open import Cubical.Functions.Morphism
open import Cubical.Foundations.Path

private
  variable ℓ : Level

  _* = AbGroup→Group

EM-raw : (G : AbGroup ℓ) (n : ℕ) → Type ℓ
EM-raw G zero = fst G
EM-raw G (suc zero) = EM₁ (G *)
EM-raw G (suc (suc n)) = Susp (EM-raw G (suc n))

ptS : {n : ℕ} {G : AbGroup ℓ} → EM-raw G n
ptS {n = zero} {G = G} = AbGroupStr.0g (snd G)
ptS {n = suc zero} {G = G} = embase
ptS {n = suc (suc n)} {G = G} = north

EM-raw-elim : (G : AbGroup ℓ) (n : ℕ) {A : EM-raw G (suc n) → Type ℓ}
            → ((x : _) → isOfHLevel (suc n) (A x) )
            → A ptS
            → (x : _) → A x
EM-raw-elim G zero hlev b = elimProp _ hlev b
EM-raw-elim G (suc n) hlev b north = b
EM-raw-elim G (suc n) {A = A} hlev b south = subst A (merid ptS) b
EM-raw-elim G (suc n) {A = A} hlev b (merid a i) = help a i
  where
  help : (a : _) → PathP (λ i → A (merid a i)) b (subst A (merid ptS) b)
  help = EM-raw-elim G n (λ _ → isOfHLevelPathP' (suc n) (hlev _) _ _)
         λ i → transp (λ j → A (merid ptS (j ∧ i))) (~ i) b

EM : (G : AbGroup ℓ) (n : ℕ) → Type ℓ
EM G zero = EM-raw G zero
EM G (suc zero) = EM-raw G 1
EM G (suc (suc n)) = hLevelTrunc (4 + n) (EM-raw G (suc (suc n)))

0ₖ : {G : AbGroup ℓ} (n : ℕ) → EM G n
0ₖ {G = G} zero = AbGroupStr.0g (snd G)
0ₖ (suc zero) = embase
0ₖ (suc (suc n)) = ∣ ptS ∣

EM∙ : (G : AbGroup ℓ) (n : ℕ) → Pointed ℓ
EM∙ G n = EM G n , (0ₖ n)

hLevelEM : (G : AbGroup ℓ) (n : ℕ) → isOfHLevel (2 + n) (EM G n)
hLevelEM G zero = AbGroupStr.is-set (snd G)
hLevelEM G (suc zero) = emsquash
hLevelEM G (suc (suc n)) = isOfHLevelTrunc (4 + n)

EM-raw→EM : (G : AbGroup ℓ) (n : ℕ) → EM-raw G n → EM G n
EM-raw→EM G zero x = x
EM-raw→EM G (suc zero) x = x
EM-raw→EM G (suc (suc n)) = ∣_∣

EM-elim : {G : AbGroup ℓ} (n : ℕ) {A : EM G n → Type ℓ}
        → ((x : _) → isOfHLevel (2 + n) (A x))
        → ((x : EM-raw G n) → A (EM-raw→EM G n x))
        → (x : _) → A x
EM-elim zero hlev hyp x = hyp x
EM-elim (suc zero) hlev hyp x = hyp x
EM-elim (suc (suc n)) hlev hyp = trElim (λ _ → hlev _) hyp