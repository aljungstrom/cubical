{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Homotopy.ConnectedSn where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Fibration
open import Cubical.Data.Nat
open import Cubical.Data.Prod hiding (map)
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec)
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.Data.Bool
open import Cubical.Data.Unit

open import Cubical.Homotopy.Connected using (isConnected ; isConnectedFun)


isIsoPrecompose 

{-
module elim {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
  private
    inv : ∀ {ℓ'''} (n : HLevel) (P : B → TypeOfHLevel ℓ''' (suc n))
        → ((a : A) → P (f a) .fst)
        → (b : B)
        → hLevelTrunc (suc n) (fiber f b) → P b .fst
    inv n P t b =
      Trunc.rec
        (P b .snd)
        (λ {(a , p) → subst (fst ∘ P) p (t a)})

  isIsoPrecompose : ∀ {ℓ'''} (n : ℕ) (P : B → TypeOfHLevel ℓ''' n)
                   → isConnectedFun n f
                   → Iso ((b : B) → P b .fst) ((a : A) → P (f a) .fst)
  isIsoPrecompose zero P fConn = isContr→Iso (isOfHLevelΠ _ (λ b → P b .snd)) (isOfHLevelΠ _ λ a → P (f a) .snd)
  Iso.fun (isIsoPrecompose (suc n) P fConn) = _∘ f
  Iso.inv (isIsoPrecompose (suc n) P fConn) t b = inv n P t b (fConn b .fst)
  Iso.rightInv (isIsoPrecompose (suc n) P fConn) t =
    funExt λ a → cong (inv n P t (f a)) (fConn (f a) .snd ∣ a , refl ∣)
               ∙ substRefl {B = fst ∘ P} (t a)
  Iso.leftInv (isIsoPrecompose (suc n) P fConn) s =
    funExt λ b →
          Trunc.elim
            {B = λ d → inv n P (s ∘ f) b d ≡ s b}
            (λ _ → isOfHLevelPath (suc n) (P b .snd) _ _)
            (λ {(a , p) i → transp (λ j → P (p (j ∨ i)) .fst) i (s (p i))})
            (fConn b .fst)

  isEquivPrecompose : ∀ {ℓ'''} (n : ℕ) (P : B → TypeOfHLevel ℓ''' n)
                   → isConnectedFun n f
                   → isEquiv (λ(s : (b : B) → P b .fst) → s ∘ f)
  isEquivPrecompose zero P fConn = isoToIsEquiv theIso
    where
    theIso : Iso ((b : B) → P b .fst) ((a : A) → P (f a) .fst)
    Iso.fun theIso = λ(s : (b : B) → P b .fst) → s ∘ f
    Iso.inv theIso = λ _ b → P b .snd .fst
    Iso.rightInv theIso g = funExt λ x → P (f x) .snd .snd (g x)
    Iso.leftInv theIso g = funExt λ x → P x .snd .snd (g x)
  isEquivPrecompose (suc n) P fConn = isoToIsEquiv (isIsoPrecompose (suc n) P fConn)

  isConnectedPrecompose : (n : ℕ) → ((P : B → TypeOfHLevel (ℓ-max ℓ ℓ') n)
                                    → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f))
                       → isConnectedFun n f
  isConnectedPrecompose zero P→sect b = isContrUnit*
  isConnectedPrecompose (suc n) P→sect b = c n P→sect b , λ y →  sym (fun n P→sect b y)
    where
    P : (n : HLevel) → ((P : B → TypeOfHLevel ℓ (suc n))
     → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f))
     → B → Type _
    P n s b = hLevelTrunc (suc n) (fiber f b)

    c : (n : HLevel) → ((P : B → TypeOfHLevel (ℓ-max ℓ ℓ') (suc n))
     → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f)) → (b : B)
     → hLevelTrunc (suc n) (fiber f b)
    c n s = (s λ b → (hLevelTrunc (suc n) (fiber f b) , isOfHLevelTrunc _)) .fst
              λ a → ∣ a , refl ∣

    fun : (n : HLevel) (P→sect : ((P : B → TypeOfHLevel (ℓ-max ℓ ℓ') (suc n))
                     → hasSection λ(s : (b : B) → P b .fst) → s ∘ f))
      → (b : B) (w : (hLevelTrunc (suc n) (fiber f b)))
      → w ≡ c n P→sect b
    fun n P→sect b = Trunc.elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc _) _ _)
                                       λ a → J (λ b p → ∣ (fst a) , p ∣ ≡ c n P→sect b)
                                               (c* (fst a))
                                               (snd a)
        where
        c* : ((a : A) → ∣ (a , refl {x = f a}) ∣ ≡ c n P→sect (f a))
        c* a = sym (cong (λ x → x a) (P→sect (λ b → hLevelTrunc (suc n) (fiber f b) , isOfHLevelTrunc _) .snd λ a → ∣ a , refl ∣))

-}
