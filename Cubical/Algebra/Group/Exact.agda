{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Exact where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec)
open import Cubical.Algebra.Group.GroupPath

open import Cubical.Algebra.Group.Instances.Unit

open import Cubical.Structures.Successor
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (Unit)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Vec

open SuccStr

funSeqFin : {ℓ : Level} (n : ℕ)
         (Gr :  Fin (suc n) → Group ℓ)
       → Type ℓ
funSeqFin n Gr = (k : Fin n) → GroupHom (Gr (Fin↪sucFin k)) (Gr (sucFin k))

funSeqFinTail : {ℓ : Level} (n : ℕ)
         (Gr :  Fin (suc n) → Group ℓ)
      → Group ℓ
funSeqFinTail n Gr = Gr fmax

funSeqFinHead : {ℓ : Level} (n : ℕ)
         (Gr :  Fin (suc n) → Group ℓ)
      → Group ℓ
funSeqFinHead n Gr = Gr fzero

module FIN2 {ℓ ℓ' : Level} (S : SuccStr ℓ) (n : ℕ)
         (Gr : Index S → Fin (suc n) → Group ℓ')
  where
  ℓ'' = ℓ-max ℓ ℓ'

  Hom : Type _
  Hom = (s : Index S) → funSeqFin n (Gr s)

  diagHom : Type ℓ''
  diagHom = (s : Index S)
    → GroupHom (funSeqFinTail n (Gr s))
                (funSeqFinHead n (Gr (succ S s)))

  transportIm-hom≡Ker-homs : (s : Index S) (k : Fin n)
        → (p : suc (fst k) < n)
        → fst (Gr s (sucFin k))
        → fst (Gr s (Fin↪sucFin (suc (fst k) , p)))
  transportIm-hom≡Ker-homs s k p x =
    subst (λ x → fst (Gr s x)) (Σ≡Prop (λ _ → m≤n-isProp) refl) x

  transportIm-diaghom≡Ker-homs : (s : Index S) (k : Fin n) (p : 0 < n)
    → Gr s fzero .fst
    → Gr s (Fin↪sucFin (0 , p)) .fst
  transportIm-diaghom≡Ker-homs s k p x =
    subst (λ x → fst (Gr s x))
      (Σ≡Prop (λ _ → m≤n-isProp) refl) x

  open import Cubical.Data.Empty

  finalFin : {n : ℕ} → 0 < n → Fin n
  finalFin {n = zero} p = rec (¬-<-zero p)
  finalFin {n = suc n} p = fmax

  transportIm-homs≡Ker-Ker-diaghom : (s : Index S) (p : 0 < n)
     → Gr s (sucFin (finalFin p)) .fst → Gr s fmax .fst
  transportIm-homs≡Ker-Ker-diaghom s p = subst (λ x → fst (Gr s x)) (help n p)
    where
    help : (n : ℕ) (p : 0 < n) → sucFin (finalFin p) ≡ fmax
    help zero p = rec (¬-<-zero p)
    help (suc n) p = Σ≡Prop (λ _ → m≤n-isProp) refl


  Im-homs≡Ker-diaghoms : Hom → diagHom → Type ℓ''
  Im-homs≡Ker-diaghoms homs diaghoms =
       (s : Index S) (k : Fin n)
       (p : 0 < n)
       (x : Gr s (sucFin (finalFin p)) .fst)
     → (isInIm (homs s (finalFin p)) x
     → isInKer (diaghoms s) (transportIm-homs≡Ker-Ker-diaghom s p x))
     × (isInKer (diaghoms s) (transportIm-homs≡Ker-Ker-diaghom s p x)
     → isInIm (homs s (finalFin p)) x)

  Im-diaghom≡Ker-homs : Hom → diagHom → Type ℓ''
  Im-diaghom≡Ker-homs homs diaghoms = (s : Index S) (k : Fin n)
           (x : Gr (succ S s) fzero .fst)
        → (p : 0 < n)
        → (isInIm (diaghoms s) x
        → isInKer (homs (succ S s) (0 , p))
             (transportIm-diaghom≡Ker-homs (succ S s) k p x))
        × (isInKer (homs (succ S s) (0 , p))
             (transportIm-diaghom≡Ker-homs (succ S s) k p x)
        → isInIm (diaghoms s) x)

  Im≡Ker-homs : Hom → Type ℓ''
  Im≡Ker-homs homs = (s : Index S) (k : Fin n)
           (x : fst (Gr s (sucFin k)))
        → (p : suc (fst k) < n)
        → (y : fst (Gr s (sucFin (suc (fst k) , p))))
        → (isInIm (homs s k) x
        → isInKer (homs s ((suc (fst k)) , p)) (transportIm-hom≡Ker-homs s k p x))
        × (isInKer (homs s ((suc (fst k)) , p)) (transportIm-hom≡Ker-homs s k p x)
        → isInIm (homs s k) x)

  record funSeq : Type ℓ'' where
    no-eta-equality
    constructor
      funseq
    field
      vertHoms : Hom
      diagHoms : diagHom

      im≡ker-vert-vert : Im≡Ker-homs vertHoms
      im≡ker-diag-vert : Im-diaghom≡Ker-homs vertHoms diagHoms
      im≡ker-vert-diag : Im-homs≡Ker-diaghoms vertHoms diagHoms
      
LES : ∀ {ℓ ℓ'} (S : SuccStr ℓ) (n : ℕ) → Type _
LES {ℓ' = ℓ'} S n = Σ[ Gr ∈ (Index S → Fin (suc n) → Group ℓ') ] FIN2.funSeq S n Gr

Unit+ : SuccStr ℓ-zero
Index Unit+ = fst Unit
succ Unit+ x = x

sucSucc×Fin : {!!}
sucSucc×Fin = {!Nat.Order.dichotomy!}

open import Cubical.Data.Sum hiding (rec)
decEq : {n : ℕ} (k : Fin (suc n)) → (fmax ≡ k) ⊎ (fst k < n)
decEq {n} (k , p) = {!p!}

FiniteSeq : ∀ {ℓ} {S : SuccStr ℓ} (n : ℕ) → (s : Index S × Fin (suc n))
  → (fmax ≡ (snd s)) ⊎ (fst (snd s) < n)
  → Index S × Fin (suc n)
FiniteSeq {S = S} n (s , k) (inl x) = succ S s , fzero
FiniteSeq {S = S} n (s , k) (inr x) = s , (suc (fst k)) , suc-≤-suc x

-- TODO : Define exact sequences
-- (perhaps short, finite, ℕ-indexed and ℤ-indexed)

SES→isEquiv : ∀ {ℓ ℓ'} {L R : Group ℓ-zero}
  → {G : Group ℓ} {H : Group ℓ'}
  → Unit ≡ L
  → Unit ≡ R
  → (lhom : GroupHom L G) (midhom : GroupHom G H) (rhom : GroupHom H R)
  → ((x : _) → isInKer midhom x → isInIm lhom x)
  → ((x : _) → isInKer rhom x → isInIm midhom x)
  → isEquiv (fst midhom)
SES→isEquiv {R = R} {G = G} {H = H} =
  J (λ L _ → Unit ≡ R →
      (lhom : GroupHom L G) (midhom : GroupHom G H)
      (rhom : GroupHom H R) →
      ((x : fst G) → isInKer midhom x → isInIm lhom x) →
      ((x : fst H) → isInKer rhom x → isInIm midhom x) →
      isEquiv (fst midhom))
      ((J (λ R _ → (lhom : GroupHom Unit G) (midhom : GroupHom G H)
                   (rhom : GroupHom H R) →
                   ((x : fst G) → isInKer midhom x → isInIm lhom x) →
                   ((x : _) → isInKer rhom x → isInIm midhom x) →
                   isEquiv (fst midhom))
         main))
  where
  main : (lhom : GroupHom Unit G) (midhom : GroupHom G H)
         (rhom : GroupHom H Unit) →
         ((x : fst G) → isInKer midhom x → isInIm lhom x) →
         ((x : fst H) → isInKer rhom x → isInIm midhom x) →
         isEquiv (fst midhom)
  main lhom midhom rhom lexact rexact =
    BijectionIsoToGroupEquiv {G = G} {H = H}
      bijIso' .fst .snd
    where
    bijIso' : BijectionIso G H
    BijectionIso.fun bijIso' = midhom
    BijectionIso.inj bijIso' x inker =
      pRec (GroupStr.is-set (snd G) _ _)
           (λ s → sym (snd s) ∙ IsGroupHom.pres1 (snd lhom))
           (lexact _ inker)
    BijectionIso.surj bijIso' x = rexact x refl
