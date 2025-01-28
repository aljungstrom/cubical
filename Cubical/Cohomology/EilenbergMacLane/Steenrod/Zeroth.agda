{-# OPTIONS --safe --cubical --lossy-unification #-}
module Cubical.Cohomology.EilenbergMacLane.Steenrod.Zeroth where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Fin
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.SmashProduct

open import Cubical.HITs.S1 as S1 renaming (_·_ to _*_)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge

open import Cubical.Foundations.HLevels
open import Cubical.Homotopy.Loopspace

private
  variable
     ℓ ℓ' : Level
     A : Pointed ℓ
     B : Pointed ℓ'

PathP→compPathR∙∙ : ∀ {ℓ} {A : Type ℓ}
  {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
  → PathP (λ i → p i ≡ q i) r s
  → r ≡ p ∙∙ s ∙∙ sym q
PathP→compPathR∙∙ {p = p} {q = q} {r = r} {s = s} P j i =
    hcomp (λ k → λ { (i = i0) → p (j ∧ ~ k)
                   ; (i = i1) → q (j ∧ ~ k)
                   ; (j = i0) → r i
                   ; (j = i1) → doubleCompPath-filler  p s (sym q) k i})
          (P j i)


Δ : typ A → A ⋀ A
Δ x = inr (x , x)

Δ∙ : A →∙ (A ⋀∙ A)
fst Δ∙ = Δ
snd (Δ∙ {A = A}) = sym (push (inl (pt A)))


data L {ℓ : Level} (A : Type ℓ) : Type ℓ where
  Lpt : L A
  Ll : (a : A) → Lpt ≡ Lpt

data Suspσ {ℓ : Level} (A : Pointed ℓ) : Type ℓ where
  𝕟 : Suspσ A
  𝕝 : (a : typ A) → 𝕟 ≡ 𝕟
  𝕝∙ : 𝕝 (pt A) ≡ refl

Suspσ→L : (A : Pointed ℓ) → Suspσ A → L (typ A)
Suspσ→L A 𝕟 = Lpt
Suspσ→L A (𝕝 a i) = (Ll a ∙ Ll (pt A) ⁻¹) i
Suspσ→L A (𝕝∙ i j) = rCancel (Ll (pt A)) i j

L→Suspσ : (A : Pointed ℓ) → L (typ A) → Suspσ A
L→Suspσ A Lpt = 𝕟
L→Suspσ A (Ll a i) = 𝕝 a i

Suspσ→L→Suspσ : (A : Pointed ℓ) (x : Suspσ A) → L→Suspσ A (Suspσ→L A x) ≡ x
Suspσ→L→Suspσ A 𝕟 = 𝕝 (pt A)
Suspσ→L→Suspσ A (𝕝 a i) j =
  hcomp (λ k → λ {(i = i0) → 𝕝∙ (~ k) j
                 ; (i = i1) → 𝕝 (pt A) (~ k ∨ j)
                 ; (j = i0) → L→Suspσ A (compPath-filler (Ll a) (Ll (pt A) ⁻¹) k i)
                 ; (j = i1) → 𝕝 a i})
        (𝕝 a i)
Suspσ→L→Suspσ A (𝕝∙ i j) k =
  hcomp (λ r → λ {(i = i1) → 𝕝∙ (~ r ∧ ~ j) k
                 ; (j = i0) → 𝕝∙ (~ r) k
                 ; (j = i1) → 𝕝 (pt A) ((~ r ∧ ~ i) ∨ k)
                 ; (k = i0) → L→Suspσ A (rCancel-filler (Ll (pt A)) r i j)
                 ; (k = i1) → 𝕝∙ i j})
          (help (𝕝 (pt A)) (sym 𝕝∙) k j i)
     where
     help : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (q : refl ≡ p)
       → Cube (λ j i → p (j ∧ ~ i)) (λ j i → q (~ i) j)
               refl (λ k i → p (~ i ∨ k))
               (λ k j → p j) (λ k j → q j k)
     help = J> refl

Susp→≡ : (A : Pointed ℓ) {P : Suspσ A → Type ℓ'}
  → {f g : (x : Suspσ A) → P x}
  → (d : (x : L (typ A)) → f (L→Suspσ A x) ≡ g (L→Suspσ A x))
  → (x : _) → f x ≡ g x
Susp→≡ A {P} {f} {g} d x =
  subst (λ x → f x ≡ g x) (Suspσ→L→Suspσ A x) (h (Suspσ→L A x))
  where
  ptEq = d Lpt
  s = cong d ∘ Ll

  h : (x : L (typ A)) → f (L→Suspσ A x) ≡ g (L→Suspσ A x)
  h Lpt = ptEq
  h (Ll a i) j = s a i j

Suspσ∙ : (A : Pointed ℓ)  → Pointed ℓ
fst (Suspσ∙ A) = Suspσ A
snd (Suspσ∙ A) = 𝕟


module SSS {A : Type ℓ} (l nn : A)
   (pl∙ pr∙ : l ≡ nn)
   (plr : pl∙ ≡ pr∙)
   where
  module _ {ℓ} {B : Type ℓ} (F : A → B) (b : B) (Fp : F l ≡ b)
    (Fcl : F l ≡ F l) (Fc*∙ : Square (sym Fp) (sym Fp) refl Fcl)
    (Fc𝕟 : F nn ≡ F nn)
    (F^ : Square Fcl Fc𝕟 (cong F pl∙) (cong F pr∙)) where
    sq1* sq2* sq3* : (i j k : I) → B
    sq1* i j k =
      hfill (λ k → λ {(i = i0) → Fp (~ k)
                     ; (i = i1) → Fp (~ k)
                     ; (j = i0) → Fc*∙ i k
                     ; (j = i1) → Fp (~ k)})
                 (inS b) k
    sq2* i j k =
      hfill (λ k → λ {(i = i0) → F (pl∙ (k ∧ ~ j))
                     ; (i = i1) → F (pr∙ (k ∧ ~ j))
                     ; (j = i0) → F^ k i
                     ; (j = i1) → F l })
             (inS (sq1* i j i1))
             k
    sq3* i j k =
      hfill (λ k → λ {(i = i0) →  F (plr k (~ j))
                     ; (i = i1) → F (pr∙ (~ j))
                     ; (j = i0) → Fc𝕟 i
                     ; (j = i1) → F l})
       (inS ((sq2* i j i1))) k

  module S2 (inr-l : nn ≡ nn) (ap-pl : Square refl inr-l pl∙ pl∙)
           (inr-r : nn ≡ nn)
           (ap-pr : Square refl inr-r pr∙ pr∙)
           (SQ : Square inr-l inr-l inr-r inr-r) where

  -- Δσ∙f₁' Δσ∙f₂ Δσ∙f₂'
    Δσ∙f₁ Δσ∙f₁' Δσ∙f₂ Δσ∙f₂' : (i j k : I) → A
    Δσ∙f₁ i j k =
      hfill (λ k → λ {(i = i0) → ap-pr (~ j) (~ k)
                     ; (i = i1) → ap-pl (~ j) k
                     ; (j = i0) → SQ (i ∨ ~ k) (i ∧ k) -- inr (𝕝 a (i ∨ ~ k) , 𝕝 a (i ∧ k))
                     ; (j = i1) → l})
            (inS (plr (~ i) (~ j))) k

    Δσ∙f₂ i j k =
      hfill (λ k → λ {(i = i0) → pr∙ (~ j) -- push (inl 𝕟) (~ j)
                     ; (i = i1) → plr k (~ j)
                     ; (j = i0) → SQ i i
                     ; (j = i1) → l}) -- inl tt})
                     (inS (Δσ∙f₁ i j i1)) k

    Δσ∙f₁' i j k =
      hfill (λ k → λ {(i = i0) → ap-pl (~ j) (~ k)
                     ; (i = i1) → ap-pr (~ j) k
                     ; (j = i0) → SQ (i ∧ k) (i ∨ ~ k)
                     ; (j = i1) → l})
            (inS (plr i (~ j))) k
    Δσ∙f₂' i j k =
      hfill (λ k → λ {(i = i0) → pl∙ (~ j)
                     ; (i = i1) → plr (~ k) (~ j)
                     ; (j = i0) → SQ i i
                     ; (j = i1) → l})
            (inS (Δσ∙f₁' i j i1)) k

    P2𝕝s* P2𝕝f* : (i j k : I) → A
    P2𝕝s* i j k =
      hfill (λ k → λ {(i = i0) → inr-l j
                     ; (i = i1) → l
                     ; (j = i0) → plr k (~ i) -- plr (~ k) (~ i)
                     ; (j = i1) → plr k (~ i) -- plr (~ k) (~ i)
                     })
           (inS (ap-pl (~ i) j)) k -- (inS (ap-pr (~ i) j)) k
    P2𝕝f* i j k =
      hfill (λ k → λ {(i = i0) → P2𝕝s* k j i1
                     ; (i = i1) → P2𝕝s* k j i1
                     ; (j = i0) → ap-pr (~ k) i
                     ; (j = i1) → ap-pr (~ k) i
                     })
           (inS (SQ i j)) k

masterCube : ∀ {ℓ'} {A : Type ℓ}  {B : Type ℓ'} (F : A → B) (l nn : A)
   (pl∙ pr∙ : l ≡ nn)
   (plr : pl∙ ≡ pr∙)
   (inr-l : nn ≡ nn)
   (ap-pl : Square refl inr-l pl∙ pl∙)
   (inr-r : nn ≡ nn)
   (ap-pr : Square refl inr-r pr∙ pr∙)
   (SQ : Square inr-l inr-l inr-r inr-r)
    (b : B) (Fp : F l ≡ b)
    (Fcl : F l ≡ F l) (Fc*∙ : Square refl Fcl (sym Fp) (sym Fp))
    (Fc𝕟 : F nn ≡ F nn)
    (F^ : Square Fcl Fc𝕟 (cong F pl∙) (cong F pr∙))
    (F^' : Square Fcl Fc𝕟 (cong F pr∙) (cong F pl∙))
    (F^≡ : Cube F^ F^' (λ i j → Fcl j) (λ i j → Fc𝕟 j) (λ i j → F (plr i j)) λ i j → F (plr (~ i) j))
    (Fc𝕟-loop-l : Square (λ i → F (inr-l i)) (λ i → F (inr-r i)) Fc𝕟 Fc𝕟)
    (Fc𝕟-loop-l∙ : Cube (λ i j → Fcl i) Fc𝕟-loop-l (λ i j → F (ap-pl i j))
                             (λ i j → F (ap-pr i j))
                             F^
                             F^)
    (Fc𝕟-loop-r : Square (λ i → F (inr-r i)) (λ i → F (inr-l i)) Fc𝕟 Fc𝕟)
    (Fc𝕟-loop-r∙ : Cube (λ i j → Fcl i) Fc𝕟-loop-r (λ i j → F (ap-pr i j))
                             (λ i j → F (ap-pl i j))
                             F^'
                             F^')
    (FLSQ : Cube (λ i j → F (SQ i j)) (λ i j → F (SQ j i))
                 Fc𝕟-loop-l
                 Fc𝕟-loop-l
                 Fc𝕟-loop-r
                 Fc𝕟-loop-r)
   → Cube (λ j k → F (SSS.S2.Δσ∙f₂ l nn pl∙ pr∙ plr inr-l ap-pl inr-r ap-pr SQ k j i1))
           (λ j k → F (SSS.S2.Δσ∙f₂ l nn pl∙ pr∙ plr inr-l ap-pl inr-r ap-pr SQ k j i1))
           (λ i k → FLSQ i k k)
           (λ i k → F (SSS.S2.P2𝕝f* l nn pl∙ pr∙ plr inr-l ap-pl inr-r ap-pr SQ k i i1))
           (λ i j → SSS.sq3* l nn pl∙ pr∙ plr F b Fp Fcl (flipSquare Fc*∙) Fc𝕟 F^ i j i1)
           λ i j → SSS.sq3* l nn pl∙ pr∙ plr F b Fp Fcl (flipSquare Fc*∙) Fc𝕟 F^ i j i1
masterCube {A = A} {B = B} F l = J> (J> (J> (J> λ SQ
  → J> (J> (J> (J> (J> (J> main SQ)))))))) -- J> (J> (J> (main SQ))))))
  where
   module _ (SQ : Square (λ _ → l) (λ _ → l) (λ _ → l) (λ _ → l))

            (FLSQ : Cube (λ i j → F (SQ i j)) (λ i j → F (SQ j i)) refl refl refl refl) where
     open SSS l l refl refl refl
     open S2 refl refl refl refl SQ

     S3 = sq3* F _ refl refl refl refl refl
     S2 = sq2* F _ refl refl refl refl refl
     S1 = sq1* F _ refl refl refl refl refl

     C1 : Cube (λ i j → S3 i j i1) (λ _ _ → F l) (λ _ _ → F l) (λ _ _ → F l) (λ _ _ → F l) λ _ _ → F l
     C1 = (λ k i j → S3 i j (~ k)) ∙ (λ k i j → S2 i j (~ k)) ∙ λ k i j → S1 i j (~ k)

     C2 : Cube (λ i j → P2𝕝f* i j i1) SQ (λ _ _ → l) (λ _ _ → l) (λ _ _ → l) λ _ _ → l
     C2 k i j =
       hcomp (λ r → λ {(i = i0) → P2𝕝s* r j (~ k)
                      ; (i = i1) → P2𝕝s* r j (~ k)
                      ; (j = i0) → l
                      ; (j = i1) → l
                      ; (k = i0) → P2𝕝f* i j r
                      ; (k = i1) → SQ i j})
              (SQ i j)

     main : Cube (λ j k → F (Δσ∙f₂ k j i1 ))
                 (λ j k → F (Δσ∙f₂ k j i1))
                 (λ i k → FLSQ i k k)
                 (λ i k → F (P2𝕝f* k i i1))
                 (λ i j → S3 i j i1)
                 λ i j → S3 i j i1
     main i j k =
       hcomp (λ r → λ {(i = i0) → F (Δσ∙f₂ k j r)
                      ; (i = i1) → F (Δσ∙f₂ k j r)
                      ; (j = i0) → FLSQ i k k
                      ; (j = i1) → F (P2𝕝f* k i i1)
                      ; (k = i0) → C1 (~ r) i j
                      ; (k = i1) → C1 (~ r) i j})
        (hcomp (λ r → λ {(i = i0) → F (Δσ∙f₁ k j r)
                      ; (i = i1) → F (Δσ∙f₁ k j r)
                      ; (j = i0) → help r k i --
                      ; (j = i1) → F (C2 (~ r) k i)
                      ; (k = i0) → F l
                      ; (k = i1) → F l})
               (F (SQ k i)))
         where

         mains : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (SQ : refl ≡ p)
               → Cube SQ
                       (λ j i → SQ (~ i) i)
                       (λ k i → (SQ (~ i) (i ∧ k))) -- (λ _ _ → x)
                       (λ k i → SQ (~ i ∨ ~ k) i)
                       refl -- (λ k j → SQ j k)
                       refl
         mains = J> refl
         help : Cube (λ k i → F (SQ k i)) (λ k i → FLSQ i k k)
                     (λ _ _ → F l) (λ _ _ → F l)
                     (λ r k → F (SQ (k ∨ ~ r) (k ∧ r)))
                     (λ r k → F (SQ (k ∨ ~ r) (k ∧ r)))
         help i j k = hcomp (λ r → λ {(i = i0) → F (SQ j k)
                      ; (i = i1) → FLSQ k (j ∨ ~ r) (j ∧ r)
                      ; (j = i0) → F (SQ (~ i) (~ r ∧ i ∧ k))
                      ; (j = i1) → F (SQ ((r ∨ ~ i) ∨ ~ k) i)
                      ; (k = i0) → F (SQ (j ∨ ~ i ∨ ~ r) (j ∧ i ∧ r))
                      ; (k = i1) → F (SQ ((j ∧ r) ∨ ~ i) ((j ∨ ~ r) ∧ i))})
           (hcomp (λ r → λ {(i = i0) → diag? (~ r) j k
                      ; (i = i1) → F l
                      ; (j = i0) → F (SQ (~ i) (i ∧ k ∧ r))
                      ; (j = i1) → F (SQ (~ i ∨ ~ k ∨ ~ r) i)
                      ; (k = i0) → F l
                      ; (k = i1) → mains {x = F l} refl (cong (cong F) SQ) r j i})
                 (F (SQ j (i ∨ ~ k))))
           where
           P1 : cong (cong F) SQ ≡ flipSquare (cong (cong F) SQ)
           P1 k i j = FLSQ k i j
           diag? : cong (cong F) SQ ≡ λ i j → F (SQ i (~ j))
           diag? = P1 ∙ sym (sym≡flipSquare _)
                 ∙ sym≡cong-sym _



module _ {ℓ} (A : Pointed ℓ) where
  open SSS {A = Suspσ∙ A ⋀ Suspσ∙ A}
           (inl tt) (inr (𝕟 , 𝕟))
           (push (inr 𝕟)) (push (inl 𝕟))
           (λ i j → push (push tt (~ i)) j)
           public
           {-

           -}
  module _ (a : typ A) where
    open S2 (λ i → inr (𝕟 , 𝕝 a i))
             (λ i j → push (inr (𝕝 a j)) i)
             (λ i → inr (𝕝 a i , 𝕟))
             (λ i j → push (inl (𝕝 a j)) i)
             (λ i j →  inr (𝕝 a i , 𝕝 a j)) public


Δσ : ∀ {ℓ} (A : Pointed ℓ)
     (a : Suspσ A) → Δ {A = Suspσ∙ A} a ≡ inl tt
Δσ A 𝕟 = sym (push (inl 𝕟))
Δσ A (𝕝 a i) j = Δσ∙f₂ A a i j i1
Δσ A (𝕝∙ i j) k =
  hcomp (λ r → λ {(i = i1) → push (push tt (~ r ∧ j)) (~ k)
                 ; (j = i0) → push (inl 𝕟) (~ k)
                 ; (j = i1) → push (push tt (~ r)) (~ k)
                 ; (k = i0) → inr (𝕝∙ i j , 𝕝∙ i j)
                 ; (k = i1) → inl tt})
    (hcomp (λ r → λ {(i = i1) → push (push tt j) (~ k)
                 ; (j = i0) → push (inl (𝕝∙ i (~ r))) (~ k)
                 ; (j = i1) → push (inr (𝕝∙ i r)) (~ k)
                 ; (k = i0) → inr (𝕝∙ i (j ∨ ~ r) , 𝕝∙ i (j ∧ r))
                 ; (k = i1) → inl tt})
           (push (push tt j) (~ k)))



open import Cubical.HITs.Susp
open import Cubical.Foundations.Isomorphism


module _ {ℓ} (A : Pointed ℓ) where
  Susp→Suspσ : Susp (typ A) → Suspσ A
  Susp→Suspσ north = 𝕟
  Susp→Suspσ south = 𝕟
  Susp→Suspσ (merid a i) = 𝕝 a i

  Suspσ→Susp : Suspσ A → Susp (typ A)
  Suspσ→Susp 𝕟 = north
  Suspσ→Susp (𝕝 a i) = toSusp A a i
  Suspσ→Susp (𝕝∙ i i₁) = rCancel (merid (pt A)) i i₁

  Suspσ→Susp→Suspσ : (x : Suspσ A) → Susp→Suspσ (Suspσ→Susp x) ≡ x
  Suspσ→Susp→Suspσ = Susp→≡ A λ { Lpt → refl
                                  ; (Ll a i) j → help a j i}
    where
    help : (x : typ A) → _
    help x = cong-∙ Susp→Suspσ (merid x) (sym (merid (pt A)))
      ∙ cong₂ _∙_ refl (cong sym 𝕝∙)
      ∙ sym (rUnit _)

  Susp→Suspσ→Susp : (x : Susp (typ A)) → Suspσ→Susp (Susp→Suspσ x) ≡ x
  Susp→Suspσ→Susp north = refl
  Susp→Suspσ→Susp south = merid (pt A)
  Susp→Suspσ→Susp (merid a i) j =
    compPath-filler (merid a) (sym (merid (pt A))) (~ j) i

  Iso-Suspσ-Susp : Iso (Suspσ A) (Susp (typ A))
  Iso.fun Iso-Suspσ-Susp = Suspσ→Susp
  Iso.inv Iso-Suspσ-Susp = Susp→Suspσ
  Iso.rightInv Iso-Suspσ-Susp = Susp→Suspσ→Susp
  Iso.leftInv Iso-Suspσ-Susp = Suspσ→Susp→Suspσ

  Suspσ≃∙Susp : (Suspσ∙ A) ≃∙ (Susp∙ (typ A))
  fst Suspσ≃∙Susp = isoToEquiv Iso-Suspσ-Susp
  snd Suspσ≃∙Susp = refl

  Susp≃∙Suspσ : (Susp∙ (typ A)) ≃∙ (Suspσ∙ A)
  fst Susp≃∙Suspσ = isoToEquiv (invIso Iso-Suspσ-Susp)
  snd Susp≃∙Suspσ = refl


makeComm : ∀ {ℓ} {C : Pointed ℓ} →  A ⋀∙ B →∙ C → B ⋀∙ A →∙ C
fst (makeComm F) = fst F ∘ ⋀comm→
snd (makeComm F) = snd F

module _ (A B : Pointed ℓ) (F : Suspσ∙ A ⋀∙ Suspσ∙ A →∙ B) (Fc : F ≡ (makeComm F)) where
  P1 : (x : Suspσ A) → (F .fst ∘ Δ) x ≡ (F .fst ∘ Δ) x
  P1 x i = Fc i .fst (inr (x , x))

  P2𝕝s : (a : typ A) (i j k : I) → Suspσ∙ A ⋀ Suspσ∙ A
  P2𝕝s a i j k = P2𝕝s* A a i j k

  P2h : (a : typ A)
    → Square {A = Suspσ∙ A ⋀ Suspσ∙ A} (λ i → inr (𝕟 , 𝕝 a i))
             refl (sym (push (inl 𝕟))) (sym (push (inl 𝕟)))
  P2h a i j = P2𝕝s a i j i1

  P2𝕝f : (a : typ A) (i j k : I) → Suspσ∙ A ⋀ Suspσ∙ A
  P2𝕝f a i j k = P2𝕝f* A a i j k

  canon : (a : typ A) → (Ω^ 2) (Suspσ∙ A ⋀∙ Suspσ∙ A) .fst
  canon a i j = P2𝕝f a i j i1

  canonvan : canon (pt A) ≡ refl
  canonvan k i j =
    hcomp (λ r → λ {(i = i0) → help r j k
                   ; (i = i1) → help r j k
                   ; (j = i0) → push (inl (𝕝∙ k i)) (~ r)
                   ; (j = i1) → push (inl (𝕝∙ k i)) (~ r)
                   ; (k = i0) → P2𝕝f (pt A) i j r
                   ; (k = i1) → push (inl 𝕟) (~ r)
                   })
          (inr (𝕝∙ k i , 𝕝∙ k j))
    where
    help : Cube {A =  (Suspσ∙ A ⋀ Suspσ∙ A)}
                (λ j k → inr (𝕟 , 𝕝∙ k j))
                (λ j k → inl tt)
                (λ r k → push (inl 𝕟) (~ r))
                (λ r k → push (inl 𝕟) (~ r))
                (λ r j → P2𝕝f (pt A) i1 j r)
                λ r j → push (inl 𝕟) (~ r)
    help r j k =
      hcomp (λ i → λ {(r = i0) → inr (𝕟 , 𝕝∙ k j)
                   ; (r = i1) → inl tt
                   ; (j = i0) → push (push tt (~ i)) (~ r)
                   ; (j = i1) → push (push tt (~ i)) (~ r)
                   ; (k = i1) → push (push tt (~ i)) (~ r)})
         (push (inr (𝕝∙ k j)) (~ r))

  Suspσ→Sq : (x : Suspσ A) → Ω (Suspσ∙ A ⋀∙ Suspσ∙ A) .fst
  Suspσ→Sq 𝕟 = refl
  Suspσ→Sq (𝕝 a i) = canon a i
  Suspσ→Sq (𝕝∙ i i₁) = canonvan i i₁

  P2 : (x : Suspσ A) → Ω (fst B , fst F (inl tt)) .fst
  P2 x = cong (fst F) (Suspσ→Sq x)

  mainlemma : (x : Suspσ A) → Square (cong (fst F) (Δσ A x)) (cong (fst F) (Δσ A x)) (P1 x) (P2 x)
  mainlemma x = compPathR→PathP∙∙ ((Susp→≡ A
    {f = λ x → cong (fst F) (Δσ A x)}
    {g = λ x → P1 x ∙∙  cong (fst F) (Δσ A x) ∙∙ sym (P2 x)}
    (λ y → PathP→compPathR∙∙ (c y))
    x))
    where
    sq1 sq2 sq3 : (i j k : I) → fst B
    sq1 i j k = sq1* A (fst F) (pt B) (snd F)
                (λ i → Fc i .fst (inl tt))
                (λ i j → Fc i .snd (~ j))
                ((λ i → Fc i .fst (inr (𝕟 , 𝕟))))
                (λ i j → Fc j .fst (push (inr 𝕟) i)) i j k
    sq2 i j k = sq2* A (fst F) (pt B) (snd F)
                (λ i → Fc i .fst (inl tt))
                (λ i j → Fc i .snd (~ j))
                ((λ i → Fc i .fst (inr (𝕟 , 𝕟))))
                (λ i j → Fc j .fst (push (inr 𝕟) i)) i j k
    sq3 i j k = sq3* A (fst F) (pt B) (snd F)
                (λ i → Fc i .fst (inl tt))
                (λ i j → Fc i .snd (~ j))
                ((λ i → Fc i .fst (inr (𝕟 , 𝕟))))
                (λ i j → Fc j .fst (push (inr 𝕟) i)) i j k

    c : (x : L (typ A))
      → Square (cong (fst F) (Δσ A (L→Suspσ A x)))
                (cong (fst F) (Δσ A (L→Suspσ A x)))
                (P1 (L→Suspσ A x)) (P2 (L→Suspσ A x))
    c Lpt i j = sq3 i j i1 --
    c (Ll a k) i j = help i j k --
      where
      help : Cube (λ j k → fst F (Δσ A (𝕝 a k) j))
                  (λ j k → fst F (Δσ A (𝕝 a k) j))
                  (λ i k → Fc i .fst (inr (𝕝 a k , 𝕝 a k)))
                  (λ i k → fst F (canon a k i))
                  (λ i j → sq3 i j i1)
                  (λ i j → sq3 i j i1)
      help i j k = HELP i j k
        where
        HELP = masterCube (fst F) (inl tt) (inr (𝕟 , 𝕟))
                          (push (inr 𝕟)) (push (inl 𝕟))
                          (λ i j → push (push tt (~ i)) j)
                          (λ i → inr (𝕟 , 𝕝 a i))
                          (λ i j → push (inr (𝕝 a j)) i)
                          (λ i → inr (𝕝 a i , 𝕟))
                          ((λ i j → push (inl (𝕝 a j)) i))
                          (λ i j →  inr (𝕝 a i , 𝕝 a j)) (snd B)
                          (snd F) (λ i → Fc i .fst (inl tt))
                          (λ i j → Fc j .snd (~ i))
                          (λ i → Fc i .fst (inr (𝕟 , 𝕟)))
                          (λ i j → Fc j .fst (push (inr 𝕟) i))
                          (λ i j → Fc j .fst (push (inl 𝕟) i))
                          (λ k i j → Fc j .fst (push (push tt (~ k)) i))
                          (λ i j → Fc i .fst (inr (𝕟 , 𝕝 a j)))
                          (λ k i j → Fc i .fst (push (inr (𝕝 a j)) k))
                          (λ i j → Fc i .fst (inr (𝕝 a j , 𝕟)))
                          (λ k i j → Fc i .fst (push (inl (𝕝 a j)) k))
                          (λ k i j → Fc k. fst (inr (𝕝 a i , 𝕝 a j)))

  module theorem where
    Fun1 Fun2 : Susp∙ (Suspσ A) →∙ B
    fst Fun1 north = fst F (inl tt)
    fst Fun1 south = fst F (inl tt)
    fst Fun1 (merid a i) = (sym (cong (fst F) (Δσ A a)) ∙∙ P1 a ∙∙ cong (fst F) (Δσ A a)) i
    snd Fun1 = snd F
    fst Fun2 north = fst F (inl tt)
    fst Fun2 south = fst F (inl tt)
    fst Fun2 (merid a i) = P2 a i
    snd Fun2 = snd F

    main : Fun1 ≡ Fun2
    main = ΣPathP ((funExt (λ { north → refl ; south → refl
                             ; (merid a i) j → transport (PathP≡doubleCompPathˡ _ _ _ _)
                                                  (flipSquare (mainlemma a)) j i}))
                             , refl)
