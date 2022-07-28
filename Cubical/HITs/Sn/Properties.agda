{-# OPTIONS --safe #-}
module Cubical.HITs.Sn.Properties where

open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1 renaming (_·_ to _*_) hiding (rec ; elim)
open import Cubical.HITs.S2 renaming (S¹×S¹→S² to S¹×S¹→S²')
open import Cubical.HITs.S3
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Join renaming (joinS¹S¹→S³ to joinS¹S¹→S3)
open import Cubical.Data.Bool

private
  variable
    ℓ : Level

open Iso

IsoSucSphereSusp : (n : ℕ) → Iso (S₊ (suc n)) (Susp (S₊ n))
IsoSucSphereSusp zero = S¹IsoSuspBool
IsoSucSphereSusp (suc n) = idIso

IsoSucSphereSusp∙ : (n : ℕ)
  → Iso.inv (IsoSucSphereSusp n) north ≡ ptSn (suc n)
IsoSucSphereSusp∙ zero = refl
IsoSucSphereSusp∙ (suc n) = refl

-- Elimination principles for spheres
sphereElim : (n : ℕ) {A : (S₊ (suc n)) → Type ℓ} → ((x : S₊ (suc n)) → isOfHLevel (suc n) (A x))
          → A (ptSn (suc n))
          → (x : S₊ (suc n)) → A x
sphereElim zero hlev pt = toPropElim hlev pt
sphereElim (suc n) hlev pt north = pt
sphereElim (suc n) {A = A} hlev pt south = subst A (merid (ptSn (suc n))) pt
sphereElim (suc n) {A = A} hlev pt (merid a i) =
  sphereElim n {A = λ a → PathP (λ i → A (merid a i)) pt (subst A (merid (ptSn (suc n))) pt)}
               (λ a → isOfHLevelPathP' (suc n) (hlev south) _ _)
               (λ i → transp (λ j → A (merid (ptSn (suc n)) (i ∧ j))) (~ i) pt)
               a i

sphereElim2 : ∀ {ℓ} (n : ℕ) {A : (S₊ (suc n)) → (S₊ (suc n)) → Type ℓ}
          → ((x y : S₊ (suc n)) → isOfHLevel (suc n) (A x y))
          → A (ptSn (suc n)) (ptSn (suc n))
          → (x y : S₊ (suc n)) → A x y
sphereElim2 n hlev pt = sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → hlev _ _)
                                     (sphereElim n (hlev _ ) pt)

private
  compPath-lem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y)
              → PathP (λ i → (p ∙ sym q) i ≡ y) p q
  compPath-lem {y = y} p q i j =
    hcomp (λ k → λ { (i = i0) → p j
                    ; (i = i1) → q (~ k ∨ j)
                    ; (j = i1) → y })
          (p (j ∨ i))

sphereToPropElim : (n : ℕ) {A : (S₊ (suc n)) → Type ℓ} → ((x : S₊ (suc n)) → isProp (A x))
          → A (ptSn (suc n))
          → (x : S₊ (suc n)) → A x
sphereToPropElim zero = toPropElim
sphereToPropElim (suc n) hlev pt north = pt
sphereToPropElim (suc n) {A = A} hlev pt south = subst A (merid (ptSn (suc n))) pt
sphereToPropElim (suc n) {A = A} hlev pt (merid a i) =
  isProp→PathP {B = λ i → A (merid a i)} (λ _ → hlev _) pt (subst A (merid (ptSn (suc n))) pt) i

-- Elimination rule for fibrations (x : Sⁿ) → (y : Sᵐ) → A x y of h-Level (n + m).
-- The following principle is just the special case of the "Wedge Connectivity Lemma"
-- for spheres (See Cubical.Homotopy.WedgeConnectivity or chapter 8.6 in the HoTT book).
-- We prove it directly here for three reasons:
-- (i) it should perform better
-- (ii) we get a slightly stronger statement for spheres: one of the homotopies will, by design, be refl
-- (iii) the fact that the two homotopies only differ by (composition with) the homotopy leftFunction(base) ≡ rightFunction(base)
-- is close to trivial

wedgeconFun : (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
          → ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y))
          → (f : (x : _) → A (ptSn (suc n)) x)
          → (g : (x : _) → A x (ptSn (suc m)))
          → (g (ptSn (suc n)) ≡ f (ptSn (suc m)))
          → (x : S₊ (suc n)) (y : S₊ (suc m)) → A x y
wedgeconLeft : (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
             → (hLev : ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y)))
             → (f : (x : _) → A (ptSn (suc n)) x)
             → (g : (x : _) → A x (ptSn (suc m)))
             → (hom : g (ptSn (suc n)) ≡ f (ptSn (suc m)))
             → (x : _) → wedgeconFun n m hLev f g hom (ptSn (suc n)) x ≡ f x
wedgeconRight : (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
             → (hLev : ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y)))
             → (f : (x : _) → A (ptSn (suc n)) x)
             → (g : (x : _) → A x (ptSn (suc m)))
             → (hom : g (ptSn (suc n)) ≡ f (ptSn (suc m)))
             → (x : _) → wedgeconFun n m hLev f g hom x (ptSn (suc m)) ≡ g x
wedgeconFun zero zero {A = A} hlev f g hom = F
  where
  helper : SquareP (λ i j → A (loop i) (loop j)) (cong f loop) (cong f loop)
                        (λ i → hcomp (λ k → λ { (i = i0) → hom k
                                                ; (i = i1) → hom k })
                                      (g (loop i)))
                         λ i → hcomp (λ k → λ { (i = i0) → hom k
                                                ; (i = i1) → hom k })
                                       (g (loop i))
  helper = toPathP (isOfHLevelPathP' 1 (hlev _ _) _ _ _ _)

  F : (x y : S¹) → A x y
  F base y = f y
  F (loop i) base = hcomp (λ k → λ { (i = i0) → hom k
                                    ; (i = i1) → hom k })
                          (g (loop i))
  F (loop i) (loop j) = helper i j

wedgeconFun zero (suc m) {A = A} hlev f g hom = F₀
  module _ where
  transpLemma₀ : (x : S₊ (suc m)) → transport (λ i₁ → A base (merid x i₁)) (g base) ≡ f south
  transpLemma₀ x = cong (transport (λ i₁ → A base (merid x i₁)))
                                  hom
              ∙ (λ i → transp (λ j → A base (merid x (i ∨ j))) i
                               (f (merid x i)))

  pathOverMerid₀ : (x : S₊ (suc m)) → PathP (λ i₁ → A base (merid x i₁))
                                            (g base)
                                            (transport (λ i₁ → A base (merid (ptSn (suc m)) i₁))
                                                       (g base))
  pathOverMerid₀ x i = hcomp (λ k → λ { (i = i0) → g base
                                      ; (i = i1) → (transpLemma₀ x ∙ sym (transpLemma₀ (ptSn (suc m)))) k})
                            (transp (λ i₁ → A base (merid x (i₁ ∧ i))) (~ i)
                                    (g base))

  pathOverMeridId₀ : pathOverMerid₀ (ptSn (suc m)) ≡ λ i → transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                                                                 (g base)
  pathOverMeridId₀  =
       (λ j i → hcomp (λ k → λ {(i = i0) → g base
                               ; (i = i1) → rCancel (transpLemma₀ (ptSn (suc m))) j k})
                      (transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                              (g base)))
     ∙ λ j i → hfill (λ k → λ { (i = i0) → g base
                                ; (i = i1) → transport (λ i₁ → A base (merid (ptSn (suc m)) i₁))
                                                        (g base)})
                      (inS (transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                                   (g base))) (~ j)

  indStep₀ : (x : _) (a : _) → PathP (λ i → A x (merid a i))
                                             (g x)
                                             (subst (λ y → A x y) (merid (ptSn (suc m)))
                                                    (g x))
  indStep₀ = wedgeconFun zero m (λ _ _ → isOfHLevelPathP' (2 + m) (hlev _ _) _ _)
                              pathOverMerid₀
                              (λ a i → transp (λ i₁ → A a (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                                               (g a))
                              (sym pathOverMeridId₀)

  F₀ : (x : S¹) (y : Susp (S₊ (suc m))) → A x y
  F₀ x north = g x
  F₀ x south = subst (λ y → A x y) (merid (ptSn (suc m))) (g x)
  F₀ x (merid a i) = indStep₀ x a i
wedgeconFun (suc n) m {A = A} hlev f g hom = F₁
  module _ where
  transpLemma₁ : (x : S₊ (suc n)) → transport (λ i₁ → A (merid x i₁) (ptSn (suc m))) (f (ptSn (suc m))) ≡ g south
  transpLemma₁ x = cong (transport (λ i₁ → A (merid x i₁) (ptSn (suc m))))
                       (sym hom)
                ∙ (λ i → transp (λ j → A (merid x (i ∨ j)) (ptSn (suc m))) i
                                 (g (merid x i)))

  pathOverMerid₁ : (x : S₊ (suc n)) → PathP (λ i₁ → A (merid x i₁) (ptSn (suc m)))
                                            (f (ptSn (suc m)))
                                            (transport (λ i₁ → A (merid (ptSn (suc n)) i₁) (ptSn (suc m)))
                                                       (f (ptSn (suc m))))
  pathOverMerid₁ x i = hcomp (λ k → λ { (i = i0) → f (ptSn (suc m))
                                      ; (i = i1) → (transpLemma₁ x ∙ sym (transpLemma₁ (ptSn (suc n)))) k })
                            (transp (λ i₁ → A (merid x (i₁ ∧ i)) (ptSn (suc m))) (~ i)
                                    (f (ptSn (suc m))))

  pathOverMeridId₁ : pathOverMerid₁ (ptSn (suc n)) ≡ λ i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i)
                                                                 (f (ptSn (suc m)))
  pathOverMeridId₁ =
        (λ j i → hcomp (λ k → λ { (i = i0) → f (ptSn (suc m))
                                  ; (i = i1) → rCancel (transpLemma₁ (ptSn (suc n))) j k })
                        (transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i)
                                (f (ptSn (suc m)))))
       ∙ λ j i → hfill (λ k → λ { (i = i0) → f (ptSn (suc m))
                                  ; (i = i1) → transport (λ i₁ → A (merid (ptSn (suc n)) i₁) (ptSn (suc m)))
                                                          (f (ptSn (suc m))) })
                        (inS (transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i)
                                     (f (ptSn (suc m))))) (~ j)

  indStep₁ : (a : _) (y : _) → PathP (λ i → A (merid a i) y)
                                             (f y)
                                             (subst (λ x → A x y) (merid (ptSn (suc n)))
                                                    (f y))
  indStep₁ = wedgeconFun n m (λ _ _ → isOfHLevelPathP' (suc (n + suc m)) (hlev _ _) _ _)
                           (λ a i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) a) (~ i)
                                            (f a))
                           pathOverMerid₁
                           pathOverMeridId₁

  F₁ : (x : Susp (S₊ (suc n))) (y : S₊ (suc m))  → A x y
  F₁ north y = f y
  F₁ south y = subst (λ x → A x y) (merid (ptSn (suc n))) (f y)
  F₁ (merid a i) y = indStep₁ a y i
wedgeconRight zero zero {A = A} hlev f g hom = right
  where
  right : (x : S¹) → _
  right base = sym hom
  right (loop i) j = hcomp (λ k → λ { (i = i0) → hom (~ j ∧ k)
                                     ; (i = i1) → hom (~ j ∧ k)
                                     ; (j = i1) → g (loop i) })
                           (g (loop i))
wedgeconRight zero (suc m) {A = A} hlev f g hom x = refl
wedgeconRight (suc n) m {A = A} hlev f g hom = right
  where
  lem : (x : _) → indStep₁ n m hlev f g hom x (ptSn (suc m)) ≡ _
  lem = wedgeconRight n m (λ _ _ → isOfHLevelPathP' (suc (n + suc m)) (hlev _ _) _ _)
                           (λ a i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) a) (~ i)
                                            (f a))
                           (pathOverMerid₁ n m hlev f g hom)
                           (pathOverMeridId₁ n m hlev f g hom)

  right : (x : Susp (S₊ (suc n))) → _ ≡ g x
  right north = sym hom
  right south = cong (subst (λ x → A x (ptSn (suc m)))
                            (merid (ptSn (suc n))))
                            (sym hom)
              ∙ λ i → transp (λ j → A (merid (ptSn (suc n)) (i ∨ j)) (ptSn (suc m))) i
                              (g (merid (ptSn (suc n)) i))
  right (merid a i) j =
    hcomp (λ k → λ { (i = i0) → hom (~ j)
                    ; (i = i1) → transpLemma₁ n m hlev f g hom (ptSn (suc n)) j
                    ; (j = i0) → lem a (~ k) i
                    ; (j = i1) → g (merid a i)})
          (hcomp (λ k →  λ { (i = i0) → hom (~ j)
                            ; (i = i1) → compPath-lem (transpLemma₁ n m hlev f g hom a) (transpLemma₁ n m hlev f g hom (ptSn (suc n))) k j
                            ; (j = i1) → g (merid a i)})
                 (hcomp (λ k → λ { (i = i0) → hom (~ j)
                                  ; (j = i0) → transp (λ i₂ → A (merid a (i₂ ∧ i)) (ptSn (suc m))) (~ i)
                                                       (f (ptSn (suc m)))
                                  ; (j = i1) → transp (λ j → A (merid a (i ∧ (j ∨ k))) (ptSn (suc m))) (k ∨ ~ i)
                                                       (g (merid a (i ∧ k))) })
                        (transp (λ i₂ → A (merid a (i₂ ∧ i)) (ptSn (suc m))) (~ i)
                                (hom (~ j)))))
wedgeconLeft zero zero {A = A} hlev f g hom x = refl
wedgeconLeft zero (suc m) {A = A} hlev f g hom = help
  where
  left₁ : (x : _) → indStep₀ m hlev f g hom base x ≡ _
  left₁ = wedgeconLeft zero m (λ _ _ → isOfHLevelPathP' (2 + m) (hlev _ _) _ _)
                              (pathOverMerid₀ m hlev f g hom)
                              (λ a i → transp (λ i₁ → A a (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                                               (g a))
                              (sym (pathOverMeridId₀ m hlev f g hom))

  help : (x : S₊ (suc (suc m))) → _
  help north = hom
  help south = cong (subst (A base) (merid (ptSn (suc m)))) hom
             ∙ λ i → transp (λ j → A base (merid (ptSn (suc m)) (i ∨ j))) i
                             (f (merid (ptSn (suc m)) i))
  help (merid a i) j =
    hcomp (λ k → λ { (i = i0) → hom j
                    ; (i = i1) → transpLemma₀ m hlev f g hom (ptSn (suc m)) j
                    ; (j = i0) → left₁ a (~ k) i
                    ; (j = i1) → f (merid a i)})
          (hcomp (λ k →  λ { (i = i0) → hom j
                            ; (i = i1) → compPath-lem (transpLemma₀ m hlev f g hom a)
                                                       (transpLemma₀ m hlev f g hom (ptSn (suc m))) k j
                            ; (j = i1) → f (merid a i)})
                 (hcomp (λ k → λ { (i = i0) → hom j
                                  ; (j = i0) → transp (λ i₂ → A base (merid a (i₂ ∧ i))) (~ i)
                                                       (g base)
                                  ; (j = i1) → transp (λ j → A base (merid a (i ∧ (j ∨ k)))) (k ∨ ~ i)
                                                       (f (merid a (i ∧ k)))})
                        (transp (λ i₂ → A base (merid a (i₂ ∧ i))) (~ i)
                                (hom j))))
wedgeconLeft (suc n) m {A = A} hlev f g hom _ = refl

wedgeconRightN : (n m : ℕ) {A : (S₊ (2 + n)) → (S₊ (2 + m)) → Type ℓ}
             → (hLev : ((x : S₊ (2 + n)) (y : S₊ (2 + m)) → isOfHLevel ((2 + n) + (2 + m)) (A x y)))
             → (f : (x : _) → A north x)
             → (g : (x : _) → A x north)
             → (hom : g north ≡ f north)
             → wedgeconRight (suc n) (suc m) hLev f g hom north ≡ sym hom
wedgeconRightN n m hlev f g hom = refl 


---------- Connectedness -----------

sphereConnected : (n : HLevel) → isConnected (suc n) (S₊ n)
sphereConnected n = ∣ ptSn n ∣ , elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
                                     (λ a → sym (spoke ∣_∣ (ptSn n)) ∙ spoke ∣_∣ a)

-- The fact that path spaces of Sn are connected can be proved directly for Sⁿ.
-- (Unfortunately, this does not work for higher paths)
pathIdTruncSⁿ : (n : ℕ) (x y : S₊ (suc n))
             → Path (hLevelTrunc (2 + n) (S₊ (suc n))) ∣ x ∣ ∣ y ∣
             → hLevelTrunc (suc n) (x ≡ y)
pathIdTruncSⁿ n = sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → isOfHLevelΠ (suc n)  λ _ → isOfHLevelTrunc (suc n))
                     (sphereElim n (λ _ → isOfHLevelΠ (suc n)  λ _ → isOfHLevelTrunc (suc n))
                       λ _ → ∣ refl ∣)

pathIdTruncSⁿ⁻ : (n : ℕ) (x y : S₊ (suc n))
             → hLevelTrunc (suc n) (x ≡ y)
             → Path (hLevelTrunc (2 + n) (S₊ (suc n))) ∣ x ∣ ∣ y ∣
pathIdTruncSⁿ⁻ n x y = rec (isOfHLevelTrunc (2 + n) _ _)
                           (J (λ y _ → Path (hLevelTrunc (2 + n) (S₊ (suc n))) ∣ x ∣ ∣ y ∣) refl)

pathIdTruncSⁿretract : (n : ℕ) (x y : S₊ (suc n)) → (p : hLevelTrunc (suc n) (x ≡ y)) → pathIdTruncSⁿ n x y (pathIdTruncSⁿ⁻ n x y p) ≡ p
pathIdTruncSⁿretract n =
  sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → isOfHLevelΠ (suc n) λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
    λ y → elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
      (J (λ y p → pathIdTruncSⁿ n (ptSn (suc n)) y (pathIdTruncSⁿ⁻ n (ptSn (suc n)) y ∣ p ∣) ≡ ∣ p ∣)
         (cong (pathIdTruncSⁿ n (ptSn (suc n)) (ptSn (suc n))) (transportRefl refl) ∙ pm-help n))
  where
  pm-help : (n : ℕ) → pathIdTruncSⁿ n (ptSn (suc n)) (ptSn (suc n)) refl  ≡ ∣ refl ∣
  pm-help zero = refl
  pm-help (suc n) = refl

isConnectedPathSⁿ : (n : ℕ) (x y : S₊ (suc n)) → isConnected (suc n) (x ≡ y)
isConnectedPathSⁿ n x y =
  isContrRetract
   (pathIdTruncSⁿ⁻ n x y)
   (pathIdTruncSⁿ n x y)
   (pathIdTruncSⁿretract n x y)
     ((isContr→isProp (sphereConnected (suc n)) ∣ x ∣ ∣ y ∣)
      , isProp→isSet (isContr→isProp (sphereConnected (suc n))) _ _ _)

-- Some lemmas on the H space structure on S¹
rUnitS¹ : (x : S¹) → x * base ≡ x
rUnitS¹ base = refl
rUnitS¹ (loop i₁) = refl

commS¹ : (a x : S¹) → a * x ≡ x * a
commS¹ = wedgeconFun _ _ (λ _ _ → isGroupoidS¹ _ _)
         (sym ∘ rUnitS¹)
         rUnitS¹
         refl

assocS¹ : (x y z : S¹) → x * (y * z) ≡ (x * y) * z
assocS¹ = wedgeconFun _ _ (λ _ _ → isSetΠ λ _ → isGroupoidS¹ _ _)
          (λ _ _ → refl)
          (λ x z i → (rUnitS¹ x (~ i)) * z)
          refl

invLooperDistr : (x y : S¹) → invLooper (x * y) ≡ invLooper x * invLooper y
invLooperDistr =
  wedgeconFun 0 0 (λ _ _ → isGroupoidS¹ _ _) (λ _ → refl)
    (λ x → cong invLooper (rUnitS¹ x) ∙ sym (rUnitS¹ (invLooper x)))
    (sym (rUnit refl))

SuspS¹-hom : (a x : S¹)
  → Path (Path (hLevelTrunc 4 (S₊ 2)) _ _)
          (cong ∣_∣ₕ (σ (S₊∙ 1) (a * x)))
          (cong ∣_∣ₕ (σ (S₊∙ 1) a)
        ∙ (cong ∣_∣ₕ (σ (S₊∙ 1) x)))
SuspS¹-hom = wedgeconFun _ _ (λ _ _ → isOfHLevelTrunc 4 _ _ _ _)
           (λ x → lUnit _
                 ∙ cong (_∙ cong ∣_∣ₕ (σ (S₊∙ 1) x))
                        (cong (cong ∣_∣ₕ) (sym (rCancel (merid base)))))
           (λ x → (λ i → cong ∣_∣ₕ (σ (S₊∙ 1) (rUnitS¹ x i)))
               ∙∙ rUnit _
               ∙∙ cong (cong ∣_∣ₕ (σ (S₊∙ 1) x) ∙_)
                       (cong (cong ∣_∣ₕ) (sym (rCancel (merid base)))))
           (sym (l (cong ∣_∣ₕ (σ (S₊∙ 1) base))
                (cong (cong ∣_∣ₕ) (sym (rCancel (merid base))))))
  where
  l : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (P : refl ≡ p)
    → lUnit p ∙ cong (_∙ p) P ≡ rUnit p ∙ cong (p ∙_) P
  l p = J (λ p P → lUnit p ∙ cong (_∙ p) P ≡ rUnit p ∙ cong (p ∙_) P) refl

rCancelS¹ : (x : S¹) → ptSn 1 ≡ x * (invLooper x)
rCancelS¹ base = refl
rCancelS¹ (loop i) j =
  hcomp (λ r → λ {(i = i0) → base ; (i = i1) → base ; (j = i0) → base})
        base

SuspS¹-inv : (x : S¹) → Path (Path (hLevelTrunc 4 (S₊ 2)) _ _)
                         (cong ∣_∣ₕ (σ (S₊∙ 1) (invLooper x)))
                         (cong ∣_∣ₕ (sym (σ (S₊∙ 1) x)))
SuspS¹-inv x = (lUnit _
       ∙∙ cong (_∙ cong ∣_∣ₕ (σ (S₊∙ 1) (invLooper x)))
               (sym (lCancel (cong ∣_∣ₕ (σ (S₊∙ 1) x))))
                  ∙∙ sym (assoc _ _ _))
       ∙∙ cong (sym (cong ∣_∣ₕ (σ (S₊∙ 1) x)) ∙_) lem
       ∙∙ (assoc _ _ _
       ∙∙ cong (_∙ (cong ∣_∣ₕ (sym (σ (S₊∙ 1) x))))
               (lCancel (cong ∣_∣ₕ (σ (S₊∙ 1) x)))
       ∙∙ sym (lUnit _))
  where
  lem : cong ∣_∣ₕ (σ (S₊∙ 1) x)
      ∙ cong ∣_∣ₕ (σ (S₊∙ 1) (invLooper x))
     ≡ cong ∣_∣ₕ (σ (S₊∙ 1) x)
     ∙ cong ∣_∣ₕ (sym (σ (S₊∙ 1) x))
  lem = sym (SuspS¹-hom x (invLooper x))
     ∙ ((λ i → cong ∣_∣ₕ (σ (S₊∙ 1) (rCancelS¹ x (~ i))))
     ∙ cong (cong ∣_∣ₕ) (rCancel (merid base))) ∙ sym (rCancel _)

-------------------- join Sⁿ Sᵐ ≃ Sⁿ⁺¹⁺ᵐ -------------------------
{-
This section contains a proof that join Sⁿ Sᵐ ≃ Sⁿ⁺ᵐ⁺¹. This is easy using
various properties proved in HITs.Join. However, we would like the map
join Sⁿ Sᵐ → Sⁿ⁺ᵐ⁺¹
to be nice, in particular when n = m = 1. Therefore, we put in some extra work into
the equivalence.
-}


{- We begin with join S¹ S¹ ≃ S³. The iso is induced by: -}
S¹×S¹→S² : S¹ → S¹ → S₊ 2
S¹×S¹→S² base y = north
S¹×S¹→S² (loop i) base = north
S¹×S¹→S² (loop i) (loop j) =
  (sym (rCancel (merid base))
  ∙∙ (λ i → merid (loop i) ∙ sym (merid base))
  ∙∙ rCancel (merid base)) i j

joinS¹S¹→S³ : join S¹ S¹ → S₊ 3
joinS¹S¹→S³ (inl x) = north
joinS¹S¹→S³ (inr x) = south
joinS¹S¹→S³ (push a b i) = merid (S¹×S¹→S² a b) i

{- Proving that this is an equivalence directly is painful,
  so we simply prove that it is equal to the old definition of
  the equivalence join S¹ S¹ ≃ S³ ≃ S₊ 3
  To this end, we start by rephrasing the map -}
private
  3cell : (r i j k : I) → S₊ 3
  3cell r i j k =
    hfill (λ r → λ {(i = i0) → merid (merid base j) (k ∧ ~ r)
                   ; (i = i1) → merid (merid base j) (k ∧ ~ r)
                   ; (j = i0) → merid north (k ∧ ~ r)
                   ; (j = i1) → merid south (k ∧ ~ r)
                   ; (k = i0) → north
                   ; (k = i1) → merid (merid base j) (~ r)})
          (inS (merid (merid (loop i) j) k))
          r

joinS¹S¹→S³' : join S¹ S¹ → S₊ 3
joinS¹S¹→S³' (inl x) = north
joinS¹S¹→S³' (inr x) = north
joinS¹S¹→S³' (push base b i) = north
joinS¹S¹→S³' (push (loop i₁) base i) = north
joinS¹S¹→S³' (push (loop i₁) (loop i₂) i) = 3cell i1 i₁ i₂ i

{- These two maps are equal -}
joinS¹S¹→S³'≡joinS¹S¹→S³' : (x : _) → joinS¹S¹→S³ x ≡ joinS¹S¹→S³' x
joinS¹S¹→S³'≡joinS¹S¹→S³' (inl base) = refl
joinS¹S¹→S³'≡joinS¹S¹→S³' (inl (loop i)) = refl
joinS¹S¹→S³'≡joinS¹S¹→S³' (inr base) = sym (merid north)
joinS¹S¹→S³'≡joinS¹S¹→S³' (inr (loop i)) = sym (merid north)
joinS¹S¹→S³'≡joinS¹S¹→S³' (push base base i) k = merid north (~ k ∧ i)
joinS¹S¹→S³'≡joinS¹S¹→S³' (push base (loop i₁) i) k  = merid north (~ k ∧ i)
joinS¹S¹→S³'≡joinS¹S¹→S³' (push (loop i₁) base i) k =  (merid north) (~ k ∧ i)
joinS¹S¹→S³'≡joinS¹S¹→S³' (push (loop i) (loop j) k) l =
  hcomp (λ r → λ { (i = i0) → merid (sym (rCancel (merid base)) (~ r) j)
                                      (~ l ∧ k)
                  ; (i = i1) → merid (sym (rCancel (merid base)) (~ r) j)
                                      (~ l ∧ k)
                  ; (j = i0) → merid north (~ l ∧ k)
                  ; (j = i1) → merid north (~ l ∧ k)
                  ; (k = i0) → north
                  ; (k = i1) → merid (sym (rCancel (merid base)) (~ r) j) (~ l)
                  ; (l = i0) → merid (doubleCompPath-filler
                                      (sym (rCancel (merid base)))
                                      (cong (σ (S₊∙ 1)) loop)
                                      (rCancel (merid base)) r i j) k
                  ; (l = i1) → 3cell i1 i j k})
    (hcomp (λ r → λ {(i = i0) → merid (cp-fill base r j) (k ∧ ~ l)
                   ; (i = i1) → merid (cp-fill base r j) (k ∧ ~ l)
                   ; (j = i0) → merid north (~ l ∧ k)
                   ; (j = i1) → merid (merid base (~ r)) (~ l ∧ k)
                   ; (k = i0) → north
                   ; (k = i1) → merid (cp-fill base r j) (~ l)
                   ; (l = i0) → merid (cp-fill (loop i) r j) k
                   ; (l = i1) → 3cell i1 i j k})
       (hcomp (λ r → λ {(i = i0) → merid (merid base j) (k ∧ (~ r ∨ ~ l))
                   ; (i = i1) → merid (merid base j) (k ∧ (~ r ∨ ~ l))
                   ; (j = i0) → merid north (k ∧ (~ l ∨ ~ r))
                   ; (j = i1) → merid south (k ∧ (~ l ∨ ~ r))
                   ; (k = i0) → north
                   ; (k = i1) → merid (merid base j) (~ r ∨ ~ l)
                   ; (l = i0) → merid (merid (loop i) j) k
                   ; (l = i1) → 3cell r i j k})
              (merid (merid (loop i) j) k)))
  where
  cp-fill : (a : S¹) → _
  cp-fill a = compPath-filler (merid a) (sym (merid base))

{- joinS¹S¹→S³' is equal to the original
  equivalence (modulo a flipping of interval variables) -}
joinS¹S¹→S³'Id : (x : join S¹ S¹)
  → joinS¹S¹→S³' x ≡ (Iso.fun IsoS³S3 ∘ flip₀₂S³ ∘ joinS¹S¹→S3) x
joinS¹S¹→S³'Id (inl x) = refl
joinS¹S¹→S³'Id (inr x) = refl
joinS¹S¹→S³'Id (push base base i) = refl
joinS¹S¹→S³'Id (push base (loop i₁) i) = refl
joinS¹S¹→S³'Id (push (loop i₁) base i) = refl
joinS¹S¹→S³'Id (push (loop i) (loop j) k) l =
  hcomp (λ r → λ {(i = i0) → merid (merid base (j ∧ ~ l)) (~ r ∧ k)
                 ; (i = i1) → merid (merid base (j ∧ ~ l)) (~ r ∧ k)
                 ; (j = i0) → merid north (k ∧ ~ r)
                 ; (j = i1) → merid (merid base (~ l)) (~ r ∧ k)
                 ; (k = i0) → north
                 ; (k = i1) → merid (merid base (j ∧ ~ l)) (~ r)
                 ; (l = i0) → 3cell r i j k
                 ; (l = i1) → Iso.fun (IsoType→IsoSusp S²IsoSuspS¹)
                                       (meridian-contraction-2 k j i r)})
        (merid (S²Cube i j l) k)
  where
  S²Cube : Cube {A = S₊ 2} (λ j l → merid base (j ∧ ~ l))
                             (λ j l → merid base (j ∧ ~ l))
                             (λ i l → north)
                             (λ i l → merid base (~ l))
                             (λ i j → merid (loop i) j)
                             λ i j → fun S²IsoSuspS¹ (surf j i)
  S²Cube i j l =
    hcomp (λ r → λ {(i = i0) → merid base (j ∧ (~ l ∨ ~ r))
                 ; (i = i1) → merid base (j ∧ (~ l ∨ ~ r))
                 ; (j = i0) → north
                 ; (j = i1) → merid base (~ l ∨ ~ r)
                 ; (l = i0) → merid (loop i) j
                 ; (l = i1) → meridian-contraction j i r})
           (merid (loop i) j)

{-So, finally our map joinS¹S¹→S³ is an iso. We state its inverse explicitly. -}
Iso-joinS¹S¹-S³ : Iso (join S¹ S¹) (S₊ 3)
fun Iso-joinS¹S¹-S³ = joinS¹S¹→S³
inv Iso-joinS¹S¹-S³ = S³→joinS¹S¹ ∘ flip₀₂S³ ∘ Iso.inv IsoS³S3
rightInv Iso-joinS¹S¹-S³ x =
     joinS¹S¹→S³'≡joinS¹S¹→S³'
       ((S³→joinS¹S¹ ∘ flip₀₂S³ ∘ Iso.inv IsoS³S3) x)
  ∙∙ joinS¹S¹→S³'Id ((S³→joinS¹S¹ ∘ flip₀₂S³ ∘ Iso.inv IsoS³S3) x)
  ∙∙ Iso.leftInv (compIso (invIso IsoS³S3)
                  (compIso flip₀₂S³Iso (S³IsojoinS¹S¹))) x
leftInv Iso-joinS¹S¹-S³ x =
     cong (S³→joinS¹S¹ ∘ flip₀₂S³ ∘ inv IsoS³S3)
          (joinS¹S¹→S³'≡joinS¹S¹→S³' x ∙ joinS¹S¹→S³'Id x)
   ∙ Iso.rightInv (compIso (invIso IsoS³S3) (compIso flip₀₂S³Iso (S³IsojoinS¹S¹))) x

{- We now get the full iso Sⁿ * Sᵐ ≃ Sⁿ⁺ᵐ⁺¹ -}
IsoSphereJoin : (n m : ℕ)
  → Iso (join (S₊ n) (S₊ m)) (S₊ (suc (n + m)))
IsoSphereJoin zero zero = compIso (invIso Susp-iso-joinBool) (invIso S¹IsoSuspBool)
IsoSphereJoin zero (suc m) = compIso join-comm (invIso Susp-iso-joinBool)
IsoSphereJoin (suc zero) zero = (invIso Susp-iso-joinBool)
IsoSphereJoin (suc zero) (suc zero) = Iso-joinS¹S¹-S³
IsoSphereJoin (suc zero) (suc (suc m)) =
  compIso join-comm
    (compIso (compIso (Iso-joinSusp-suspJoin {A = S₊∙ (suc m)} {B = S₊∙ (suc zero)})
      (congSuspIso join-comm))
      (congSuspIso (IsoSphereJoin (suc zero) (suc m))))
IsoSphereJoin (suc (suc n)) m =
  compIso (Iso-joinSusp-suspJoin {A = S₊∙ (suc n)} {B = S₊∙ m}) (congSuspIso (IsoSphereJoin (suc n) m))

{- Pointedness holds by refl.
  This is due to the explicit definition of Iso-joinSusp-suspJoin  -}
IsoSphereJoinPres∙ : (n m : ℕ)
  → Iso.fun (IsoSphereJoin n m) (inl (ptSn n)) ≡ ptSn (suc (n + m))
IsoSphereJoinPres∙ zero zero = refl
IsoSphereJoinPres∙ zero (suc m) = refl
IsoSphereJoinPres∙ (suc zero) zero = refl
IsoSphereJoinPres∙ (suc zero) (suc zero) = refl
IsoSphereJoinPres∙ (suc zero) (suc (suc m)) = refl
IsoSphereJoinPres∙ (suc (suc n)) m = refl

IsoSphereJoin⁻Pres∙ : (n m : ℕ)
  → Iso.inv (IsoSphereJoin n m) (ptSn (suc (n + m))) ≡ inl (ptSn n)
IsoSphereJoin⁻Pres∙ n m =
     cong (Iso.inv (IsoSphereJoin n m)) (sym (IsoSphereJoinPres∙ n m))
   ∙ Iso.leftInv (IsoSphereJoin n m) (inl (ptSn n))

-- Inversion on spheres
invSphere : {n : ℕ} → S₊ n → S₊ n
invSphere {n = zero} = not
invSphere {n = (suc zero)} = invLooper
invSphere {n = (suc (suc n))} = invSusp

invSphere² : (n : ℕ) (x : S₊ n) → invSphere (invSphere x) ≡ x
invSphere² zero = notnot
invSphere² (suc zero) base = refl
invSphere² (suc zero) (loop i) = refl
invSphere² (suc (suc n)) = invSusp²

-- Interaction between σ and invSphere
σ-invSphere : (n : ℕ) (x : S₊ (suc n))
                 → σ (S₊∙ (suc n)) (invSphere x)
                 ≡ sym (σ (S₊∙ (suc n)) x)
σ-invSphere zero base =
  rCancel (merid base) ∙∙ refl ∙∙ cong sym (sym (rCancel (merid base)))
σ-invSphere zero (loop i) j =
  hcomp (λ k → λ { (j = i0) → doubleCompPath-filler
                                 (sym (rCancel (merid base)))
                                 (λ i → (σ (S₊∙ 1) (loop (~ i))))
                                 (rCancel (merid base)) (~ k) i
                  ; (j = i1) → doubleCompPath-filler
                                  (sym (cong sym (rCancel (merid base))))
                                  (λ i → sym (σ (S₊∙ 1) (loop i)))
                                  (cong sym (rCancel (merid base))) (~ k) i})
        (sym≡cong-sym  (sym (rCancel (merid base))
                    ∙∙ (λ i → (σ (S₊∙ 1) (loop i)))
                    ∙∙ (rCancel (merid base))) j i)
σ-invSphere (suc n) x = toSusp-invSusp (S₊∙ (suc n)) x


-- Some facts about the map S¹×S¹→S²
-- Todo: generalise to Sⁿ×Sᵐ→Sⁿ⁺ᵐ
S¹×S¹→S²rUnit : (a : S¹) → S¹×S¹→S² a base ≡ north
S¹×S¹→S²rUnit base = refl
S¹×S¹→S²rUnit (loop i) = refl

S¹×S¹→S²x+x : (x : S¹) → S¹×S¹→S² x x ≡ north
S¹×S¹→S²x+x base = refl
S¹×S¹→S²x+x (loop i) k = lem k i
  where
  lem : cong₂ S¹×S¹→S² loop loop ≡ refl
  lem = cong₂Funct S¹×S¹→S² loop loop
    ∙ (λ i → rUnit (cong (λ x → S¹×S¹→S²rUnit x i) loop) (~ i))

S¹×S¹→S²-antiComm : (a b : S¹) → S¹×S¹→S² a b ≡ S¹×S¹→S² b (invLooper a)
S¹×S¹→S²-antiComm base base = refl
S¹×S¹→S²-antiComm base (loop i) = refl
S¹×S¹→S²-antiComm (loop i) base = refl
S¹×S¹→S²-antiComm (loop i) (loop j) k =
  sym≡flipSquare (λ j i → S¹×S¹→S² (loop i) (loop j)) (~ k) i j

private
  S¹×S¹→S²-Distr-filler : (i : I)
    → cong₂ (λ b c → S¹×S¹→S² ((loop i) * b) c) loop loop
    ≡ cong (S¹×S¹→S² (loop i)) loop
  S¹×S¹→S²-Distr-filler i =
    cong₂Funct (λ b c → S¹×S¹→S² ((loop i) * b) c) loop loop
     ∙∙ (λ j → cong (λ x → S¹×S¹→S²rUnit (rotLoop x i) j) loop ∙
                cong (λ c → S¹×S¹→S² (loop i) c) loop)
     ∙∙ sym (lUnit _)

S¹×S¹→S²-Distr : (a b : S¹) → S¹×S¹→S² (a * b) b ≡ S¹×S¹→S² a b
S¹×S¹→S²-Distr a base j = S¹×S¹→S² (rUnitS¹ a j) base
S¹×S¹→S²-Distr base (loop i) k = S¹×S¹→S²-Distr-filler i0 k i
S¹×S¹→S²-Distr (loop i₁) (loop i) k = S¹×S¹→S²-Distr-filler i₁ k i

invSusp∘S¹×S¹→S² : (a b : S¹)
  → S¹×S¹→S² a (invLooper b) ≡ invSusp (S¹×S¹→S² a b)
invSusp∘S¹×S¹→S² base b = merid base
invSusp∘S¹×S¹→S² (loop i) base = merid base
invSusp∘S¹×S¹→S² (loop i) (loop j) k =
  hcomp (λ r → λ {(i = i0) → i-Boundary₂ r j k
                 ; (i = i1) → i-Boundary₂ r j k
                 ; (j = i0) → m-b k
                 ; (j = i1) → m-b k
                 ; (k = i0) → doubleCompPath-filler
                                rCancel-mb⁻¹ (cong σ₁ loop) rCancel-mb r i (~ j)
                 ; (k = i1)
                    → invSusp (doubleCompPath-filler
                                 rCancel-mb⁻¹ (cong σ₁ loop) rCancel-mb r i j)})
   (hcomp (λ r → λ {(i = i0) → i-Boundary r (~ j) k
                   ; (i = i1) → i-Boundary r (~ j) k
                   ; (j = i0) → merid base (~ r ∨ k)
                   ; (j = i1) → merid base (r ∧ k)
                   ; (k = i0) → cp-filler (loop i) r (~ j)
                   ; (k = i1) → invSusp (cp-filler (loop i) r j)})
           (merid (loop i) (~ j)))
  where
  σ₁ = σ (S₊∙ 1)
  m-b = merid base
  rCancel-mb = rCancel m-b
  rCancel-mb⁻¹ = sym (rCancel m-b)

  cp-filler : (a : S¹) (i j : I) → S₊ 2
  cp-filler a i j = compPath-filler (merid a) (sym (merid base)) i j

  i-Boundary : I → I → I → S₊ 2
  i-Boundary r j k =
    hfill (λ r → λ{(j = i0) → m-b (k ∧ r)
                  ; (j = i1) → m-b (~ r ∨ k)
                  ; (k = i0) → cp-filler base r j
                  ; (k = i1) → invSusp (cp-filler base r (~ j))})
          (inS (m-b j))
          r

  i-Boundary₂ : I → I → I → S₊ 2
  i-Boundary₂ r j k =
    hcomp (λ i → λ {(r = i0) → i-Boundary i (~ j) k
                 ; (r = i1) → m-b k
                 ; (j = i0) → m-b (k ∨ (~ i ∧ ~ r))
                 ; (j = i1) → m-b (k ∧ (i ∨ r))
                 ; (k = i0) → rCancel-filler m-b i r (~ j)
                 ; (k = i1) → invSusp (rCancel-filler m-b i r j) })
     (hcomp (λ i → λ {(r = i0) → m-b (~ j ∨ (~ i ∧ k))
                 ; (r = i1) → m-b (k ∨ (~ i ∧ ~ j))
                 ; (j = i0) → m-b (k ∨ (~ r ∨ ~ i))
                 ; (j = i1) → m-b (k ∧ (~ i ∨ r))
                 ; (k = i0) → m-b (~ j ∧ (~ r ∨ ~ i))
                 ; (k = i1) → m-b ((~ j ∨ ~ i) ∨ r) })
            (m-b (~ j ∨ k)))

-- Interaction between S¹×S¹→S² and SuspS¹→S²
SuspS¹→S²-S¹×S¹→S² : (a b : S¹)
  → (SuspS¹→S² (S¹×S¹→S² a b)) ≡ (S¹×S¹→S²' b a)
SuspS¹→S²-S¹×S¹→S² base base = refl
SuspS¹→S²-S¹×S¹→S² base (loop i) = refl
SuspS¹→S²-S¹×S¹→S² (loop i) base = refl
SuspS¹→S²-S¹×S¹→S² (loop i) (loop j) k =
  hcomp (λ r → λ {(i = i0) → rUnit (λ _ → base) (~ r ∧ ~ k) j
                 ; (i = i1) → rUnit (λ _ → base) (~ r ∧ ~ k) j
                 ; (j = i0) → base
                 ; (j = i1) → base
                 ; (k = i0) → SuspS¹→S² (doubleCompPath-filler (
                                 sym (rCancel (merid base)))
                                 ((λ i → merid (loop i) ∙ sym (merid base)))
                                 (rCancel (merid base)) r i j )
                 ; (k = i1) → surf j i})
    (hcomp (λ r → λ {(i = i0) → rUnit (λ _ → base) (r ∧ ~ k) j
                 ; (i = i1) → rUnit (λ _ → base) (r ∧ ~ k) j
                 ; (j = i0) → base
                 ; (j = i1) → base
                 ; (k = i0) → SuspS¹→S²
                       (compPath-filler (merid (loop i)) (sym (merid base)) r j)
                 ; (k = i1) → surf j i})
           (surf j i))




-- J₂ : Type
-- J₂ = Pushout {A = S₊∙ 2 ⋁ S₊∙ 2 } {B = S₊ 2 × S₊ 2} {C = S₊ 2} ⋁↪ fold⋁

-- isOfHLev : (x : J₂) → isOfHLevel 4 (S₊∙ 2 →∙ (hLevelTrunc 6 J₂ , ∣ x ∣))
-- isOfHLev x = {!!}

-- commS : (x a : S₊ 2) → Path J₂ (inl (x , a)) (inl (a , x))
-- commS north a = {!!}
-- commS south a = {!!}
-- commS (merid a₁ i) a = {!!}

-- LF : (x : S₊ 2) → (S₊∙ 2 →∙ (hLevelTrunc 6 J₂ , ∣ inl (north , x) ∣))
-- fst (LF y) x = ∣ inl (x , y) ∣ₕ
-- snd (LF x) = refl

-- RF : (x : S₊ 2) → (S₊∙ 2 →∙ (hLevelTrunc 6 J₂ , ∣ inl (x , north) ∣))
-- fst (RF x) y = ∣ inl (y , x) ∣ₕ
-- snd (RF x) = cong ∣_∣ₕ (push (inr x) ∙ sym (push (inl x)))

-- MID : RF north ≡ LF north
-- fst (MID i) y = ∣ inl (y , north) ∣
-- snd (MID i) j = ∣ ((λ j → (push (push tt (~ j)) ∙ sym (push (inl north)))) ∙ rCancel' (push (inl north))) i j ∣ₕ

-- open import Cubical.Foundations.Pointed.Homogeneous
-- incl' : (x y : S₊ 2) → (S₊∙ 2 →∙ (hLevelTrunc 6 J₂ , ∣ inl (x , y) ∣))
-- incl' = wedgeconFun 1 1 (λ x y → isOfHLev _) LF RF MID

-- incl : (x y : S₊ 2) → (S₊∙ 2 →∙ (hLevelTrunc 6 J₂ , ∣ inl (x , y) ∣))
-- incl =
--   wedgeconFun 1 1
--     (λ x y → isOfHLev _)
--     (λ y → (λ x → ∣ inl (x , y) ∣ₕ) , refl)
--     (λ x → (λ y → ∣ inl (x , y) ∣ₕ) , refl)
--     (ΣPathP ((funExt (λ x → cong ∣_∣ₕ (push (inr x) ∙ sym (push (inl x)))))
--           , λ i j → ∣ ((λ j → (push (push tt (~ j)) ∙ sym (push (inl north)))) ∙ rCancel' (push (inl north))) j i ∣ₕ))


-- eq : (a x : S₊ 2)  → incl' a (pt (Susp S¹ , snd (S₊∙ 2))) .fst x ≡ ∣ inl (x , a) ∣
-- eq a x = funExt⁻ (cong fst (wedgeconRight 1 1
--   (λ x y → isOfHLev _) LF RF MID a)) x

-- incl'' : (x : S₊ 2) → {!!}
-- incl'' x = {!!}

-- pp : S₊ 2 → (i j k : I) → hLevelTrunc 6 J₂
-- pp x i j k =
--   hfill (λ k → λ {(i = i0) → incl' x (pt (Susp S¹ , snd (S₊∙ 2))) .snd j
--                  ; (i = i1) → ∣ compPath-filler (push (inr x)) (sym (push (inl x))) (~ k) j ∣ₕ
--                  ; (j = i0) → eq x north i
--                  ; (j = i1) → ∣ push (inl x) (i ∧ k) ∣ₕ})
--         (inS ((wedgeconRight 1 1 {A = λ x y → S₊∙ 2 →∙ (hLevelTrunc 6 J₂ , ∣ inl (x , y) ∣)} (λ x y → isOfHLev _) LF RF MID x) i .snd j))
--         k

-- S2-act : S₊ 2 → J₂ → hLevelTrunc 6 J₂
-- S2-act x (inl (y , z)) = incl' y z .fst x
-- S2-act x (inr y) = ∣ inl (x , y) ∣
-- S2-act x (push (inl a) i) = eq a x i -- eq a x i
-- S2-act x (push (inr b) i) = ∣ inl (x , b) ∣
-- S2-act x (push (push tt i₁) i) = ∣ inl (x , north) ∣

-- S2→J² : S₊ 2 → hLevelTrunc 6 J₂ → hLevelTrunc 6 J₂
-- S2→J² x = rec (isOfHLevelTrunc 6) (S2-act x)

-- S2-actId : (x : _) → S2-act north x ≡ ∣ x ∣
-- S2-actId (inl x) = incl' (fst x) (snd x) .snd
-- S2-actId (inr x) = cong ∣_∣ₕ (push (inr x))
-- S2-actId (push (inl x) i) j = pp x i j i1
-- S2-actId (push (inr x) i) j = ∣ push (inr x) (i ∧ j) ∣
-- S2-actId (push (push a k) i) j =
--   hcomp (λ r → λ {(i = i0) → ∣ inl (north , north) ∣ₕ
--                  ; (i = i1) → cubie r j k
--                  ; (j = i0) →  ∣ inl (north , north) ∣
--                  ; (j = i1) → ∣ push (push a k) (i ∧ r) ∣
--                  ; (k = i0) → pp (snd (S₊∙ 2)) i j r
--                  ; (k = i1) →  ∣ push (inr (snd (S₊∙ 2))) (i ∧ r ∧ j) ∣ })
--         (pp (snd (S₊∙ 2)) (i ∧ ~ k) j i0)
--   where -- r j k
--   genLem : ∀ {ℓ} {A : Type ℓ} (x y : A) (pushinl pushinr : x ≡ y) (pushtt : pushinl ≡ pushinr)
--          → Cube (λ j k → ((λ j → pushtt (~ j) ∙ sym pushinl) ∙ rCancel' pushinl) k j)
--                  (λ j k → pushinr j)
--                  (λ r k → x)
--                  (λ r k → pushtt k r)
--                  (λ r j → compPath-filler pushinr (sym pushinl) (~ r) j)
--                  λ r j → pushinr (r ∧ j)
--   genLem x = J> (J> (cong flipSquare (sym (lUnit (rCancel' refl))) ◁ λ i j k → rCancel-filler' (refl {x = x}) k i j))

--   cubie : Cube {A = hLevelTrunc 6 J₂}
--                (λ j k → ∣ ((λ j → (push (push tt (~ j))
--                         ∙ sym (push (inl north))))
--                         ∙ rCancel' (push (inl north))) k j ∣ₕ)
--                (λ j k → ∣ push (inr (snd (S₊∙ 2))) j ∣)
--                (λ r k → ∣ inl (north , north) ∣)
--                (λ r k → ∣ push (push tt k) r ∣)
--                (λ r j → ∣ compPath-filler (push (inr (snd (S₊∙ 2)))) (λ i₁ → push (inl (snd (S₊∙ 2))) (~ i₁)) (~ (r ∧ i1)) j ∣) -- (λ r j → pp (snd (S₊∙ 2)) i1 j i1)
--                λ r j → ∣ push (inr (snd (S₊∙ 2))) (r ∧ j) ∣
--   cubie i j k = ∣ genLem (inl (north , north)) (inr north) (push (inl north)) (push (inr north)) (λ k → push (push tt k)) i j k ∣ₕ

-- S2→J²-north : S2→J² north ≡ idfun _
-- S2→J²-north = funExt (elim (λ _ → isOfHLevelPath 6 (isOfHLevelTrunc 6) _ _) S2-actId)

-- S2→J²-isEquiv : (x : _) → isEquiv (S2→J² x)
-- S2→J²-isEquiv = sphereElim 1 (λ _ → isProp→isSet (isPropIsEquiv _))
--                    (subst isEquiv (sym S2→J²-north) (idEquiv _ .snd))

-- S2→J²auto : S₊ 2 → hLevelTrunc 6 J₂ ≃ hLevelTrunc 6 J₂
-- fst (S2→J²auto x) = S2→J² x
-- snd (S2→J²auto x) = S2→J²-isEquiv x

-- J²-fib : S₊ 3 → Type
-- J²-fib north = hLevelTrunc 6 J₂
-- J²-fib south = hLevelTrunc 6 J₂
-- J²-fib (merid a i) = ua (S2→J²auto a) (~ i)

-- -- σ (a ⌣ b) 

-- tta : S₊ 2 → S₊ 2 → Susp (join S¹ S¹)
-- tta north y = north
-- tta south y = south
-- tta (merid a i) north = merid (inl a) i
-- tta (merid a i) south = merid (inl base) i
-- tta (merid a i) (merid b j) = merid ((push a b ∙ sym (push base b)) j) i



-- S¹→ : {!!}
-- S¹→ = {!!}

-- Pash : J₂ → Susp (join S¹ S¹)
-- Pash (inl x) = tta (fst x) (snd x)
-- Pash (inr x) = north
-- Pash (push (inl north) i) = north
-- Pash (push (inl south) i) = merid (inr base) (~ i)
-- Pash (push (inl (merid a j)) i) =
--   hcomp (λ k → λ {(i = i0) → merid (inl a) j
--                  ; (i = i1) → merid (inr base) (j ∧ ~ k)
--                  ; (j = i0) → north
--                  ; (j = i1) → merid (inr base) (~ i ∨ ~ k)})
--         (merid (push a base i) j)
-- Pash (push (inr x) i) = north
-- Pash (push (push a i₁) i) = north
-- {-
-- j = i0 ⊢ north
-- j = i1 ⊢ merid (inr base) (~ i)
-- i = i0 ⊢ merid (inl a) j
-- i = i1 ⊢ north
-- -}



-- TT→S3 : S₊ 2 → S₊ 2 → join S¹ S¹
-- TT→S3 north y = inl base
-- TT→S3 south y = inl base
-- TT→S3 (merid a i) north = inl base
-- TT→S3 (merid a i) south = inl base
-- TT→S3 (merid a i) (merid a₁ j) = {!!}

-- S3-fib : (x : S₊ 3) → Type
-- S3-fib north = {!!}
-- S3-fib south = {!!}
-- S3-fib (merid a i) = {!!}

-- +S : join S¹ S¹ → join S¹ S¹ → join S¹ S¹
-- +S (inl x) (inl y) = inl (x * y)
-- +S (inl x) (inr y) = inr (x * y)
-- +S (inl x) (push a b i) = push (x * a) (x * b) i
-- +S (inr x) (inl y) = inl (x * y)
-- +S (inr x) (inr y) = inr (x * y)
-- +S (inr x) (push a b i) = push (x * a) (x * b) i
-- +S (push a b i) (inl x) = (push (a * x) (b * x) ∙ sym (push (b * x) (b * x))) i -- (push (a * x) (invLooper b * x) ∙ sym (push (invLooper b * x) (invLooper b * x))) i
-- +S (push a b i) (inr x) = {!push!}
-- +S (push a b i) (push c d j) = {!!}

-- fib : join S¹ S¹ → Type
-- fib (inl x) = S¹ × S¹
-- fib (inr x) = S¹ × S¹
-- fib (push a b i) = isoToPath (Σ-cong-iso (idIso {A = S¹}) λ _ → S¹-act (invLooper b)) (~ i)

-- inci : S₊ 1 → S₊ 1 → S₊ 1 → Susp (join S¹ S¹)
-- inci x base z = north
-- inci x (loop i) z = (merid (inl (x * z)) ∙ sym (merid (inl base))) i

-- inci2 : S₊ 1 → S₊ 1 → S₊ 1 → Susp (join S¹ S¹)
-- inci2 x base z = north
-- inci2 x (loop i) z = (merid (inr (x * z)) ∙ sym (merid (inl base))) i

-- fib→' : (x : join S¹ S¹) → fib x → Susp (join S¹ S¹)
-- fib→' (inl x) p = inci x (fst p) (snd p) -- x * z
-- fib→' (inr x) p = {!!}
-- fib→' (push a b i) p = {!!}                -- push (x * l) (x

-- baha : (a x y b : S¹) → inci a x (invLooper b * y) ≡ inci2 b x y
-- baha a base y b = refl
-- baha a (loop i) y b j = (merid (push (a * ((invLooper b) * y)) (b * y) j) ∙ sym (merid (inl base))) i

-- fib→ : (x : join S¹ S¹) → fib x → Susp (join S¹ S¹)
-- fib→ (inl x) (y , z) = inci x y z
-- fib→ (inr x) (y , z) = inci2 x y z
-- fib→ (push a b i) p =
--   hcomp (λ j → λ {(i = i0) → inci a (fst p) (snd p)
--                  ; (i = i1) → baha a (fst p) (snd p) b j})
--         (inci a (fst s) (snd s))
--   where
--   s = ua-unglue (isoToEquiv (Σ-cong-iso idIso (λ _ → S¹-act (invLooper b)))) (~ i) p


-- fibA : Σ _ fib → S₊ 3
-- fibA = uncurry λ x p → suspFun Hopf (fib→ x p)

-- fibA' : Σ _ fib → S₊ 3
-- fibA' = uncurry λ x _ → joinS¹S¹→S³ x

-- J∙ : Pointed ℓ-zero
-- J∙ = join S¹ S¹ , inl base

-- loopSquare : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (i j k : I) → A
-- loopSquare p i j k =
--   hfill (λ k → λ {(i = i0) → p (j ∨ ~ k)
--                  ; (i = i1) → p (j ∧ k)
--                  ; (j = i0) → p (i ∨ ~ k)
--                  ; (j = i1) → p (k ∧ i)})
--          (inS (p i0))
--          k


-- lemi : S₊ 2 → S₊ 2 → Susp (join S¹ S¹)
-- lemi north north = north
-- lemi north south = north
-- lemi north (merid b i) = σ J∙ (inr b) i
-- lemi south north = north
-- lemi south south = north
-- lemi south (merid b i) = σ J∙ (inr b) i
-- lemi (merid a i) north = σ J∙ (inl a) i
-- lemi (merid a i) south = σ J∙ (inl a) i
-- lemi (merid a i) (merid b j) =
--   hcomp (λ k → λ {(i = i0) → σ J∙ (push a b k) j
--                  ; (i = i1) → σ J∙ (push a b k) j
--                  ; (j = i0) → σ J∙ (inl a) i
--                  ; (j = i1) → σ J∙ (inl a) i})
--         (loopSquare (σ J∙ (inl a)) i j i1)

-- fibmap : (x : join S¹ S¹) → fib x → Susp (join S¹ S¹)
-- fibmap (inl x) p = lemi (S¹×S¹→S² x (fst p)) (S¹×S¹→S² x (snd p))
-- fibmap (inr x) p = lemi (S¹×S¹→S² (fst p) x) (S¹×S¹→S² (snd p) x)
-- fibmap (push a b i) p = {!!}

-- asd : (x : _) → fibA x ≡ fibA' x
-- asd (inl x , base , z) = refl
-- asd (inl x , loop i , z) j = (cong-∙ (suspFun Hopf) (merid (inl (x * z))) (sym ( (merid (inl base)))) ∙ rCancel (merid north)) j i
-- asd (inr x , base , z) = merid north
-- asd (inr x , loop i , z) = {!!}
-- asd (push a b i , p) = {!!}

-- -- lola : (x y : _) → suspFun Hopf (tta x y) ≡ north
-- -- lola x y = {!!}

-- -- Total→ : (x : _) → J²-fib x → hLevelTrunc 6 (Susp (join S¹ S¹))
-- -- Total→ north = map Pash
-- -- Total→ south _ = ∣ north ∣
-- -- Total→ (merid a i) = {!

-- -- !}
-- --   where
-- --   help : PathP (λ i → ua (S2→J²auto a) (~ i) → hLevelTrunc 6 (Susp (join S¹ S¹))) (map Pash) λ _ → ∣ north ∣
-- --   help = toPathP (funExt (elim {!!} λ x → (λ i → transportRefl (rec₊ (isOfHLevelTrunc 6) (λ a₁ → ∣ Pash a₁ ∣ₕ) (transportRefl (S2-act a x) i)) i)
-- --                                         ∙ {!λ _ → ∣ ? ∣ₕ!}
-- --                                         ∙ {!!})) -- (λ i → transportRefl (transportRefl (map Pash {!∣ x ∣!}) i) i) ∙ {!!}))
-- --     where
-- --     Fun1 : (a : S₊ 2) → S₊∙ 2 →∙ ((S₊∙ 2) →∙ hLevelTrunc∙ 6 (Susp (join S¹ S¹) , north) ∙)
-- --     fst (fst (Fun1 a) x) y = map Pash (S2-act a (inl (x , y))) 
-- --     snd (fst (Fun1 a) x) = {!incl' north x .fst a!}
-- --     snd (Fun1 a) = {!!}

-- --     wedgeap : (a x y : S₊ 2) → map Pash (S2-act a (inl (x , y))) ≡ ∣ north ∣
-- --     wedgeap a = {!!}

-- --     lem2 : (a : _) (x : _) → map Pash (S2-act a x) ≡ ∣ north ∣
-- --     lem2 a (inl (x , y)) = {!!}
-- --     lem2 a (inr x) = {!!}
-- --     lem2 a (push a₁ i) = {!!}

-- -- lem1 : (x : _) (y : J²-fib x) → map (suspFun Hopf) (Total→ x y) ≡ ∣ x ∣
-- -- lem1 north = elim {!!} λ { (inl (north , north)) → refl ; (inl (south , north)) → cong ∣_∣ₕ (sym (merid north))
-- --                           ; (inl (merid a i , north)) → {!!}
-- --                           ; (inl (x , south)) → {!!}
-- --                           ; (inl (x , merid a i)) → {!!}
-- --                           ; (inr x) → {!!}
-- --                           ; (push a i) → {!!}}
-- -- lem1 south = {!!}
-- -- lem1 (merid a i) y = {!!}




-- -- {-
-- -- k = i0 ⊢ pp (snd (S₊∙ 2)) i j i1
-- -- k = i1 ⊢ ∣ push (inr (snd (S₊∙ 2))) (i ∧ j) ∣
-- -- i = i0 ⊢ incl' (pt (Susp S¹ , snd (S₊∙ 2)))
-- --          (pt (Susp S¹ , snd (S₊∙ 2))) .snd j
-- -- i = i1 ⊢ ∣ push (inr (snd (S₊∙ 2))) j ∣
-- -- j = i0 ⊢ ∣ inl (north , north) ∣
-- -- j = i1 ⊢ ∣ push (push a k) i ∣
-- -- -}

-- -- -- ss : S₊ 2 → Susp (S¹ × S¹) → Susp (S¹ × S¹)
-- -- -- ss north y = y
-- -- -- ss south y = y
-- -- -- ss (merid a i) y = {!!}
-- -- --   where
-- -- --   gr : (a : S¹) (y : Susp (S¹ × S¹)) → y ≡ y
-- -- --   gr a y = {!!}

-- -- -- Suspi : S₊ 3 → Type
-- -- -- Suspi north = Susp (S¹ × S¹)
-- -- -- Suspi south = Susp (S¹ × S¹)
-- -- -- Suspi (merid a i) = {!!}

-- -- -- joinFib : join (S₊ 2) (S₊ 2) → Susp (join S¹ S¹)
-- -- -- joinFib (inl x) = suspFun inl x
-- -- -- joinFib (inr x) = suspFun inr x
-- -- -- joinFib (push north north i) = north
-- -- -- joinFib (push north south i) = merid (inl base) i
-- -- -- joinFib (push north (merid a j) i) = {!!}
-- -- -- joinFib (push south b i) = {!b!}
-- -- -- joinFib (push (merid a i₁) north i) = {!!}
-- -- -- joinFib (push (merid a i₁) south i) = {!!}
-- -- -- joinFib (push (merid a i₁) (merid a₁ i₂) i) = {!!}

-- -- -- -- test : J₂ → hLevelTrunc 6 (Susp (join S¹ S¹))
-- -- -- -- test (inl (north , north)) = ∣ north ∣
-- -- -- -- test (inl (north , south)) = ∣ north ∣
-- -- -- -- test (inl (north , merid a i)) = ∣ σ ((join S¹ S¹) , inl base) (inr a) i ∣
-- -- -- -- test (inl (south , north)) = ∣ north ∣
-- -- -- -- test (inl (south , south)) = ∣ north ∣
-- -- -- -- test (inl (south , merid a i)) = ∣ north ∣
-- -- -- -- test (inl (merid a j , north)) = ∣ σ ((join S¹ S¹) , inl base) (inl a) j ∣
-- -- -- -- test (inl (merid a j , south)) = ∣ north ∣
-- -- -- -- test (inl (merid a j , merid b i)) = {!!}
-- -- -- -- test (inr x) = {!!}
-- -- -- -- test (push a i) = {!!}

-- -- -- -- S¹act : S₊ 2 → S₊ 2 → S₊ 2 → hLevelTrunc 6 J₂
-- -- -- -- S¹act north x y = ∣ inl (x , north) ∣
-- -- -- -- S¹act south x y = ∣ inl (north , y) ∣
-- -- -- -- S¹act (merid a i) x y = {!!}

-- -- -- -- S2-act : S₊ 2 → J₂ → hLevelTrunc 4 J₂
-- -- -- -- S2-act x (inl (a , b)) = {!!}
-- -- -- -- S2-act x (inr x₁) = {!!}
-- -- -- -- S2-act x (push a i) = {!!}

-- -- -- -- fib : S₊ 3 → Type
-- -- -- -- fib north = J₂
-- -- -- -- fib south = J₂
-- -- -- -- fib (merid a i) = {!!}
-- -- -- --   where
-- -- -- --   l : (a : S¹) (b : S₊ 2) → b ≡ b 
-- -- -- --   l a north = merid a ∙ sym (merid base)
-- -- -- --   l a south = sym (merid base) ∙ merid a
-- -- -- --   l a (merid b i) = {!!}

-- -- -- -- {- isoToPath (IsoType→IsoSusp (S¹-act (a * invLooper b))) (~ i)
-- -- -- -- -}

-- -- -- -- -- fib→ : Σ _ fib → Susp (join S¹ S¹)
-- -- -- -- -- fib→ (inl x , y) = suspFun (λ y →  inl (y * x)) y
-- -- -- -- -- fib→ (inr x , y) = suspFun (λ y →  inr (y * invLooper x)) y
-- -- -- -- -- fib→ (push a b i , y) = {!!}
-- -- -- -- --   where
-- -- -- -- --   h : PathP (λ i → isoToPath (IsoType→IsoSusp (S¹-act (a * invLooper b))) (~ i) → Susp (join S¹ S¹)) (suspFun (λ y →  inl (a * y))) (suspFun (λ y →  inr (y * invLooper b)))
-- -- -- -- --   h = toPathP (funExt λ x → (λ i → transportRefl (suspFun (λ y₁ → inl (a * y₁)) (transportRefl (suspFun (Iso.fun (S¹-act (a * invLooper b))) x) i)) i)
-- -- -- -- --             ∙ {!!}) -- (λ i → transportRefl {!transportRefl (IsoType→IsoSusp (S¹-act (a * invLooper b)) .fun x) i!} i) ∙ {!!})
-- -- -- -- --     where
-- -- -- -- --     l : (a b : S¹) (x : _) → suspFun (λ y₁ → inl (a * y₁))
-- -- -- -- --       (suspFun (λ y₁ → a * invLooper b * y₁) x)
-- -- -- -- --       ≡ suspFun (λ y₁ → inr (y₁ * invLooper b)) x
-- -- -- -- --     l a b north = refl
-- -- -- -- --     l a b south = refl
-- -- -- -- --     l a b (merid c i) j = {!!}

-- -- -- -- -- -- r : (a : S¹) → S₊ 2 → S₊ 2
-- -- -- -- -- -- r a north = north
-- -- -- -- -- -- r a south = south
-- -- -- -- -- -- r a (merid a₁ i) = merid (a * a₁) i

-- -- -- -- -- -- lem : (a : S¹) → isEquiv (r a)
-- -- -- -- -- -- lem = sphereElim 0 (λ _ → isPropIsEquiv _)
-- -- -- -- -- --        (subst isEquiv
-- -- -- -- -- --          (funExt (λ { north → refl
-- -- -- -- -- --                     ; south → refl
-- -- -- -- -- --                     ; (merid a i) → refl}))
-- -- -- -- -- --          (idEquiv (S₊ 2) .snd))

-- -- -- -- -- -- l : S₊ 2 → Type
-- -- -- -- -- -- l north = S₊ 2
-- -- -- -- -- -- l south = S₊ 2
-- -- -- -- -- -- l (merid a i) = ua (r a , lem a) (~ i)

-- -- -- -- -- -- open import Cubical.HITs.SmashProduct
-- -- -- -- -- -- tts : Σ (S₊ 2) l → Smash (S₊∙ 2) (S₊∙ 2)
-- -- -- -- -- -- tts (north , p) = proj p north
-- -- -- -- -- -- tts (south , p) = proj north p
-- -- -- -- -- -- tts (merid a i , p) =
-- -- -- -- -- --   hcomp (λ k → λ {(i = i0) → proj p north
-- -- -- -- -- --                  ; (i = i1) → (gluel (r a p) ∙∙ (sym (gluel north) ∙ gluer north) ∙∙ sym (gluer p)) k})
-- -- -- -- -- --         (proj (ua-unglue (r a , lem a) (~ i) p) north)

-- -- -- -- -- -- p1 : S₊ 2 → Susp (join S¹ S¹)
-- -- -- -- -- -- p1 north = north
-- -- -- -- -- -- p1 south = south
-- -- -- -- -- -- p1 (merid a i) = merid (inl a) i

-- -- -- -- -- -- p2 : S₊ 2 → Susp (join S¹ S¹)
-- -- -- -- -- -- p2 north = north
-- -- -- -- -- -- p2 south = south
-- -- -- -- -- -- p2 (merid a i) = merid (inr a) i

-- -- -- -- -- -- malem : (a : S¹) (x : S₊ 2) → p1 (r a x) ≡ p2 x
-- -- -- -- -- -- malem a north = refl
-- -- -- -- -- -- malem a south = refl
-- -- -- -- -- -- malem a (merid b i) j = merid (push (a * b) b j) i -- merid (push b (a * b) j) i

-- -- -- -- -- -- tssfill : (i j : I) (a : S¹) (p : ua (r a , lem a) (~ i)) → Susp (join S¹ S¹)
-- -- -- -- -- -- tssfill i j a p =
-- -- -- -- -- --   hfill (λ k → λ {(i = i0) → p1 p
-- -- -- -- -- --                  ; (i = i1) → malem a p k})
-- -- -- -- -- --         (inS (p1 (ua-unglue (r a , lem a) (~ i) p)))
-- -- -- -- -- --         j

-- -- -- -- -- -- ttss : Σ (S₊ 2) l → Susp (join S¹ S¹)
-- -- -- -- -- -- ttss (north , p) = p1 p
-- -- -- -- -- -- ttss (south , p) = p2 p
-- -- -- -- -- -- ttss (merid a i , p) = tssfill i i1 a p

-- -- -- -- -- -- Hopf : join S¹ S¹ → S₊ 2
-- -- -- -- -- -- Hopf (inl x) = north
-- -- -- -- -- -- Hopf (inr x) = south
-- -- -- -- -- -- Hopf (push a b i) = merid (a * (invLooper b)) i

-- -- -- -- -- -- Hopf' : join S¹ S¹ → S₊ 2
-- -- -- -- -- -- Hopf' (inl x) = north
-- -- -- -- -- -- Hopf' (inr x) = north
-- -- -- -- -- -- Hopf' (push a b i) = σ (S₊∙ 1) (a * (invLooper b)) i

-- -- -- -- -- -- SuspS : Susp (join S¹ S¹) → S₊ 3
-- -- -- -- -- -- SuspS = suspFun Hopf

-- -- -- -- -- -- module _ (a b : S¹) where
-- -- -- -- -- --   fillib : (i j k : I) → join S¹ S¹
-- -- -- -- -- --   fillib i j k = hfill
-- -- -- -- -- --     (λ k → λ {(i = i0) → push base (a * invLooper b) (~ j ∧ ~ k)
-- -- -- -- -- --              ; (i = i1) → push base (a * invLooper b) (~ j ∧ ~ k)
-- -- -- -- -- --              ; (j = i0) → push base (a * invLooper b) (~ k)
-- -- -- -- -- --              ; (j = i1) → inl (loop i)})
-- -- -- -- -- --              (inS (push (loop i) (a * invLooper b) (~ j))) k

-- -- -- -- -- --   filli' : (i j k : I) → join S¹ S¹
-- -- -- -- -- --   filli' i j k =
-- -- -- -- -- --     hfill ((λ k → λ {(i = i0) → push base base (j ∧ k)
-- -- -- -- -- --              ; (i = i1) → push base base (j ∧ k)
-- -- -- -- -- --              ; (j = i0) → inl base
-- -- -- -- -- --              ; (j = i1) → push (loop i) base k}))
-- -- -- -- -- --            (inS (fillib i j i1)) k

-- -- -- -- -- -- filli : (a b : S¹) (i j k : I) → join S¹ S¹
-- -- -- -- -- -- filli a b i j k =
-- -- -- -- -- --   hfill (λ k → λ {(i = i0) → ((push (a * invLooper b) base) ∙ (sym (push base base))) k
-- -- -- -- -- --                 ; (i = i1) → (push base (loop j)) (~ k)
-- -- -- -- -- --                 ; (j = i0) → compPath-filler' (push (a * invLooper b) base) (sym (push base base)) (~ i) k 
-- -- -- -- -- --                 ; (j = i1) → compPath-filler' (push (a * invLooper b) base) (sym (push base base)) (~ i) k })
-- -- -- -- -- --         (inS (push (a * invLooper b) (loop j) i))
-- -- -- -- -- --         k

-- -- -- -- -- -- SuspS' : Susp (join S¹ S¹) → join S¹ S¹
-- -- -- -- -- -- SuspS' north = inl base
-- -- -- -- -- -- SuspS' south = inl base
-- -- -- -- -- -- SuspS' (merid (inl x) i) = inl base
-- -- -- -- -- -- SuspS' (merid (inr x) i) = inl base
-- -- -- -- -- -- SuspS' (merid (push a b i) j) = filli a b i j i1

-- -- -- -- -- -- SuspS* : Susp (join S¹ S¹) → join S¹ S¹
-- -- -- -- -- -- SuspS* north = inl base
-- -- -- -- -- -- SuspS* south = inl base
-- -- -- -- -- -- SuspS* (merid (inl x) i) = inl base
-- -- -- -- -- -- SuspS* (merid (inr x) i) = inl base
-- -- -- -- -- -- SuspS* (merid (push a b i) j) =
-- -- -- -- -- --   hcomp {!!}
-- -- -- -- -- --         (hcomp {!!}
-- -- -- -- -- --                {!inS (push (loop i) (a * invLooper b) j)!})

-- -- -- -- -- -- filS3 : (a : S¹) (i j k : I) → join S¹ S¹
-- -- -- -- -- -- filS3 a i j k =
-- -- -- -- -- --   hfill (λ k → λ {(i = i0) → rCancel (push base a) k j
-- -- -- -- -- --                  ; (i = i1) → rCancel (push base a) k j
-- -- -- -- -- --                  ; (j = i0) → inl (loop i)
-- -- -- -- -- --                  ; (j = i1) → inl base})
-- -- -- -- -- --         (inS ((push (loop i) a ∙ sym (push base a)) j))
-- -- -- -- -- --         k

-- -- -- -- -- -- S₊3→ : S₊ 3 → join S¹ S¹
-- -- -- -- -- -- S₊3→ north = inl base
-- -- -- -- -- -- S₊3→ south = inl base
-- -- -- -- -- -- S₊3→ (merid north i) = inl (loop i)
-- -- -- -- -- -- S₊3→ (merid south i) = inl base
-- -- -- -- -- -- S₊3→ (merid (merid a j) i) =
-- -- -- -- -- --   filS3 a i j i1

-- -- -- -- -- -- SuspS'' : Susp (join S¹ S¹) → join S¹ S¹
-- -- -- -- -- -- SuspS'' north = inl base
-- -- -- -- -- -- SuspS'' south = inr base
-- -- -- -- -- -- SuspS'' (merid (inl x) i) = push base base i
-- -- -- -- -- -- SuspS'' (merid (inr x) i) = push base base i
-- -- -- -- -- -- SuspS'' (merid (push a b i) j) = filli' a b i j i1

-- -- -- -- -- -- blahem : Susp (join S¹ S¹) → S₊ 2
-- -- -- -- -- -- blahem x = Hopf (SuspS' x)

-- -- -- -- -- -- ra : (q : _) → Hopf' (S₊3→ (SuspS (p1 q))) ≡ north
-- -- -- -- -- -- ra north = refl
-- -- -- -- -- -- ra south = refl
-- -- -- -- -- -- ra (merid a i) = refl

-- -- -- -- -- -- la : (q : _) → Hopf' (S₊3→ (SuspS (p2 q))) ≡ south
-- -- -- -- -- -- la north = merid base
-- -- -- -- -- -- la south = merid base
-- -- -- -- -- -- la (merid a i) = merid base

-- -- -- -- -- -- haha : (p : _) → Hopf' (S₊3→ {!p2!}) ≡ {!!}
-- -- -- -- -- -- haha = {!!}

-- -- -- -- -- -- baa : (x : _) → Hopf' (S₊3→ (SuspS (ttss x))) ≡ fst x
-- -- -- -- -- -- baa (north , q) = ra q
-- -- -- -- -- -- baa (south , p) = la p
-- -- -- -- -- -- baa (merid a i , p) j =
-- -- -- -- -- --   hcomp (λ k → λ {(i = i0) → {!!} -- l2 a p j k
-- -- -- -- -- --                  ; (i = i1) → {!!} -- l1 a p j k
-- -- -- -- -- --                  ; (j = i0) → Hopf' (S₊3→ (SuspS (tssfill i k a p)))
-- -- -- -- -- --                  ; (j = i1) → merid a (i ∧ k)})
-- -- -- -- -- --     (hcomp (λ k → λ {(i = i0) → {!ra (ua-unglue (r a , lem a) (~ i) p) (~ k)!}
-- -- -- -- -- --                  ; (i = i1) → {!ra (ua-unglue (r a , lem a) (~ i) p) (~ k)!}
-- -- -- -- -- --                  ; (j = i0) → ra (ua-unglue (r a , lem a) (~ i) p) (~ k)
-- -- -- -- -- --                  ; (j = i1) → north})
-- -- -- -- -- --            {!!})
-- -- -- -- -- --   where
-- -- -- -- -- --   rightL : (a : S¹) (p : _) → Hopf' (S₊3→ (suspFun Hopf (p1 p))) ≡ north
-- -- -- -- -- --   rightL a north = refl
-- -- -- -- -- --   rightL a south = refl
-- -- -- -- -- --   rightL a (merid a₁ i) = refl

-- -- -- -- -- --   leftL : (a : S¹) (p : _) → Hopf' (S₊3→ (suspFun Hopf (p1 (r a p)))) ≡ north
-- -- -- -- -- --   leftL a north = refl
-- -- -- -- -- --   leftL a south = refl
-- -- -- -- -- --   leftL a (merid b i) j = Hopf' (S₊3→ (suspFun Hopf (merid (push a b j) i)))

-- -- -- -- -- -- --   l2 : (a : S¹) (p : _) → PathP (λ i → rightL a p i ≡ ra p i) (λ k → Hopf' (S₊3→ (suspFun Hopf (p1 p)))) refl
-- -- -- -- -- -- --   l2 a north = refl
-- -- -- -- -- -- --   l2 a south = refl
-- -- -- -- -- -- --   l2 a (merid a₁ i) = refl

-- -- -- -- -- -- --   l1 : (a : S¹) (p : _) → PathP (λ i → leftL a p i ≡ la p i) (λ k → Hopf' (S₊3→ (suspFun Hopf (malem a p k)))) (merid a)
-- -- -- -- -- -- --   l1 a north i j = compPath-filler (merid base) (sym (merid a)) (~ j) i
-- -- -- -- -- -- --   l1 a south i j = compPath-filler (merid base) (sym (merid a)) (~ j) i
-- -- -- -- -- -- --   l1 a (merid b k) i j =
-- -- -- -- -- -- --     hcomp (λ r → λ {(i = i0) → Hopf' (filS3 (a * b * invLooper b) k j r)
-- -- -- -- -- -- --                  ; (i = i1) → {!!}
-- -- -- -- -- -- --                  ; (j = i0) → {!!} -- compPath-filler (merid base) (sym (merid a)) (~ j) i
-- -- -- -- -- -- --                  ; (j = i1) → {!!} -- compPath-filler (merid base) (sym (merid a)) (~ j) i
-- -- -- -- -- -- --                  ; (k = i0) → {!Hopf' (filS3 (a * b * invLooper b) k j r)!} -- Hopf {!suspFun Hopf (malem a p k))) -- filS3 (a * b * invLooper b) j i r!}
-- -- -- -- -- -- --                  ; (k = i1) → {!!}})
-- -- -- -- -- -- --           {!!}

-- -- -- -- -- -- --   l' : PathP (λ i → (p : l (merid a i))
-- -- -- -- -- -- --                   → Hopf' (S₊3→ (SuspS (ttss (merid a i , p)))) ≡ merid a i)
-- -- -- -- -- -- --                   ra
-- -- -- -- -- -- --                   la
-- -- -- -- -- -- --   l' = toPathP (funExt (λ x → cong (transport (λ i → Hopf' (S₊3→ (SuspS (ttss (merid a i , transp (λ j → ua (r a , lem a) (~ i ∧ j)) i x)))) ≡ merid a i))
-- -- -- -- -- -- --                                                (λ _ → ra (transport refl (r a x)))
-- -- -- -- -- -- --                                 ∙∙ {!!}
-- -- -- -- -- -- --                                 ∙∙ {!transp (λ j → ua (r a , lem a) (~ i ∧ j)) i x!}))

-- -- -- -- -- -- -- blahem'' : (x : _) → Iso.fun (IsoSphereJoin 1 1) (SuspS'' x) ≡ suspFun Hopf' x
-- -- -- -- -- -- -- blahem'' north = refl
-- -- -- -- -- -- -- blahem'' south = refl
-- -- -- -- -- -- -- blahem'' (merid (inl x) i) = refl
-- -- -- -- -- -- -- blahem'' (merid (inr x) i) = refl
-- -- -- -- -- -- -- blahem'' (merid (push a b i) j) k =
-- -- -- -- -- -- --   hcomp (λ r → λ {(i = i0) → merid north (j ∧ (r ∨ k))
-- -- -- -- -- -- --                  ; (i = i1) → merid north (j ∧ (r ∨ k))
-- -- -- -- -- -- --                  ; (j = i0) → north -- north
-- -- -- -- -- -- --                  ; (j = i1) → merid north (r ∨ k)
-- -- -- -- -- -- --                  ; (k = i0) → fun (IsoSphereJoin 1 1) (filli' a b i j r)
-- -- -- -- -- -- --                  ; (k = i1) → suspFun Hopf' (merid (push a b i) j)})
-- -- -- -- -- -- --     (hcomp (λ r → λ {(i = i0) → merid north ((~ j ∧ ~ r) ∨ (j ∧ k))
-- -- -- -- -- -- --                     ; (i = i1) → merid north ((~ j ∧ ~ r) ∨ (j ∧ k)) 
-- -- -- -- -- -- --                     ; (j = i0) → merid north (~ r)
-- -- -- -- -- -- --                     ; (j = i1) → merid north k -- merid north k
-- -- -- -- -- -- --                     ; (k = i0) → fun (IsoSphereJoin 1 1) (fillib a b i j r)
-- -- -- -- -- -- --                     ; (k = i1) → {!suspFun Hopf' (merid (push a b i) ((~ j ∧ ~ r) ∨ j))!}})
-- -- -- -- -- -- --               {!!})
-- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- i = i0 ⊢ merid north j
-- -- -- -- -- -- -- i = i1 ⊢ merid north j
-- -- -- -- -- -- -- j = i0 ⊢ north
-- -- -- -- -- -- -- j = i1 ⊢ south
-- -- -- -- -- -- -- k = i0 ⊢ fun (IsoSphereJoin 1 1) (SuspS'' (merid (push a b i) j))
-- -- -- -- -- -- -- k = i1 ⊢ suspFun Hopf' (merid (push a b i) j)
-- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- blahem' : (x : _) → Iso.fun (IsoSphereJoin 1 1) (SuspS' x) ≡ suspFun Hopf' x
-- -- -- -- -- -- -- -- blahem' north = refl
-- -- -- -- -- -- -- -- blahem' south = merid north
-- -- -- -- -- -- -- -- blahem' (merid (inl x) i) j = merid north (i ∧ j)
-- -- -- -- -- -- -- -- blahem' (merid (inr x) i) j = merid north (i ∧ j)
-- -- -- -- -- -- -- -- blahem' (merid (push a b i) j) k = help i j k
-- -- -- -- -- -- -- --   where -- i j k
-- -- -- -- -- -- -- --   help : Cube (λ j k → merid north (j ∧ k)) (λ j k → merid north (j ∧ k))
-- -- -- -- -- -- -- --               (λ _ _ → north)
-- -- -- -- -- -- -- --               (λ i k → merid north k)
-- -- -- -- -- -- -- --               (λ i j → fun (IsoSphereJoin 1 1) (SuspS' (merid (push a b i) j)))
-- -- -- -- -- -- -- --               λ i j → merid (σ (S₊∙ 1) (a * invLooper b) i) j
-- -- -- -- -- -- -- --   help i j k =
-- -- -- -- -- -- -- --     hcomp (λ r → λ {(i = i0) → {!!} -- merid north (j ∧ k)
-- -- -- -- -- -- -- --                    ; (i = i1) → {!compPath-filler (merid (compPath-filler (merid (a * invLooper b)) (sym (merid base)) r i)) (sym (merid north)) (~ r) j!} -- merid (merid base (~ r)) (j ∧ k)
-- -- -- -- -- -- -- --                    ; (j = i0) → north -- north
-- -- -- -- -- -- -- --                    ; (j = i1) → merid north (k ∧ r) -- merid (merid base (i ∧ ~ r)) k
-- -- -- -- -- -- -- --                    ; (k = i0) → Iso.fun (IsoSphereJoin 1 1) (filli a b i j i1)
-- -- -- -- -- -- -- --                    ; (k = i1) → compPath-filler (merid (compPath-filler (merid (a * invLooper b)) (sym (merid base)) r i)) (sym (merid north)) (~ r) j }) -- merid (compPath-filler (merid (a * invLooper b)) (sym (merid base)) r i) j})
-- -- -- -- -- -- -- --      (hcomp (λ r → λ {(i = i0) → {!!}
-- -- -- -- -- -- -- --                    ; (i = i1) → {!!}
-- -- -- -- -- -- -- --                    ; (j = i0) → Iso.fun (IsoSphereJoin 1 1) (compPath-filler' (push (a * invLooper b) base) (sym (push base base)) (~ i) r)
-- -- -- -- -- -- -- --                    ; (j = i1) → {!Iso.fun (IsoSphereJoin 1 1) (compPath-filler' (push (a * invLooper b) base) (sym (push base base)) (~ i) i1)!}
-- -- -- -- -- -- -- --                    ; (k = i0) → Iso.fun (IsoSphereJoin 1 1) (filli a b i j r)
-- -- -- -- -- -- -- --                    ; (k = i1) → {!!}})
-- -- -- -- -- -- -- --             {!!})
-- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- --     help' : cong (Iso.fun (IsoSphereJoin 1 1)) ((push (a * invLooper b) base) ∙ (sym (push base base))) ≡ refl
-- -- -- -- -- -- -- --     help' = cong-∙ ( (Iso.fun (IsoSphereJoin 1 1)))
-- -- -- -- -- -- -- --                    (push (a * invLooper b) base) (sym (push base base))
-- -- -- -- -- -- -- --                  ∙ ((cong (λ x → merid x ∙ sym (merid north)) (S¹×S¹→S²rUnit (a * invLooper b))
-- -- -- -- -- -- -- --                  ∙ rCancel (merid north)))
-- -- -- -- -- -- -- --     helpC : cong (Iso.fun (IsoSphereJoin 1 1)) ≡ {!!}
-- -- -- -- -- -- -- --     helpC = {!!}

-- -- -- -- -- -- -- --     Square1 : Cube (λ i k → merid north (~ k))
-- -- -- -- -- -- -- --                    (λ j k → (Iso.fun (IsoSphereJoin 1 1))
-- -- -- -- -- -- -- --                    ((push base (loop j)) (~ k)))
-- -- -- -- -- -- -- --                    (λ i k → merid north (~ k))
-- -- -- -- -- -- -- --                    (λ i k → merid north (~ k))
-- -- -- -- -- -- -- --                    (λ _ _ → south) λ _ _ → north
-- -- -- -- -- -- -- --     Square1 i j k = merid north (~ k)

-- -- -- -- -- -- -- --     -- r j k
-- -- -- -- -- -- -- --     helpi0 : Cube {!λ _ !} (λ j k → merid north (j ∧ k))
-- -- -- -- -- -- -- --                   {!!} -- (λ r k → help' k r) -- (λ r k → Iso.fun (IsoSphereJoin 1 1) (filli a b i0 i0 r))
-- -- -- -- -- -- -- --                   {!!} -- (flipSquare (compPath-filler (cong (Iso.fun (IsoSphereJoin 1 1)) (λ r → filli a b i0 i1 r)) (merid north)))
-- -- -- -- -- -- -- --                   (λ r j → Iso.fun (IsoSphereJoin 1 1)  (filli a b i0 j r))
-- -- -- -- -- -- -- --                   {!λ r j → Iso.fun (IsoSphereJoin 1 1)  (filli a b i0 j r)!}
-- -- -- -- -- -- -- --     helpi0 = {!!}

-- -- -- -- -- -- -- --     help'' : Cube (λ _ _ → south)
-- -- -- -- -- -- -- --                   (λ j k → merid north (j ∧ k))
-- -- -- -- -- -- -- --                   (λ r k → merid north (~ r))
-- -- -- -- -- -- -- --                   (λ r k → merid north (~ r ∨ k))
-- -- -- -- -- -- -- --                   (λ r j → Iso.fun (IsoSphereJoin 1 1) ((push base (loop j)) (~ r)))
-- -- -- -- -- -- -- --                   λ r j → merid north (~ r ∨ j)
-- -- -- -- -- -- -- --     help'' r j k = merid north (~ r ∨ (k ∧ j))

-- -- -- -- -- -- -- -- -- open import Cubical.HITs.Pushout


-- -- -- -- -- -- -- -- -- SS : Susp (join S¹ S¹) → S₊ 2
-- -- -- -- -- -- -- -- -- SS x = Hopf (Iso.inv (IsoSphereJoin 1 1) (SuspS x))

-- -- -- -- -- -- -- -- -- SS2 : Σ (S₊ 2) l → S₊ 2
-- -- -- -- -- -- -- -- -- SS2 x = SS (ttss x)

-- -- -- -- -- -- -- -- -- rs : (p : _) → SS2 (north , p) ≡ north
-- -- -- -- -- -- -- -- -- rs north = refl
-- -- -- -- -- -- -- -- -- rs south = refl
-- -- -- -- -- -- -- -- -- rs (merid a i) j = Hopf (inv (IsoSphereJoin 1 1) (merid (merid a j) i))

-- -- -- -- -- -- -- -- -- ls : (p : _) → SS2 (south , p) ≡ south
-- -- -- -- -- -- -- -- -- ls north = merid base
-- -- -- -- -- -- -- -- -- ls south = merid base
-- -- -- -- -- -- -- -- -- ls (merid a i) = merid base

-- -- -- -- -- -- -- -- -- lem' : (x : Σ (S₊ 2) l) → SS2 x ≡ fst x
-- -- -- -- -- -- -- -- -- lem' (north , x) = rs x
-- -- -- -- -- -- -- -- -- lem' (south , p) = ls p
-- -- -- -- -- -- -- -- -- lem' (merid a i , p) j =
-- -- -- -- -- -- -- -- --   hcomp (λ k → λ {(i = i0) → rs p j
-- -- -- -- -- -- -- -- --                  ; (i = i1) → {!!} -- lol a p j k
-- -- -- -- -- -- -- -- --                  ; (j = i0) → SS (tssfill i k a p)
-- -- -- -- -- -- -- -- --                  ; (j = i1) → merid a (i ∧ k)})
-- -- -- -- -- -- -- -- --         (hcomp (λ k → λ {(i = i0) → {!!}
-- -- -- -- -- -- -- -- --                  ; (i = i1) → {!!} -- cooll a p j k
-- -- -- -- -- -- -- -- --                  ; (j = i0) → {!!} -- blat2 a (ua-unglue (r a , lem a) (~ i) p) (~ k)
-- -- -- -- -- -- -- -- --                  ; (j = i1) → north})
-- -- -- -- -- -- -- -- --                {!!})

-- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- i = i0 ⊢ rs p j
-- -- -- -- -- -- -- -- -- i = i1 ⊢ ls p j
-- -- -- -- -- -- -- -- -- j = i0 ⊢ SS2 (merid a i , p)
-- -- -- -- -- -- -- -- -- j = i1 ⊢ merid a i
-- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   blat : (a : _) (p : _) → SS (p1 (r a p)) ≡ north
-- -- -- -- -- -- -- -- --   blat a north = merid base ∙ sym (merid a)
-- -- -- -- -- -- -- -- --   blat a south = merid base ∙ sym (merid a)
-- -- -- -- -- -- -- -- --   blat a (merid a₁ i) = {!!} -- merid base ∙ sym (merid a)

-- -- -- -- -- -- -- -- --   blat2 : (a : S¹) → (p : _) → SS (p1 p) ≡ north
-- -- -- -- -- -- -- -- --   blat2 a north = refl -- merid base ∙ sym (merid a)
-- -- -- -- -- -- -- -- --   blat2 a south = refl -- merid base ∙ sym (merid a)
-- -- -- -- -- -- -- -- --   blat2 a (merid b i) j = {!Hopf (inv (IsoSphereJoin 1 1) (merid (merid ? k)))!} -- merid base ∙ sym (merid a)

-- -- -- -- -- -- -- -- -- --   cooll : (a : S¹) → (p : _) → Square (sym (blat2 a (r a p))) (λ _ → north) refl (blat a p)
-- -- -- -- -- -- -- -- -- --   cooll a north i j = (merid base ∙ sym (merid a)) (~ j ∨ i)
-- -- -- -- -- -- -- -- -- --   cooll a south i j = (merid base ∙ sym (merid a)) (~ j ∨ i)
-- -- -- -- -- -- -- -- -- --   cooll a (merid a₁ _) i j = (merid base ∙ sym (merid a)) (~ j ∨ i)


-- -- -- -- -- -- -- -- -- --   lol : (a : S¹) (p : S₊ (suc (suc zero)))
-- -- -- -- -- -- -- -- -- --     → Square (cong SS (malem a p)) (merid a) (blat a p) (ls p)
-- -- -- -- -- -- -- -- -- --   lol a north j k = compPath-filler (merid base) (sym (merid a)) (~ k) j
-- -- -- -- -- -- -- -- -- --   lol a south j k = compPath-filler (merid base) (sym (merid a)) (~ k) j
-- -- -- -- -- -- -- -- -- --   lol a (merid a₁ i) j k =
-- -- -- -- -- -- -- -- -- --     hcomp (λ r → λ {(i = i0) → compPath-filler (merid base) (λ i₂ → merid a (~ i₂)) (~ k) j
-- -- -- -- -- -- -- -- -- --                    ; (i = i1) → compPath-filler (merid base) (λ i₂ → merid a (~ i₂)) (~ k) j
-- -- -- -- -- -- -- -- -- --                    ; (j = i0) → Hopf (inv (IsoSphereJoin 1 1) (merid (merid (cool (~ r)) k) i ))
-- -- -- -- -- -- -- -- -- --                    ; (j = i1) → merid a k -- compPath-filler (merid base) (λ i₂ → merid a (~ i₂)) (~ k) j
-- -- -- -- -- -- -- -- -- --                    ; (k = i0) → (merid base ∙ (λ i₂ → merid a (~ i₂))) j
-- -- -- -- -- -- -- -- -- --                    ; (k  = i1) → merid base j})
-- -- -- -- -- -- -- -- -- --           (hcomp (λ r → λ {(i = i0) → compPath-filler (merid base) (λ i₂ → merid a (~ i₂)) (~ k ∧ r) j
-- -- -- -- -- -- -- -- -- --                           ; (i = i1) → compPath-filler (merid base) (λ i₂ → merid a (~ i₂)) (~ k ∧ r) j
-- -- -- -- -- -- -- -- -- --                           ; (j = i0) → lem1 a (~ r) k i -- Hopf (inv (IsoSphereJoin 1 1) (merid (merid a k) i))
-- -- -- -- -- -- -- -- -- --                           ; (j = i1) → merid a (k ∨ ~ r)
-- -- -- -- -- -- -- -- -- --                           ; (k = i0) → compPath-filler (merid base) (λ i₂ → merid a (~ i₂)) r j
-- -- -- -- -- -- -- -- -- --                           ; (k  = i1) → merid base j})
-- -- -- -- -- -- -- -- -- --                   (merid base j))
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --     cool : a * a₁ * invLooper a₁ ≡ a
-- -- -- -- -- -- -- -- -- --     cool = {!S¹assoc!} ∙ {!!}

-- -- -- -- -- -- -- -- -- --     kebab = S³→joinS¹S¹

-- -- -- -- -- -- -- -- -- --     lem1 : (a : S¹) → cong (cong (Hopf ∘ inv (IsoSphereJoin 1 1))) (cong merid (merid a))
-- -- -- -- -- -- -- -- -- --          ≡ refl
-- -- -- -- -- -- -- -- -- --     lem1 a = {!!}

-- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- i = i0 ⊢ compPath-filler (merid base) (λ i₂ → merid a (~ i₂)) (~ k)
-- -- -- -- -- -- -- -- -- --          j
-- -- -- -- -- -- -- -- -- -- i = i1 ⊢ compPath-filler (merid base) (λ i₂ → merid a (~ i₂)) (~ k)
-- -- -- -- -- -- -- -- -- --          j
-- -- -- -- -- -- -- -- -- -- j = i0 ⊢ cong SS (λ j₂ → merid (push (a * a₁) (invLooper a₁) j₂) i)
-- -- -- -- -- -- -- -- -- --          k
-- -- -- -- -- -- -- -- -- -- j = i1 ⊢ merid a k
-- -- -- -- -- -- -- -- -- -- k = i0 ⊢ (merid base ∙ (λ i₂ → merid a (~ i₂))) j
-- -- -- -- -- -- -- -- -- -- k = i1 ⊢ merid base j
-- -- -- -- -- -- -- -- -- -- -}



-- -- -- -- -- -- -- -- -- --   asd : PathP (λ i → (p : ua (r a , lem a) (~ i)) → SS2 (merid a i , p) ≡ merid a i) rs ls
-- -- -- -- -- -- -- -- -- --   asd = toPathP (funExt λ x → (λ i → transport (λ j → SS2 (merid a j , transp (λ k → ua (r a , lem a) (~ (j ∨ ~ k))) j x) ≡ merid a j)
-- -- -- -- -- -- -- -- -- --                                                  (rs (transport refl (r a x))))
-- -- -- -- -- -- -- -- -- --                     ∙ {!rs!}
-- -- -- -- -- -- -- -- -- --                     ∙ {!!})
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --     help : (x : _) → rs (transport (λ j → ua (r a , lem a) (~ (i0 ∨ ~ j))) x) ≡ {!rs (r a x)!} -- r a x
-- -- -- -- -- -- -- -- -- --     help x = {!!}
-- -- -- -- -- -- -- -- -- -- -- cool : Σ (S₊ 2) l → join S¹ S¹
-- -- -- -- -- -- -- -- -- -- -- cool (north , snd₁) = q1 snd₁
-- -- -- -- -- -- -- -- -- -- -- cool (south , snd₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- cool (merid a i , b) = {!!}

-- -- -- -- -- -- -- -- -- -- -- compi : Σ (S₊ 2) l → S₊ 2
-- -- -- -- -- -- -- -- -- -- -- compi x = Hopf {!!}


-- -- -- -- -- -- -- -- -- -- -- -- idi : Iso (Σ (S₊ 2) l) (S₊ 2 × S₊ 2)
-- -- -- -- -- -- -- -- -- -- -- -- fun idi (north , p) = p , p
-- -- -- -- -- -- -- -- -- -- -- -- fun idi (south , p) = p , p
-- -- -- -- -- -- -- -- -- -- -- -- fun idi (merid a i , p) = help i p
-- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- --   help : PathP (λ i → (ua (r a , lem a) i) → S₊ 2 × S₊ 2) (λ p → p , p) (λ p → p , p)
-- -- -- -- -- -- -- -- -- -- -- --   help = toPathP (funExt λ x → (λ i → transportRefl (invEq (r a , lem a) (transportRefl x i) , invEq (r a , lem a) (transportRefl x i)) i) ∙ {!!})
-- -- -- -- -- -- -- -- -- -- -- -- inv idi = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- rightInv idi = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- leftInv idi = {!!}
