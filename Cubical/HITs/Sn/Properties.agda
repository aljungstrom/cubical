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


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int

open import Cubical.HITs.S1 hiding (encode)
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Join
open import Cubical.HITs.SetTruncation as SetTrunc
open import Cubical.HITs.GroupoidTruncation as GroupoidTrunc
open import Cubical.HITs.2GroupoidTruncation as 2GroupoidTrunc
open import Cubical.HITs.Truncation as Trunc
open import Cubical.HITs.Susp renaming (toSusp to σ)

open import Cubical.Homotopy.Loopspace

Bool∙ S¹∙ S³∙ : Pointed₀
Bool∙ = (Bool , true)
S¹∙ = (S¹ , base)
S³∙ = (S³ , base)

∥_∥₃∙ ∥_∥₄∙ : Pointed₀ → Pointed₀
∥ A , a ∥₃∙ = ∥ A ∥₃ , ∣ a ∣₃
∥ A , a ∥₄∙ = ∥ A ∥₄ , ∣ a ∣₄

join∙ : Pointed₀ → Type₀ → Pointed₀
join∙ (A , a) B = join A B , inl a

Ω² Ω³ : Pointed₀ → Pointed₀
Ω² = Ω^ 2
Ω³ = Ω^ 3

mapΩrefl : {A : Pointed₀} {B : Type₀} (f : A .fst → B) → Ω A .fst → Ω (B , f (pt A)) .fst
mapΩrefl f p i = f (p i)

mapΩ²refl : {A : Pointed₀} {B : Type₀} (f : A .fst → B) → Ω² A .fst → Ω² (B , f (pt A)) .fst
mapΩ²refl f p i j = f (p i j)

mapΩ³refl : {A : Pointed₀} {B : Type₀} (f : A .fst → B) → Ω³ A .fst → Ω³ (B , f (pt A)) .fst
mapΩ³refl f p i j k = f (p i j k)

meridS² : S¹ → Path S² base base
meridS² base _ = base
meridS² (loop i) j = surf i j

alpha : join S¹ S¹ → S²
alpha (inl x) = base
alpha (inr y) = base
alpha (push x y i) = (meridS² y ∙ meridS² x) i

connectionBoth : {A : Type₀} {a : A} (p : Path A a a) → PathP (λ i → Path A (p i) (p i)) p p
connectionBoth {a = a} p i j =
  hcomp
    (λ k → λ
      { (i = i0) → p (j ∨ ~ k)
      ; (i = i1) → p (j ∧ k)
      ; (j = i0) → p (i ∨ ~ k)
      ; (j = i1) → p (i ∧ k)
      })
    a

data PostTotalHopf : Type₀ where
  base : S¹ → PostTotalHopf
  loop : (x : S¹) → PathP (λ i → Path PostTotalHopf (base x) (base (rotLoop x (~ i)))) refl refl

-- Direct construction of Hopf fibration for S¹
module S¹Hopf where
  Border : (x : S¹) → (j : I) → Partial (j ∨ ~ j) (Σ Type₀ (λ T → T ≃ S¹))
  Border x j (j = i0) = S¹ , (x *_) , rotIsEquiv x
  Border x j (j = i1) = S¹ , idEquiv S¹

  -- Hopf fibration using SuspS¹
  HopfSuspS¹ : SuspS¹ → Type₀
  HopfSuspS¹ north = S¹
  HopfSuspS¹ south = S¹
  HopfSuspS¹ (merid x j) = Glue S¹ (Border x j)

  -- Hopf fibration using S²
  -- TODO : prove that it is equivalent to HopfSuspS¹
  HopfS² : S² → Type₀
  HopfS² base = S¹
  HopfS² (surf i j) = Glue S¹ (λ { (i = i0) → _ , idEquiv S¹
                                 ; (i = i1) → _ , idEquiv S¹
                                 ; (j = i0) → _ , idEquiv S¹
                                 ; (j = i1) → _ , _ , rotIsEquiv (loop i) } )

open S¹Hopf

tee12 : (x : S²) → HopfS² x → PostTotalHopf
tee12 base y = base y
tee12 (surf i j) y =
  hcomp
    (λ k → λ
      { (i = i0) → base y
      ; (i = i1) → base y
      ; (j = i0) → base y
      ; (j = i1) → base (rotLoopInv y (~ i) k)
      })
    (loop (unglue (i ∨ ~ i ∨ j ∨ ~ j) y) i j)

tee34 : PostTotalHopf → join S¹ S¹
tee34 (base x) = inl x
tee34 (loop x i j) =
  hcomp
    (λ k → λ
      { (i = i0) → push x x (j ∧ ~ k)
      ; (i = i1) → push x x (j ∧ ~ k)
      ; (j = i0) → inl x
      ; (j = i1) → push (rotLoop x (~ i)) x (~ k)
      })
    (push x x j)

tee : (x : S²) → HopfS² x → join S¹ S¹
tee x y = tee34 (tee12 x y)

fibΩ : {B : Pointed₀} (P : B .fst → Type₀) → P (pt B) → Ω B .fst → Type₀
fibΩ P f p = PathP (λ i → P (p i)) f f

fibΩ² : {B : Pointed₀} (P : B .fst → Type₀) → P (pt B) → Ω² B .fst → Type₀
fibΩ² P f = fibΩ (fibΩ P f) refl

fibΩ³ : {B : Pointed₀} (P : B .fst → Type₀) → P (pt B) → Ω³ B .fst → Type₀
fibΩ³ P f = fibΩ² (fibΩ P f) refl

Ω³Hopf : Ω³ S²∙ .fst → Type₀
Ω³Hopf = fibΩ³ HopfS² base

isGp-HopfS² : (x : S²) → isGroupoid (HopfS² x)
isGp-HopfS² = S²ToSetElim (λ _ → isProp→isSet isPropIsGroupoid) isGroupoidS¹

fibContrΩ³Hopf : ∀ p → Ω³Hopf p
fibContrΩ³Hopf p i j k =
  isOfHLevel→isOfHLevelDep 3 {B = HopfS²}
    isGp-HopfS² {a0 = base} {a1 = base} base base refl refl refl refl p i j k

h : Ω³ S²∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
h p i j k = tee (p i j k) (fibContrΩ³Hopf p i j k)

multTwoAux : (x : S²) → Path (Path ∥ S² ∥₄ ∣ x ∣₄ ∣ x ∣₄) refl refl
multTwoAux base i j = ∣ surf i j ∣₄
multTwoAux (surf k l) i j =
  hcomp
    (λ m → λ
      { (i = i0) → ∣ surf k l ∣₄
      ; (i = i1) → ∣ surf k l ∣₄
      ; (j = i0) → ∣ surf k l ∣₄
      ; (j = i1) → ∣ surf k l ∣₄
      ; (k = i0) → ∣ surf i j ∣₄
      ; (k = i1) → ∣ surf i j ∣₄
      ; (l = i0) → ∣ surf i j ∣₄
      ; (l = i1) → squash₄ _ _ _ _ _ _ (λ k i j → step₁ k i j) refl m k i j
      })
    (step₁ k i j)

  where
  step₁ : I → I → I → ∥ S² ∥₄
  step₁ k i j =
    hcomp {A = ∥ S² ∥₄}
      (λ m → λ
        { (i = i0) → ∣ surf k (l ∧ m) ∣₄
        ; (i = i1) → ∣ surf k (l ∧ m) ∣₄
        ; (j = i0) → ∣ surf k (l ∧ m) ∣₄
        ; (j = i1) → ∣ surf k (l ∧ m) ∣₄
        ; (k = i0) → ∣ surf i j ∣₄
        ; (k = i1) → ∣ surf i j ∣₄
        ; (l = i0) → ∣ surf i j ∣₄
        })
     ∣ surf i j ∣₄

multTwoTildeAux : (t : ∥ S² ∥₄) → Path (Path ∥ S² ∥₄ t t) refl refl
multTwoTildeAux ∣ x ∣₄ = multTwoAux x
multTwoTildeAux (squash₄ _ _ _ _ _ _ t u k l m n) i j =
  squash₄ _ _ _ _ _ _
    (λ k l m → multTwoTildeAux (t k l m) i j)
    (λ k l m → multTwoTildeAux (u k l m) i j)
    k l m n

-- f* : I → I → ∥ S² ∥₄ → ∥ S² ∥₄
-- f* i j t = multTwoTildeAux t i j

-- multTwoEquivAux : Path (Path (∥ S² ∥₄ ≃ ∥ S² ∥₄) (idEquiv _) (idEquiv _)) refl refl
-- fst (multTwoEquivAux i j) = f* i j
-- snd (multTwoEquivAux i j) =
--   isOfHLevel→isOfHLevelDep 2 {B = isEquiv} (λ _ → isProp→isSet (isPropIsEquiv _)) (idIsEquiv ∥ S² ∥₄) (idIsEquiv ∥ S² ∥₄) refl refl (λ i j → f* i j) i j

-- tHopf³ : S³ → Type₀
-- tHopf³ base = ∥ S² ∥₄
-- tHopf³ (surf i j k) =
--   Glue ∥ S² ∥₄
--     (λ { (i = i0) → (∥ S² ∥₄ , idEquiv _)
--        ; (i = i1) → (∥ S² ∥₄ , idEquiv _)
--        ; (j = i0) → (∥ S² ∥₄ , idEquiv _)
--        ; (j = i1) → (∥ S² ∥₄ , idEquiv _)
--        ; (k = i0) → (∥ S² ∥₄ , multTwoEquivAux i j)
--        ; (k = i1) → (∥ S² ∥₄ , idEquiv _)
--        })

-- π₃S³ : Ω³ S³∙ .fst → Ω² ∥ S²∙ ∥₄∙ .fst
-- π₃S³ p i j = transp (λ k → tHopf³ (p j k i)) i0 ∣ base ∣₄

-- codeS² : S² → hGroupoid _
-- codeS² s = ∥ HopfS² s ∥₃ , squash₃

-- codeTruncS² : ∥ S² ∥₄ → hGroupoid _
-- codeTruncS² = 2GroupoidTrunc.rec (isOfHLevelTypeOfHLevel 3) codeS²

-- encodeTruncS² : Ω ∥ S²∙ ∥₄∙ .fst → ∥ S¹ ∥₃
-- encodeTruncS² p = transp (λ i → codeTruncS² (p i) .fst) i0 ∣ base ∣₃

-- codeS¹ : S¹ → hSet _
-- codeS¹ s = ∥ helix s ∥₂ , squash₂

-- codeTruncS¹ : ∥ S¹ ∥₃ → hSet _
-- codeTruncS¹ = GroupoidTrunc.rec (isOfHLevelTypeOfHLevel 2) codeS¹

-- encodeTruncS¹ : Ω ∥ S¹∙ ∥₃∙ .fst → ∥ ℤ ∥₂
-- encodeTruncS¹ p = transp (λ i → codeTruncS¹ (p i) .fst) i0 ∣ pos zero ∣₂


-- -- THE BIG GAME

-- f3 : Ω³ S³∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
-- f3 = mapΩ³refl S³→joinS¹S¹

-- f4 : Ω³ (join∙ S¹∙ S¹) .fst → Ω³ S²∙ .fst
-- f4 = mapΩ³refl alpha

-- f5 : Ω³ S²∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
-- f5 = h

-- f6 : Ω³ (join∙ S¹∙ S¹) .fst → Ω³ S³∙ .fst
-- f6 = mapΩ³refl joinS¹S¹→S3

-- f7 : Ω³ S³∙ .fst → Ω² ∥ S²∙ ∥₄∙ .fst
-- f7 = π₃S³

-- g8 : Ω² ∥ S²∙ ∥₄∙ .fst → Ω ∥ S¹∙ ∥₃∙ .fst
-- g8 = mapΩrefl encodeTruncS²

-- g9 : Ω ∥ S¹∙ ∥₃∙ .fst → ∥ ℤ ∥₂
-- g9 = encodeTruncS¹

-- g10 : ∥ ℤ ∥₂ → ℤ
-- g10 = SetTrunc.rec isSetℤ (idfun ℤ)

-- -- don't run me
-- brunerie : ℤ
-- brunerie = g10 (g9 (g8 (f7 (f6 (f5 (f4 (f3 (λ i j k → surf i j k))))))))


-- -- IsoSucSphereSusp : (n : ℕ) → Iso (S₊ (suc n)) (Susp (S₊ n))
-- -- IsoSucSphereSusp zero = S¹IsoSuspBool
-- -- IsoSucSphereSusp (suc n) = idIso

-- -- IsoSucSphereSusp∙ : (n : ℕ)
-- --   → Iso.inv (IsoSucSphereSusp n) north ≡ ptSn (suc n)
-- -- IsoSucSphereSusp∙ zero = refl
-- -- IsoSucSphereSusp∙ (suc n) = refl

-- -- -- Elimination principles for spheres
-- -- sphereElim : (n : ℕ) {A : (S₊ (suc n)) → Type ℓ} → ((x : S₊ (suc n)) → isOfHLevel (suc n) (A x))
-- --           → A (ptSn (suc n))
-- --           → (x : S₊ (suc n)) → A x
-- -- sphereElim zero hlev pt = toPropElim hlev pt
-- -- sphereElim (suc n) hlev pt north = pt
-- -- sphereElim (suc n) {A = A} hlev pt south = subst A (merid (ptSn (suc n))) pt
-- -- sphereElim (suc n) {A = A} hlev pt (merid a i) =
-- --   sphereElim n {A = λ a → PathP (λ i → A (merid a i)) pt (subst A (merid (ptSn (suc n))) pt)}
-- --                (λ a → isOfHLevelPathP' (suc n) (hlev south) _ _)
-- --                (λ i → transp (λ j → A (merid (ptSn (suc n)) (i ∧ j))) (~ i) pt)
-- --                a i

-- -- sphereElim2 : ∀ {ℓ} (n : ℕ) {A : (S₊ (suc n)) → (S₊ (suc n)) → Type ℓ}
-- --           → ((x y : S₊ (suc n)) → isOfHLevel (suc n) (A x y))
-- --           → A (ptSn (suc n)) (ptSn (suc n))
-- --           → (x y : S₊ (suc n)) → A x y
-- -- sphereElim2 n hlev pt = sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → hlev _ _)
-- --                                      (sphereElim n (hlev _ ) pt)

-- -- private
-- --   compPath-lem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y)
-- --               → PathP (λ i → (p ∙ sym q) i ≡ y) p q
-- --   compPath-lem {y = y} p q i j =
-- --     hcomp (λ k → λ { (i = i0) → p j
-- --                     ; (i = i1) → q (~ k ∨ j)
-- --                     ; (j = i1) → y })
-- --           (p (j ∨ i))

-- -- sphereToPropElim : (n : ℕ) {A : (S₊ (suc n)) → Type ℓ} → ((x : S₊ (suc n)) → isProp (A x))
-- --           → A (ptSn (suc n))
-- --           → (x : S₊ (suc n)) → A x
-- -- sphereToPropElim zero = toPropElim
-- -- sphereToPropElim (suc n) hlev pt north = pt
-- -- sphereToPropElim (suc n) {A = A} hlev pt south = subst A (merid (ptSn (suc n))) pt
-- -- sphereToPropElim (suc n) {A = A} hlev pt (merid a i) =
-- --   isProp→PathP {B = λ i → A (merid a i)} (λ _ → hlev _) pt (subst A (merid (ptSn (suc n))) pt) i

-- -- -- Elimination rule for fibrations (x : Sⁿ) → (y : Sᵐ) → A x y of h-Level (n + m).
-- -- -- The following principle is just the special case of the "Wedge Connectivity Lemma"
-- -- -- for spheres (See Cubical.Homotopy.WedgeConnectivity or chapter 8.6 in the HoTT book).
-- -- -- We prove it directly here for three reasons:
-- -- -- (i) it should perform better
-- -- -- (ii) we get a slightly stronger statement for spheres: one of the homotopies will, by design, be refl
-- -- -- (iii) the fact that the two homotopies only differ by (composition with) the homotopy leftFunction(base) ≡ rightFunction(base)
-- -- -- is close to trivial

-- -- wedgeconFun : (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
-- --           → ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y))
-- --           → (f : (x : _) → A (ptSn (suc n)) x)
-- --           → (g : (x : _) → A x (ptSn (suc m)))
-- --           → (g (ptSn (suc n)) ≡ f (ptSn (suc m)))
-- --           → (x : S₊ (suc n)) (y : S₊ (suc m)) → A x y
-- -- wedgeconLeft : (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
-- --              → (hLev : ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y)))
-- --              → (f : (x : _) → A (ptSn (suc n)) x)
-- --              → (g : (x : _) → A x (ptSn (suc m)))
-- --              → (hom : g (ptSn (suc n)) ≡ f (ptSn (suc m)))
-- --              → (x : _) → wedgeconFun n m hLev f g hom (ptSn (suc n)) x ≡ f x
-- -- wedgeconRight : (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
-- --              → (hLev : ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y)))
-- --              → (f : (x : _) → A (ptSn (suc n)) x)
-- --              → (g : (x : _) → A x (ptSn (suc m)))
-- --              → (hom : g (ptSn (suc n)) ≡ f (ptSn (suc m)))
-- --              → (x : _) → wedgeconFun n m hLev f g hom x (ptSn (suc m)) ≡ g x
-- -- wedgeconFun zero zero {A = A} hlev f g hom = F
-- --   where
-- --   helper : SquareP (λ i j → A (loop i) (loop j)) (cong f loop) (cong f loop)
-- --                         (λ i → hcomp (λ k → λ { (i = i0) → hom k
-- --                                                 ; (i = i1) → hom k })
-- --                                       (g (loop i)))
-- --                          λ i → hcomp (λ k → λ { (i = i0) → hom k
-- --                                                 ; (i = i1) → hom k })
-- --                                        (g (loop i))
-- --   helper = toPathP (isOfHLevelPathP' 1 (hlev _ _) _ _ _ _)

-- --   F : (x y : S¹) → A x y
-- --   F base y = f y
-- --   F (loop i) base = hcomp (λ k → λ { (i = i0) → hom k
-- --                                     ; (i = i1) → hom k })
-- --                           (g (loop i))
-- --   F (loop i) (loop j) = helper i j

-- -- wedgeconFun zero (suc m) {A = A} hlev f g hom = F₀
-- --   module _ where
-- --   transpLemma₀ : (x : S₊ (suc m)) → transport (λ i₁ → A base (merid x i₁)) (g base) ≡ f south
-- --   transpLemma₀ x = cong (transport (λ i₁ → A base (merid x i₁)))
-- --                                   hom
-- --               ∙ (λ i → transp (λ j → A base (merid x (i ∨ j))) i
-- --                                (f (merid x i)))

-- --   pathOverMerid₀ : (x : S₊ (suc m)) → PathP (λ i₁ → A base (merid x i₁))
-- --                                             (g base)
-- --                                             (transport (λ i₁ → A base (merid (ptSn (suc m)) i₁))
-- --                                                        (g base))
-- --   pathOverMerid₀ x i = hcomp (λ k → λ { (i = i0) → g base
-- --                                       ; (i = i1) → (transpLemma₀ x ∙ sym (transpLemma₀ (ptSn (suc m)))) k})
-- --                             (transp (λ i₁ → A base (merid x (i₁ ∧ i))) (~ i)
-- --                                     (g base))

-- --   pathOverMeridId₀ : pathOverMerid₀ (ptSn (suc m)) ≡ λ i → transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
-- --                                                                  (g base)
-- --   pathOverMeridId₀  =
-- --        (λ j i → hcomp (λ k → λ {(i = i0) → g base
-- --                                ; (i = i1) → rCancel (transpLemma₀ (ptSn (suc m))) j k})
-- --                       (transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
-- --                               (g base)))
-- --      ∙ λ j i → hfill (λ k → λ { (i = i0) → g base
-- --                                 ; (i = i1) → transport (λ i₁ → A base (merid (ptSn (suc m)) i₁))
-- --                                                         (g base)})
-- --                       (inS (transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
-- --                                    (g base))) (~ j)

-- --   indStep₀ : (x : _) (a : _) → PathP (λ i → A x (merid a i))
-- --                                              (g x)
-- --                                              (subst (λ y → A x y) (merid (ptSn (suc m)))
-- --                                                     (g x))
-- --   indStep₀ = wedgeconFun zero m (λ _ _ → isOfHLevelPathP' (2 + m) (hlev _ _) _ _)
-- --                               pathOverMerid₀
-- --                               (λ a i → transp (λ i₁ → A a (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
-- --                                                (g a))
-- --                               (sym pathOverMeridId₀)

-- --   F₀ : (x : S¹) (y : Susp (S₊ (suc m))) → A x y
-- --   F₀ x north = g x
-- --   F₀ x south = subst (λ y → A x y) (merid (ptSn (suc m))) (g x)
-- --   F₀ x (merid a i) = indStep₀ x a i
-- -- wedgeconFun (suc n) m {A = A} hlev f g hom = F₁
-- --   module _ where
-- --   transpLemma₁ : (x : S₊ (suc n)) → transport (λ i₁ → A (merid x i₁) (ptSn (suc m))) (f (ptSn (suc m))) ≡ g south
-- --   transpLemma₁ x = cong (transport (λ i₁ → A (merid x i₁) (ptSn (suc m))))
-- --                        (sym hom)
-- --                 ∙ (λ i → transp (λ j → A (merid x (i ∨ j)) (ptSn (suc m))) i
-- --                                  (g (merid x i)))

-- --   pathOverMerid₁ : (x : S₊ (suc n)) → PathP (λ i₁ → A (merid x i₁) (ptSn (suc m)))
-- --                                             (f (ptSn (suc m)))
-- --                                             (transport (λ i₁ → A (merid (ptSn (suc n)) i₁) (ptSn (suc m)))
-- --                                                        (f (ptSn (suc m))))
-- --   pathOverMerid₁ x i = hcomp (λ k → λ { (i = i0) → f (ptSn (suc m))
-- --                                       ; (i = i1) → (transpLemma₁ x ∙ sym (transpLemma₁ (ptSn (suc n)))) k })
-- --                             (transp (λ i₁ → A (merid x (i₁ ∧ i)) (ptSn (suc m))) (~ i)
-- --                                     (f (ptSn (suc m))))

-- --   pathOverMeridId₁ : pathOverMerid₁ (ptSn (suc n)) ≡ λ i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i)
-- --                                                                  (f (ptSn (suc m)))
-- --   pathOverMeridId₁ =
-- --         (λ j i → hcomp (λ k → λ { (i = i0) → f (ptSn (suc m))
-- --                                   ; (i = i1) → rCancel (transpLemma₁ (ptSn (suc n))) j k })
-- --                         (transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i)
-- --                                 (f (ptSn (suc m)))))
-- --        ∙ λ j i → hfill (λ k → λ { (i = i0) → f (ptSn (suc m))
-- --                                   ; (i = i1) → transport (λ i₁ → A (merid (ptSn (suc n)) i₁) (ptSn (suc m)))
-- --                                                           (f (ptSn (suc m))) })
-- --                         (inS (transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i)
-- --                                      (f (ptSn (suc m))))) (~ j)

-- --   indStep₁ : (a : _) (y : _) → PathP (λ i → A (merid a i) y)
-- --                                              (f y)
-- --                                              (subst (λ x → A x y) (merid (ptSn (suc n)))
-- --                                                     (f y))
-- --   indStep₁ = wedgeconFun n m (λ _ _ → isOfHLevelPathP' (suc (n + suc m)) (hlev _ _) _ _)
-- --                            (λ a i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) a) (~ i)
-- --                                             (f a))
-- --                            pathOverMerid₁
-- --                            pathOverMeridId₁

-- --   F₁ : (x : Susp (S₊ (suc n))) (y : S₊ (suc m))  → A x y
-- --   F₁ north y = f y
-- --   F₁ south y = subst (λ x → A x y) (merid (ptSn (suc n))) (f y)
-- --   F₁ (merid a i) y = indStep₁ a y i
-- -- wedgeconRight zero zero {A = A} hlev f g hom = right
-- --   where
-- --   right : (x : S¹) → _
-- --   right base = sym hom
-- --   right (loop i) j = hcomp (λ k → λ { (i = i0) → hom (~ j ∧ k)
-- --                                      ; (i = i1) → hom (~ j ∧ k)
-- --                                      ; (j = i1) → g (loop i) })
-- --                            (g (loop i))
-- -- wedgeconRight zero (suc m) {A = A} hlev f g hom x = refl
-- -- wedgeconRight (suc n) m {A = A} hlev f g hom = right
-- --   where
-- --   lem : (x : _) → indStep₁ n m hlev f g hom x (ptSn (suc m)) ≡ _
-- --   lem = wedgeconRight n m (λ _ _ → isOfHLevelPathP' (suc (n + suc m)) (hlev _ _) _ _)
-- --                            (λ a i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) a) (~ i)
-- --                                             (f a))
-- --                            (pathOverMerid₁ n m hlev f g hom)
-- --                            (pathOverMeridId₁ n m hlev f g hom)

-- --   right : (x : Susp (S₊ (suc n))) → _ ≡ g x
-- --   right north = sym hom
-- --   right south = cong (subst (λ x → A x (ptSn (suc m)))
-- --                             (merid (ptSn (suc n))))
-- --                             (sym hom)
-- --               ∙ λ i → transp (λ j → A (merid (ptSn (suc n)) (i ∨ j)) (ptSn (suc m))) i
-- --                               (g (merid (ptSn (suc n)) i))
-- --   right (merid a i) j =
-- --     hcomp (λ k → λ { (i = i0) → hom (~ j)
-- --                     ; (i = i1) → transpLemma₁ n m hlev f g hom (ptSn (suc n)) j
-- --                     ; (j = i0) → lem a (~ k) i
-- --                     ; (j = i1) → g (merid a i)})
-- --           (hcomp (λ k →  λ { (i = i0) → hom (~ j)
-- --                             ; (i = i1) → compPath-lem (transpLemma₁ n m hlev f g hom a) (transpLemma₁ n m hlev f g hom (ptSn (suc n))) k j
-- --                             ; (j = i1) → g (merid a i)})
-- --                  (hcomp (λ k → λ { (i = i0) → hom (~ j)
-- --                                   ; (j = i0) → transp (λ i₂ → A (merid a (i₂ ∧ i)) (ptSn (suc m))) (~ i)
-- --                                                        (f (ptSn (suc m)))
-- --                                   ; (j = i1) → transp (λ j → A (merid a (i ∧ (j ∨ k))) (ptSn (suc m))) (k ∨ ~ i)
-- --                                                        (g (merid a (i ∧ k))) })
-- --                         (transp (λ i₂ → A (merid a (i₂ ∧ i)) (ptSn (suc m))) (~ i)
-- --                                 (hom (~ j)))))
-- -- wedgeconLeft zero zero {A = A} hlev f g hom x = refl
-- -- wedgeconLeft zero (suc m) {A = A} hlev f g hom = help
-- --   where
-- --   left₁ : (x : _) → indStep₀ m hlev f g hom base x ≡ _
-- --   left₁ = wedgeconLeft zero m (λ _ _ → isOfHLevelPathP' (2 + m) (hlev _ _) _ _)
-- --                               (pathOverMerid₀ m hlev f g hom)
-- --                               (λ a i → transp (λ i₁ → A a (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
-- --                                                (g a))
-- --                               (sym (pathOverMeridId₀ m hlev f g hom))

-- --   help : (x : S₊ (suc (suc m))) → _
-- --   help north = hom
-- --   help south = cong (subst (A base) (merid (ptSn (suc m)))) hom
-- --              ∙ λ i → transp (λ j → A base (merid (ptSn (suc m)) (i ∨ j))) i
-- --                              (f (merid (ptSn (suc m)) i))
-- --   help (merid a i) j =
-- --     hcomp (λ k → λ { (i = i0) → hom j
-- --                     ; (i = i1) → transpLemma₀ m hlev f g hom (ptSn (suc m)) j
-- --                     ; (j = i0) → left₁ a (~ k) i
-- --                     ; (j = i1) → f (merid a i)})
-- --           (hcomp (λ k →  λ { (i = i0) → hom j
-- --                             ; (i = i1) → compPath-lem (transpLemma₀ m hlev f g hom a)
-- --                                                        (transpLemma₀ m hlev f g hom (ptSn (suc m))) k j
-- --                             ; (j = i1) → f (merid a i)})
-- --                  (hcomp (λ k → λ { (i = i0) → hom j
-- --                                   ; (j = i0) → transp (λ i₂ → A base (merid a (i₂ ∧ i))) (~ i)
-- --                                                        (g base)
-- --                                   ; (j = i1) → transp (λ j → A base (merid a (i ∧ (j ∨ k)))) (k ∨ ~ i)
-- --                                                        (f (merid a (i ∧ k)))})
-- --                         (transp (λ i₂ → A base (merid a (i₂ ∧ i))) (~ i)
-- --                                 (hom j))))
-- -- wedgeconLeft (suc n) m {A = A} hlev f g hom _ = refl

-- -- ---------- Connectedness -----------

-- -- sphereConnected : (n : HLevel) → isConnected (suc n) (S₊ n)
-- -- sphereConnected n = ∣ ptSn n ∣ , elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
-- --                                      (λ a → sym (spoke ∣_∣ (ptSn n)) ∙ spoke ∣_∣ a)

-- -- -- The fact that path spaces of Sn are connected can be proved directly for Sⁿ.
-- -- -- (Unfortunately, this does not work for higher paths)
-- -- pathIdTruncSⁿ : (n : ℕ) (x y : S₊ (suc n))
-- --              → Path (hLevelTrunc (2 + n) (S₊ (suc n))) ∣ x ∣ ∣ y ∣
-- --              → hLevelTrunc (suc n) (x ≡ y)
-- -- pathIdTruncSⁿ n = sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → isOfHLevelΠ (suc n)  λ _ → isOfHLevelTrunc (suc n))
-- --                      (sphereElim n (λ _ → isOfHLevelΠ (suc n)  λ _ → isOfHLevelTrunc (suc n))
-- --                        λ _ → ∣ refl ∣)

-- -- pathIdTruncSⁿ⁻ : (n : ℕ) (x y : S₊ (suc n))
-- --              → hLevelTrunc (suc n) (x ≡ y)
-- --              → Path (hLevelTrunc (2 + n) (S₊ (suc n))) ∣ x ∣ ∣ y ∣
-- -- pathIdTruncSⁿ⁻ n x y = rec (isOfHLevelTrunc (2 + n) _ _)
-- --                            (J (λ y _ → Path (hLevelTrunc (2 + n) (S₊ (suc n))) ∣ x ∣ ∣ y ∣) refl)

-- -- pathIdTruncSⁿretract : (n : ℕ) (x y : S₊ (suc n)) → (p : hLevelTrunc (suc n) (x ≡ y)) → pathIdTruncSⁿ n x y (pathIdTruncSⁿ⁻ n x y p) ≡ p
-- -- pathIdTruncSⁿretract n =
-- --   sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → isOfHLevelΠ (suc n) λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
-- --     λ y → elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
-- --       (J (λ y p → pathIdTruncSⁿ n (ptSn (suc n)) y (pathIdTruncSⁿ⁻ n (ptSn (suc n)) y ∣ p ∣) ≡ ∣ p ∣)
-- --          (cong (pathIdTruncSⁿ n (ptSn (suc n)) (ptSn (suc n))) (transportRefl refl) ∙ pm-help n))
-- --   where
-- --   pm-help : (n : ℕ) → pathIdTruncSⁿ n (ptSn (suc n)) (ptSn (suc n)) refl  ≡ ∣ refl ∣
-- --   pm-help zero = refl
-- --   pm-help (suc n) = refl

-- -- isConnectedPathSⁿ : (n : ℕ) (x y : S₊ (suc n)) → isConnected (suc n) (x ≡ y)
-- -- isConnectedPathSⁿ n x y =
-- --   isContrRetract
-- --    (pathIdTruncSⁿ⁻ n x y)
-- --    (pathIdTruncSⁿ n x y)
-- --    (pathIdTruncSⁿretract n x y)
-- --      ((isContr→isProp (sphereConnected (suc n)) ∣ x ∣ ∣ y ∣)
-- --       , isProp→isSet (isContr→isProp (sphereConnected (suc n))) _ _ _)

-- -- -- Some lemmas on the H space structure on S¹
-- -- rUnitS¹ : (x : S¹) → x * base ≡ x
-- -- rUnitS¹ base = refl
-- -- rUnitS¹ (loop i₁) = refl

-- -- commS¹ : (a x : S¹) → a * x ≡ x * a
-- -- commS¹ = wedgeconFun _ _ (λ _ _ → isGroupoidS¹ _ _)
-- --          (sym ∘ rUnitS¹)
-- --          rUnitS¹
-- --          refl

-- -- assocS¹ : (x y z : S¹) → x * (y * z) ≡ (x * y) * z
-- -- assocS¹ = wedgeconFun _ _ (λ _ _ → isSetΠ λ _ → isGroupoidS¹ _ _)
-- --           (λ _ _ → refl)
-- --           (λ x z i → (rUnitS¹ x (~ i)) * z)
-- --           refl

-- -- invLooperDistr : (x y : S¹) → invLooper (x * y) ≡ invLooper x * invLooper y
-- -- invLooperDistr =
-- --   wedgeconFun 0 0 (λ _ _ → isGroupoidS¹ _ _) (λ _ → refl)
-- --     (λ x → cong invLooper (rUnitS¹ x) ∙ sym (rUnitS¹ (invLooper x)))
-- --     (sym (rUnit refl))

-- -- SuspS¹-hom : (a x : S¹)
-- --   → Path (Path (hLevelTrunc 4 (S₊ 2)) _ _)
-- --           (cong ∣_∣ₕ (σ (S₊∙ 1) (a * x)))
-- --           (cong ∣_∣ₕ (σ (S₊∙ 1) a)
-- --         ∙ (cong ∣_∣ₕ (σ (S₊∙ 1) x)))
-- -- SuspS¹-hom = wedgeconFun _ _ (λ _ _ → isOfHLevelTrunc 4 _ _ _ _)
-- --            (λ x → lUnit _
-- --                  ∙ cong (_∙ cong ∣_∣ₕ (σ (S₊∙ 1) x))
-- --                         (cong (cong ∣_∣ₕ) (sym (rCancel (merid base)))))
-- --            (λ x → (λ i → cong ∣_∣ₕ (σ (S₊∙ 1) (rUnitS¹ x i)))
-- --                ∙∙ rUnit _
-- --                ∙∙ cong (cong ∣_∣ₕ (σ (S₊∙ 1) x) ∙_)
-- --                        (cong (cong ∣_∣ₕ) (sym (rCancel (merid base)))))
-- --            (sym (l (cong ∣_∣ₕ (σ (S₊∙ 1) base))
-- --                 (cong (cong ∣_∣ₕ) (sym (rCancel (merid base))))))
-- --   where
-- --   l : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (P : refl ≡ p)
-- --     → lUnit p ∙ cong (_∙ p) P ≡ rUnit p ∙ cong (p ∙_) P
-- --   l p = J (λ p P → lUnit p ∙ cong (_∙ p) P ≡ rUnit p ∙ cong (p ∙_) P) refl

-- -- rCancelS¹ : (x : S¹) → ptSn 1 ≡ x * (invLooper x)
-- -- rCancelS¹ base = refl
-- -- rCancelS¹ (loop i) j =
-- --   hcomp (λ r → λ {(i = i0) → base ; (i = i1) → base ; (j = i0) → base})
-- --         base

-- -- SuspS¹-inv : (x : S¹) → Path (Path (hLevelTrunc 4 (S₊ 2)) _ _)
-- --                          (cong ∣_∣ₕ (σ (S₊∙ 1) (invLooper x)))
-- --                          (cong ∣_∣ₕ (sym (σ (S₊∙ 1) x)))
-- -- SuspS¹-inv x = (lUnit _
-- --        ∙∙ cong (_∙ cong ∣_∣ₕ (σ (S₊∙ 1) (invLooper x)))
-- --                (sym (lCancel (cong ∣_∣ₕ (σ (S₊∙ 1) x))))
-- --                   ∙∙ sym (assoc _ _ _))
-- --        ∙∙ cong (sym (cong ∣_∣ₕ (σ (S₊∙ 1) x)) ∙_) lem
-- --        ∙∙ (assoc _ _ _
-- --        ∙∙ cong (_∙ (cong ∣_∣ₕ (sym (σ (S₊∙ 1) x))))
-- --                (lCancel (cong ∣_∣ₕ (σ (S₊∙ 1) x)))
-- --        ∙∙ sym (lUnit _))
-- --   where
-- --   lem : cong ∣_∣ₕ (σ (S₊∙ 1) x)
-- --       ∙ cong ∣_∣ₕ (σ (S₊∙ 1) (invLooper x))
-- --      ≡ cong ∣_∣ₕ (σ (S₊∙ 1) x)
-- --      ∙ cong ∣_∣ₕ (sym (σ (S₊∙ 1) x))
-- --   lem = sym (SuspS¹-hom x (invLooper x))
-- --      ∙ ((λ i → cong ∣_∣ₕ (σ (S₊∙ 1) (rCancelS¹ x (~ i))))
-- --      ∙ cong (cong ∣_∣ₕ) (rCancel (merid base))) ∙ sym (rCancel _)

-- -- -------------------- join Sⁿ Sᵐ ≃ Sⁿ⁺¹⁺ᵐ -------------------------
-- -- {-
-- -- This section contains a proof that join Sⁿ Sᵐ ≃ Sⁿ⁺ᵐ⁺¹. This is easy using
-- -- various properties proved in HITs.Join. However, we would like the map
-- -- join Sⁿ Sᵐ → Sⁿ⁺ᵐ⁺¹
-- -- to be nice, in particular when n = m = 1. Therefore, we put in some extra work into
-- -- the equivalence.
-- -- -}


-- -- {- We begin with join S¹ S¹ ≃ S³. The iso is induced by: -}
-- -- S¹×S¹→S² : S¹ → S¹ → S₊ 2
-- -- S¹×S¹→S² base y = north
-- -- S¹×S¹→S² (loop i) base = north
-- -- S¹×S¹→S² (loop i) (loop j) =
-- --   (sym (rCancel (merid base))
-- --   ∙∙ (λ i → merid (loop i) ∙ sym (merid base))
-- --   ∙∙ rCancel (merid base)) i j

-- -- joinS¹S¹→S³ : join S¹ S¹ → S₊ 3
-- -- joinS¹S¹→S³ (inl x) = north
-- -- joinS¹S¹→S³ (inr x) = south
-- -- joinS¹S¹→S³ (push a b i) = merid (S¹×S¹→S² a b) i

-- -- {- Proving that this is an equivalence directly is painful,
-- --   so we simply prove that it is equal to the old definition of
-- --   the equivalence join S¹ S¹ ≃ S³ ≃ S₊ 3
-- --   To this end, we start by rephrasing the map -}
-- -- private
-- --   3cell : (r i j k : I) → S₊ 3
-- --   3cell r i j k =
-- --     hfill (λ r → λ {(i = i0) → merid (merid base j) (k ∧ ~ r)
-- --                    ; (i = i1) → merid (merid base j) (k ∧ ~ r)
-- --                    ; (j = i0) → merid north (k ∧ ~ r)
-- --                    ; (j = i1) → merid south (k ∧ ~ r)
-- --                    ; (k = i0) → north
-- --                    ; (k = i1) → merid (merid base j) (~ r)})
-- --           (inS (merid (merid (loop i) j) k))
-- --           r

-- -- joinS¹S¹→S³' : join S¹ S¹ → S₊ 3
-- -- joinS¹S¹→S³' (inl x) = north
-- -- joinS¹S¹→S³' (inr x) = north
-- -- joinS¹S¹→S³' (push base b i) = north
-- -- joinS¹S¹→S³' (push (loop i₁) base i) = north
-- -- joinS¹S¹→S³' (push (loop i₁) (loop i₂) i) = 3cell i1 i₁ i₂ i

-- -- {- These two maps are equal -}
-- -- joinS¹S¹→S³'≡joinS¹S¹→S³' : (x : _) → joinS¹S¹→S³ x ≡ joinS¹S¹→S³' x
-- -- joinS¹S¹→S³'≡joinS¹S¹→S³' (inl base) = refl
-- -- joinS¹S¹→S³'≡joinS¹S¹→S³' (inl (loop i)) = refl
-- -- joinS¹S¹→S³'≡joinS¹S¹→S³' (inr base) = sym (merid north)
-- -- joinS¹S¹→S³'≡joinS¹S¹→S³' (inr (loop i)) = sym (merid north)
-- -- joinS¹S¹→S³'≡joinS¹S¹→S³' (push base base i) k = merid north (~ k ∧ i)
-- -- joinS¹S¹→S³'≡joinS¹S¹→S³' (push base (loop i₁) i) k  = merid north (~ k ∧ i)
-- -- joinS¹S¹→S³'≡joinS¹S¹→S³' (push (loop i₁) base i) k =  (merid north) (~ k ∧ i)
-- -- joinS¹S¹→S³'≡joinS¹S¹→S³' (push (loop i) (loop j) k) l =
-- --   hcomp (λ r → λ { (i = i0) → merid (sym (rCancel (merid base)) (~ r) j)
-- --                                       (~ l ∧ k)
-- --                   ; (i = i1) → merid (sym (rCancel (merid base)) (~ r) j)
-- --                                       (~ l ∧ k)
-- --                   ; (j = i0) → merid north (~ l ∧ k)
-- --                   ; (j = i1) → merid north (~ l ∧ k)
-- --                   ; (k = i0) → north
-- --                   ; (k = i1) → merid (sym (rCancel (merid base)) (~ r) j) (~ l)
-- --                   ; (l = i0) → merid (doubleCompPath-filler
-- --                                       (sym (rCancel (merid base)))
-- --                                       (cong (σ (S₊∙ 1)) loop)
-- --                                       (rCancel (merid base)) r i j) k
-- --                   ; (l = i1) → 3cell i1 i j k})
-- --     (hcomp (λ r → λ {(i = i0) → merid (cp-fill base r j) (k ∧ ~ l)
-- --                    ; (i = i1) → merid (cp-fill base r j) (k ∧ ~ l)
-- --                    ; (j = i0) → merid north (~ l ∧ k)
-- --                    ; (j = i1) → merid (merid base (~ r)) (~ l ∧ k)
-- --                    ; (k = i0) → north
-- --                    ; (k = i1) → merid (cp-fill base r j) (~ l)
-- --                    ; (l = i0) → merid (cp-fill (loop i) r j) k
-- --                    ; (l = i1) → 3cell i1 i j k})
-- --        (hcomp (λ r → λ {(i = i0) → merid (merid base j) (k ∧ (~ r ∨ ~ l))
-- --                    ; (i = i1) → merid (merid base j) (k ∧ (~ r ∨ ~ l))
-- --                    ; (j = i0) → merid north (k ∧ (~ l ∨ ~ r))
-- --                    ; (j = i1) → merid south (k ∧ (~ l ∨ ~ r))
-- --                    ; (k = i0) → north
-- --                    ; (k = i1) → merid (merid base j) (~ r ∨ ~ l)
-- --                    ; (l = i0) → merid (merid (loop i) j) k
-- --                    ; (l = i1) → 3cell r i j k})
-- --               (merid (merid (loop i) j) k)))
-- --   where
-- --   cp-fill : (a : S¹) → _
-- --   cp-fill a = compPath-filler (merid a) (sym (merid base))

-- -- {- joinS¹S¹→S³' is equal to the original
-- --   equivalence (modulo a flipping of interval variables) -}
-- -- joinS¹S¹→S³'Id : (x : join S¹ S¹)
-- --   → joinS¹S¹→S³' x ≡ (Iso.fun IsoS³S3 ∘ flip₀₂S³ ∘ joinS¹S¹→S3) x
-- -- joinS¹S¹→S³'Id (inl x) = refl
-- -- joinS¹S¹→S³'Id (inr x) = refl
-- -- joinS¹S¹→S³'Id (push base base i) = refl
-- -- joinS¹S¹→S³'Id (push base (loop i₁) i) = refl
-- -- joinS¹S¹→S³'Id (push (loop i₁) base i) = refl
-- -- joinS¹S¹→S³'Id (push (loop i) (loop j) k) l =
-- --   hcomp (λ r → λ {(i = i0) → merid (merid base (j ∧ ~ l)) (~ r ∧ k)
-- --                  ; (i = i1) → merid (merid base (j ∧ ~ l)) (~ r ∧ k)
-- --                  ; (j = i0) → merid north (k ∧ ~ r)
-- --                  ; (j = i1) → merid (merid base (~ l)) (~ r ∧ k)
-- --                  ; (k = i0) → north
-- --                  ; (k = i1) → merid (merid base (j ∧ ~ l)) (~ r)
-- --                  ; (l = i0) → 3cell r i j k
-- --                  ; (l = i1) → Iso.fun (IsoType→IsoSusp S²IsoSuspS¹)
-- --                                        (meridian-contraction-2 k j i r)})
-- --         (merid (S²Cube i j l) k)
-- --   where
-- --   S²Cube : Cube {A = S₊ 2} (λ j l → merid base (j ∧ ~ l))
-- --                              (λ j l → merid base (j ∧ ~ l))
-- --                              (λ i l → north)
-- --                              (λ i l → merid base (~ l))
-- --                              (λ i j → merid (loop i) j)
-- --                              λ i j → fun S²IsoSuspS¹ (surf j i)
-- --   S²Cube i j l =
-- --     hcomp (λ r → λ {(i = i0) → merid base (j ∧ (~ l ∨ ~ r))
-- --                  ; (i = i1) → merid base (j ∧ (~ l ∨ ~ r))
-- --                  ; (j = i0) → north
-- --                  ; (j = i1) → merid base (~ l ∨ ~ r)
-- --                  ; (l = i0) → merid (loop i) j
-- --                  ; (l = i1) → meridian-contraction j i r})
-- --            (merid (loop i) j)

-- -- {-So, finally our map joinS¹S¹→S³ is an iso. We state its inverse explicitly. -}
-- -- Iso-joinS¹S¹-S³ : Iso (join S¹ S¹) (S₊ 3)
-- -- fun Iso-joinS¹S¹-S³ = joinS¹S¹→S³
-- -- inv Iso-joinS¹S¹-S³ = S³→joinS¹S¹ ∘ flip₀₂S³ ∘ Iso.inv IsoS³S3
-- -- rightInv Iso-joinS¹S¹-S³ x =
-- --      joinS¹S¹→S³'≡joinS¹S¹→S³'
-- --        ((S³→joinS¹S¹ ∘ flip₀₂S³ ∘ Iso.inv IsoS³S3) x)
-- --   ∙∙ joinS¹S¹→S³'Id ((S³→joinS¹S¹ ∘ flip₀₂S³ ∘ Iso.inv IsoS³S3) x)
-- --   ∙∙ Iso.leftInv (compIso (invIso IsoS³S3)
-- --                   (compIso flip₀₂S³Iso (S³IsojoinS¹S¹))) x
-- -- leftInv Iso-joinS¹S¹-S³ x =
-- --      cong (S³→joinS¹S¹ ∘ flip₀₂S³ ∘ inv IsoS³S3)
-- --           (joinS¹S¹→S³'≡joinS¹S¹→S³' x ∙ joinS¹S¹→S³'Id x)
-- --    ∙ Iso.rightInv (compIso (invIso IsoS³S3) (compIso flip₀₂S³Iso (S³IsojoinS¹S¹))) x

-- -- {- We now get the full iso Sⁿ * Sᵐ ≃ Sⁿ⁺ᵐ⁺¹ -}
-- -- IsoSphereJoin : (n m : ℕ)
-- --   → Iso (join (S₊ n) (S₊ m)) (S₊ (suc (n + m)))
-- -- IsoSphereJoin zero zero = compIso (invIso Susp-iso-joinBool) (invIso S¹IsoSuspBool)
-- -- IsoSphereJoin zero (suc m) = compIso join-comm (invIso Susp-iso-joinBool)
-- -- IsoSphereJoin (suc zero) zero = (invIso Susp-iso-joinBool)
-- -- IsoSphereJoin (suc zero) (suc zero) = Iso-joinS¹S¹-S³
-- -- IsoSphereJoin (suc zero) (suc (suc m)) =
-- --   compIso join-comm
-- --     (compIso (compIso (Iso-joinSusp-suspJoin {A = S₊∙ (suc m)} {B = S₊∙ (suc zero)})
-- --       (congSuspIso join-comm))
-- --       (congSuspIso (IsoSphereJoin (suc zero) (suc m))))
-- -- IsoSphereJoin (suc (suc n)) m =
-- --   compIso (Iso-joinSusp-suspJoin {A = S₊∙ (suc n)} {B = S₊∙ m}) (congSuspIso (IsoSphereJoin (suc n) m))

-- -- {- Pointedness holds by refl.
-- --   This is due to the explicit definition of Iso-joinSusp-suspJoin  -}
-- -- IsoSphereJoinPres∙ : (n m : ℕ)
-- --   → Iso.fun (IsoSphereJoin n m) (inl (ptSn n)) ≡ ptSn (suc (n + m))
-- -- IsoSphereJoinPres∙ zero zero = refl
-- -- IsoSphereJoinPres∙ zero (suc m) = refl
-- -- IsoSphereJoinPres∙ (suc zero) zero = refl
-- -- IsoSphereJoinPres∙ (suc zero) (suc zero) = refl
-- -- IsoSphereJoinPres∙ (suc zero) (suc (suc m)) = refl
-- -- IsoSphereJoinPres∙ (suc (suc n)) m = refl

-- -- IsoSphereJoin⁻Pres∙ : (n m : ℕ)
-- --   → Iso.inv (IsoSphereJoin n m) (ptSn (suc (n + m))) ≡ inl (ptSn n)
-- -- IsoSphereJoin⁻Pres∙ n m =
-- --      cong (Iso.inv (IsoSphereJoin n m)) (sym (IsoSphereJoinPres∙ n m))
-- --    ∙ Iso.leftInv (IsoSphereJoin n m) (inl (ptSn n))

-- -- -- Inversion on spheres
-- -- invSphere : {n : ℕ} → S₊ n → S₊ n
-- -- invSphere {n = zero} = not
-- -- invSphere {n = (suc zero)} = invLooper
-- -- invSphere {n = (suc (suc n))} = invSusp

-- -- invSphere² : (n : ℕ) (x : S₊ n) → invSphere (invSphere x) ≡ x
-- -- invSphere² zero = notnot
-- -- invSphere² (suc zero) base = refl
-- -- invSphere² (suc zero) (loop i) = refl
-- -- invSphere² (suc (suc n)) = invSusp²

-- -- -- Interaction between σ and invSphere
-- -- σ-invSphere : (n : ℕ) (x : S₊ (suc n))
-- --                  → σ (S₊∙ (suc n)) (invSphere x)
-- --                  ≡ sym (σ (S₊∙ (suc n)) x)
-- -- σ-invSphere zero base =
-- --   rCancel (merid base) ∙∙ refl ∙∙ cong sym (sym (rCancel (merid base)))
-- -- σ-invSphere zero (loop i) j =
-- --   hcomp (λ k → λ { (j = i0) → doubleCompPath-filler
-- --                                  (sym (rCancel (merid base)))
-- --                                  (λ i → (σ (S₊∙ 1) (loop (~ i))))
-- --                                  (rCancel (merid base)) (~ k) i
-- --                   ; (j = i1) → doubleCompPath-filler
-- --                                   (sym (cong sym (rCancel (merid base))))
-- --                                   (λ i → sym (σ (S₊∙ 1) (loop i)))
-- --                                   (cong sym (rCancel (merid base))) (~ k) i})
-- --         (sym≡cong-sym  (sym (rCancel (merid base))
-- --                     ∙∙ (λ i → (σ (S₊∙ 1) (loop i)))
-- --                     ∙∙ (rCancel (merid base))) j i)
-- -- σ-invSphere (suc n) x = toSusp-invSusp (S₊∙ (suc n)) x


-- -- -- Some facts about the map S¹×S¹→S²
-- -- -- Todo: generalise to Sⁿ×Sᵐ→Sⁿ⁺ᵐ
-- -- S¹×S¹→S²rUnit : (a : S¹) → S¹×S¹→S² a base ≡ north
-- -- S¹×S¹→S²rUnit base = refl
-- -- S¹×S¹→S²rUnit (loop i) = refl

-- -- S¹×S¹→S²x+x : (x : S¹) → S¹×S¹→S² x x ≡ north
-- -- S¹×S¹→S²x+x base = refl
-- -- S¹×S¹→S²x+x (loop i) k = lem k i
-- --   where
-- --   lem : cong₂ S¹×S¹→S² loop loop ≡ refl
-- --   lem = cong₂Funct S¹×S¹→S² loop loop
-- --     ∙ (λ i → rUnit (cong (λ x → S¹×S¹→S²rUnit x i) loop) (~ i))

-- -- S¹×S¹→S²-antiComm : (a b : S¹) → S¹×S¹→S² a b ≡ S¹×S¹→S² b (invLooper a)
-- -- S¹×S¹→S²-antiComm base base = refl
-- -- S¹×S¹→S²-antiComm base (loop i) = refl
-- -- S¹×S¹→S²-antiComm (loop i) base = refl
-- -- S¹×S¹→S²-antiComm (loop i) (loop j) k =
-- --   sym≡flipSquare (λ j i → S¹×S¹→S² (loop i) (loop j)) (~ k) i j

-- -- private
-- --   S¹×S¹→S²-Distr-filler : (i : I)
-- --     → cong₂ (λ b c → S¹×S¹→S² ((loop i) * b) c) loop loop
-- --     ≡ cong (S¹×S¹→S² (loop i)) loop
-- --   S¹×S¹→S²-Distr-filler i =
-- --     cong₂Funct (λ b c → S¹×S¹→S² ((loop i) * b) c) loop loop
-- --      ∙∙ (λ j → cong (λ x → S¹×S¹→S²rUnit (rotLoop x i) j) loop ∙
-- --                 cong (λ c → S¹×S¹→S² (loop i) c) loop)
-- --      ∙∙ sym (lUnit _)

-- -- S¹×S¹→S²-Distr : (a b : S¹) → S¹×S¹→S² (a * b) b ≡ S¹×S¹→S² a b
-- -- S¹×S¹→S²-Distr a base j = S¹×S¹→S² (rUnitS¹ a j) base
-- -- S¹×S¹→S²-Distr base (loop i) k = S¹×S¹→S²-Distr-filler i0 k i
-- -- S¹×S¹→S²-Distr (loop i₁) (loop i) k = S¹×S¹→S²-Distr-filler i₁ k i

-- -- invSusp∘S¹×S¹→S² : (a b : S¹)
-- --   → S¹×S¹→S² a (invLooper b) ≡ invSusp (S¹×S¹→S² a b)
-- -- invSusp∘S¹×S¹→S² base b = merid base
-- -- invSusp∘S¹×S¹→S² (loop i) base = merid base
-- -- invSusp∘S¹×S¹→S² (loop i) (loop j) k =
-- --   hcomp (λ r → λ {(i = i0) → i-Boundary₂ r j k
-- --                  ; (i = i1) → i-Boundary₂ r j k
-- --                  ; (j = i0) → m-b k
-- --                  ; (j = i1) → m-b k
-- --                  ; (k = i0) → doubleCompPath-filler
-- --                                 rCancel-mb⁻¹ (cong σ₁ loop) rCancel-mb r i (~ j)
-- --                  ; (k = i1)
-- --                     → invSusp (doubleCompPath-filler
-- --                                  rCancel-mb⁻¹ (cong σ₁ loop) rCancel-mb r i j)})
-- --    (hcomp (λ r → λ {(i = i0) → i-Boundary r (~ j) k
-- --                    ; (i = i1) → i-Boundary r (~ j) k
-- --                    ; (j = i0) → merid base (~ r ∨ k)
-- --                    ; (j = i1) → merid base (r ∧ k)
-- --                    ; (k = i0) → cp-filler (loop i) r (~ j)
-- --                    ; (k = i1) → invSusp (cp-filler (loop i) r j)})
-- --            (merid (loop i) (~ j)))
-- --   where
-- --   σ₁ = σ (S₊∙ 1)
-- --   m-b = merid base
-- --   rCancel-mb = rCancel m-b
-- --   rCancel-mb⁻¹ = sym (rCancel m-b)

-- --   cp-filler : (a : S¹) (i j : I) → S₊ 2
-- --   cp-filler a i j = compPath-filler (merid a) (sym (merid base)) i j

-- --   i-Boundary : I → I → I → S₊ 2
-- --   i-Boundary r j k =
-- --     hfill (λ r → λ{(j = i0) → m-b (k ∧ r)
-- --                   ; (j = i1) → m-b (~ r ∨ k)
-- --                   ; (k = i0) → cp-filler base r j
-- --                   ; (k = i1) → invSusp (cp-filler base r (~ j))})
-- --           (inS (m-b j))
-- --           r

-- --   i-Boundary₂ : I → I → I → S₊ 2
-- --   i-Boundary₂ r j k =
-- --     hcomp (λ i → λ {(r = i0) → i-Boundary i (~ j) k
-- --                  ; (r = i1) → m-b k
-- --                  ; (j = i0) → m-b (k ∨ (~ i ∧ ~ r))
-- --                  ; (j = i1) → m-b (k ∧ (i ∨ r))
-- --                  ; (k = i0) → rCancel-filler m-b i r (~ j)
-- --                  ; (k = i1) → invSusp (rCancel-filler m-b i r j) })
-- --      (hcomp (λ i → λ {(r = i0) → m-b (~ j ∨ (~ i ∧ k))
-- --                  ; (r = i1) → m-b (k ∨ (~ i ∧ ~ j))
-- --                  ; (j = i0) → m-b (k ∨ (~ r ∨ ~ i))
-- --                  ; (j = i1) → m-b (k ∧ (~ i ∨ r))
-- --                  ; (k = i0) → m-b (~ j ∧ (~ r ∨ ~ i))
-- --                  ; (k = i1) → m-b ((~ j ∨ ~ i) ∨ r) })
-- --             (m-b (~ j ∨ k)))

-- -- -- Interaction between S¹×S¹→S² and SuspS¹→S²
-- -- SuspS¹→S²-S¹×S¹→S² : (a b : S¹)
-- --   → (SuspS¹→S² (S¹×S¹→S² a b)) ≡ (S¹×S¹→S²' b a)
-- -- SuspS¹→S²-S¹×S¹→S² base base = refl
-- -- SuspS¹→S²-S¹×S¹→S² base (loop i) = refl
-- -- SuspS¹→S²-S¹×S¹→S² (loop i) base = refl
-- -- SuspS¹→S²-S¹×S¹→S² (loop i) (loop j) k =
-- --   hcomp (λ r → λ {(i = i0) → rUnit (λ _ → base) (~ r ∧ ~ k) j
-- --                  ; (i = i1) → rUnit (λ _ → base) (~ r ∧ ~ k) j
-- --                  ; (j = i0) → base
-- --                  ; (j = i1) → base
-- --                  ; (k = i0) → SuspS¹→S² (doubleCompPath-filler (
-- --                                  sym (rCancel (merid base)))
-- --                                  ((λ i → merid (loop i) ∙ sym (merid base)))
-- --                                  (rCancel (merid base)) r i j )
-- --                  ; (k = i1) → surf j i})
-- --     (hcomp (λ r → λ {(i = i0) → rUnit (λ _ → base) (r ∧ ~ k) j
-- --                  ; (i = i1) → rUnit (λ _ → base) (r ∧ ~ k) j
-- --                  ; (j = i0) → base
-- --                  ; (j = i1) → base
-- --                  ; (k = i0) → SuspS¹→S²
-- --                        (compPath-filler (merid (loop i)) (sym (merid base)) r j)
-- --                  ; (k = i1) → surf j i})
-- --            (surf j i))

-- -- open PlusBis
-- -- open import Cubical.HITs.Susp.Properties
-- -- open import Cubical.HITs.Join

-- -- _⌣S_ : {n m : ℕ} → S₊ n → S₊ m → S₊ (n + m)
-- -- _⌣S_ {n = zero} {m = m} false y = y
-- -- _⌣S_ {n = zero} {m = m} true y = ptSn m
-- -- _⌣S_ {n = suc zero} {m = m} base y = ptSn (suc m)
-- -- _⌣S_ {n = suc zero} {m = zero} (loop i) false = loop i
-- -- _⌣S_ {n = suc zero} {m = zero} (loop i) true = base
-- -- _⌣S_ {n = suc zero} {m = suc m} (loop i) y = toSusp (S₊∙ (suc m)) y i
-- -- _⌣S_ {n = suc (suc n)} {m = m} north y = north
-- -- _⌣S_ {n = suc (suc n)} {m = m} south y = north
-- -- _⌣S_ {n = suc (suc n)} {m = m} (merid a i) y = toSusp (S₊∙ (suc n + m)) (a ⌣S y) i

-- -- ⌣S-rid : {n m : ℕ} (y : S₊ m)
-- --   → Path (S₊ (n + m)) (ptSn n ⌣S y) (ptSn (n + m))
-- -- ⌣S-rid {n = zero} {m = m} y = refl
-- -- ⌣S-rid {n = suc zero} {m = m} y = refl
-- -- ⌣S-rid {n = suc (suc n)} {m = m} y = refl

-- -- ⌣S-lid : {n m : ℕ} (x : S₊ n)
-- --   → Path (S₊ (n + m)) (x ⌣S (ptSn m)) (ptSn (n + m))
-- -- ⌣S-lid {n = zero} false = refl
-- -- ⌣S-lid {n = zero} true = refl
-- -- ⌣S-lid {n = suc zero} base = refl
-- -- ⌣S-lid {n = suc zero} {zero} (loop i) j = base
-- -- ⌣S-lid {n = suc zero} {suc m} (loop i) j = rCancel (merid (ptSn (suc m))) j i
-- -- ⌣S-lid {n = suc (suc n)} {m} north j = north
-- -- ⌣S-lid {n = suc (suc n)} {m} south j = north
-- -- ⌣S-lid {n = suc (suc n)} {m} (merid a i) j =
-- --   (cong (σ (S₊∙ (suc (n + m)))) (⌣S-lid a)
-- --   ∙ rCancel (merid (ptSn _))) j i

-- -- -- nm , (n - 1)m
-- -- open import Cubical.Data.Sum
-- -- -S^-gen : {k : ℕ} (n m : ℕ)
-- --   → isEvenT n ⊎ isOddT n
-- --   → isEvenT m ⊎ isOddT m
-- --   → S₊ k → S₊ k
-- -- -S^-gen {k = zero} n m (inl x₁) q x = x
-- -- -S^-gen {k = zero} n m (inr x₁) (inl x₂) x = x
-- -- -S^-gen {k = zero} n m (inr x₁) (inr x₂) false = true
-- -- -S^-gen {k = zero} n m (inr x₁) (inr x₂) true = false
-- -- -S^-gen {k = suc zero} n m p q base = base
-- -- -S^-gen {k = suc zero} n m (inl x) q (loop i) = loop i
-- -- -S^-gen {k = suc zero} n m (inr x) (inl x₁) (loop i) = loop i
-- -- -S^-gen {k = suc zero} n m (inr x) (inr x₁) (loop i) = loop (~ i)
-- -- -S^-gen {k = suc (suc k)} n m p q north = north
-- -- -S^-gen {k = suc (suc k)} n m p q south = north
-- -- -S^-gen {k = suc (suc k)} n m (inl x) q (merid a i) = σ (S₊∙ (suc k)) a i
-- -- -S^-gen {k = suc (suc k)} n m (inr x) (inl x₁) (merid a i) = σ (S₊∙ (suc k)) a i
-- -- -S^-gen {k = suc (suc k)} n m (inr x) (inr x₁) (merid a i) = σ (S₊∙ (suc k)) a (~ i)


-- -- suspFun↑ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
-- --   → (b : B)
-- --   → ((a : A) → Path B b b)
-- --   → Susp A → B 
-- -- suspFun↑ b f north = b
-- -- suspFun↑ b f south = b
-- -- suspFun↑ b f (merid a i) = f a i

-- -- suspFun↑≡ : {!!}
-- -- suspFun↑≡ = {!!}

-- -- S¹Fun : ∀ {ℓ} {B : Type ℓ}
-- --   → (b : B)
-- --   → (Path B b b)
-- --   → S¹ → B 
-- -- S¹Fun b p base = b
-- -- S¹Fun b p (loop i) = p i

-- -- toLoopS : {n : ℕ} → S₊ n → Path (S₊ (suc n)) (ptSn _) (ptSn _)
-- -- toLoopS {n = zero} false = loop
-- -- toLoopS {n = zero} true = refl
-- -- toLoopS {n = suc n} x = σ (S₊∙ _) x

-- -- S¹Fun-⌣ : (m : ℕ) (x : S¹) (y : S₊ m)
-- --   → S¹Fun {B = S₊ m → S₊ (suc m)} (λ _ → ptSn (suc m)) (λ i y → toLoopS y i) x y
-- --    ≡ (x ⌣S y)
-- -- S¹Fun-⌣ zero base false = refl
-- -- S¹Fun-⌣ zero (loop i) false = refl
-- -- S¹Fun-⌣ zero base true = refl
-- -- S¹Fun-⌣ zero (loop i) true = refl
-- -- S¹Fun-⌣ (suc m) base y = refl
-- -- S¹Fun-⌣ (suc m) (loop i) y = refl


-- -- suspFun-⌣ : (n m : ℕ) (x : S₊ (suc (suc n))) (y : S₊ m)
-- --   → suspFun↑ {A = S₊ (suc n)} {B = S₊ m → S₊ (suc (suc n) + m)}
-- --       (λ _ → north) (λ x i y → σ (S₊∙ _) (x ⌣S y) i) x y
-- --       ≡ x ⌣S y
-- -- suspFun-⌣ n m north y = refl
-- -- suspFun-⌣ n m south y = refl
-- -- suspFun-⌣ n m (merid a i) y = refl

-- -- invSphere' : {n : ℕ} → S₊ n → S₊ n
-- -- invSphere' {n = zero} = not
-- -- invSphere' {n = (suc zero)} = invLooper
-- -- invSphere' {n = suc (suc n)} north = north
-- -- invSphere' {n = suc (suc n)} south = north
-- -- invSphere' {n = suc (suc n)} (merid a i) = σ (S₊∙ _) a (~ i)

-- -- invSphere'≡ : {n : ℕ} → (x : S₊ n) → invSphere' x ≡ invSphere x
-- -- invSphere'≡ {n = zero} x = refl
-- -- invSphere'≡ {n = suc zero} x = refl
-- -- invSphere'≡ {n = suc (suc n)} north = merid (ptSn _)
-- -- invSphere'≡ {n = suc (suc n)} south = refl
-- -- invSphere'≡ {n = suc (suc n)} (merid a i) j =
-- --   compPath-filler (merid a) (sym (merid (ptSn _))) (~ j) (~ i)


-- -- -S^ : {k : ℕ} (n : ℕ) → S₊ k → S₊ k
-- -- -S^ zero x = x
-- -- -S^ (suc n) x = invSphere (-S^ n x)


-- -- invSphere-S^-comm : {k : ℕ} (n : ℕ) (x : S₊ k) → invSphere (-S^ n x) ≡ -S^ n (invSphere x)
-- -- invSphere-S^-comm zero x = refl
-- -- invSphere-S^-comm (suc n) x = cong invSphere (invSphere-S^-comm n x)


-- -- -S^² : {k : ℕ} (n : ℕ) (x : S₊ k) → -S^ n (-S^ n x) ≡ x
-- -- -S^² zero x = refl
-- -- -S^² (suc n) x =
-- --   cong invSphere (sym (invSphere-S^-comm n (-S^ n x)))
-- --   ∙ invSphere² _ (-S^ n (-S^ n x))
-- --   ∙ -S^² n x

-- -- -S^Iso : {k : ℕ} (n : ℕ) → Iso (S₊ k) (S₊ k)
-- -- fun (-S^Iso n) = -S^ n
-- -- inv (-S^Iso n) = -S^ n
-- -- rightInv (-S^Iso n) = -S^² n
-- -- leftInv (-S^Iso n) = -S^² n

-- -- -S^-comp : {k : ℕ} (n m : ℕ) (x : S₊ k)
-- --   → -S^ n (-S^ m x) ≡ -S^ (n + m) x
-- -- -S^-comp zero m x = refl
-- -- -S^-comp (suc n) m x = cong invSphere (-S^-comp n m x)

-- -- -S^·2 : {k : ℕ} (n : ℕ) (x : S₊ k) → -S^ (n + n) x ≡ x
-- -- -S^·2 zero x = refl
-- -- -S^·2 (suc n) x =
-- --     cong invSphere (λ i → -S^ (+-comm n (suc n) i) x)
-- --   ∙ invSphere² _ (-S^ (n + n) x)
-- --   ∙ -S^·2 n x

-- -- -S^-transp : {k : ℕ} (m : ℕ) (p : k ≡ m) (n : ℕ) (x : S₊ k) → subst S₊ p (-S^ n x) ≡ -S^ n (subst S₊ p x)
-- -- -S^-transp = J> λ n x → transportRefl _ ∙ sym (cong (-S^ n) (transportRefl x))

-- -- sym^ : ∀ {ℓ} {A : Type ℓ} {x : A} (n : ℕ) → x ≡ x → x ≡ x
-- -- sym^ zero p = p
-- -- sym^ (suc n) p = sym (sym^ n p)

-- -- toLoop-S^ : {k : ℕ} (n : ℕ) (x : S₊ (suc k)) → toLoopS (-S^ n x) ≡ sym^ n (toLoopS x)
-- -- toLoop-S^ {k = k} zero x = refl
-- -- toLoop-S^ {k = k} (suc n) x =
-- --   σ-invSphere k _ ∙ cong sym (toLoop-S^ n x)


-- -- toLoopSym : (m : ℕ) (x : S¹) (y : S₊ (suc (suc m)))
-- --   → (x ⌣S y)
-- --    ≡ suspFun↑ north (λ y → sym (σ (S₊∙ _) (x ⌣S y))) y
-- -- toLoopSym m base north = refl
-- -- toLoopSym m base south = refl
-- -- toLoopSym m base (merid a i) j = rCancel (merid north) (~ j) (~ i)
-- -- toLoopSym m (loop i) north j = rCancel (merid north) j i
-- -- toLoopSym m (loop i) south j = (cong (σ (S₊∙ _)) (sym (merid (ptSn _))) ∙ rCancel (merid north)) j i
-- -- toLoopSym m (loop i) (merid a j) k =
-- --   hcomp (λ r → λ {(i = i0) → rCancel (merid north) (~ k) (~ j)
-- --                  ; (i = i1) → rCancel (merid north) (~ k) (~ j)
-- --                  ; (j = i0) → rCancel (merid north) k i
-- --                  ; (j = i1) → compPath-filler' (cong (σ (S₊∙ (suc (suc m))))
-- --                                 (sym (merid (ptSn (suc m))))) (rCancel (merid north)) r k i
-- --                  ; (k = i0) → σ (S₊∙ (suc (suc m))) (compPath-filler (merid a)
-- --                                 (sym (merid (ptSn (suc m)))) (~ r) j) i
-- --                  ; (k = i1) → (σ (S₊∙ (suc (suc m))) (σ (S₊∙ (suc m)) a i)) (~ j)})
-- --         (main _ (sym (rCancel (merid north)))
-- --           (λ i j → σ (S₊∙ _) (σ (S₊∙ _) a i) j) i j k)
-- --   where
-- --   main : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (coh : refl ≡ p) (q : p ≡ p)
-- --        → Cube (λ k j → coh j (~ k)) (λ k j → coh j (~ k))
-- --                (λ i j → coh (~ j) i) (λ i j → coh (~ j) i)
-- --                (λ i j → q j i)
-- --                λ i j → q i (~ j)
-- --   main = J> λ q i j k → sym≡flipSquare q k (~ j) i

-- -- suspFun-pres-sym^ : (n m k : ℕ) (x : S₊ (2 + n)) (y : S₊ m)
-- --   → {!suspFun↑ north (λ y → sym (σ (S₊∙ _) (x ⌣S y))) ? !}
-- -- suspFun-pres-sym^ = {!!}

-- -- suspFun-pres- : (n m : ℕ) (x : S₊ (2 + n)) (y : S₊ m)
-- --   → invSphere'
-- --       (suspFun↑ {A = S₊ (suc n)} {B = S₊ m → S₊ (suc (suc n) + m)}
-- --        (λ _ → north) (λ x i y → σ (S₊∙ _) (x ⌣S y) i) x y)
-- --    ≡ (suspFun↑ {A = S₊ (suc n)} {B = S₊ m → S₊ (suc (suc n) + m)}
-- --         (λ _ → north) (λ x i y → σ (S₊∙ _) (invSphere' (x ⌣S y)) i) x y)
-- -- suspFun-pres- n m north y = refl
-- -- suspFun-pres- n m south y = refl
-- -- suspFun-pres- n m (merid a i) y j = help j i
-- --   where
-- --   help : cong invSphere' (σ (S₊∙ (suc (n + m))) (a ⌣S y))
-- --        ≡ σ (S₊∙ _) (invSphere' (a ⌣S y))
-- --   help = cong-∙ invSphere' (merid (a ⌣S y)) (sym (merid (ptSn _)))
-- --        ∙ cong (sym (σ (S₊∙ (suc (n + m))) (a ⌣S y)) ∙_)
-- --               (rCancel (merid _))
-- --        ∙ sym (rUnit _)
-- --        ∙ sym (σ-invSphere _ (a ⌣S y))
-- --        ∙ cong (σ (S₊∙ (suc (n + m)))) (sym (invSphere'≡ (a ⌣S y)))

-- -- suspFun-pres** : (n m k k' : ℕ) (p : k ≡ k')
-- --   (f : S₊ n → S₊ m → S₊ k') (x : _) (y : _)
-- --   → suspFun↑ {A = S₊ n} {B = S₊ m → S₊ (suc k)}
-- --               (λ _ → ptSn (suc k))
-- --               (λ x → funExt λ y → toLoopS (subst S₊ (sym p) (f x y))) x y
-- --    ≡ subst S₊ (cong suc (sym p))
-- --        (suspFun↑ {A = S₊ n} {B = S₊ m → S₊ (suc k')} (λ _ → ptSn _) (λ x → funExt (λ y → toLoopS (f x y))) x y)
-- -- suspFun-pres** n m k =
-- --   J> λ f x y → (λ i → suspFun↑ {A = S₊ n} {B = S₊ m → S₊ (suc k)}
-- --               (λ _ → ptSn (suc k))
-- --               (λ x → funExt λ y → toLoopS (transportRefl (f x y) i)) x y)
-- --     ∙ sym (transportRefl _)

-- -- suspFun-pres-gen : (n m : ℕ)
-- --   (f : S₊ (suc n) → S₊ m → S₊ (suc n + m))
-- --      (x : S₊ (2 + n)) (y : S₊ m)
-- --   → invSphere'
-- --       (suspFun↑ {A = S₊ (suc n)} {B = S₊ m → S₊ (suc (suc n) + m)}
-- --        (λ _ → north) (λ x i y → σ (S₊∙ _) (f x y) i) x y)
-- --    ≡ (suspFun↑ {A = S₊ (suc n)} {B = S₊ m → S₊ (suc (suc n) + m)}
-- --         (λ _ → north) (λ x i y → σ (S₊∙ _) (invSphere' (f x y)) i) x y)
-- -- suspFun-pres-gen n m f north y = refl
-- -- suspFun-pres-gen n m f south y = refl
-- -- suspFun-pres-gen n m f (merid a i) y j = help j i
-- --   where
-- --   help : cong invSphere' (σ (S₊∙ (suc (n + m))) (f a y))
-- --        ≡ σ (S₊∙ _) (invSphere' (f a y))
-- --   help = cong-∙ invSphere' (merid (f a y)) (sym (merid (ptSn _)))
-- --        ∙ cong (sym (σ (S₊∙ (suc (n + m))) (f a y)) ∙_)
-- --               (rCancel (merid _))
-- --        ∙ sym (rUnit _)
-- --        ∙ sym (σ-invSphere _ (f a y))
-- --        ∙ cong (σ (S₊∙ (suc (n + m)))) (sym (invSphere'≡ (f a y)))

-- -- suspFun-pres-gen' : (n m : ℕ)(f : S₊ (suc n) → S₊ m → S₊ (suc n + m))
-- --      (x : S₊ (2 + n)) (y : S₊ m)
-- --   → invSphere
-- --       (suspFun↑ {A = S₊ (suc n)} {B = S₊ m → S₊ (suc (suc n) + m)}
-- --        (λ _ → north) (λ x i y → σ (S₊∙ _) (f x y) i) x y)
-- --    ≡ (suspFun↑ {A = S₊ (suc n)} {B = S₊ m → S₊ (suc (suc n) + m)}
-- --         (λ _ → north) (λ x i y → σ (S₊∙ _) (invSphere (f x y)) i) x y)
-- -- suspFun-pres-gen' n m f x y =
-- --      sym (invSphere'≡ (suspFun↑ {A = S₊ (suc n)} {B = S₊ m → S₊ (suc (suc n) + m)}
-- --        (λ _ → north) (λ x i y → σ (S₊∙ _) (f x y) i) x y))
-- --   ∙∙ suspFun-pres-gen n m f x y
-- --   ∙∙ λ j → suspFun↑ {A = S₊ (suc n)} {B = S₊ m → S₊ (suc (suc n) + m)}
-- --        (λ _ → north)
-- --       (λ x₁ i y₁ → σ (S₊∙ (suc (n + m))) (invSphere'≡ (f x₁ y₁) j) i) x y


-- -- invSphere'-pt : (n : ℕ) → invSphere' (ptSn (suc n)) ≡ ptSn (suc n)
-- -- invSphere'-pt zero = refl
-- -- invSphere'-pt (suc n) = refl

-- -- -S^-ind : {k m : ℕ}
-- --   → (f : S₊ k → S₊ m)
-- --   → ((x : S₊ k) → invSphere (f x) ≡ f (invSphere x))
-- --   →  (n : ℕ)
-- --   → ((x : S₊ k) → f (-S^ n x) ≡ -S^ n (f x))
-- -- -S^-ind {k = k} {m = m} f r zero x = refl
-- -- -S^-ind {k = k} {m = m} f r (suc n) x =
-- --   cong f (invSphere-S^-comm n _)
-- --   ∙ -S^-ind f r n (invSphere x) ∙ cong (-S^ n) (sym (r x))
-- --   ∙ sym (invSphere-S^-comm n _)

-- -- sphereFun↑ : {n m k : ℕ}
-- --   → (f : S₊ n → S₊ m → S₊ k)
-- --   → S₊ (suc n) → S₊ m → S₊ (suc k)
-- -- sphereFun↑ {n = zero} {m = m} f base y = ptSn _
-- -- sphereFun↑ {n = zero} {m = m} f (loop i) y = toLoopS (f false y) i
-- -- sphereFun↑ {n = suc n} {m = m} f north y = ptSn _
-- -- sphereFun↑ {n = suc n} {m = m} f south y = ptSn _
-- -- sphereFun↑ {n = suc n} {m = m} f (merid a i) y = toLoopS (f a y) i

-- -- sphereFun↑-subst : {n m : ℕ} (k' k : ℕ) (p : k' ≡ k)
-- --   → (f : S₊ n → S₊ m → S₊ k') (x : S₊ _) (y : S₊ _)
-- --   → sphereFun↑ (λ x y → subst S₊ p (f x y)) x y
-- --    ≡ subst S₊ (cong suc p) (sphereFun↑ f x y)
-- -- sphereFun↑-subst k' = J> λ f x y
-- --   → (λ i → sphereFun↑ (λ x₁ y₁ → transportRefl (f x₁ y₁) i) x y)
-- --    ∙ sym (transportRefl _)

-- -- sphereFun↑-' : {n m k : ℕ}
-- --   → (f : S₊ (suc n) → S₊ (suc m) → S₊ (suc k)) (x : S₊ _) (y : S₊ _)
-- --   → sphereFun↑ (λ x y → invSphere' (f x y)) x y
-- --    ≡ invSphere' (sphereFun↑ (λ x y → (f x y)) x y)
-- -- sphereFun↑-' {n = n} {m = m} {k = k} f north y = refl
-- -- sphereFun↑-' {n = n} {m = m} {k = k} f south y = refl
-- -- sphereFun↑-' {n = n} {m = m} {k = k} f (merid a i) y j =
-- --   lem k (f a y) j i
-- --   where
-- --   lem : (k : ℕ) (x : S₊ (suc k))
-- --     → (toLoopS (invSphere' x)) ≡ (cong invSphere' (toLoopS x))
-- --   lem k x =
-- --     sym (cong-∙ invSphere' (merid x) (sym (merid (ptSn _)))
-- --       ∙∙ cong (cong invSphere' (merid x) ∙_)
-- --           (rCancel (merid (ptSn _)))
-- --       ∙∙ (sym (rUnit _)
-- --         ∙ sym (σ-invSphere k x)
-- --         ∙ cong (σ (S₊∙ (suc k)))
-- --            (sym (invSphere'≡ x))))

-- -- sphereFun↑^ : {n m k : ℕ} (l : ℕ)
-- --   → (f : S₊ (suc n) → S₊ (suc m) → S₊ (suc k)) (x : S₊ _) (y : S₊ _)
-- --   → sphereFun↑ (λ x y → -S^ l (f x y)) x y
-- --    ≡ -S^ l (sphereFun↑ (λ x y → (f x y)) x y)
-- -- sphereFun↑^ zero f x y = refl
-- -- sphereFun↑^ (suc l) f x y =
-- --     (λ i → sphereFun↑ (λ x₁ y₁ → invSphere'≡ (-S^ l (f x₁ y₁)) (~ i)) x y)
-- --   ∙ sphereFun↑-' (λ x₁ y₁ → (-S^ l (f x₁ y₁))) x y
-- --   ∙ invSphere'≡ ((sphereFun↑ (λ x₁ y₁ → -S^ l (f x₁ y₁)) x y))
-- --   ∙ cong invSphere (sphereFun↑^ l f x y)

-- -- sphereFun↑-⌣ : {n m : ℕ} (x : S₊ (suc n)) (y : S₊ m)
-- --   → sphereFun↑ {n = n} {m = m} _⌣S_ x y ≡ x ⌣S y
-- -- sphereFun↑-⌣ {n = zero} {m = m} base y = refl
-- -- sphereFun↑-⌣ {n = zero} {m = zero} (loop i) false = refl
-- -- sphereFun↑-⌣ {n = zero} {m = zero} (loop i) true = refl
-- -- sphereFun↑-⌣ {n = zero} {m = suc m} (loop i) y = refl
-- -- sphereFun↑-⌣ {n = suc n} {m = m} north y = refl
-- -- sphereFun↑-⌣ {n = suc n} {m = m} south y = refl
-- -- sphereFun↑-⌣ {n = suc n} {m = m} (merid a i) y = refl

-- -- S^-even : {k : ℕ} (n : ℕ) (x : S₊ k) → isEvenT n → -S^ n x ≡ x
-- -- S^-even zero x p = refl
-- -- S^-even (suc (suc n)) x p = invSphere² _ (-S^ n x) ∙ S^-even n x p

-- -- move-transp-S^ : {k : ℕ} (n : ℕ) (p : k ≡ n) (m : ℕ)
-- --   → (x : S₊ k) (y : S₊ n)
-- --   → subst S₊ p (-S^ m x) ≡ y
-- --   → subst S₊ (sym p) (-S^ m y) ≡ x
-- -- move-transp-S^ =
-- --   J> λ m x → J> transportRefl _
-- --   ∙ cong (-S^ m) (transportRefl _)
-- --   ∙ -S^² m x

-- -- master-lem : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (coh : refl ≡ p)
-- --   (q : p ≡ p)
-- --   → Cube (λ j k → coh j (~ k)) (λ j k → coh j (~ k))
-- --           (λ i k → q k i) (λ i k → q i (~ k))
-- --           (λ j k → coh (~ k) j) λ j k → coh (~ k) j
-- -- master-lem = J> λ q → λ i j k → sym≡flipSquare q j (~ k) i

-- -- gr-comm-l : {m : ℕ} → (x : S¹) (y : S₊ (suc m))
-- --   → (x ⌣S y)
-- --    ≡ subst S₊ (+-comm (suc m) 1)
-- --            (-S^ (suc m) (y ⌣S x))
-- -- gr-comm-l {m = zero} x y = (main x y ∙ invSphere'≡ (y ⌣S x)) ∙ sym (transportRefl (invSusp (y ⌣S x)))
-- --   where
-- --   pp-main : (x : S¹) → PathP (λ i → ⌣S-lid {m = 1} x i
-- --           ≡ ⌣S-lid {m = 1} x i) (cong (x ⌣S_) loop) (sym (σ (S₊∙ _) x))
-- --   pp-main base i j = rCancel (merid base) (~ i) (~ j) 
-- --   pp-main (loop k) i j = master-lem _ (sym (rCancel (merid base))) (λ j k → σ (S₊∙ 1) (loop j) k) k i j

-- --   pp-help : (x : S¹) → PathP (λ i → ⌣S-lid {m = 1} x i
-- --           ≡ ⌣S-lid {m = 1} x i) (cong (x ⌣S_) loop) (cong invSphere' (σ (S₊∙ _) x))
-- --   pp-help x = pp-main x
-- --     ▷ (rUnit _
-- --     ∙∙ cong (sym (σ (S₊∙ _) x) ∙_) (sym (rCancel (merid base)))
-- --     ∙∙ sym (cong-∙ invSphere' (merid x) (sym (merid base))))

-- --   main : (x y : S¹) → (x ⌣S y) ≡ invSphere' (y ⌣S x)
-- --   main x base = ⌣S-lid {m = 1} x
-- --   main x (loop i) = flipSquare (pp-help x) i
-- -- gr-comm-l {m = suc m} x y =
-- --     (main-lem x y
-- --    ∙ sym (transportRefl (invSphere' (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)))
-- --   ∙ sym (compSubstℕ {A = S₊} (cong suc (sym (+-comm (suc m) 1))) (+-comm (suc (suc m)) 1) refl
-- --      {x = invSphere' (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)}))
-- --   ∙ cong (subst S₊ (+-comm (suc (suc m)) 1))
-- --       (cong (subst S₊ (cong suc (sym (+-comm (suc m) 1))))
-- --         (sym (S^-lem (suc m) (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)))
-- --       ∙ -S^-transp _ (cong suc (sym (+-comm (suc m) 1)))
-- --          (suc (suc m) + suc m)
-- --          (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)
-- --       ∙ sym (-S^-comp (suc (suc m)) (suc m)
-- --          (subst S₊ (cong suc (sym (+-comm (suc m) 1)))
-- --            (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x))))
-- --   ∙ cong (subst S₊ (+-comm (suc (suc m)) 1)
-- --        ∘ -S^ (suc (suc m)))
-- --        ((sym (-S^-transp _ (cong suc (sym (+-comm (suc m) 1))) (suc m) (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x))
-- --        ∙ cong (subst S₊ (cong suc (sym (+-comm (suc m) 1))))
-- --              (sym (sphereFun↑^ (suc m)
-- --               (λ x₂ x₃ →  (x₃ ⌣S x₂)) y x))
-- --        ∙ sym (sphereFun↑-subst _ _ (sym (+-comm (suc m) 1))
-- --          (λ x₂ x₃ →  (-S^ (suc m) (x₃ ⌣S x₂))) y x))
-- --        ∙∙ cong (λ (s : S₊ (suc m) → S¹ → S₊ (suc m + 1))
-- --                 → sphereFun↑ s y x)
-- --                (refl
-- --              ∙ sym (funExt λ x → funExt λ y
-- --              → sym (move-transp-S^ _ (+-comm (suc m) 1)
-- --              (suc m) (x ⌣S y) (y ⌣S x)
-- --               (sym (gr-comm-l y x)))
-- --              ∙ refl))
-- --        ∙∙ sphereFun↑-⌣ y x)
-- --   where
-- --   S^-lem : {k : ℕ} (m : ℕ) (x : S₊ k)
-- --     → -S^ (suc m + m) x ≡ invSphere' x
-- --   S^-lem m x =
-- --        sym (invSphere'≡ (-S^ (m + m) x))
-- --      ∙ cong invSphere' (-S^·2 m x)

-- --   pst : +-comm (suc (suc m)) 1
-- --       ∙ cong suc (sym (+-comm (suc m) 1)) ≡ refl
-- --   pst = isSetℕ _ _ _ _

-- --   ⌣S-south : (x : S¹) → x ⌣S south ≡ north
-- --   ⌣S-south base = refl
-- --   ⌣S-south (loop i) j =
-- --     (cong (σ (S₊∙ _)) (sym (merid (ptSn (suc m))) )
-- --     ∙ rCancel (merid (ptSn _))) j i


-- --   PathP-main : (x : S¹) (a : S₊ (suc m))
-- --     → PathP (λ i → ⌣S-lid x i ≡ ⌣S-south x i) (cong (x ⌣S_) (merid a))
-- --         (sym (σ (S₊∙ _) (x ⌣S a))) 
-- --   PathP-main base a j i = rCancel (merid north) (~ j) (~ i)
-- --   PathP-main (loop k) a j i =
-- --     hcomp (λ r → λ {(i = i0) → rCancel (merid north) j k
-- --                    ; (i = i1) → compPath-filler' (cong (σ (S₊∙ (suc (suc m)))) (sym (merid (ptSn (suc m))))) (rCancel (merid north)) r j k
-- --                    ; (j = i0) → σ (S₊∙ (suc (suc m))) (compPath-filler (merid a) (sym (merid (ptSn (suc m)))) (~ r) i) k
-- --                    ; (j = i1) → σ (S₊∙ (suc (suc m))) (σ (S₊∙ (suc m)) a k) (~ i)
-- --                    ; (k = i0) → rCancel (merid north) (~ j) (~ i)
-- --                    ; (k = i1) → rCancel (merid north) (~ j) (~ i)})
-- --           (master-lem _ (sym (rCancel (merid north)))
-- --            (λ i k → σ (S₊∙ (suc (suc m))) (loop i ⌣S a) k) k j i)

-- --   pp : (x : S¹) (a : S₊ (suc m))
-- --     → PathP (λ i → ⌣S-lid x i ≡ ⌣S-south x i) (cong (x ⌣S_) (merid a))
-- --         (cong invSphere' (σ (S₊∙ _) (x ⌣S a))) 
-- --   pp x a = PathP-main x a
-- --       ▷ (rUnit _
-- --      ∙∙ cong (sym (σ (S₊∙ _) (x ⌣S a)) ∙_) (sym (rCancel (merid north)))
-- --      ∙∙ sym (cong-∙ invSphere' (merid (x ⌣S a)) (sym (merid north))))

-- --   main-lem : (x : S¹) (y : S₊ (2 + m))
-- --     → (x ⌣S y)
-- --       ≡ invSphere' (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)
-- --   main-lem x north = ⌣S-lid x
-- --   main-lem x south = ⌣S-south x
-- --   main-lem x (merid a i) j = pp x a j i

-- -- gr-comm-lem : {n m : ℕ}
-- --   → ((x : S₊ (suc n)) (y : S₊ (suc (suc m)))
-- --      → (x ⌣S y) ≡ subst S₊ (+-comm (suc (suc m)) (suc n)) (-S^ (suc (suc m) · (suc n)) (y ⌣S x)))
-- --   → (((x : S₊ (suc m)) (y : S₊ (suc (suc n)))
-- --      → (x ⌣S y) ≡ subst S₊ (+-comm (suc (suc n)) (suc m)) (-S^ ((suc (suc n)) · (suc m)) (y ⌣S x))))
-- --   → (((x : S₊ (suc n)) (y : S₊ (suc m))
-- --      → (y ⌣S x) ≡ subst S₊ (sym (+-comm (suc m) (suc n))) (-S^ ((suc n) · (suc m)) (x ⌣S y))))
-- --   → (x : S₊ (suc (suc n))) (y : S₊ (suc (suc m)))
-- --   → (x ⌣S y) ≡ subst S₊ (+-comm (suc (suc m)) (suc (suc n))) (-S^ (suc (suc m) · (suc (suc n))) (y ⌣S x))
-- -- gr-comm-lem {n = n} {m = m} ind1 ind2 ind3 x y =
-- --      sym (sphereFun↑-⌣ x y)
-- --   ∙∙ cong (λ (s : S₊ (suc n) → S₊ (suc (suc m)) → S₊ ((suc n) + (suc (suc m)))) → sphereFun↑ s x y)
-- --           (funExt (λ x → funExt λ y
-- --           → ind1 x y))
-- --   ∙∙ (sphereFun↑-subst _ _ (+-comm (suc (suc m)) (suc n)) (λ x y → -S^ (suc (suc m) · suc n) (y ⌣S x)) x y
-- --   ∙ cong (subst S₊ (cong suc (+-comm (suc (suc m)) (suc n))))
-- --       (sphereFun↑^ (suc (suc m) · suc n)  (λ x y → y ⌣S x) x y
-- --       ∙ cong (-S^ (suc (suc m) · suc n))
-- --          (cong (λ (s : S₊ (suc n) → S₊ (suc (suc m)) → S₊ ((suc (suc m)) + (suc n))) → sphereFun↑ s x y)
-- --            (funExt (λ x → funExt λ y →
-- --             sym (sphereFun↑-⌣ y x)
-- --           ∙ cong (λ (s : S₊ (suc m) → S₊ (suc n) → S₊ ((suc m) + (suc n))) → sphereFun↑ s y x)
-- --              (funExt λ x
-- --                     → funExt λ y
-- --                      → ind3 y x)
-- --           ∙ sphereFun↑-subst _ _ (sym (+-comm (suc m) (suc n)))
-- --               (λ x y → -S^ (suc n · suc m) (y ⌣S x)) y x
-- --           ∙ cong (subst S₊ (cong suc (sym (+-comm (suc m) (suc n)))))
-- --                  (sphereFun↑^ (suc n · suc m) (λ x y → (y ⌣S x)) y x
-- --                 ∙ cong (-S^ (suc n · suc m) )
-- --                    refl)
-- --           ∙ refl))
-- --           ∙ sphereFun↑-subst _ _  (sym (cong suc (+-comm (suc m) (suc n))))
-- --               ((λ x₁ x₂ →
-- --                (-S^ (suc n · suc m) (sphereFun↑ (λ x₃ y₁ → y₁ ⌣S x₃) x₂ x₁)))) x y
-- --           ∙ cong (subst S₊ (sym (cong (suc ∘ suc) (+-comm (suc m) (suc n)))))
-- --                    ((sphereFun↑^ (suc n · suc m)
-- --                      ((λ x₁ x₂ → (sphereFun↑ (λ x₃ y₁ → y₁ ⌣S x₃) x₂ x₁))) x y
-- --                   ∙ cong (-S^ (suc n · suc m)) (cool x y))))
-- --           ∙ refl)
-- --   ∙ big-lem (suc n) (suc m)
-- --       _ (λ i → suc (suc (+-comm (suc m) (suc n) (~ i))))
-- --       _ (λ i → suc (+-comm (suc (suc m)) (suc n) i)) _
-- --       (sym (+-comm (suc (suc m)) (suc (suc n))))
-- --       (λ i → suc (+-comm (suc (suc n)) (suc m) i))
-- --       (sphereFun↑ (λ x₁ y₂ → y₂ ⌣S x₁) y x)
-- --   ∙ sym (cong (subst S₊ (+-comm (suc (suc m)) (suc (suc n))))
-- --          (cong (-S^ (suc (suc m) · suc (suc n)))
-- --           (sym (sphereFun↑-⌣ y x)
-- --          ∙ (λ i → sphereFun↑ (λ x y → ind2 x y i) y x)
-- --          ∙ sphereFun↑-subst _ _
-- --              (+-comm (suc (suc n)) (suc m)) (λ x y → -S^ (suc (suc n) · suc m) (y ⌣S x)) y x
-- --          ∙ cong (subst S₊ (cong suc (+-comm (suc (suc n)) (suc m))))
-- --             (sphereFun↑^ (suc (suc n) · suc m) (λ x y → y ⌣S x) y x
-- --             ∙ refl)))))
-- --     where
-- --     ℕ-p : (n m : ℕ)
-- --       → (suc m · suc n + suc n · m)
-- --        ≡ (m + m) + ((n · m + n · m) + (suc n))
-- --     ℕ-p n m =
-- --       cong suc (cong (_+ (m + n · m)) (cong (n +_) (·-comm m (suc n)))
-- --              ∙ sym (+-assoc n (m + n · m) _)
-- --              ∙ +-comm n _
-- --              ∙ cong (_+ n) (+-assoc (m + n · m) m (n · m)
-- --                          ∙ cong (_+ (n · m))
-- --                               (sym (+-assoc m (n · m) m)
-- --                             ∙ cong (m +_) (+-comm (n · m) m)
-- --                             ∙ +-assoc m m (n · m))
-- --                             ∙ sym (+-assoc (m + m) (n · m) (n · m))))
-- --       ∙ sym (+-suc (m + m + (n · m + n · m)) n)
-- --       ∙ sym (+-assoc (m + m) (n · m + n · m) (suc n))

-- --     ℕ-p2 : (n m : ℕ) → suc m · n + n · m + 1 ≡ (((n · m) + (n · m)) + (suc n))
-- --     ℕ-p2 n m = (λ _ → ((n + m · n) + n · m) + 1)
-- --       ∙ cong (_+ 1) (sym (+-assoc n (m · n) (n · m))
-- --                     ∙ (λ i → +-comm n ((·-comm m n i) + n · m) i)
-- --                     ∙ refl)
-- --       ∙ sym (+-assoc (n · m + n · m) n 1)
-- --       ∙ cong (n · m + n · m +_) (+-comm n 1)

-- --     big-lem : (n m : ℕ) {x : ℕ} (y : ℕ) (p : x ≡ y) (z : ℕ) (s : y ≡ z)
-- --               (d : ℕ) (r : z ≡ d) (t : x ≡ d)
-- --        (a : S₊ x)
-- --       → subst S₊ s (-S^ (suc m · n) (subst S₊ p (-S^ (n · m) (invSphere' a))))
-- --       ≡ subst S₊ (sym r)
-- --           (-S^ (suc m · suc n)
-- --            (subst S₊ t (-S^ (suc n · m) a)))
-- --     big-lem n m =
-- --       J> (J> (J> λ t a
-- --       → transportRefl _
-- --       ∙ cong (-S^ (n + m · n)) (transportRefl _)
-- --       ∙ sym (transportRefl _
-- --            ∙ cong (-S^ (suc m · suc n)) ((λ i → subst S₊ (isSetℕ _ _ t refl i) (-S^ (m + n · m) a))
-- --                ∙ transportRefl (-S^ (m + n · m) a) )
-- --            ∙ -S^-comp (suc m · suc n) (suc n · m) a
-- --            ∙ ((funExt⁻ (cong -S^ (ℕ-p n m)) a
-- --              ∙ (sym (-S^-comp (m + m) _ a)
-- --               ∙ -S^·2 m (-S^ (n · m + n · m + suc n) a))
-- --              ∙ funExt⁻ (cong -S^ (sym (ℕ-p2 n m))) a)
-- --             ∙ sym (-S^-comp (suc m · n + n · m) 1 a)
-- --             ∙ cong (-S^ (suc m · n + n · m))
-- --                (sym (invSphere'≡ a)))
-- --            ∙ sym (-S^-comp (suc m · n) (n · m) (invSphere' a)) )))

-- --     l1 : (x :  S₊ (2 + n))
-- --       → sphereFun↑ (λ x₂ x₃ → sphereFun↑ (λ x₄ y₁ → y₁ ⌣S x₄) x₃ x₂) x north ≡ north
-- --     l1 north = refl
-- --     l1 south = refl
-- --     l1 (merid a i) j = rCancel (merid north) j i

-- --     l2 : (x :  S₊ (2 + n))
-- --       → sphereFun↑ (λ x₂ x₃
-- --         → sphereFun↑ (λ x₄ y₁ → y₁ ⌣S x₄) x₃ x₂) x south
-- --         ≡ north
-- --     l2 north = refl
-- --     l2 south = refl
-- --     l2 (merid a i) j = rCancel (merid north) j i

-- --     cool : (x : S₊ (2 + n)) (y : S₊ (2 + m))
-- --        → (sphereFun↑ (λ x₁ x₂
-- --           → sphereFun↑ (λ x₃ y₁ → y₁ ⌣S x₃) x₂ x₁) x y)
-- --         ≡ invSphere' (sphereFun↑ (λ x₁ y₂ → y₂ ⌣S x₁) y x)
-- --     cool x north = l1 x
-- --     cool x south = l2 x
-- --     cool x (merid a i) j = h j i
-- --       where
-- --       main : (x : _) → PathP (λ i → l1 x i ≡ l2 x i)
-- --              (cong (sphereFun↑ (λ x₂ x₃
-- --               → sphereFun↑ (λ x₄ y₁ → y₁ ⌣S x₄) x₃ x₂) x )
-- --                (merid a))
-- --              (sym (σ (S₊∙ (suc (suc (n + suc m)))) (x ⌣S a)))
-- --       main north = cong sym (sym (rCancel (merid north)))
-- --       main south = cong sym (sym (rCancel (merid north)))
-- --       main (merid z i) j k =
-- --         master-lem _
-- --           (sym (rCancel (merid north)))
-- --           (cong (λ x → σ (S₊∙ (suc (suc (n + suc m))))
-- --            (x ⌣S a)) (merid z)) i j k

-- --       h : PathP (λ i → l1 x i ≡ l2 x i)
-- --                 (cong (sphereFun↑
-- --                  (λ x₂ x₃ → sphereFun↑ (λ x₄ y₁ → y₁ ⌣S x₄) x₃ x₂) x)
-- --                   (merid a)) (cong invSphere' (σ (S₊∙ _) (x ⌣S a)))
-- --       h = main x
-- --         ▷ ((rUnit _ ∙ cong (sym (σ (S₊∙ _) (x ⌣S a)) ∙_)
-- --             (sym (rCancel (merid north))))
-- --            ∙ sym (cong-∙ invSphere'
-- --               (merid (x ⌣S a)) (sym (merid (ptSn _)))))

-- -- ⌣S-comm₀ : (x : Bool) (m : ℕ) (y : S₊ m)
-- --   → PathP (λ i → S₊ (+-zero m (~ i))) (x ⌣S y) (y ⌣S x)
-- -- ⌣S-comm₀ false =
-- --   elim+2 (λ { false → refl ; true → refl})
-- --     (λ { base → refl ; (loop i) → refl})
-- --     ind
-- --   where
-- --   ind : (n : ℕ) →
-- --       ((y : S₊ (suc n)) →
-- --        PathP (λ i → S₊ (suc (+-zero n (~ i)))) y (y ⌣S false)) →
-- --       (y : Susp (S₊ (suc n))) →
-- --       PathP (λ i → Susp (S₊ (suc (+-zero n (~ i))))) y (y ⌣S false)
-- --   ind n p north i = north
-- --   ind n p south i = merid (ptSn (suc (+-zero n (~ i)))) (~ i)
-- --   ind n p (merid a j) i =
-- --     comp (λ k → Susp (S₊ (suc (+-zero n (~ i ∨ ~ k)))))
-- --          (λ r →
-- --          λ {(i = i0) → merid a j
-- --           ; (i = i1) →
-- --             σ (S₊∙ (suc (+-zero n (~ r)))) (p a r) j
-- --           ; (j = i0) → north
-- --           ; (j = i1) → merid (ptSn (suc (+-zero n (~ i ∨ ~ r)))) (~ i)})
-- --          (compPath-filler (merid a) (sym (merid (ptSn _))) i j)
-- -- ⌣S-comm₀ true m y = (λ i → ptSn (+-zero m (~ i))) ▷ (sym (⌣S-lid y))

-- -- ⌣S-comm : {n m : ℕ} (x : S₊ n) (y : S₊ m)
-- --   → (x ⌣S y) ≡ subst S₊ (+-comm m n) (-S^ (m · n) (y ⌣S x))
-- -- ⌣S-comm {n = zero} {m = m} x y =
-- --   sym (fromPathP (symP {A = λ i → S₊ (+-zero m i)} ( (⌣S-comm₀ x m y))))
-- --   ∙ sym (cong (subst S₊ (+-zero m))
-- --         ((λ i → -S^ (0≡m·0 m (~ i)) (y ⌣S x))))
-- -- ⌣S-comm {n = suc n} {m = zero} x y =
-- --   sym (fromPathP (⌣S-comm₀ y (suc n) x))
-- --   ∙ (λ i → subst S₊ (isSetℕ _ _
-- --              (sym (+-comm (suc n) zero))
-- --              (+-comm zero (suc n)) i) (y ⌣S x))
-- -- ⌣S-comm {n = suc zero} {m = suc m} x y =
-- --     gr-comm-l x y
-- --   ∙ cong (subst S₊ (+-comm (suc m) 1))
-- --      λ i → -S^ (·-identityʳ (suc m) (~ i)) (y ⌣S x)
-- -- ⌣S-comm {n = suc (suc n)} {m = suc zero} x y =
-- --     sym (substSubst⁻ S₊ (+-comm 1 (suc (suc n))) (x ⌣S y))
-- --   ∙ cong (subst S₊ (+-comm 1 (suc (suc n))))
-- --         ((λ i → subst S₊ (isSetℕ _ _
-- --            (sym (+-comm 1 (suc (suc n)))) (+-comm (suc (suc n)) 1) i)
-- --            (x ⌣S y))
-- --       ∙ (sym (sym
-- --          (-S^-transp _ (+-comm (suc (suc n)) 1) (1 · suc (suc n))
-- --            (-S^ (suc (suc n)) (x ⌣S y)))
-- --             ∙ cong (subst S₊ (+-comm (suc (suc n)) 1))
-- --                (cong (-S^ (1 · suc (suc n)))
-- --                  (λ i → -S^ (·-identityˡ (suc (suc n)) (~ i)) (x ⌣S y))
-- --               ∙ -S^² (1 · suc (suc n)) (x ⌣S y)))))
-- --   ∙ sym (cong (subst S₊ (+-comm 1 (suc (suc n)))
-- --              ∘ -S^ (1 · suc (suc n))) (gr-comm-l y x))
-- -- ⌣S-comm {n = suc (suc n)} {m = suc (suc m)} x y =
-- --   gr-comm-lem ⌣S-comm ⌣S-comm
-- --     (λ x y → (sym (cong (subst S₊ (sym (+-comm (suc m) (suc n))))
-- --                (sym (-S^-transp _ (+-comm (suc m) (suc n))
-- --                  (suc n · suc m) (-S^ (suc m · suc n) (y ⌣S x)))
-- --              ∙ cong (subst S₊ (+-comm (suc m) (suc n)))
-- --                 (cong (-S^ (suc n · suc m))
-- --                     (λ i → -S^ (·-comm (suc m) (suc n) i) (y ⌣S x))
-- --                   ∙ -S^² (suc n · suc m) (y ⌣S x) ))
-- --             ∙ subst⁻Subst S₊ (+-comm (suc m) (suc n)) (y ⌣S x) ))
-- --       ∙ sym (cong (subst S₊ (sym (+-comm (suc m) (suc n)))
-- --                  ∘ -S^ (suc n · suc m))
-- --          (⌣S-comm x y))) x y

-- -- sphereFun↑-⌣' : {n m : ℕ} (N : ℕ → ℕ → ℕ)
-- --   → (N-comm : (n m : ℕ) → N n m ≡ N m n)
-- --   → (f : (n m : ℕ) → S₊ n → S₊ m → S₊ (N n m)) (x : _) (y : _)
-- --   →  sphereFun↑ {n = (suc n)} {m = suc (suc m)}
-- --        (λ x y → sphereFun↑  (λ y x → f (suc m) (suc n) y x) y x) x y
-- --      ≡ {!!}
-- -- sphereFun↑-⌣' = {!gr-comm-lem!}

-- -- JoinS→ : {n m : ℕ} → join (S₊ n) (S₊ m) → S₊ (suc (n + m))
-- -- JoinS→ {n = n} {m = m} (inl x) = ptSn (suc (n + m))
-- -- JoinS→ {n = n} {m = m} (inr x) = ptSn (suc (n + m))
-- -- JoinS→ {n = zero} {m = zero} (push false false i) = loop i
-- -- JoinS→ {n = zero} {m = zero} (push false true i) = base
-- -- JoinS→ {n = zero} {m = zero} (push true b i) = base
-- -- JoinS→ {n = zero} {m = suc m} (push a b i) = toSusp (S₊∙ (suc m)) (a ⌣S b) i
-- -- JoinS→ {n = suc n} {m = m} (push a b i) = toSusp (S₊∙ (suc n + m)) (a ⌣S b) i

-- -- Join↑ : (n m : ℕ) → join (S₊ n) (S₊ m)
-- --   → Path (join (S₊ (suc n)) (S₊ m)) (inl (ptSn (suc n))) (inr (ptSn m))
-- -- Join↑ n m (inl x) = {!!}
-- -- Join↑ n m (inr x) = {!!}
-- -- Join↑ n m (push a b i) = {!!}

-- -- JoinIso : {n m : ℕ} → S₊ (suc (n + m)) → join (S₊ n) (S₊ m)
-- -- JoinIso {n = zero} {m = m} x = {!!}
-- -- JoinIso {n = suc n} {m = zero} x = {!!}
-- -- JoinIso {n = suc zero} {m = suc zero} x = {!!}
-- -- JoinIso {n = suc zero} {m = suc (suc m)} x = {!!}
-- -- JoinIso {n = suc (suc n)} {m = suc m} north = inl north
-- -- JoinIso {n = suc (suc n)} {m = suc m} south = inr (ptSn (suc m))
-- -- JoinIso {n = suc (suc n)} {m = suc m} (merid a i) = {!!}


-- -- asd = joinSusp→suspJoin


-- -- module _ {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} where

-- --   Susp→Join : Susp (typ A) → typ B → join (typ A) (typ B)
-- --   Susp→Join north b = inr (pt B)
-- --   Susp→Join south b = inl (pt A)
-- --   Susp→Join (merid a i) b =
-- --     (sym (push a (pt B)) ∙∙ push a b ∙∙ sym (push (pt A) b)) i

-- --   Susp→Join' : typ A → Susp (typ B) → join (typ A) (typ B)
-- --   Susp→Join' a north = inr (pt B)
-- --   Susp→Join' a south = inl (pt A)
-- --   Susp→Join' a (merid b i) =
-- --     (sym (push a (pt B)) ∙∙ push a b ∙∙ sym (push (pt A) b)) i


-- --   joinSusp→suspJoin' : join (Susp (typ A)) (typ B) → Susp (join (typ A) (typ B))
-- --   joinSusp→suspJoin' (inl x) = north
-- --   joinSusp→suspJoin' (inr x) = south
-- --   joinSusp→suspJoin' (push a b i) = merid (Susp→Join a b) i

-- --   joinSusp→suspJoin'' : join (typ A) (Susp (typ B))
-- --     → Susp (join (typ A) (typ B))
-- --   joinSusp→suspJoin'' (inl x) = north
-- --   joinSusp→suspJoin'' (inr x) = south
-- --   joinSusp→suspJoin'' (push a b i) = merid (Susp→Join' a b) i

-- -- joinSuspFiller* : {ℓ : Level} {A : Type ℓ}
-- --   (inl* a b : A) (p : inl* ≡ b) (z : a ≡ b)
-- --     → I → I → I → Susp A
-- -- joinSuspFiller* inl* a b q z i j k =
-- --   hfill (λ k → λ {(i = i0) → merid (z (~ k)) j
-- --                    ; (i = i1) → north
-- --                    ; (j = i0) → north
-- --                    ; (j = i1) → merid (q (~ k)) (~ i)})
-- --           (inS (merid b (~ i ∧ j)))
-- --           k
-- -- module _ {ℓ : Level} {A : Type ℓ} (inl* : A) where
-- --   pl : (inr* : A) (push* : inl* ≡ inr*) (a : A) (p : inr* ≡ a)
-- --     → Square {A = Susp A} (merid inr*) (λ _ → south) (merid a) refl
-- --   pl inr* push* = J> λ i j → merid inr* (i ∨ j)

-- --   main : (inr* : A) (push* : inl* ≡ inr*) (a : A) (p : inr* ≡ a) (b : A) (q : inl* ≡ b) (z : a ≡ b)
-- --     → Cube (pl inr* push* a p) (λ _ _ → north)
-- --             ((λ j k → merid inr* (~ j ∧ k))) -- 
-- --             (λ j k → merid inl* (~ j))
-- --             ((λ i k → joinSuspFiller* inl* a b q z i k i1))
-- --             λ i j → merid ((p ∙∙ z ∙∙ sym q) j) (~ i)
-- --   main = J> (J> (J> λ z →
-- --       transport (λ m
-- --       → Cube (pl inl* refl inl* refl) (λ _ _ → north)
-- --             ((λ j k → merid inl* (~ j ∧ k))) -- 
-- --             (λ j k → merid inl* (~ j))
-- --             ((λ i k → joinSuspFiller* inl* inl* inl* refl z i k i1))
-- --             λ i j → merid (rUnit z m j) (~ i))
-- --        (transportRefl {A = Square _ _ _ _} (λ i j → merid inl* (i ∨ j))
-- --        ◁ help _ (merid inl*) (cong merid z))))
-- --     where
-- --     the-f : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) (q : p ≡ p)
-- --           → I → I → I → A
-- --     the-f {x = x} y p q i j k =
-- --       hfill (λ k → λ {(i = i0) → q (~ k) j
-- --                    ; (i = i1) → x
-- --                    ; (j = i0) → x
-- --                    ; (j = i1) → p (~ i)})
-- --                 (inS (p (~ i ∧ j))) k

-- --     help : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) (q : p ≡ p)
-- --       → Cube (λ j k → p (j ∨ k)) (λ _ _ → x)
-- --               (λ j k → p (~ j ∧ k)) (λ j k → p (~ j))
-- --               (λ i j → the-f y p q i j i1)
-- --               λ i j →  q j (~ i)
-- --     help {x = x} =
-- --       J> λ q i j k → 
-- --         hcomp (λ r → λ {(i = i0) → q (~ r ∧ ~ k) j -- q (~ r ∨ k) j
-- --                       ; (i = i1) → x
-- --                       ; (j = i0) → x
-- --                       ; (j = i1) → x
-- --                       ; (k = i0) → the-f x refl q i j r
-- --                       ; (k = i1) → sym≡flipSquare q r (~ i) j})
-- --               (q (i ∨ ~ k) j)

-- -- module _ {ℓ : Level} (A B : Pointed ℓ) where
-- --   joinSusp→suspJoin'≡ : (x : _)
-- --     → joinSusp→suspJoin {A = A} {B = B} x
-- --     ≡ invSusp (joinSusp→suspJoin' {A = A} {B = B} x)
-- --   joinSusp→suspJoin'≡ (inl north) = merid (inr (pt B))
-- --   joinSusp→suspJoin'≡ (inl south) = refl
-- --   joinSusp→suspJoin'≡ (inl (merid a i)) j =
-- --     pl (inl (pt A)) (inr (pt B)) (push (pt A) (pt B))
-- --        (inl a) (sym (push a (pt B))) i j 
-- --   joinSusp→suspJoin'≡ (inr x) = refl
-- --   joinSusp→suspJoin'≡ (push north b i) j = merid (inr (pt B)) (j ∧ ~ i)
-- --   joinSusp→suspJoin'≡ (push south b i) j = merid (inl (pt A)) (~ i)
-- --   joinSusp→suspJoin'≡ (push (merid a j) b i) k =
-- --     main (inl (pt A)) (inr (pt B)) (push (pt A) (pt B))
-- --          (inl a) (sym (push a (pt B))) (inr b) (push (pt A) b) (push a b) i j k

-- --   joinSusp→suspJoin'≡* : {!join (Susp (typ A)) (typ B))!}
-- --   joinSusp→suspJoin'≡* = {!!}


-- --   JoinSusp-SuspJoin :
-- --     Iso (join (Susp (typ A)) (typ B))
-- --         (Susp (join (typ A) (typ B)))
-- --   fun JoinSusp-SuspJoin = joinSusp→suspJoin' {A = A} {B = B}
-- --   inv JoinSusp-SuspJoin = suspJoin→joinSusp {A = A} {B = B} ∘ invSusp
-- --   rightInv JoinSusp-SuspJoin x =
-- --        sym (Iso.rightInv invSuspIso _)
-- --     ∙∙ cong invSusp (sym (joinSusp→suspJoin'≡
-- --         (suspJoin→joinSusp (invSusp x)))
-- --      ∙ Iso.rightInv Iso-joinSusp-suspJoin (invSusp x))
-- --     ∙∙ Iso.rightInv invSuspIso x
-- --   leftInv JoinSusp-SuspJoin x =
-- --        cong suspJoin→joinSusp
-- --          (sym (joinSusp→suspJoin'≡ x))
-- --      ∙ Iso.leftInv Iso-joinSusp-suspJoin x
-- -- {-
-- -- isEq** : (n m : ℕ) (x : join (S₊ (suc ) (S₊ m))
-- --   → JoinS→ x
-- --    ≡ suspFun JoinS→
-- --        (joinSusp→suspJoin''
-- --       {A = S₊∙ n} {B = S₊∙ m} x)
-- -- isEq** = ?
-- -- -}

-- -- isEq* : (m : ℕ) (x : join (S₊ (suc zero)) (S₊ (suc (suc m))))
-- --   → JoinS→ x
-- --   ≡ invSusp (suspFun JoinS→
-- --        (joinSusp→suspJoin''
-- --       {A = S₊∙ (suc zero)} {B = S₊∙ (suc m)} x))
-- -- isEq* m (inl x) = merid north
-- -- isEq* m (inr x) = refl
-- -- isEq* m (push a b i) = {!!}
-- --   where
-- --   bs : (a : S¹) → (a ⌣S south) ≡ north
-- --   bs a = {!!}

-- --   lem : (a : S¹) (b : S₊ (suc (suc m)))
-- --     → (a ⌣S b)
-- --      ≡ invSphere' (JoinS→ (Susp→Join' {A = S₊∙ _} {B = S₊∙ _} a b))
-- --   lem a north = ⌣S-lid a
-- --   lem a south = bs a
-- --   lem a (merid b i) = {!!}

-- --   m* : σ (S₊∙ (suc (suc (suc m)))) (a ⌣S b)
-- --      ≡ sym (σ (S₊∙ (suc (suc (suc m)))) (JoinS→ (Susp→Join' a b)))
-- --   m* = (cong (σ (Susp∙ (typ (S₊∙ (suc (suc m))))))
-- --         (lem a b
-- --       ∙ invSphere'≡ (JoinS→ (Susp→Join' a b))))
-- --     ∙ toSusp-invSusp (S₊∙ (suc (suc m))) (JoinS→ (Susp→Join' a b))

-- -- isEq' : (m : ℕ) (x : join (S₊ (suc zero)) (S₊ (suc (suc m))))
-- --   → JoinS→ x
-- --    ≡ suspFun JoinS→
-- --        (joinSusp→suspJoin''
-- --       {A = S₊∙ (suc zero)} {B = S₊∙ (suc m)} x)
-- -- isEq' m (inl x) = refl
-- -- isEq' m (inr x) = merid (ptSn _)
-- -- isEq' m (push a b i) j = {!JoinS→ (Susp→Join' a b)!}
-- --   where
-- --   p-const : (a : S¹) (b : S₊ (suc m)) → north ≡ north
-- --   p-const a b = cong JoinS→ (sym (push a (ptSn (suc m)))
-- --                  ∙∙ push a b
-- --                  ∙∙ sym (push base b))

-- --   ll : (a : S¹) (b : S₊ (suc m))
-- --     → p-const a b ≡ σ (S₊∙ _) (a ⌣S b)
-- --   ll a b =
-- --     cong-∙∙ JoinS→ (sym (push a (ptSn (suc m))))
-- --                  (push a b)
-- --                  (sym (push base b))
-- --     ∙ (λ i → sym ((cong (σ (S₊∙ _)) (⌣S-lid a)
-- --             ∙ rCancel (merid north)) i)
-- --            ∙∙ σ (S₊∙ (suc (suc m))) (a ⌣S b)
-- --            ∙∙ sym (rCancel (merid north) i))
-- --     ∙ sym (rUnit _)

-- --   ⌣S-lid' : (a : S¹) → (a ⌣S south) ≡ north
-- --   ⌣S-lid' base = refl
-- --   ⌣S-lid' (loop i) j =
-- --       (cong (σ (S₊∙ (suc (suc m)))) (sym (merid (ptSn (suc m))))
-- --     ∙ rCancel (merid north)) j i

-- --   pa : (a : S¹) (b : S₊ (2 + m))
-- --     → (a ⌣S b)
-- --     ≡ JoinS→ (Susp→Join' {A = S₊∙ (suc zero)} {B = S₊∙ (suc m)} a b)
-- --   pa a north = ⌣S-lid a
-- --   pa a south = ⌣S-lid' a
-- --   pa a (merid b i) j = (main-l a ▷ (sym (ll a b))) j i
-- --     where
-- --     main-l : (a : S¹)
-- --       → PathP (λ i → ⌣S-lid a i ≡ ⌣S-lid' a i)
-- --                (λ i → a ⌣S merid b i) (σ (S₊∙ _) (a ⌣S b))
-- --     main-l base = sym (rCancel (merid north))
-- --     main-l (loop i) j k = {!!}
-- -- JoinS→-lem : (n m : ℕ) (x : join (S₊ (suc (suc n))) (S₊ m))
-- --   → JoinS→ x
-- --    ≡ suspFun JoinS→
-- --      (joinSusp→suspJoin'
-- --       {A = S₊∙ (suc n)} {B = S₊∙ m} x)
-- -- JoinS→-lem n m (inl x) = refl
-- -- JoinS→-lem n m (inr x) = merid (ptSn _)
-- -- JoinS→-lem n m (push x b i) j = σ↑ j i
-- --   where
-- --   help : (n m : ℕ) (x : S₊ (suc (suc n))) (y : S₊ m)
-- --     → x ⌣S y ≡ JoinS→ (Susp→Join {A = S₊∙ (suc n)} {B = S₊∙ m} x y)
-- --   help n m north y = refl
-- --   help n m south y = refl
-- --   help n m (merid a i) y j = help' j i
-- --     where
-- --     help' : cong (_⌣S y) (merid a)
-- --           ≡ cong JoinS→
-- --               (cong (λ x → Susp→Join
-- --                 {A = S₊∙ (suc n)} {B = S₊∙ m} x y) (merid a))
-- --     help' = rUnit _
-- --         ∙∙ (λ i → sym ((cong (toSusp (S₊∙ (suc n + m))) (⌣S-rid a)
-- --                             ∙ rCancel _) (~ i))
-- --                 ∙∙ toSusp (S₊∙ (suc n + m)) (a ⌣S y)
-- --                 ∙∙ sym ((cong (toSusp (S₊∙ (suc n + m))) (⌣S-rid {n = suc n} y)
-- --                             ∙ rCancel _) (~ i)))
-- --         ∙∙ sym (cong-∙∙ JoinS→ (sym (push a (ptSn m))) (push a y)
-- --                (sym (push (ptSn (suc n)) y)))

-- --   σ↑ : Square (σ (S₊∙ (suc (suc (n + m)))) (x ⌣S b))
-- --               (merid (JoinS→ (Susp→Join
-- --                 {A = S₊∙ (suc n)} {B = S₊∙ m} x b)))
-- --               refl
-- --               (merid north)
-- --   σ↑ = (symP (compPath-filler (merid (x ⌣S b))
-- --                (sym (merid north))))
-- --      ▷ cong merid (help n m x b)

-- -- -- JoinS→-lem n zero x = {!!}
-- -- -- JoinS→-lem n (suc m) (inl north) = refl
-- -- -- JoinS→-lem n (suc m) (inl south) = merid north
-- -- -- JoinS→-lem n (suc m) (inl (merid a i)) j = merid north (i ∧ j)
-- -- -- JoinS→-lem n (suc m) (inr x) = refl
-- -- -- JoinS→-lem n (suc m) (push a b i) j = {!joinSusp→suspJoin (push a b i)!}

-- -- -- Join→≡ : {n m : ℕ} (x : join (S₊ n) (S₊ m)) → Iso.fun (IsoSphereJoin n m) x ≡ JoinS→ x
-- -- -- Join→≡ {n = zero} {m = zero} (inl x) = refl
-- -- -- Join→≡ {n = zero} {m = zero} (inr false) = refl
-- -- -- Join→≡ {n = zero} {m = zero} (inr true) = refl
-- -- -- Join→≡ {n = zero} {m = zero} (push false false i) = refl
-- -- -- Join→≡ {n = zero} {m = zero} (push false true i) = refl
-- -- -- Join→≡ {n = zero} {m = zero} (push true false i) = refl
-- -- -- Join→≡ {n = zero} {m = zero} (push true true i) = refl
-- -- -- Join→≡ {n = zero} {m = suc zero} (inl false) = sym (merid base) 
-- -- -- Join→≡ {n = zero} {m = suc zero} (inl true) = refl
-- -- -- Join→≡ {n = zero} {m = suc zero} (inr x) = refl
-- -- -- Join→≡ {n = zero} {m = suc zero} (push false b i) j = {!compPath-filler (merid b) (sym (merid base)) (~ j)!}
-- -- -- Join→≡ {n = zero} {m = suc zero} (push true b i) j = rCancel (merid base) (~ j) i
-- -- -- Join→≡ {n = zero} {m = suc (suc m)} x = {!!}
-- -- -- Join→≡ {n = suc n} {m = zero} x = {!!}
-- -- -- Join→≡ {n = suc zero} {m = suc zero} (inl x) = refl
-- -- -- Join→≡ {n = suc zero} {m = suc zero} (inr x) = {!!}
-- -- -- Join→≡ {n = suc zero} {m = suc zero} (push a b i) = {!!}
-- -- -- Join→≡ {n = suc zero} {m = suc (suc m)} x = {!!}
-- -- -- Join→≡ {n = suc (suc n)} {m = suc m} (inl x) = {!joinSusp→suspJoin (inl x)!}
-- -- -- Join→≡ {n = suc (suc n)} {m = suc m} (inr x) = refl
-- -- -- Join→≡ {n = suc (suc n)} {m = suc m} (push a b i) = {!!}
-- -- -- -- IsoSphereJoin
