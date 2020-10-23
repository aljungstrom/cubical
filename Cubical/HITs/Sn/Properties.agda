{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Sn.Properties where

open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Bool
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
open import Cubical.HITs.S1
open import Cubical.HITs.S3
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp
open import Cubical.Data.Unit
open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation.Properties
open import Cubical.HITs.Pushout
open import Cubical.HITs.SmashProduct
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected

open Iso

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

sphereElim : ∀ {ℓ} (n : ℕ) {A : (S₊ (suc n)) → Type ℓ} → ((x : S₊ (suc n)) → isOfHLevel (suc n) (A x))
          → A (ptSn (suc n))
          → (x : S₊ (suc n)) → A x
sphereElim zero hlev pt = toPropElim hlev pt
sphereElim (suc n) hlev pt north = pt
sphereElim (suc n) {A = A} hlev pt south = subst A (merid (ptSn (suc n))) pt
sphereElim (suc n) {A = A} hlev pt (merid a i) = helper i
  where
  helper : PathP (λ i → A (merid a i)) pt (subst A (merid (ptSn (suc n))) pt)
  helper = sphereElim n {A = λ a → PathP (λ i → A (merid a i)) pt (subst A (merid (ptSn (suc n))) pt)}
                        (λ a → isOfHLevelPathP' (suc n) (hlev south) _ _)
                        (λ i → transp (λ j → A (merid (ptSn (suc n)) (i ∧ j))) (~ i) pt)
                        a

sphereElim2 : ∀ {ℓ} (n : ℕ) {A : (S₊ (suc n)) → (S₊ (suc n)) → Type ℓ} → ((x y : S₊ (suc n)) → isOfHLevel (suc n) (A x y))
          → A (ptSn (suc n)) (ptSn (suc n))
          → (x y : S₊ (suc n)) → A x y
sphereElim2 n hlev pt = sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → hlev _ _)
                         (sphereElim n (hlev _ ) pt)

private
  compPath-lem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y) → PathP (λ i → (p ∙ sym q) i ≡ y) p q
  compPath-lem {y = y} p q i j =
    hcomp (λ k → λ { (i = i0) → p j
                    ; (i = i1) → q (~ k ∨ j)
                    ; (j = i1) → y})
          (p (j ∨ i))

-- Direct proof of of the "Wedge Connectivity Lemma" for spheres
-- (See Cubical.Homotopy.WedgeConnectivity or chapter 8.6 in the HoTT book
-- Note that the left homotopy (λ x → F base x ≡ f x) holds definitionally
wedgeConSn : ∀ {ℓ} (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
          → ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y))
          → (f : (x : _) → A (ptSn (suc n)) x)
          → (g : (x : _) → A x (ptSn (suc m)))
          → (g (ptSn (suc n)) ≡ f (ptSn (suc m)))
          → Σ[ F ∈ ((x : S₊ (suc n)) (y : S₊ (suc m)) → A x y) ]
              ((x : S₊ (suc m)) → F (ptSn (suc n)) x ≡ f x) × ((x : S₊ (suc n)) → F x (ptSn (suc m)) ≡ g x)
wedgeConSn zero zero {A = A} hlev f g hom = F , (λ _ → refl) , right
  where
  helper : SquareP (λ i j → A (loop i) (loop j)) (cong f loop) (cong f loop)
                        (λ i → hcomp (λ k → λ { (i = i0) → hom k
                                                ; (i = i1) → hom k})
                                      (g (loop i)))
                         λ i → hcomp (λ k → λ { (i = i0) → hom k
                                                ; (i = i1) → hom k})
                                       (g (loop i))
  helper = transport (sym (PathP≡Path _ _ _))
                     (isOfHLevelPathP' 1 (hlev base base) _ _ _ _)

  F : (x y : S¹) → A x y
  F base y = f y
  F (loop i) base = hcomp (λ k → λ { (i = i0) → hom k
                                    ; (i = i1) → hom k})
                          (g (loop i))
  F (loop i) (loop j) = helper i j

  right : (x : S¹) → F x base ≡ g x
  right base = sym hom
  right (loop i) j = hcomp (λ k → λ {(i = i0) → hom (~ j ∧ k)
                                    ; (i = i1) → hom (~ j ∧ k)
                                    ; (j = i1) → g (loop i)})
                           (g (loop i))
wedgeConSn zero (suc m) {A = A} hlev f g hom = F , left , (λ _ → refl)
  where
  helper2 : (x : S₊ (suc m)) → transport (λ i₁ → A base (merid x i₁)) (g base) ≡ f south
  helper2 x = cong (transport (λ i₁ → A base (merid x i₁))) hom
              ∙ (λ i → transp (λ j → A base (merid x (i ∨ j))) i (f (merid x i)))

  merid-a : (x : S₊ (suc m)) → PathP (λ i₁ → A base (merid x i₁)) (g base)
                                        (transport (λ i₁ → A base (merid (ptSn (suc m)) i₁)) (g base))
  merid-a x i = hcomp (λ k → λ { (i = i0) → g base
                                ; (i = i1) → (helper2 x ∙ sym (helper2 (ptSn (suc m)))) k})
                      (transp (λ i₁ → A base (merid x (i₁ ∧ i))) (~ i) (g base))

  merid-aId : merid-a (ptSn (suc m)) ≡ λ i → transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g base)
  merid-aId =
        (λ j i → hcomp (λ k → λ {(i = i0) → g base
                                ; (i = i1) → rCancel (helper2 (ptSn (suc m))) j k})
                       (transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g base)))
      ∙ λ j i → hfill (λ k → λ { (i = i0) → g base
                                 ; (i = i1) → transport (λ i₁ → A base (merid (ptSn (suc m)) i₁)) (g base)})
                       (inS (transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g base))) (~ j)

  theHelper : Σ[ F ∈ ((x : _) (a : _) → PathP (λ i → A x (merid a i)) (g x) (subst (λ y → A x y) (merid (ptSn (suc m))) (g x))) ] _
  theHelper = wedgeConSn zero m {A = λ x a → PathP (λ i → A x (merid a i)) (g x) (subst (λ y → A x y) (merid (ptSn (suc m))) (g x))}
                                (λ _ _ → isOfHLevelPathP' (2 + m) (hlev _ _) _ _)
                                merid-a
                                (λ a i → transp (λ i₁ → A a (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g a))
                                (sym merid-aId)

  F : (x : S¹) (y : Susp (S₊ (suc m))) → A x y
  left : (x : Susp (S₊ (suc m))) → F base x ≡ f x
  F x north = g x
  F x south = subst (λ y → A x y) (merid (ptSn (suc m))) (g x)
  F x (merid a i) = theHelper .fst x a i
  left north = hom
  left south = cong (subst (A base) (merid (ptSn (suc m)))) hom
             ∙ λ i → transp (λ j → A base (merid (ptSn (suc m)) (i ∨ j))) i (f (merid (ptSn (suc m)) i))
  left (merid a i) j =
    hcomp (λ k → λ { (i = i0) → hom j
                    ; (i = i1) → helper2 (ptSn (suc m)) j
                    ; (j = i0) → theHelper .snd .fst a (~ k) i
                    ; (j = i1) → f (merid a i)})
          (hcomp (λ k →  λ { (i = i0) → hom j
                            ; (i = i1) → compPath-lem (helper2 a) (helper2 (ptSn (suc m))) k j
                            ; (j = i1) → f (merid a i)})
                 (hcomp (λ k → λ { (i = i0) → hom j
                                  ; (j = i0) → transp (λ i₂ → A base (merid a (i₂ ∧ i))) (~ i) (g base)
                                  ; (j = i1) → transp (λ j → A base (merid a (i ∧ (j ∨ k)))) (k ∨ ~ i) (f (merid a (i ∧ k)))})
                        (transp (λ i₂ → A base (merid a (i₂ ∧ i))) (~ i) (hom j))))


wedgeConSn (suc n) m {A = A} hlev f g hom = F , ((λ _ → refl) , right)
  where
  helper2 : (x : S₊ (suc n)) → transport (λ i₁ → A (merid x i₁) (ptSn (suc m))) (f (ptSn (suc m))) ≡ g south
  helper2 x = cong (transport (λ i₁ → A (merid x i₁) (ptSn (suc m)))) (sym hom)
            ∙ (λ i → transp (λ j → A (merid x (i ∨ j)) (ptSn (suc m))) i (g (merid x i)))

  merid-a : (x : S₊ (suc n)) → PathP (λ i₁ → A (merid x i₁) (ptSn (suc m))) (f (ptSn (suc m)))
                                      (transport (λ i₁ → A (merid (ptSn (suc n)) i₁) (ptSn (suc m))) (f (ptSn (suc m))))
  merid-a x i = hcomp (λ k → λ { (i = i0) → f (ptSn (suc m))
                                ; (i = i1) → (helper2 x ∙ sym (helper2 (ptSn (suc n)))) k})
                      (transp (λ i₁ → A (merid x (i₁ ∧ i)) (ptSn (suc m))) (~ i) (f (ptSn (suc m))))

  merid-aId : merid-a (ptSn (suc n)) ≡ λ i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i) (f (ptSn (suc m)))
  merid-aId =
        (λ j i → hcomp (λ k → λ {(i = i0) → f (ptSn (suc m))
                                ; (i = i1) → rCancel (helper2 (ptSn (suc n))) j k})
                       (transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i) (f (ptSn (suc m)))))
      ∙ λ j i → hfill (λ k → λ { (i = i0) → f (ptSn (suc m))
                                 ; (i = i1) → transport (λ i₁ → A (merid (ptSn (suc n)) i₁) (ptSn (suc m))) (f (ptSn (suc m)))})
                       (inS (transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i) (f (ptSn (suc m))))) (~ j)

  theHelper : Σ[ F ∈ ((a : _) (y : _) → PathP (λ i → A (merid a i) y) (f y) (subst (λ x → A x y) (merid (ptSn (suc n))) (f y))) ] _
  theHelper = wedgeConSn n m {A = λ a y → PathP (λ i → A (merid a i) y) (f y) (subst (λ x → A x y) (merid (ptSn (suc n))) (f y))}
                                (λ _ _ → isOfHLevelPathP' (suc (n + suc m)) (hlev _ _) _ _)
                                (λ a i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) a) (~ i) (f a))
                                merid-a
                                merid-aId

  F : (x : Susp (S₊ (suc n))) (y : S₊ (suc m))  → A x y
  right : (x : Susp (S₊ (suc n))) → F x (ptSn (suc m)) ≡ g x
  F north y = f y
  F south y = subst (λ x → A x y) (merid (ptSn (suc n))) (f y)
  F (merid a i) y = theHelper .fst a y i
  right north = sym hom
  right south = cong (subst (λ x → A x (ptSn (suc m))) (merid (ptSn (suc n)))) (sym hom)
              ∙ λ i → transp (λ j → A (merid (ptSn (suc n)) (i ∨ j)) (ptSn (suc m))) i (g (merid (ptSn (suc n)) i))
  right (merid a i) j =
    hcomp (λ k → λ { (i = i0) → hom (~ j)
                    ; (i = i1) → helper2 (ptSn (suc n)) j
                    ; (j = i0) → theHelper .snd .snd a (~ k) i
                    ; (j = i1) → g (merid a i)})
          (hcomp (λ k →  λ { (i = i0) → hom (~ j)
                            ; (i = i1) → compPath-lem (helper2 a) (helper2 (ptSn (suc n))) k j
                            ; (j = i1) → g (merid a i)})
                 (hcomp (λ k → λ { (i = i0) → hom (~ j)
                                  ; (j = i0) → transp (λ i₂ → A (merid a (i₂ ∧ i)) (ptSn (suc m))) (~ i) (f (ptSn (suc m)))
                                  ; (j = i1) → transp (λ j → A (merid a (i ∧ (j ∨ k))) (ptSn (suc m))) (k ∨ ~ i) (g (merid a (i ∧ k))) })
                        (transp (λ i₂ → A (merid a (i₂ ∧ i)) (ptSn (suc m))) (~ i) (hom (~ j)))))

-- We get ∥ Sⁿ⁺² ∥ₙ₊₂ ≃ ∥ Ω Sⁿ⁺³ ∥ₙ₊₂ from the Freudenthal suspension theorem.
-- Cavallos proof of the Freudenthal suspenion theorem (see Cubical.Homotopy.Freudenthal)
-- can be designed to completely avoid theory about connectedness if one
-- only considers (n+2)-spheres:

module miniFreudenthal (n : HLevel) where
  σ : S₊ (2 + n) → typ (Ω (S₊∙ (3 + n)))
  σ a = merid a ∙ merid north ⁻¹

  S2+n = S₊ (2 + n)
  4n+2 = (2 + n) + (2 + n)

  module WC-S (p : north ≡ north) where
    P : (a b : S₊ (2 + n)) → Type₀
    P a b = σ b ≡ p → hLevelTrunc 4n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p)

    hLevelP : (a b : S₊ (2 + n)) → isOfHLevel 4n+2 (P a b)
    hLevelP _ _ = isOfHLevelΠ 4n+2 λ _ → isOfHLevelTrunc 4n+2

    leftFun : (a : S₊ (2 + n)) → P a north
    leftFun a r = ∣ a , (rCancel' (merid a) ∙ rCancel' (merid north) ⁻¹) ∙ r ∣

    rightFun : (b : S₊ (2 + n)) → P north b
    rightFun b r = ∣ b , r ∣

    funsAgree : leftFun north ≡ rightFun north
    funsAgree =
      funExt λ r →
        cong′ (λ w → ∣ north , w ∣)
          (cong (_∙ r) (rCancel' (rCancel' (merid north)))
           ∙ lUnit r ⁻¹)

    totalFun : (a b : S2+n) → P a b
    totalFun =  wedgeConSn (suc n) (suc n) hLevelP rightFun leftFun funsAgree .fst

    rightId : totalFun north ≡ rightFun
    rightId = refl

    leftId : (λ x → totalFun x north) ≡ leftFun
    leftId x i = wedgeConSn (suc n) (suc n) hLevelP rightFun leftFun funsAgree .snd .snd i x

  fwd : (p : north ≡ north) (a : S2+n)
    → hLevelTrunc 4n+2 (fiber σ p)
    → hLevelTrunc 4n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p)
  fwd p a = rec (isOfHLevelTrunc 4n+2) (uncurry (WC-S.totalFun p a))

  fwdnorth : (p : north ≡ north) → fwd p north ≡ idfun _
  fwdnorth p = funExt (elim (λ _ → isOfHLevelPath 4n+2 (isOfHLevelTrunc 4n+2) _ _)
                      λ p → refl)

  isEquivFwd : (p : north ≡ north) (a : S2+n) → isEquiv (fwd p a)
  isEquivFwd p =
    suspToPropElim (ptSn (suc n))
                   (λ _ → isPropIsEquiv _)
                   helper
    where
    helper : isEquiv (fwd p north)
    helper = subst isEquiv (sym (fwdnorth p)) (idIsEquiv _)

  interpolate : (a : S2+n)
          → PathP (λ i → S2+n → north ≡ merid a i) (λ x → merid x ∙ merid a ⁻¹) merid
  interpolate a i x j = compPath-filler (merid x) (merid a ⁻¹) (~ i) j

  Code : (y : Susp S2+n) → north ≡ y → Type₀
  Code north p = hLevelTrunc 4n+2 (fiber σ p)
  Code south q = hLevelTrunc 4n+2 (fiber merid q)
  Code (merid a i) p =
    Glue
      (hLevelTrunc 4n+2 (fiber (interpolate a i) p))
      (λ
        { (i = i0) → _ , (fwd p a , isEquivFwd p a)
        ; (i = i1) → _ , idEquiv _
        })

  encodeS : (y : S₊ (3 + n)) (p : north ≡ y) → Code y p
  encodeS y = J Code ∣ north , rCancel' (merid north) ∣

  encodeMerid : (a : S2+n) → encodeS south (merid a) ≡ ∣ a , refl ∣
  encodeMerid a =
    cong (transport (λ i → gluePath i))
      (funExt⁻ (funExt⁻ (WC-S.leftId refl) a) _ ∙ λ i → ∣ a , lem (rCancel' (merid a)) (rCancel' (merid north)) i ∣)
    ∙ transport (PathP≡Path gluePath _ _)
      (λ i → ∣ a , (λ j k → rCancel-filler' (merid a) i j k) ∣)
    where
    gluePath : I → Type _
    gluePath i = hLevelTrunc 4n+2 (fiber (interpolate a i) (λ j → merid a (i ∧ j)))

    lem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y) → (p ∙ q ⁻¹) ∙ q ≡ p
    lem p q = assoc p (q ⁻¹) q ⁻¹ ∙ cong (p ∙_) (lCancel q) ∙ rUnit p ⁻¹

  contractCodeSouth : (p : north ≡ south) (c : Code south p) → encodeS south p ≡ c
  contractCodeSouth p =
    elim
      (λ _ → isOfHLevelPath 4n+2 (isOfHLevelTrunc 4n+2) _ _)
      (uncurry λ a →
        J (λ p r → encodeS south p ≡ ∣ a , r ∣) (encodeMerid a))

  contractCodeNorth : (p : north ≡ north) (c : Code north p) → encodeS north p ≡ c
  contractCodeNorth = transport (λ i → (p : north ≡ merid north (~ i)) (c : Code (merid north (~ i)) p) → encodeS (merid north (~ i)) p ≡ c)
                                contractCodeSouth

  isConnectedMerid : isConnectedFun 4n+2 (merid {A = S2+n})
  isConnectedMerid p = encodeS south p , contractCodeSouth p

  isConnectedσ : isConnectedFun 4n+2 σ
  fst (isConnectedσ p) = encodeS north p
  snd (isConnectedσ p) = contractCodeNorth p

isConnectedσ-Sn : (n : ℕ) → isConnectedFun (4 + n) (miniFreudenthal.σ n)
isConnectedσ-Sn n = isConnectedFunSubtr _ n _ (subst (λ x → isConnectedFun x (miniFreudenthal.σ n)) helper (miniFreudenthal.isConnectedσ n))
  where
  helper : 2 + (n + (2 + n)) ≡ n + (4 + n)
  helper = cong suc (sym (+-suc n _)) ∙ sym (+-suc n _)

stabSpheres-n≥2 : (n : ℕ) → Iso (hLevelTrunc (4 + n) (S₊ (2 + n))) (hLevelTrunc (4 + n) (typ (Ω (S₊∙ (3 + n)))))
stabSpheres-n≥2 n = connectedTruncIso (4 + n) (miniFreudenthal.σ n) (isConnectedσ-Sn n)
