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
open import Cubical.HITs.S1
open import Cubical.Data.Nat hiding (elim ; _·_)
open import Cubical.Data.Sigma
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level

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


rot-comm : (a b : S¹) → a · b ≡ b · a
rot-comm =
  wedgeconFun 0 0
    (λ _ _ → isGroupoidS¹ _ _)
    (λ { base → refl ; (loop i) → refl})
    (λ { base → refl ; (loop i) → refl})
    refl

rot-assoc : (a b c : S¹) → a · (b · c) ≡ (a · b) · c
rot-assoc =
  wedgeconFun 0 0 (λ _ _ → isSetΠ (λ _ → isGroupoidS¹ _ _))
    (λ _ _ → refl)
    (wedgeconFun 0 0
      (λ _ _ → isGroupoidS¹ _ _)
      (λ _ → refl)
      (λ x → sym (rot-comm (x · base) base))
      refl)
    refl

rot-rUnit : (x : S¹) → x · base ≡ x
rot-rUnit x = rot-comm x base

rot-rCancel : (x : S¹) → x · rot⁻ x ≡ base
rot-rCancel base = refl
rot-rCancel (loop i) j = help j i
  where
  help : cong₂ _·_ loop (sym loop) ≡ refl
  help = cong₂Funct _·_ loop (sym loop)
       ∙∙ (λ i → cong (λ x → rot-rUnit x i) loop ∙ sym loop)
       ∙∙ rCancel loop

rot-lCancel : (x : S¹) → rot⁻ x · x ≡ base
rot-lCancel base = refl
rot-lCancel (loop i) = rot-rCancel (loop (~ i))

rotIso : (a : S¹) → Iso S¹ S¹
Iso.fun (rotIso a) = a ·_
Iso.inv (rotIso a) b = rot⁻ a · b
Iso.rightInv (rotIso a) b = rot-assoc a (rot⁻ a) b ∙ cong (_· b) (rot-rCancel a)
Iso.leftInv (rotIso a) b = rot-assoc (rot⁻ a) a b ∙ cong (_· b) (rot-lCancel a)

rot⁻≡sym : (p : ΩS¹) → cong rot⁻ p ≡ sym p
rot⁻≡sym p = rotToSym base p
  where
  rot-ext : (x : S¹) → (p : base ≡ x) → x ≡ base
  rot-ext base p = (cong rot⁻ p)
  rot-ext (loop i) p = help i p
    where
    help : PathP (λ i → base ≡ loop i → loop i ≡ base)
                 (λ p → (cong rot⁻ p))
                 (λ p → (cong rot⁻ p))
    help =
      toPathP (funExt (λ p → (λ i → transport (λ j → loop j ≡ base)
                      ((cong rot⁻ (transp (λ j → base ≡ loop (~ j ∧ ~ i)) i
                        (compPath-filler p (sym loop) i)))))
        ∙∙ cong (transport (λ j → loop j ≡ base))
                  (cong-∙ rot⁻ p (sym loop)
                ∙ comm-ΩS¹ (cong rot⁻ p) loop)
        ∙∙ (λ i → transp (λ j → loop (i ∨ j) ≡ base) i
                   ((λ j → loop (i ∨ j)) ∙ cong rot⁻ p))
         ∙ sym (lUnit (cong rot⁻ p))))

  rotToSym : (x : S¹) (p : base ≡ x) → rot-ext x p ≡ sym p
  rotToSym x = J (λ x p → rot-ext x p ≡ sym p) refl

isEquiv-rot : (a : S¹) → isEquiv (a ·_)
isEquiv-rot a = isoToIsEquiv (rotIso a)
