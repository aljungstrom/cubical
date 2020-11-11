{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.GroupStructure where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; setTruncIsSet to §)
open import Cubical.Data.Int renaming (_+_ to _ℤ+_)
open import Cubical.Data.Nat hiding (+-comm ; +-assoc)
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3 ; map2 to trMap2)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.Homotopy.Freudenthal
open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.NatMinusOne

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base hiding (map)
open import Cubical.Data.HomotopyGroup

open Iso renaming (inv to inv')

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'
    A' : Pointed ℓ

infixr 34 _+ₖ_
infixr 34 _+ₕ_

-- Addition in the Eilenberg-Maclane spaces is uniquely determined if we require it to have left- and right-unit laws,
-- such that these agree on 0. In particular, any h-structure (see http://ericfinster.github.io/files/emhott.pdf) is unique.
private
  genAddId : (n : ℕ) → (comp1 comp2 : coHomK (suc n) → coHomK (suc n) → coHomK (suc n))
           → (rUnit1 : (x : _) → comp1 x (coHom-pt (suc n)) ≡ x)
           → (lUnit1 : (x : _) → comp1 (coHom-pt (suc n)) x ≡ x)
           → (rUnit2 : (x : _) → comp2 x (coHom-pt (suc n)) ≡ x)
           → (lUnit2 : (x : _) → comp2 (coHom-pt (suc n)) x ≡ x)
           → (unId1 : rUnit1 (coHom-pt (suc n)) ≡ lUnit1 (coHom-pt (suc n)))
           → (unId2 : rUnit2 (coHom-pt (suc n)) ≡ lUnit2 (coHom-pt (suc n)))
           → (x y : _) → comp1 x y ≡ comp2 x y
  genAddId n comp1 comp2 rUnit1 lUnit1 rUnit2 lUnit2 unId1 unId2 =
    elim2 (λ _ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
          (wedgeConSn _ _
          (λ _ _ → help _ _)
          (λ x → lUnit1 ∣ x ∣ ∙ sym (lUnit2 ∣ x ∣))
          (λ x → rUnit1 ∣ x ∣ ∙ sym (rUnit2 ∣ x ∣))
          (cong₂ _∙_ unId1 (cong sym unId2)) .fst)
    where
    help : isOfHLevel (2 + (n + suc n)) (coHomK (suc n))
    help = subst (λ x → isOfHLevel x (coHomK (suc n))) (+-suc n (2 + n) ∙ +-suc (suc n) (suc n))
                 (isOfHLevelPlus n (isOfHLevelTrunc (3 + n)))

private
  wedgeConHLev : (n : ℕ) → isOfHLevel ((2 + n) + (2 + n)) (coHomK (2 + n))
  wedgeConHLev n = subst (λ x → isOfHLevel x (coHomK (2 + n)))
                         (sym (+-suc (2 + n) (suc n) ∙ +-suc (3 + n) n))
                         (isOfHLevelPlus' {n = n} (4 + n) (isOfHLevelTrunc (4 + n)))
  wedgeConHLev' : (n : ℕ) → isOfHLevel ((2 + n) + (2 + n)) (typ (Ω (coHomK-ptd (3 + n))))
  wedgeConHLev' n = subst (λ x → isOfHLevel x (typ (Ω (coHomK-ptd (3 + n)))))
                          (sym (+-suc (2 + n) (suc n) ∙ +-suc (3 + n) n))
                          (isOfHLevelPlus' {n = n} (4 + n) (isOfHLevelTrunc (5 + n) _ _))

  wedgeConHLevPath : (n : ℕ) → (x y : coHomK (suc n)) → isOfHLevel ((suc n) + (suc n)) (x ≡ y)
  wedgeConHLevPath zero x y = isOfHLevelTrunc 3 _ _
  wedgeConHLevPath (suc n) x y = isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev n) _ _

-- addition for n ≥ 2 together with the left- and right-unit laws (modulo truncations)
preAdd : (n : ℕ) → Σ[ f ∈ (S₊ (2 + n) → S₊ (2 + n) → coHomK (2 + n)) ]
                       ((x : S₊ (2 + n)) → f north x ≡ ∣ x ∣)
                     × ((x : S₊ (2 + n)) → f x north ≡ ∣ x ∣)
preAdd n =
  wedgeConSn _ _
             (λ _ _ → wedgeConHLev n)
             ∣_∣
             ∣_∣
             refl

-- addition for n = 1
wedgeMapS¹ : S¹ → S¹ → S¹
wedgeMapS¹ base y = y
wedgeMapS¹ (loop i) base = loop i
wedgeMapS¹ (loop i) (loop j) =
  hcomp (λ k → λ { (i = i0) → loop j
                  ; (i = i1) → loop (j ∧ k)
                  ; (j = i0) → loop i
                  ; (j = i1) → loop (i ∧ k)})
        (loop (i ∨ j))

-----------

Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
Kn→ΩKn+1 n = Iso.fun (Iso-Kn-ΩKn+1 n)

ΩKn+1→Kn : (n : ℕ) → typ (Ω (coHomK-ptd (suc n))) → coHomK n
ΩKn+1→Kn n = Iso.inv (Iso-Kn-ΩKn+1 n)

Kn≃ΩKn+1 : {n : ℕ} → coHomK n ≃ typ (Ω (coHomK-ptd (suc n)))
Kn≃ΩKn+1 {n = n} = isoToEquiv (Iso-Kn-ΩKn+1 n)

---------- Algebra/Group stuff --------

0ₖ : (n : ℕ) → coHomK n
0ₖ = coHom-pt

Kn→ΩKn+10ₖ : (n : ℕ) → Kn→ΩKn+1 n (0ₖ n) ≡ refl
Kn→ΩKn+10ₖ zero = sym (rUnit refl)
Kn→ΩKn+10ₖ (suc zero) i j = ∣ (rCancel (merid base) i j) ∣
Kn→ΩKn+10ₖ (suc (suc n)) i j = ∣ (rCancel (merid north) i j) ∣

ΩKn+1→Kn-refl : (n : ℕ) → ΩKn+1→Kn n refl ≡ 0ₖ n
ΩKn+1→Kn-refl zero = refl
ΩKn+1→Kn-refl (suc zero) = refl
ΩKn+1→Kn-refl (suc (suc zero)) = refl
ΩKn+1→Kn-refl (suc (suc (suc n))) = refl


_+ₖ_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
_+ₖ_ {n = zero} x y = x ℤ+ y
_+ₖ_ {n = suc zero} = trMap2 wedgeMapS¹
_+ₖ_ {n = suc (suc n)} = trRec (isOfHLevelΠ (4 + n) λ _ → isOfHLevelTrunc (4 + n))
                            λ x → trRec (isOfHLevelTrunc (4 + n)) λ y → preAdd n .fst x y

private
  isEquiv+ : (n : ℕ) → (x : coHomK (suc n)) → isEquiv (_+ₖ_ {n = (suc n)} x)
  isEquiv+ zero =
    trElim (λ _ → isProp→isOfHLevelSuc 2 (isPropIsEquiv _))
           (toPropElim (λ _ → isPropIsEquiv _)
                       (subst isEquiv (sym help) (idIsEquiv _)))
    where
    help : _+ₖ_ {n = 1} (coHom-pt 1) ≡ idfun _
    help = funExt (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                  λ _ → refl)
  isEquiv+ (suc n) =
    trElim (λ _ → isProp→isOfHLevelSuc (3 + n) (isPropIsEquiv _))
           (suspToPropElim (ptSn (suc n)) (λ _ → isPropIsEquiv _)
           (subst isEquiv (sym help) (idIsEquiv _)))
    where
    help : _+ₖ_ {n = (2 + n)} (coHom-pt (2 + n)) ≡ idfun _
    help = funExt (trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _) λ _ → refl)


  Kₙ≃Kₙ : (n : ℕ) (x : coHomK (suc n)) → coHomK (suc n) ≃ coHomK (suc n)
  Kₙ≃Kₙ n x = _ , isEquiv+ n x

-ₖ_ : {n : ℕ} →  coHomK n → coHomK n
-ₖ_ {n = zero} x = 0 - x
-ₖ_ {n = suc n} x = invEq (Kₙ≃Kₙ n x) (coHom-pt (suc n))

_-ₖ_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
_-ₖ_ {n = n} x y = _+ₖ_ {n = n} x (-ₖ_ {n = n} y)

+ₖ-syntax : (n : ℕ) → coHomK n → coHomK n → coHomK n
+ₖ-syntax n = _+ₖ_ {n = n}

-ₖ-syntax : (n : ℕ) → coHomK n → coHomK n
-ₖ-syntax n = -ₖ_ {n = n}

-'ₖ-syntax : (n : ℕ) → coHomK n → coHomK n → coHomK n
-'ₖ-syntax n = _-ₖ_ {n = n}

syntax +ₖ-syntax n x y = x +[ n ]ₖ y
syntax -ₖ-syntax n x = -[ n ]ₖ x
syntax -'ₖ-syntax n x y = x -[ n ]ₖ y

------- Groupoid Laws for Kₙ ---------

commₖ : (n : ℕ) → (x y : coHomK n) → x +[ n ]ₖ y ≡ y +[ n ]ₖ x
commₖ zero = +-comm
commₖ (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
        (wedgeConSn _ _
          (λ _ _ → isOfHLevelTrunc 3 _ _)
          (λ {base → refl ; (loop i) → refl})
          (λ {base → refl ; (loop i) → refl})
          refl .fst)
commₖ (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
        (wedgeConSn _ _
                    (λ x y → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev n) _ _)
                    (λ x → preAdd n .snd .fst x ∙ sym (preAdd n .snd .snd x))
                    (λ x → preAdd n .snd .snd x ∙ sym (preAdd n .snd .fst x))
                    refl .fst)

commₖ-base : (n : ℕ) → commₖ n (coHom-pt n) (coHom-pt n) ≡ refl
commₖ-base zero = refl
commₖ-base (suc zero) = refl
commₖ-base (suc (suc n)) = sym (rUnit _)

rCancelₖ : (n : ℕ) → (x : coHomK n) → x -[ n ]ₖ x ≡ coHom-pt n
rCancelₖ zero x = +-comm x (pos 0 - x) ∙ minusPlus x 0
rCancelₖ (suc n) x = retEq (Kₙ≃Kₙ n x) (coHom-pt _)

lCancelₖ : (n : ℕ) → (x : coHomK n) → (-[ n ]ₖ x) +[ n ]ₖ x ≡ coHom-pt n
lCancelₖ zero x = minusPlus x 0
lCancelₖ (suc n) x = commₖ (suc n) _ _ ∙ rCancelₖ (suc n) x

rUnitₖ : (n : ℕ) → (x : coHomK n) → x +[ n ]ₖ coHom-pt n ≡ x
rUnitₖ zero x = refl
rUnitₖ (suc zero) =
  trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
         λ {base → refl
         ; (loop i) → refl}
rUnitₖ (suc (suc n)) =
  trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
          λ x → preAdd n .snd .snd x

lUnitₖ : (n : ℕ) → (x : coHomK n) → coHom-pt n +[ n ]ₖ x ≡ x
lUnitₖ zero x = sym (pos0+ x)
lUnitₖ (suc zero) =
  trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
         λ {base → refl
         ; (loop i) → refl}
lUnitₖ (suc (suc n)) =
  trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
          λ x → refl

assocₖ : (n : ℕ) → (x y z : coHomK n) → x +[ n ]ₖ (y +[ n ]ₖ z) ≡ (x +[ n ]ₖ y) +[ n ]ₖ z
assocₖ zero = +-assoc
assocₖ (suc zero) =
  trElim3 (λ _ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
          λ x → wedgeConSn _ _
                (λ _ _ → isOfHLevelTrunc 3 _ _)
                (λ y i → rUnitₖ 1 ∣ x ∣ (~ i) +ₖ ∣ y ∣)
                (λ z → cong (∣ x ∣ +ₖ_) (rUnitₖ 1 ∣ z ∣) ∙ sym (rUnitₖ 1 (∣ x ∣ +ₖ ∣ z ∣)))
                (helper x) .fst
  where
  helper : (x : S¹) → cong (∣ x ∣ +ₖ_) (rUnitₖ 1 ∣ base ∣) ∙ sym (rUnitₖ 1 (∣ x ∣ +ₖ ∣ base ∣)) ≡ (cong (_+ₖ ∣ base ∣) (sym (rUnitₖ 1 ∣ x ∣)))
  helper = toPropElim (λ _ → isOfHLevelTrunc 3 _ _ _ _)
                      (sym (lUnit refl))
assocₖ (suc (suc n)) =
  trElim3 (λ _ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
          λ x → wedgeConSn _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev n) _ _)
                           (λ z i → preAdd n .snd .snd x (~ i) +ₖ ∣ z ∣)
                           (λ y → cong (∣ x ∣ +ₖ_) (rUnitₖ (2 + n) ∣ y ∣) ∙ sym (rUnitₖ (2 + n) (∣ x ∣ +ₖ ∣ y ∣)))
                           (helper x) .fst
  where
  helper : (x : S₊ (2 + n)) → cong (∣ x ∣ +ₖ_) (rUnitₖ (2 + n) ∣ north ∣) ∙ sym (rUnitₖ (2 + n) (∣ x ∣ +ₖ ∣ north ∣))
                          ≡ cong (_+ₖ ∣ north ∣) (sym (preAdd n .snd .snd x))
  helper = sphereElim (suc n) (λ _ → isOfHLevelTrunc (4 + n) _ _ _ _)
                              (sym (lUnit (sym (rUnitₖ (2 + n) (∣ north ∣ +ₖ ∣ north ∣)))))

lUnitₖ≡rUnitₖ : (n : ℕ) → lUnitₖ n (coHom-pt n) ≡ rUnitₖ n (coHom-pt n)
lUnitₖ≡rUnitₖ zero = isSetInt _ _ _ _
lUnitₖ≡rUnitₖ (suc zero) = refl
lUnitₖ≡rUnitₖ (suc (suc n)) = refl

------ Kn≃ΩKn is a morphism -------

private
  cheating : ∀ {ℓ} {A : Type ℓ} {a : A} (p : a ≡ a) (r : refl ≡ p)
                 → lUnit p ∙ cong (_∙ p) r ≡ rUnit p ∙ cong (p ∙_) r
  cheating p = J (λ p r → lUnit p ∙ cong (_∙ p) r ≡ rUnit p ∙ cong (p ∙_) r) refl

Kn→ΩKn+1-hom : (n : ℕ) (x y : coHomK n) → Kn→ΩKn+1 n (x +[ n ]ₖ y) ≡ Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y
Kn→ΩKn+1-hom zero x y = (λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i) (inS (∣ intLoop (x ℤ+ y) i ∣)) (~ j))
                      ∙∙ (λ j i → ∣ intLoop-hom x y (~ j) i ∣)
                      ∙∙ (congFunct ∣_∣ (intLoop x) (intLoop y)
                        ∙ cong₂ _∙_ (λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i) (inS (∣ intLoop x i ∣)) j)
                                     λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i) (inS (∣ intLoop y i ∣)) j)
Kn→ΩKn+1-hom (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 4 _ _) _ _)
        (wedgeConSn _ _
                    (λ _ _ → isOfHLevelTrunc 4 _ _ _ _ )
                    (λ x → lUnit _ ∙ cong (_∙ Kn→ΩKn+1 1 ∣ x ∣) (sym (Kn→ΩKn+10ₖ 1)))
                    (λ x → cong (Kn→ΩKn+1 1) (rUnitₖ 1 ∣ x ∣) ∙∙ rUnit _ ∙∙ cong (Kn→ΩKn+1 1 ∣ x ∣ ∙_) (sym (Kn→ΩKn+10ₖ 1)))
                    (sym (cheating (Kn→ΩKn+1 1 ∣ base ∣) (sym (Kn→ΩKn+10ₖ 1)))) .fst)
Kn→ΩKn+1-hom (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
        (wedgeConSn _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev' n) _ _)
                        (λ x → lUnit _ ∙ cong (_∙ Kn→ΩKn+1 (suc (suc n)) ∣ x ∣) (sym (Kn→ΩKn+10ₖ (2 + n))))
                        (λ y → cong (Kn→ΩKn+1 (suc (suc n))) (preAdd n .snd .snd y)
                            ∙∙ rUnit _
                            ∙∙ cong (Kn→ΩKn+1 (suc (suc n)) ∣ y ∣ ∙_) (sym (Kn→ΩKn+10ₖ (2 + n))))
                        (sym (cheating (Kn→ΩKn+1 (suc (suc n)) ∣ north ∣) (sym (Kn→ΩKn+10ₖ (2 + n))))) .fst)

ΩKn+1→Kn-hom : (n : ℕ) (x y : typ (Ω (coHomK-ptd (suc n)))) → ΩKn+1→Kn n (x ∙ y) ≡ ΩKn+1→Kn n x +[ n ]ₖ (ΩKn+1→Kn n y)
ΩKn+1→Kn-hom zero x y =
    (λ i → winding (congFunct (trRec isGroupoidS¹ (λ a → a)) x y i))
  ∙ winding-hom (cong (trRec isGroupoidS¹ (λ a → a)) x) (cong (trRec isGroupoidS¹ (λ a → a)) y)
ΩKn+1→Kn-hom (suc n) x y =
  let
  xId = rightInv (Iso-Kn-ΩKn+1 (1 + n)) x
  yId = rightInv (Iso-Kn-ΩKn+1 (1 + n)) y
  in   cong₂ (λ x y → ΩKn+1→Kn (1 + n) (x ∙ y)) (sym xId) (sym yId)
    ∙∙ cong (ΩKn+1→Kn (1 + n)) (sym (Kn→ΩKn+1-hom (suc n) (ΩKn+1→Kn (1 + n) x) (ΩKn+1→Kn (1 + n) y)))
    ∙∙ leftInv (Iso-Kn-ΩKn+1 (1 + n)) (ΩKn+1→Kn (1 + n) x +ₖ ΩKn+1→Kn (1 + n) y)

-- ΩKₙ is commutative w.r.t. path composition
isComm∙ : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
isComm∙ A = (p q : typ (Ω A)) → p ∙ q ≡ q ∙ p

abstract
  isCommA→isCommTrunc : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ A
                      → isOfHLevel (suc n) (typ A)
                      → isComm∙ (∥ typ A ∥ (suc n) , ∣ pt A ∣)
  isCommA→isCommTrunc {A = (A , a)} n comm hlev p q =
      ((λ i j → (Iso.leftInv (truncIdempotentIso (suc n) hlev) ((p ∙ q) j) (~ i)))
   ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (cong (trRec hlev (λ x → x)) (p ∙ q)))
   ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) p q i)))
   ∙ ((λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (comm (cong (trRec hlev (λ x → x)) p) (cong (trRec hlev (λ x → x)) q) i))
   ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) q p (~ i)))
   ∙∙ (λ i j → (Iso.leftInv (truncIdempotentIso (suc n) hlev) ((q ∙ p) j) i)))

  open Iso renaming (inv to inv')
  ptdIso→comm : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} (e : Iso (typ A) B) → isComm∙ A → isComm∙ (B , Iso.fun e (pt A))
  ptdIso→comm {A = (A , a)} {B = B} e comm p q =
         sym (rightInv (congIso e) (p ∙ q))
      ∙∙ (cong (fun (congIso e)) ((invCongFunct e p q)
                              ∙∙ (comm (inv' (congIso e) p) (inv' (congIso e) q))
                              ∙∙ (sym (invCongFunct e q p))))
      ∙∙ rightInv (congIso e) (q ∙ p)


-- We show that p ∙ q ≡ (λ i → (p i) +ₖ (q i)) for any p q : ΩKₙ₊₁. This allows us to prove that p ∙ q ≡ q ∙ p
-- without having to use the equivalence Kₙ ≃ ΩKₙ₊₁

∙≡+₁ : (p q : typ (Ω (coHomK-ptd 1))) → p ∙ q ≡ cong₂ _+ₖ_ p q
∙≡+₁ p q = (λ i → (λ j → rUnitₖ 1 (p j) (~ i)) ∙ λ j → lUnitₖ 1 (q j) (~ i)) ∙  sym (cong₂Funct _+ₖ_ p q)

∙≡+₂ : (n : ℕ) (p q : typ (Ω (coHomK-ptd (suc (suc n))))) → p ∙ q ≡ cong₂ _+ₖ_ p q
∙≡+₂ n p q = (λ i → (λ j → rUnitₖ (2 + n) (p j) (~ i)) ∙ λ j → lUnitₖ (2 + n) (q j) (~ i)) ∙ sym (cong₂Funct _+ₖ_ p q)

cong+ₖ-comm : (n : ℕ) (p q : typ (Ω (coHomK-ptd (suc n)))) → cong₂ _+ₖ_ p q ≡ cong₂ _+ₖ_ q p
cong+ₖ-comm zero p q =
     rUnit (cong₂ _+ₖ_ p q)
  ∙∙ (λ i → (λ j → commₖ 1 ∣ base ∣ ∣ base ∣ (i ∧ j))
     ∙∙ (λ j → commₖ 1 (p j) (q j) i)
     ∙∙ λ j → commₖ 1 ∣ base ∣ ∣ base ∣ (i ∧ ~ j))
  ∙∙ ((λ i → commₖ-base 1 i ∙∙ cong₂ _+ₖ_ q p ∙∙ sym (commₖ-base 1 i))
    ∙ sym (rUnit (cong₂ _+ₖ_ q p)))
cong+ₖ-comm (suc n) p q =
     rUnit (cong₂ _+ₖ_ p q)
  ∙∙ (λ i → (λ j → commₖ (2 + n) ∣ north ∣ ∣ north ∣ (i ∧ j))
     ∙∙ (λ j → commₖ (2 + n) (p j) (q j) i )
     ∙∙ λ j → commₖ (2 + n) ∣ north ∣ ∣ north ∣ (i ∧ ~ j))
  ∙∙ ((λ i → commₖ-base (2 + n) i ∙∙ cong₂ _+ₖ_ q p ∙∙ sym (commₖ-base (2 + n) i))
    ∙ sym (rUnit (cong₂ _+ₖ_ q p)))

isCommΩK : (n : ℕ) → isComm∙ (coHomK-ptd n)
isCommΩK zero p q = isSetInt _ _ (p ∙ q) (q ∙ p)
isCommΩK (suc zero) p q = ∙≡+₁ p q ∙∙ cong+ₖ-comm 0 p q ∙∙ sym (∙≡+₁ q p)
isCommΩK (suc (suc n)) p q = ∙≡+₂ n p q ∙∙ cong+ₖ-comm (suc n) p q ∙∙ sym (∙≡+₂ n q p)

----- some other useful lemmas about algebra in Kₙ

-0ₖ : {n : ℕ} → -[ n ]ₖ (0ₖ n) ≡ (0ₖ n)
-0ₖ {n = zero} = refl
-0ₖ {n = suc zero} = refl
-0ₖ {n = suc (suc n)} = refl

-distrₖ : (n : ℕ) (x y : coHomK n) → -[ n ]ₖ (x +[ n ]ₖ y) ≡ (-[ n ]ₖ x) +[ n ]ₖ (-[ n ]ₖ y)
-distrₖ zero x y = GroupLemmas.invDistr intGroup x y ∙ +-comm (0 - y) (0 - x)
-distrₖ (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
        (wedgeConSn _ _ (λ _ _ → isOfHLevelTrunc 3 _ _)
          (λ x → sym (lUnitₖ 1 (-[ 1 ]ₖ ∣ x ∣)))
          (λ x → cong (λ x → -[ 1 ]ₖ x) (rUnitₖ 1 ∣ x ∣) ∙ sym (rUnitₖ 1 (-[ 1 ]ₖ ∣ x ∣)))
          (sym (rUnit refl)) .fst)
-distrₖ (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
        (wedgeConSn _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev n) _ _)
                        (λ x → sym (lUnitₖ (2 + n) (-[ (2 + n) ]ₖ ∣ x ∣)))
                        (λ x → cong (λ x → -[ (2 + n) ]ₖ x) (rUnitₖ (2 + n) ∣ x ∣ ) ∙ sym (rUnitₖ (2 + n) (-[ (2 + n) ]ₖ ∣ x ∣)))
                        (sym (rUnit refl)) .fst)

-cancelRₖ : (n : ℕ) (x y : coHomK n) → (y +[ n ]ₖ x) -[ n ]ₖ x ≡ y
-cancelRₖ zero x y = sym (+-assoc y x (0 - x))
                  ∙∙ cong (y ℤ+_) (+-comm x (0 - x))
                  ∙∙ cong (y ℤ+_) (minusPlus x (pos 0))
-cancelRₖ (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
        (wedgeConSn _ _ (λ _ _ → wedgeConHLevPath 0 _ _)
                        (λ x → cong (_+ₖ ∣ base ∣) (rUnitₖ 1 ∣ x ∣) ∙ rUnitₖ 1 ∣ x ∣)
                        (λ x → rCancelₖ 1 ∣ x ∣)
                        (transportRefl refl ∙ rUnit refl) .fst)
-cancelRₖ (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
        (wedgeConSn _ _ (λ _ _ → wedgeConHLevPath (suc n) _ _)
                        (λ x → cong (_+ₖ ∣ north ∣) (rUnitₖ (2 + n) ∣ x ∣) ∙ rUnitₖ (2 + n) ∣ x ∣)
                        (λ x → rCancelₖ (2 + n) ∣ x ∣)
                        (transportRefl refl ∙ rUnit refl) .fst)

-cancelLₖ : (n : ℕ) (x y : coHomK n) → (x +[ n ]ₖ y) -[ n ]ₖ x ≡ y
-cancelLₖ n x y = cong (λ z → z -[ n ]ₖ x) (commₖ n x y) ∙ -cancelRₖ n x y

-+cancelₖ : (n : ℕ) (x y : coHomK n) → (x -[ n ]ₖ y) +[ n ]ₖ y ≡ x
-+cancelₖ zero x y = sym (+-assoc x (0 - y) y) ∙ cong (x ℤ+_) (minusPlus y (pos 0))
-+cancelₖ (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
        (wedgeConSn _ _ (λ _ _ → wedgeConHLevPath 0 _ _)
          (λ x → cong (_+ₖ ∣ x ∣) (lUnitₖ 1 (-ₖ ∣ x ∣)) ∙ lCancelₖ 1 ∣ x ∣)
          (λ x → cong (_+ₖ ∣ base ∣) (rUnitₖ 1 ∣ x ∣) ∙ rUnitₖ 1 ∣ x ∣)
          ((λ i → refl ∙ (transportRefl refl (~ i))) ∙ lUnit _) .fst)
-+cancelₖ (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
        (wedgeConSn _ _ (λ _ _ → wedgeConHLevPath (suc n) _ _)
          (λ x → cong (_+ₖ ∣ x ∣) (lUnitₖ (2 + n) (-ₖ ∣ x ∣)) ∙ lCancelₖ (2 + n) ∣ x ∣)
          (λ x → cong (_+ₖ ∣ north ∣) (rUnitₖ (2 + n) ∣ x ∣) ∙ rUnitₖ (2 + n) ∣ x ∣)
          (cong (refl ∙_) (rUnit refl ∙ (λ i → rUnit refl i ∙ transportRefl refl (~ i)))) .fst)

---- Group structure of cohomology groups ---

_+ₕ_ : {n : ℕ} → coHom n A → coHom n A → coHom n A
_+ₕ_ {n = n} = sRec2 § λ a b → ∣ (λ x → a x +[ n ]ₖ b x) ∣₂

-ₕ_  : {n : ℕ} → coHom n A → coHom n A
-ₕ_  {n = n} = sRec § λ a → ∣ (λ x → -[ n ]ₖ a x) ∣₂

_-ₕ_  : {n : ℕ} → coHom n A → coHom n A → coHom n A
_-ₕ_  {n = n} = sRec2 § λ a b → ∣ (λ x → a x -[ n ]ₖ b x) ∣₂

+ₕ-syntax : (n : ℕ) → coHom n A → coHom n A → coHom n A
+ₕ-syntax n = _+ₕ_ {n = n}

-ₕ-syntax : (n : ℕ) → coHom n A → coHom n A
-ₕ-syntax n = -ₕ_ {n = n}

-ₕ'-syntax : (n : ℕ) → coHom n A → coHom n A → coHom n A
-ₕ'-syntax n = _-ₕ_ {n = n}

syntax +ₕ-syntax n x y = x +[ n ]ₕ y
syntax -ₕ-syntax n x = -[ n ]ₕ x
syntax -ₕ'-syntax n x y = x -[ n ]ₕ y

0ₕ : (n : ℕ) → coHom n A
0ₕ n = ∣ (λ _ → (0ₖ n)) ∣₂

rUnitₕ : (n : ℕ) (x : coHom n A) → x +[ n ]ₕ (0ₕ n) ≡ x
rUnitₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                λ a i → ∣ funExt (λ x → rUnitₖ n (a x)) i ∣₂

lUnitₕ : (n : ℕ) (x : coHom n A) → (0ₕ n) +[ n ]ₕ x ≡ x
lUnitₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                  λ a i → ∣ funExt (λ x → lUnitₖ n (a x)) i ∣₂

rCancelₕ : (n : ℕ) (x : coHom n A) → x +[ n ]ₕ (-[ n ]ₕ x) ≡ 0ₕ n
rCancelₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                 λ a i → ∣ funExt (λ x → rCancelₖ n (a x)) i ∣₂

lCancelₕ : (n : ℕ) (x : coHom n A) → (-[ n ]ₕ x) +[ n ]ₕ x  ≡ 0ₕ n
lCancelₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                 λ a i → ∣ funExt (λ x → lCancelₖ n (a x)) i ∣₂

assocₕ : (n : ℕ) (x y z : coHom n A) →  (x +[ n ]ₕ (y +[ n ]ₕ z)) ≡ ((x +[ n ]ₕ y) +[ n ]ₕ z)
assocₕ n = elim3 (λ _ _ _ → isOfHLevelPath 1 (§ _ _))
               λ a b c i → ∣ funExt (λ x → assocₖ n (a x) (b x) (c x)) i ∣₂

commₕ : (n : ℕ) (x y : coHom n A) → (x +[ n ]ₕ y) ≡ (y +[ n ]ₕ x)
commₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ funExt (λ x → commₖ n (a x) (b x)) i ∣₂

-cancelLₕ : (n : ℕ) (x y : coHom n A) → (x +[ n ]ₕ y) -[ n ]ₕ x ≡ y
-cancelLₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                     λ a b i → ∣ (λ x → -cancelLₖ n (a x) (b x) i) ∣₂

-cancelRₕ : (n : ℕ) (x y : coHom n A) → (y +[ n ]ₕ x) -[ n ]ₕ x ≡ y
-cancelRₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                     λ a b i → ∣ (λ x → -cancelRₖ n (a x) (b x) i) ∣₂

-+cancelₕ : (n : ℕ) (x y : coHom n A) → (x -[ n ]ₕ y) +[ n ]ₕ y ≡ x
-+cancelₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                     λ a b i → ∣ (λ x → -+cancelₖ n (a x) (b x) i) ∣₂

-- Group structure of reduced cohomology groups (in progress - might need K to compute properly first) ---

+ₕ∙ : {A : Pointed ℓ} (n : ℕ) → coHomRed n A → coHomRed n A → coHomRed n A
+ₕ∙ zero = sRec2 § λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ zero ]ₖ b x) , (λ i → (pa i +[ zero ]ₖ pb i)) ∣₂ }
+ₕ∙ (suc zero) = sRec2 § λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ 1 ]ₖ b x) , (λ i → pa i +[ 1 ]ₖ pb i) ∙ lUnitₖ 1 (0ₖ 1) ∣₂ }
+ₕ∙ (suc (suc n)) = sRec2 § λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ (2 + n) ]ₖ b x) , (λ i → pa i +[ (2 + n) ]ₖ pb i) ∙ lUnitₖ (2 + n) (0ₖ (2 + n)) ∣₂ }

open IsSemigroup
open IsMonoid
open GroupStr
open GroupHom

coHomGr : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Group {ℓ}
coHomGr n A = coHom n A , coHomGrnA
  where
  coHomGrnA : GroupStr (coHom n A)
  0g coHomGrnA = 0ₕ n
  GroupStr._+_ coHomGrnA = λ x y → x +[ n ]ₕ y
  - coHomGrnA = λ x → -[ n ]ₕ x
  isGroup coHomGrnA = helper
    where
    abstract
      helper : IsGroup (0ₕ n) (λ x y → x +[ n ]ₕ y) (λ x → -[ n ]ₕ x)
      helper = makeIsGroup § (assocₕ n) (rUnitₕ n) (lUnitₕ n) (rCancelₕ n) (lCancelₕ n)

×coHomGr : (n : ℕ) (A : Type ℓ) (B : Type ℓ') → Group
×coHomGr n A B = dirProd (coHomGr n A) (coHomGr n B)

-- Alternative definition of cohomology using ΩKₙ instead. Useful for breaking proofs of group isos
-- up into smaller parts
coHomGrΩ : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Group {ℓ}
coHomGrΩ n A = ∥ (A → typ (Ω (coHomK-ptd (suc n)))) ∥₂ , coHomGrnA
  where
  coHomGrnA : GroupStr ∥ (A → typ (Ω (coHomK-ptd (suc n)))) ∥₂
  0g coHomGrnA = ∣ (λ _ → refl) ∣₂
  GroupStr._+_ coHomGrnA = sRec2 § λ p q → ∣ (λ x → p x ∙ q x) ∣₂
  - coHomGrnA = map λ f x → sym (f x)
  isGroup coHomGrnA = helper
    where
    abstract
      helper : IsGroup (∣ (λ _ → refl) ∣₂) (sRec2 § λ p q → ∣ (λ x → p x ∙ q x) ∣₂) (map λ f x → sym (f x))
      helper = makeIsGroup § (elim3 (λ _ _ _ → isOfHLevelPath 2 § _ _)
                                    (λ p q r → cong ∣_∣₂ (funExt λ x → assoc∙ (p x) (q x) (r x))))
                             (sElim (λ _ → isOfHLevelPath 2 § _ _) λ p → cong ∣_∣₂ (funExt λ x → sym (rUnit (p x))))
                             (sElim (λ _ → isOfHLevelPath 2 § _ _) λ p → cong ∣_∣₂ (funExt λ x → sym (lUnit (p x))))
                             (sElim (λ _ → isOfHLevelPath 2 § _ _) λ p → cong ∣_∣₂ (funExt λ x → rCancel (p x)))
                             (sElim (λ _ → isOfHLevelPath 2 § _ _) λ p → cong ∣_∣₂ (funExt λ x → lCancel (p x)))

coHom≅coHomΩ : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → GroupIso (coHomGr n A) (coHomGrΩ n A)
fun (GroupIso.map (coHom≅coHomΩ n A)) = map λ f a → Kn→ΩKn+1 n (f a)
isHom (GroupIso.map (coHom≅coHomΩ n A)) =
  sElim2 (λ _ _ → isOfHLevelPath 2 § _ _)
         λ f g → cong ∣_∣₂ (funExt λ x → Kn→ΩKn+1-hom n (f x) (g x))
GroupIso.inv (coHom≅coHomΩ n A) = map λ f a → ΩKn+1→Kn n (f a)
GroupIso.rightInv (coHom≅coHomΩ n A) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
        λ f → cong ∣_∣₂ (funExt λ x → rightInv (Iso-Kn-ΩKn+1 n) (f x))
GroupIso.leftInv (coHom≅coHomΩ n A) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
        λ f → cong ∣_∣₂ (funExt λ x → leftInv (Iso-Kn-ΩKn+1 n) (f x))

coHomFun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : ℕ) (f : A → B) → coHom n B → coHom n A
coHomFun n f = sRec § λ β → ∣ β ∘ f ∣₂

-distrLemma : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n m : ℕ) (f : GroupHom (coHomGr n A) (coHomGr m B))
              (x y : coHom n A)
            → fun f (x -[ n ]ₕ y) ≡ fun f x -[ m ]ₕ fun f y
-distrLemma n m f' x y = sym (-cancelRₕ m (f y) (f (x -[ n ]ₕ y)))
                     ∙∙ cong (λ x → x -[ m ]ₕ f y) (sym (isHom f' (x -[ n ]ₕ y) y))
                     ∙∙ cong (λ x → x -[ m ]ₕ f y) ( cong f (-+cancelₕ n _ _))
  where
  f = fun f'

--- the loopspace of Kₙ is commutative regardless of base

addIso : (n : ℕ) (x : coHomK n) → Iso (coHomK n) (coHomK n)
fun (addIso n x) y = y +[ n ]ₖ x
inv' (addIso n x) y = y -[ n ]ₖ x
rightInv (addIso n x) y = -+cancelₖ n y x
leftInv (addIso n x) y = -cancelRₖ n x y

isCommΩK-based : (n : ℕ) (x : coHomK n) → isComm∙ (coHomK n , x)
isCommΩK-based zero x p q = isSetInt _ _ (p ∙ q) (q ∙ p)
isCommΩK-based (suc zero) x =
  subst isComm∙ (λ i → coHomK 1 , lUnitₖ 1 x i)
                (ptdIso→comm {A = (_ , 0ₖ 1)} (addIso 1 x)
                              (isCommΩK 1))
isCommΩK-based (suc (suc n)) x =
  subst isComm∙ (λ i → coHomK (suc (suc n)) , lUnitₖ (suc (suc n)) x i)
                (ptdIso→comm {A = (_ , 0ₖ (suc (suc n)))} (addIso (suc (suc n)) x)
                              (isCommΩK (suc (suc n))))

---
-- hidden versions of cohom stuff using the "lock" hack. The locked versions can be used when proving things.
-- Swapping "key" for "tt*" will then give computing functions.

Unit' : Type₀
Unit' = lockUnit {ℓ-zero}

lock : ∀ {ℓ} {A : Type ℓ} → Unit' → A → A
lock unlock = λ x → x

module lockedCohom (key : Unit') where
  +K : (n : ℕ) → coHomK n → coHomK n → coHomK n
  +K n = lock key (_+ₖ_ {n = n})

  -K : (n : ℕ) → coHomK n → coHomK n
  -K n = lock key (-ₖ_ {n = n})

  -Kbin : (n : ℕ) → coHomK n → coHomK n → coHomK n
  -Kbin n x y = +K n x (-K n y)

  rUnitK : (n : ℕ) (x : coHomK n) → +K n x (0ₖ n) ≡ x
  rUnitK n x = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) x (0ₖ n) ≡ x
    pm unlock = rUnitₖ n x

  lUnitK : (n : ℕ) (x : coHomK n) → +K n (0ₖ n) x ≡ x
  lUnitK n x = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (0ₖ n) x ≡ x
    pm unlock = lUnitₖ n x

  rCancelK : (n : ℕ) (x : coHomK n) → +K n x (-K n x) ≡ 0ₖ n
  rCancelK n x = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) x (lock t (-ₖ_ {n = n}) x) ≡ 0ₖ n
    pm unlock = rCancelₖ n x

  lCancelK : (n : ℕ) (x : coHomK n) → +K n (-K n x) x ≡ 0ₖ n
  lCancelK n x = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (-ₖ_ {n = n}) x) x ≡ 0ₖ n
    pm unlock = lCancelₖ n x

  -cancelRK : (n : ℕ) (x y : coHomK n) → -Kbin n (+K n y x) x ≡ y
  -cancelRK n x y = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) y x) (lock t (-ₖ_ {n = n}) x) ≡ y
    pm unlock = -cancelRₖ n x y

  -cancelLK : (n : ℕ) (x y : coHomK n) → -Kbin n (+K n x y) x ≡ y
  -cancelLK n x y = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) x y) (lock t (-ₖ_ {n = n}) x) ≡ y
    pm unlock = -cancelLₖ n x y

  -+cancelK : (n : ℕ) (x y : coHomK n) → +K n (-Kbin n x y) y ≡ x
  -+cancelK n x y = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (_+ₖ_ {n = n})  x (lock t (-ₖ_ {n = n}) y)) y ≡ x
    pm unlock = -+cancelₖ n x y

  assocK : (n : ℕ) (x y z : coHomK n) → +K n x (+K n y z) ≡ +K n (+K n x y) z
  assocK n x y z = pm key
    where
    pm : (t : Unit') →  lock t (_+ₖ_ {n = n}) x (lock t (_+ₖ_ {n = n}) y z)
                       ≡ lock t (_+ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) x y) z
    pm unlock = assocₖ n x y z

  commK : (n : ℕ) (x y : coHomK n) → +K n x y ≡ +K n y x
  commK n x y = pm key
    where
    pm : (t : Unit') → lock t (_+ₖ_ {n = n}) x y ≡ lock t (_+ₖ_ {n = n}) y x
    pm unlock = commₖ n x y

  -- cohom

  +H : (n : ℕ) (x y : coHom n A) → coHom n A
  +H n = sRec2 § λ a b → ∣ (λ x → +K n (a x) (b x)) ∣₂

  -H : (n : ℕ) (x : coHom n A) → coHom n A
  -H n = sRec § λ a → ∣ (λ x → -K n (a x)) ∣₂

  -Hbin : (n : ℕ) → coHom n A → coHom n A → coHom n A
  -Hbin n = sRec2 § λ a b → ∣ (λ x → -Kbin n (a x) (b x)) ∣₂

  rUnitH : (n : ℕ) (x : coHom n A) → +H n x (0ₕ n) ≡ x
  rUnitH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                  λ a i → ∣ funExt (λ x → rUnitK n (a x)) i ∣₂

  lUnitH : (n : ℕ) (x : coHom n A) → +H n (0ₕ n) x ≡ x
  lUnitH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                    λ a i → ∣ funExt (λ x → lUnitK n (a x)) i ∣₂

  rCancelH : (n : ℕ) (x : coHom n A) → +H n x (-H n x) ≡ 0ₕ n
  rCancelH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                   λ a i → ∣ funExt (λ x → rCancelK n (a x)) i ∣₂

  lCancelH : (n : ℕ) (x : coHom n A) → +H n (-H n x) x  ≡ 0ₕ n
  lCancelH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                   λ a i → ∣ funExt (λ x → lCancelK n (a x)) i ∣₂

  assocH : (n : ℕ) (x y z : coHom n A) → (+H n x (+H n y z)) ≡ (+H n (+H n x y) z)
  assocH n = elim3 (λ _ _ _ → isOfHLevelPath 1 (§ _ _))
                 λ a b c i → ∣ funExt (λ x → assocK n (a x) (b x) (c x)) i ∣₂

  commH : (n : ℕ) (x y : coHom n A) → (+H n x y) ≡ (+H n y x)
  commH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                          λ a b i → ∣ funExt (λ x → commK n (a x) (b x)) i ∣₂

  -cancelRH : (n : ℕ) (x y : coHom n A) → -Hbin n (+H n y x) x ≡ y
  -cancelRH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ (λ x → -cancelRK n (a x) (b x) i) ∣₂

  -cancelLH : (n : ℕ) (x y : coHom n A) → -Hbin n (+H n x y) x ≡ y
  -cancelLH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ (λ x → -cancelLK n (a x) (b x) i) ∣₂

  -+cancelH : (n : ℕ) (x y : coHom n A) → +H n (-Hbin n x y) y ≡ x
  -+cancelH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ (λ x → -+cancelK n (a x) (b x) i) ∣₂

  Kn→ΩKn+1' : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
  Kn→ΩKn+1' n = lock key (Iso.fun (Iso-Kn-ΩKn+1 n))

  ΩKn+1→Kn' : (n : ℕ) → typ (Ω (coHomK-ptd (suc n))) → coHomK n
  ΩKn+1→Kn' n = lock key (Iso.inv (Iso-Kn-ΩKn+1 n))

  ΩKn+1→Kn→ΩKn+1 : (n : ℕ) → (x : typ (Ω (coHomK-ptd (suc n)))) → Kn→ΩKn+1' n (ΩKn+1→Kn' n x) ≡ x
  ΩKn+1→Kn→ΩKn+1 n x = pm key
    where
    pm : (key : Unit') → lock key (Iso.fun (Iso-Kn-ΩKn+1 n)) (lock key (Iso.inv (Iso-Kn-ΩKn+1 n)) x) ≡ x
    pm unlock = Iso.rightInv (Iso-Kn-ΩKn+1 n) x

  Kn→ΩKn+1→Kn : (n : ℕ) → (x : coHomK n) → ΩKn+1→Kn' n (Kn→ΩKn+1' n x) ≡ x
  Kn→ΩKn+1→Kn n x = pm key
    where
    pm : (key : Unit') → lock key (Iso.inv (Iso-Kn-ΩKn+1 n)) (lock key (Iso.fun (Iso-Kn-ΩKn+1 n)) x) ≡ x
    pm unlock = Iso.leftInv (Iso-Kn-ΩKn+1 n) x

lUnitK≡rUnitK : (key : Unit') (n : ℕ) → lockedCohom.lUnitK key n (0ₖ n) ≡ lockedCohom.rUnitK key n (0ₖ n)
lUnitK≡rUnitK unlock = lUnitₖ≡rUnitₖ