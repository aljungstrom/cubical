{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Base where


open import Cubical.Data.Int renaming (_+_ to _+z_)
open import Cubical.Data.Nat.Base renaming (_+_ to _+''_)
open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base

open import Cubical.HITs.Nullification.Base
open import Cubical.HITs.SetTruncation.Base
open import Cubical.HITs.Sn
open import Cubical.HITs.S1.Base
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.Truncation.Base

private
  variable
    ℓ : Level
    A : Type ℓ

--- Cohomology ---

{- EM-spaces Kₙ from Brunerie 2016 -}
coHomK : (n : ℕ) → Type₀
coHomK zero = Int
coHomK (suc n) =  ∥ S₊ (suc n) ∥ (3 +'' n)

{- Cohomology -}
coHom : (n : ℕ) → Type ℓ → Type ℓ
coHom n A = ∥ (A → coHomK n) ∥₂


--- Reduced cohomology ---

{- Pointed version of Kₙ  -}
coHomK-ptd : (n : ℕ) → Pointed (ℓ-zero)
coHomK-ptd 0 = coHomK 0 , 0
coHomK-ptd 1 = coHomK 1 , ∣ base ∣
coHomK-ptd (suc (suc n)) = coHomK (2 +'' n) , ∣ north ∣

{- Reduced cohomology -}
coHomRed : (n : ℕ) → (A : Pointed ℓ) → Type ℓ
coHomRed n A = ∥ A →∙ coHomK-ptd n ∥₂

coHom-pt : (n : ℕ) → coHomK n
coHom-pt 0 = 0
coHom-pt 1 = ∣ base ∣
coHom-pt (suc (suc n)) = ∣ north ∣


{- Loopspaces -}
loopSpaceK : (n : ℕ) → Type₀
loopSpaceK zero = ΩS¹
loopSpaceK (suc n) = hLevelTrunc (3 +'' n) (Path (S₊ (2 +'' n)) north north)

reflK : (n : ℕ) → loopSpaceK n
reflK zero = refl
reflK (suc n) = ∣ refl ∣



------ General
open import Cubical.Algebra.Group
open GroupStr renaming (assoc to assocG)

isAbelian : ∀ {ℓ} (G : Group {ℓ}) → Type ℓ
isAbelian G = (x y : fst G) → _+_ (snd G) x y ≡ _+_ (snd G) y x 


data K' {ℓ} (G : Group {ℓ}) (Ab : isAbelian G) : Type ℓ where
  base : K' G Ab
  loop : fst G → base ≡ base
  loop-ident : loop (0g (snd G)) ≡ refl
  loop-comp : (x y : fst G) → loop (_+_ (snd G) x y) ≡ loop y ∙ loop x

coHomie : ∀ {ℓ} (G : Group {ℓ}) (Ab : isAbelian G) → Type _
coHomie G Ab = hLevelTrunc 3 (K' G Ab)

coHomieℤ : Type {!!}
coHomieℤ = coHomie intGroup +-comm

coHomieRec : {!!}
coHomieRec = {!!}

open import Cubical.HITs.Truncation renaming (elim to trElim)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Algebra.Monoid
open IsMonoid renaming (assoc to assocM)
_+K_ : coHomieℤ → coHomieℤ → coHomieℤ
_+K_ = rec2 {!!} {!!}
  where
  help : (a b : K' intGroup +-comm) → coHomieℤ
  help base b = ∣ b ∣
  help (loop x i) base = ∣ loop x i ∣
  help (loop x i) (loop y j) = {!!}
    where
    helper : Path (Path (K' intGroup +-comm) _ _) (sym (loop y) ∙ loop x ∙ loop y) (loop x)
    helper = (cong ((sym (loop y)) ∙_) (sym (loop-comp y x) ∙∙ cong loop (+-comm y x) ∙∙ loop-comp x y)
           ∙ (assoc _ _ _
           ∙∙ cong (_∙ (loop x)) (lCancel (loop y))
           ∙∙ sym (lUnit (loop x))))
    helper2 : {!!}
    helper2 = {!!}
  help (loop x i) (loop-ident j k) = {!!}
  help (loop x i) (loop-comp x₁ y j k) = {!!}
  help (loop-ident i j) base = ∣ loop-ident i j ∣
  help (loop-ident i j) (loop x k) = {!!}
  help (loop-ident i j) (loop-ident k l) = {!!}
  help (loop-ident i j) (loop-comp x y k l) = {!!}
  help (loop-comp x y i j) b = {!!}


recK : ∀ {ℓ} {A : Type ℓ} → (a₀ : A) → (l : Int → a₀ ≡ a₀) → l 0 ≡ refl
      → ((x y : Int) → l (x +z y) ≡ l y ∙ l x)
      → isGroupoid A
      → coHomieℤ → A
recK {A = A} a₀ l id0 commie grpd = rec grpd {!!}
  where
  helper : K' intGroup +-comm → A
  helper base = a₀
  helper (loop x i) = l x i
  helper (loop-ident i i₁) = id0 i i₁
  helper (loop-comp x y i j) =
    hcomp (λ k → λ {(i = i0) → l (x +z y) j
                    ; (i = i1) → {!!}
                    ; (j = i0) → a₀
                    ; (j = i1) → a₀})
          (commie x y i j)

-K_ : coHomieℤ → coHomieℤ
-K_ = map help
  where
  help : K' intGroup +-comm → K' intGroup +-comm
  help base = base
  help (loop x i) = {!!} -- loop x (~ i)
  help (loop-ident i i₁) = loop-ident i (~ i₁)
  help (loop-comp x y i j) = {!!}
    where
    helper : (x y : Int) → Path (Path (K' intGroup +-comm) _ _) (sym (loop (x +z y))) (cong help (loop y ∙ loop x))
    helper x y = {!!} ∙∙ {!!} ∙∙ {!!}

Test : GroupStr (coHomie intGroup +-comm)
0g Test = ∣ base ∣
_+_ Test = _+K_
- Test = -K_
isSemigroup (IsGroup.isMonoid (isGroup Test)) = {!!}
identity (IsGroup.isMonoid (isGroup Test)) = trElim {!!} λ x → refl , refl
IsGroup.inverse (isGroup Test) =
  trElim {!!} helper
  where
  helper : (a : K' intGroup +-comm) →
      ((∣ a ∣ +K (-K ∣ a ∣)) ≡ ∣ base ∣) ×
      (((-K ∣ a ∣) +K ∣ a ∣) ≡ ∣ base ∣)
  helper base = {!!}
  helper (loop x i) = {!!}
  helper (loop-ident i i₁) = {!!}
  helper (loop-comp x y i i₁) = {!!}

data James {ℓ} (A : Pointed ℓ) : Type ℓ where
  ε : James A
  α : typ A → James A → James A
  δ : (x : James A) → x ≡ α (pt A) x

test13 : ∀ {ℓ} {A : Type ℓ} {f : A → A} (p : ∀ a → f a ≡ a)
  (a : A) → Path (f a ≡ f a) (λ i → p (p a (~ i)) i) refl
test13 {f = f} p a j i =
  hcomp
    (λ k → λ {
      (i = i0) → f a;
      (i = i1) → p a (j ∧ ~ k);
      (j = i0) → p (p a (~ i)) i;
      (j = i1) → p a (i ∧ ~ k)})
    (p (p a (~ i ∨ j)) i)

δnat : {A∙ : Pointed ℓ} (x : James A∙) → δ (α (pt A∙) x) ≡ cong (α (pt A∙)) (δ x)
δnat {A∙ = A , a} x i j =
  hcomp (λ k → λ { (i = i0) → δ (δ x (k ∨ j)) (~ k ∨ j)
                  ; (i = i1) → α a (δ x j)
                  ; (j = i0) → test13 (λ x → sym (δ x)) x i k
                  ; (j = i1) → α a (α a x) })
        (α a (δ x j))




open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels


test : Iso (hLevelTrunc 3 S¹) (hLevelTrunc 3 (James (S₊∙ 1)))
Iso.fun test = map λ {base → α base ε ; (loop i) → α (loop i) ε}
Iso.inv test = rec (isOfHLevelTrunc 3) helper
  where
  helper : James (S₊∙ 1) → HubAndSpoke S¹ 2
  aStupidThing : S¹ → James (S₊∙ 1) → HubAndSpoke S¹ 2
  aStupidThing base = helper
  aStupidThing (loop i) ε = ∣ (loop i) ∣
  aStupidThing (loop i) (α base x₁) = aStupidThing (loop i) x₁
  aStupidThing (loop i) (α (loop j) x₁) = aStupidThing (helper2 i j) x₁
    where
    helper2 : Square {A = S¹} loop loop loop loop
    helper2 i j = hcomp (λ k → λ { (i = i0) → loop (j ∨ ~ k) ;
                                    (i = i1) → loop j ;
                                    (j = i0) → loop (i ∨ ~ k) ;
                                    (j = i1) → loop i})
                        (loop (i ∧ j))
  aStupidThing (loop i) (δ x i₁) = aStupidThing (loop i) x
  helper ε = ∣ base ∣
  helper (α x y) = aStupidThing x y
  helper (δ x j) = helper x

Iso.rightInv test = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) helper
  where
  aSquare : (a : James (S₊∙ 1)) →
            PathP (λ j → Path (hLevelTrunc 3 (James (S₊∙ 1))) ∣ δ (α base a) j ∣ ∣ δ (α base a) j ∣)
                  (λ i → ∣ α (loop i) a ∣)
                   λ i → ∣ α (loop i) (α base a) ∣
  aSquare a i j =
    hcomp (λ k → λ { (i = i0) → ∣ α (loop j) a ∣
                    ; (i = i1) → ∣ α (loop j) (α base a) ∣
                    ; (j = i0) → ∣ δnat a (~ k) i ∣
                    ; (j = i1) → ∣ δnat a (~ k) i ∣})
          ∣ α (loop j) (δ a i) ∣

  helper : (a : James (S₊∙ 1)) → Iso.fun test (Iso.inv test ∣ a ∣) ≡ ∣ a ∣
  Agda : (a : James (S₊∙ 1)) (x : S¹) → Iso.fun test (Iso.inv test ∣ α x a ∣) ≡ ∣ α x a ∣
  Agda2 : (a : James (S₊∙ 1)) (x : S¹) (y : S¹) → Iso.fun test (Iso.inv test ∣ α x (α y a) ∣) ≡ ∣ α x (α y a) ∣
  Agda2 a = wedgeConSn 0 0 (λ _ _ → isOfHLevelTrunc 3 _ _)
             (λ {base → Agda a base ∙ λ i → ∣ δ (α base a) i ∣
              ; (loop i) j → hcomp (λ k → λ { (j = i0) → Iso.fun test (Iso.inv test ∣ (α (loop i) a) ∣)
                                              ; (j = i1) → {!!}})
                          {!!}})
             (λ {base → Agda a base ∙ λ i → ∣ δ (α base a) i ∣
              ; (loop i) j → {!!}})
             refl .fst
  Agda ε base = refl
  Agda ε (loop i) = refl
  Agda (α y a) x = Agda2 a x y
  Agda (δ a i) x = {!(α (loop i) a)!}
  helper ε i = ∣ δ ε (~ i) ∣
  helper (α x y) = Agda y x
  {-
  helper (α (loop i) ε) j =
    hcomp (λ k → λ { (i = i0) → lCancel (λ i₁ → ∣ δ ε i₁ ∣) (~ k) j ;
                      (i = i1) → lCancel (λ i₁ → ∣ δ ε i₁ ∣) (~ k) j ;
                      (j = i0) → ∣ α (loop i) ε ∣ ;
                      (j = i1) → ∣ α (loop i) ε ∣ })
           ∣ α (loop i) ε ∣
  helper (α (loop i) (α base a)) j =
    hcomp (λ k → λ { (j = i0) → Iso.fun test (Iso.inv test ∣ α (loop i) a ∣)
                    ; (j = i1) → aSquare a k i})
          (helper (α (loop i) a) j)
  helper (α (loop i) (α (loop j) a)) k =
    {!aCube i j k!}
    where
    aCube : Cube (λ j → (helper (α (loop j) a) ∙ λ i → ∣ δ (α (loop j) a) i ∣))
                 (λ j → (helper (α (loop j) a) ∙ λ i → ∣ δ (α (loop j) a) i ∣))
                 (λ i k → hcomp (λ r → λ { (k = i0) → Iso.fun test (Iso.inv test ∣ α (loop i) a ∣)
                                           ; (k = i1) → aSquare a r i})
                                 (helper (α (loop i) a) k))
                 (λ i k → hcomp (λ r → λ { (k = i0) → Iso.fun test (Iso.inv test ∣ α (loop i) a ∣)
                                           ; (k = i1) → aSquare a r i})
                                 (helper (α (loop i) a) k))
                 (λ i j → Iso.fun test (Iso.inv test ∣ α (loop i) (α (loop j) a) ∣))
                 λ i j → ∣ α (loop i) (α (loop j) a) ∣
    aCube = isGroupoid→isGroupoid' (isOfHLevelTrunc 3) _ _ _ _ _ _
  helper (α (loop i) (δ a j)) k =
    {!!} -}
  helper (δ a i) j = {!!} -- compPath-filler (helper a) (λ i → ∣ δ a i ∣ ) i j
Iso.leftInv test = trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                           λ {base → refl ; (loop i) → refl}
