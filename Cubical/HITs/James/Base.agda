{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.James.Base where

open import Cubical.Foundations.Everything renaming (J to J')
open import Cubical.HITs.S1
open import Cubical.HITs.Truncation.FromNegOne
open import Cubical.HITs.S2

data J {ℓ : Level} (A : Pointed ℓ) : Type ℓ where
  εJ : J A
  αJ : typ A → J A → J A
  δJ : (x : J A) → x ≡ αJ (pt A) x

-- better for working with suspensions
data J2 {ℓ : Level} (A : Pointed ℓ) : Type ℓ where
  εJn : J2 A
  εJs : J2 A
  n=s : εJn ≡ εJs
  αJ : typ A → J2 A → J2 A
  δJ : (x : J2 A) → x ≡ αJ (pt A) x

IsoJ2-J : ∀ {ℓ} {A : Pointed ℓ} → Iso (J A) (J2 A)
Iso.fun (IsoJ2-J {A = A}) = theFun
  where
  theFun : (J A) → (J2 A)
  mutualInd : (x : typ A) (y : J A) → J2 A
  mutualInd x y = αJ x (theFun y)
  theFun εJ = εJn
  theFun (αJ x x₁) = mutualInd x x₁
  theFun (δJ x i) = δJ (theFun x) i
Iso.inv (IsoJ2-J {A = A}) = theFun
  where
  theFun : (J2 A) → (J A)
  mutualInd : (x : typ A) (y : J2 A) → J A
  mutualInd x y = αJ x (theFun y)
  theFun εJn = εJ
  theFun εJs = εJ
  theFun (n=s i) = εJ
  theFun (αJ x x₁) = mutualInd x x₁
  theFun (δJ x i) = δJ (theFun x) i
Iso.rightInv (IsoJ2-J {A = A}) = theId
  where
  theId : (x : J2 A) → Iso.fun IsoJ2-J (Iso.inv IsoJ2-J x) ≡ x
  mutualInd : (x : typ A) (y : J2 A) → Iso.fun IsoJ2-J (Iso.inv IsoJ2-J (αJ x y)) ≡ αJ x y
  mutualInd x y i = αJ x (theId y i)
  theId εJn = refl
  theId εJs = n=s
  theId (n=s i) j = n=s (j ∧ i)
  theId (αJ x x₁) = mutualInd x x₁
  theId (δJ x i) j = δJ (theId x j) i
Iso.leftInv (IsoJ2-J {A = A}) = theId
  where
  theId : (x : J A) → Iso.inv IsoJ2-J (Iso.fun IsoJ2-J x) ≡ x
  mutualInd : (x : typ A) (y : J A) → Iso.inv IsoJ2-J (Iso.fun IsoJ2-J (αJ x y)) ≡ αJ x y
  mutualInd x y i = αJ x (theId y i)
  theId εJ = refl
  theId (αJ x x₁) = mutualInd x x₁
  theId (δJ x i) j = δJ (theId x j) i

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

{-
data ∥_∥₂* {ℓ : Level} (A : Type ℓ) : Type ℓ where
 ∣_∣₂ : A → ∥ A ∥₂*
 squash* : {x y z w : ∥ A ∥₂*} (p : x ≡ y) (q : z ≡ w) (l : x ≡ z) (r : y ≡ w)
         → Square p q l r
-}
{-
δJnat : ∀ {ℓ} {A∙ : Pointed ℓ} (x : J A∙) → δJ (αJ (pt A∙) x) ≡ cong (αJ (pt A∙)) (δJ x)
δJnat {A∙ = A , a} x i j =
  hcomp (λ k → λ { (i = i0) → δJ (δJ x (k ∨ j)) (~ k ∨ j)
                  ; (i = i1) → αJ a (δJ x j)
                  ; (j = i0) → test13 (λ x → sym (δJ x)) x i k
                  ; (j = i1) → αJ a (αJ a x) })
        (αJ a (δJ x j))
-}
open import Cubical.HITs.Susp
open import Cubical.HITs.Sn
S²∙ : Pointed₀
S²∙ = Susp S¹ , north

JS²→K₂ : J (S²∙) → hLevelTrunc 4 S²
mutualInd : (x : Susp S¹) (y : J S²∙) → hLevelTrunc 4 S²
mutualInd north y = JS²→K₂ y
mutualInd south y = JS²→K₂ y
mutualInd (merid base i) y = JS²→K₂ y
mutualInd (merid (loop j) i) εJ = ∣ surf j i ∣
mutualInd (merid (loop j) i) (αJ north y) = mutualInd (merid (loop j) i) y
mutualInd (merid (loop j) i) (αJ south y) = mutualInd (merid (loop j) i) y
mutualInd (merid (loop j) i) (αJ (merid base i₁) y) = mutualInd (merid (loop j) i) y
mutualInd (merid (loop i) j) (αJ (merid (loop k) l) y) =
  is2Groupoid→is2Groupoid' (isOfHLevelTrunc 4)
    (λ _ k l → mutualInd (merid (loop k) l) y) (λ _ k l → mutualInd (merid (loop k) l) y)
    (λ _ k l → mutualInd (merid (loop k) l) y) (λ _ k l → mutualInd (merid (loop k) l) y)
    (λ i j _ → mutualInd (merid (loop i) j) y) (λ i j _ → mutualInd (merid (loop i) j) y)
    (λ i j _ → mutualInd (merid (loop i) j) y) (λ i j _ → mutualInd (merid (loop i) j) y) i j k l
mutualInd (merid (loop j) i) (δJ y i₁) = mutualInd (merid (loop j) i) y
JS²→K₂ εJ = ∣ base ∣
JS²→K₂ (αJ x x₁) = mutualInd x x₁
JS²→K₂ (δJ x i) = JS²→K₂ x

S²→JS² : S² → J S²∙
S²→JS² base = αJ north εJ
S²→JS² (surf i j) = αJ (meridian-contraction j i i1) εJ

JamesK₂Iso : Iso (hLevelTrunc 4 (J (S²∙))) (hLevelTrunc 4 S²)
Iso.fun JamesK₂Iso = rec (isOfHLevelTrunc 4) JS²→K₂
Iso.inv JamesK₂Iso = map S²→JS²
Iso.rightInv JamesK₂Iso =
  elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
     λ {base → refl ; (surf i j) k → JS²→K₂ (αJ (meridian-contraction j i (~ k)) εJ)}
Iso.leftInv JamesK₂Iso = elim {!!} test
  where
  test : (x : J (S²∙)) → Iso.inv JamesK₂Iso (Iso.fun JamesK₂Iso ∣ x ∣) ≡ ∣ x ∣
  mutualInd' : (x : Susp S¹) (y : J (S²∙))  → Iso.inv JamesK₂Iso (Iso.fun JamesK₂Iso ∣ (αJ x y) ∣) ≡ ∣ (αJ x y) ∣
  mutualInd' north y = test y ∙ λ i → ∣ δJ y i ∣
  mutualInd' south y = (test y ∙ (λ i → ∣ δJ y i ∣)) ∙ λ i → ∣ αJ (merid base i) y ∣
  mutualInd' (merid base i) y j =
    hcomp (λ k → λ { (i = i0) → mutualInd' north y j
                   ; (j = i0) → Iso.inv JamesK₂Iso (Iso.fun JamesK₂Iso ∣ y ∣)
                   ; (j = i1) → ∣ αJ (merid base (i ∧ k)) y ∣} )
           (hcomp (λ k → λ { (j = i0) → Iso.inv JamesK₂Iso (Iso.fun JamesK₂Iso ∣ y ∣)
                           ; (j = i1) → ∣ δJ y k ∣})
                  (test y j))
  mutualInd' (merid (loop j) i) εJ k = {!!}
    where
    helper : {!cong (λ x → mutualInd' x εJ) (merid base) !}
    helper = {!!}
  mutualInd' (merid (loop j) i) (αJ north y) = {!mutualInd' (merid (loop j) i) y!}
  mutualInd' (merid (loop j) i) (αJ south y) = {!!}
  mutualInd' (merid (loop j) i) (αJ (merid a k) y) =
    {!!} -- done
  mutualInd' (merid (loop j) i) (δJ y i₁) = {!!} --done
  test εJ i = ∣ δJ εJ (~ i) ∣
  test (αJ x x₁) = mutualInd' x x₁
  test (δJ x i) j = compPath-filler (test x) (λ i₁ → ∣ δJ x i₁ ∣) i j

-- JS²→K₂ : J (S² , base) → hLevelTrunc 4 S²
-- mutualInd : (x : S²) (y : J (S² , base)) → hLevelTrunc 4 S²
-- surfsurf→2gpd : (y : J (S² , base)) →
--                 4Cube (λ _ k l → mutualInd (surf k l) y) (λ _ k l → mutualInd (surf k l) y)
--                       (λ _ k l → mutualInd (surf k l) y) (λ _ k l → mutualInd (surf k l) y)
--                       (λ i j _ → mutualInd (surf i j) y) (λ i j _ → mutualInd (surf i j) y)
--                       (λ i j _ → mutualInd (surf i j) y) λ i j _ → mutualInd (surf i j) y
-- surfsurf→2gpd y = is2Groupoid→is2Groupoid' (isOfHLevelTrunc 4) _ _ _ _ _ _ _ _
-- mutualInd base y = JS²→K₂ y
-- mutualInd (surf i j) εJ = ∣ surf i j ∣
-- mutualInd (surf i j) (αJ base y) = mutualInd (surf i j) y
-- mutualInd (surf i j) (αJ (surf k l) y) = surfsurf→2gpd y i j k l
-- mutualInd (surf i j) (δJ y i₂) =  mutualInd (surf i j) y
-- JS²→K₂ εJ = ∣ base ∣
-- JS²→K₂ (αJ x y) = mutualInd x y
-- JS²→K₂ (δJ x i) = JS²→K₂ x

-- S²→JS² : S² → J (S² , base)
-- S²→JS² base = αJ base εJ
-- S²→JS² (surf i i₁) = αJ (surf i i₁) εJ

-- JamesK₂Iso : Iso (hLevelTrunc 4 (J (S² , base))) (hLevelTrunc 4 S²)
-- Iso.fun JamesK₂Iso = rec (isOfHLevelTrunc 4) JS²→K₂
-- Iso.inv JamesK₂Iso = map S²→JS²
-- Iso.rightInv JamesK₂Iso =
--   elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
--        λ {base → refl ; (surf i j) → refl}
-- Iso.leftInv JamesK₂Iso = elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _) retrHelp
--   where
--   retrHelp : (x : J (S² , base)) → map S²→JS² (JS²→K₂ x) ≡ ∣ x ∣
--   S²S²-helper : (x : J (S² , base)) (y z : S²) → map S²→JS² (JS²→K₂ x) ≡ {!!}
--   S²S²-helper = {!!}
--   retrHelp εJ i = ∣ δJ εJ (~ i) ∣
--   retrHelp (αJ base x₁) = retrHelp x₁ ∙ λ i → ∣ δJ x₁ i ∣
--   retrHelp (αJ (surf i j) εJ) k =
--     hcomp (λ l → λ { (i = i0) → lCancel (λ i₁ → ∣ δJ εJ i₁ ∣) (~ l) k
--                    ; (i = i1) → lCancel (λ i₁ → ∣ δJ εJ i₁ ∣) (~ l) k
--                    ; (j = i0) → lCancel (λ i₁ → ∣ δJ εJ i₁ ∣) (~ l) k
--                    ; (j = i1) → lCancel (λ i₁ → ∣ δJ εJ i₁ ∣) (~ l) k
--                    ; (k = i0) → ∣ αJ (surf i j) εJ ∣
--                    ; (k = i1) → ∣ αJ (surf i j) εJ ∣ })
--           ∣ αJ (surf i j) εJ ∣
--   retrHelp (αJ (surf i j) (αJ y x)) k = {!!}

-- {-
--     hcomp (λ l → λ { (k = i0) → map S²→JS² (JS²→K₂ (αJ (surf i j) (αJ y x)))
--                    ; (k = i1) → acube y x l i j })
--            (map S²→JS² (JS²→K₂ (αJ (surf i j) (αJ y x))))
--     where
--     acube : (y : S²) (x : J (S² , base))
--           → Cube {A = hLevelTrunc 4 (J (S² , base))}
--                  (λ i j → map S²→JS² (JS²→K₂ (αJ (surf i j) (αJ y x)))) -- (λ i j → map S²→JS² (JS²→K₂ (αJ (surf i j) (αJ y x)))) --(λ _ i j → map S²→JS² (JS²→K₂ (αJ (surf i j) (αJ y x))))
--                  (λ i j → ∣ αJ (surf i j) (αJ y x) ∣) -- (λ i j → ∣ αJ (surf i j) (αJ y x) ∣ ) -- ((λ _ i j → ∣ αJ (surf i j) (αJ y x) ∣))
--                  {!!}
--                  {!!}
--                  (λ i j → {!!})
--                  {!!}
--     acube = {!!} -}
--   {-
--     hcomp (λ l → λ { (k = i0) → map S²→JS² (JS²→K₂ (αJ (surf i j) (αJ base x)))
--                    ; (k = i1) → {!map S²→JS² (JS²→K₂ (αJ base (αJ base x)))!} })
--           {!!}
-- -}
-- {-
-- i = i0 ⊢ ((retrHelp x ∙ (λ i₁ → ∣ δJ x i₁ ∣)) ∙
--           (λ i₁ → ∣ δJ (αJ base x) i₁ ∣))
--          k
-- i = i1 ⊢ ((retrHelp x ∙ (λ i₁ → ∣ δJ x i₁ ∣)) ∙
--           (λ i₁ → ∣ δJ (αJ base x) i₁ ∣))
--          k
-- j = i0 ⊢ ((retrHelp x ∙ (λ i₁ → ∣ δJ x i₁ ∣)) ∙
--           (λ i₁ → ∣ δJ (αJ base x) i₁ ∣))
--          k
-- j = i1 ⊢ ((retrHelp x ∙ (λ i₁ → ∣ δJ x i₁ ∣)) ∙
--           (λ i₁ → ∣ δJ (αJ base x) i₁ ∣))
--          k
-- -}
--   -- retrHelp (αJ (surf i j) (αJ (surf k l) x₁)) = {!!}
--   retrHelp (αJ (surf i i₁) (δJ x₁ i₂)) j = {!!}
--   retrHelp (δJ εJ i) j = compPath-filler (λ i₁ → ∣ δJ εJ (~ i₁) ∣) (λ i₁ → ∣ δJ εJ i₁ ∣) i j
--   retrHelp (δJ (αJ x x₁) i) j = {!hcomp (λ k → ) ? !}
--   retrHelp (δJ (δJ εJ i₁) i) j = {!!}
--   retrHelp (δJ (δJ (αJ x x₁) i₁) i) j = {!!}
--   retrHelp (δJ (δJ (δJ x i₂) i₁) i) j = {!!}

-- -- test : J (S¹ , base) → hLevelTrunc 2 S¹
-- -- test εJ = ∣ base ∣
-- -- test (αJ base x) = test x
-- -- test (αJ (loop i) εJ) = ∣ loop i ∣
-- -- test (αJ (loop i) (αJ base y)) = test (αJ (loop i) y)
-- -- test (αJ (loop i) (αJ (loop j) y)) = {! SquareHelp i j !}
-- --   where
-- --   SquareHelp : Square (λ j → test (αJ (loop j) y)) (λ j → test (αJ (loop j) y))
-- --                       (λ j → test (αJ (loop j) y)) λ j → test (αJ (loop j) y)
-- --   SquareHelp = isSet→isSet' (isOfHLevelTrunc 2) _ _ _ _
-- -- test (αJ (loop i) (δJ y i₁)) = test (αJ (loop i) y)
-- -- test (δJ x i) = test x
