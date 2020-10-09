{-# OPTIONS --cubical --no-import-sorts #-}
module Cubical.HITs.James.Base where

open import Cubical.Foundations.Everything renaming (J to J')
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.Pushout

open import Cubical.HITs.S1
open import Cubical.HITs.Truncation.FromNegOne

private
  variable
    ℓ : Level
    A B : Type ℓ
    A∙ : Pointed ℓ

data J (A : Pointed ℓ) : Type ℓ where
  εJ : J A
  αJ : typ A → J A → J A
  δJ : (x : J A) → x ≡ αJ (pt A) x

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


δnatJ : {A∙ : Pointed ℓ} (x : J A∙) → δJ (αJ (pt A∙) x) ≡ cong (αJ (pt A∙)) (δJ x)
δnatJ {A∙ = A , a} x i j =
  hcomp (λ k → λ { (i = i0) → δJ (δJ x (k ∨ j)) (~ k ∨ j)
                  ; (i = i1) → αJ a (δJ x j)
                  ; (j = i0) → test13 (λ x → sym (δJ x)) x i k
                  ; (j = i1) → αJ a (αJ a x) })
        (αJ a (δJ x j))

open import Cubical.HITs.S2

{-
testHelp : {A : J (S² , base) → Type₀}
         → ((x : J (S² , base)) → isOfHLevel 4 (A x))
         → (f : ((x : J (S² , base)) → A (αJ base (αJ base x))))
         → ((x : J (S² , base)) → PathP (λ i → PathP (λ j → A (αJ (surf i j) (αJ base x))) (f x) (f x)) (λ _ → f x) λ _ → f x)
         → ((x : J (S² , base)) → PathP (λ i → PathP (λ j → A (αJ base (αJ (surf i j) x))) (f x) (f x)) (λ _ → f x) λ _ → f x)
         → (z : J (S² , base)) (x y : S²) → A (αJ x (αJ y z))
testHelp hlev f pl pr z base base = f z
testHelp hlev f pl pr z base (surf i i₁) = pr z i i₁
testHelp hlev f pl pr z (surf i i₁) base = pl z i i₁
testHelp hlev f pl pr z (surf i i₁) (surf i₂ i₃) = {!!}

amap2 : J (S² , base) → S²
amap2 εJ = base
amap2 (αJ base x₁) = amap2 x₁
amap2 (αJ (surf i i₁) εJ) = surf i i₁
amap2 (αJ (surf i i₁) (αJ base x₁)) = amap2 (αJ (surf i i₁) x₁)
amap2 (αJ (surf i j) (αJ (surf k l) εJ)) =
  {!isOfHLevel→isOfHLevelDep 1!}
  where
  test4 : PathP (λ i → PathP {!!} (PathP (λ k → PathP (λ l → Path S² (surf i j) (surf k l)) {!!} {!!}) {!!}) {!!}) {!!} {!!}
  test4 = {!!}
amap2 (αJ (surf i i₁) (αJ (surf i₂ i₃) (αJ x x₁))) = {!!}
amap2 (αJ (surf i i₁) (αJ (surf i₂ i₃) (δJ x₁ i₄))) = {!!}
  where
  test2 : (x : S²) → Path (Path S² (amap2 (αJ x x₁)) (amap2 (αJ x x₁))) refl refl
  test2 = S²ToSetRec (λ _ → hlevS2 _ _ _ _) (cong (cong (λ x → amap2 (αJ x x₁))) surf)
    where
    help2 : (x₁ : J (S² , base)) → Path (Path S² (amap2 x₁) (amap2 x₁)) refl refl
    help2 x = {!!}

amap2 (αJ (surf i i₁) (δJ x₁ i₂)) = amap2 (αJ (surf i i₁) x₁)
amap2 (δJ x i) = {!!}
-}

amap2 : J (S² , base) → hLevelTrunc 4 S²
mutualInd : (x : S²) (y : J (S² , base)) → hLevelTrunc 4 S²
mutualInd base y = amap2 y
mutualInd (surf i i₁) εJ = ∣ surf i i₁ ∣
mutualInd (surf i i₁) (αJ base y) = mutualInd (surf i i₁) y
mutualInd (surf i i₁) (αJ (surf i₂ i₃) y) = helper i i₁ i₂ i₃
  where
  helper :  4Cube (λ _ k l  → mutualInd (surf k l) y) (λ _ k l  → mutualInd (surf k l) y)
             (λ _ k l  → mutualInd (surf k l) y) (λ _ k l  → mutualInd (surf k l) y) 
             (λ i j _  → mutualInd (surf i j) y) (λ i j _  → mutualInd (surf i j) y)
             (λ i j _  → mutualInd (surf i j) y) (λ i j _  → mutualInd (surf i j) y)
  helper = is2Groupoid→is2Groupoid' (isOfHLevelTrunc 4) _ _ _ _ _ _ _ _
mutualInd (surf i i₁) (δJ y i₂) = mutualInd (surf i i₁) y

amap2 εJ = ∣ base ∣
amap2 (αJ x y) = mutualInd x y
amap2 (δJ x i) = amap2 x

amap2back : S² → hLevelTrunc 4 (J (S² , base))
amap2back base = ∣ αJ base εJ ∣
amap2back (surf i i₁) = ∣ (αJ (surf i i₁) εJ) ∣

theIso : Iso (hLevelTrunc 4 (J (S² , base))) (hLevelTrunc 4 S²)
Iso.fun theIso = rec (isOfHLevelTrunc 4) amap2
Iso.inv theIso = rec (isOfHLevelTrunc 4) amap2back
Iso.rightInv theIso =
  elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
       λ {base → refl ; (surf i j) → refl }
Iso.leftInv theIso =
  elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
       {!!}
  where
  helper : (a : J (S² , base)) → Iso.inv theIso (Iso.fun theIso ∣ a ∣) ≡ ∣ a ∣
  mutualInd' : (x : S²) (y : J(S² , base)) → Iso.inv theIso (Iso.fun theIso ∣ (αJ x y) ∣) ≡ ∣ (αJ x y) ∣
  mutualInd'' : (x1 x2 : S²) (y : J (S² , base)) → Iso.inv theIso (Iso.fun theIso ∣ (αJ x1 (αJ x2 y)) ∣) ≡ ∣ (αJ x1 (αJ x2 y)) ∣
  mutualInd'' base x2 y = {!mutualInd' x2 y ∙ ?!}
  mutualInd'' (surf i i₁) x2 y = {!!}

{-
  mutualInd'' base y i j k = {!!}
  mutualInd'' (surf i j) y k l m = helper2 i j k l m
    where
    helper2 : PathP (λ i → 4Cube (λ k l m → mutualInd'' base y k l m)
                                  (λ k l m → mutualInd'' base y k l m)
                                  (λ j l m → Iso.inv theIso (Iso.fun theIso ∣ αJ (surf l m) (αJ (surf i j) y) ∣))
                                  (λ j l m → ∣ αJ (surf l m) (αJ (surf i j) y) ∣)
                                  (λ j k m → mutualInd' base (αJ (surf i j) y) k)
                                  (λ j k m → mutualInd' base (αJ (surf i j) y) k)
                                  (λ j k l → mutualInd' base (αJ (surf i j) y) k)
                                  λ j k l → mutualInd' base (αJ (surf i j) y) k ) -- (λ j k l → ∣ αJ (surf i j) (αJ (surf k l) y) ∣))
                    (λ _ k l m → mutualInd'' base y k l m)
                    (λ _ k l m → mutualInd'' base y k l m)
    helper2 = transport⁻ (PathP≡Path _ _ _)
                (transport⁻ (cong isProp (PathP≡Path _ _ _))
                  (transport⁻ (cong isSet (PathP≡Path _ _ _))
                    (transport⁻  (cong isGroupoid (PathP≡Path _ _ _))
                      (transport⁻  (cong is2Groupoid (PathP≡Path _ _ _))
                        (isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
                          _ _) _ _) _ _) _ _) -}
    
  mutualInd' base εJ = refl
  mutualInd' (surf i i₁) εJ = {!!}
  mutualInd' x (αJ x₁ y) = mutualInd'' x x₁ y
  mutualInd' x (δJ y i) = {!!}
{-
    hcomp (λ m → λ { (i = i0) → lCancel (λ i → ∣ δJ εJ i ∣) (~ m) k
                    ; (i = i1) → lCancel (λ i → ∣ δJ εJ i ∣) (~ m) k
                    ; (j = i0) → lCancel (λ i → ∣ δJ εJ i ∣) (~ m) k
                    ; (j = i1) → lCancel (λ i → ∣ δJ εJ i ∣) (~ m) k
                    ; (k = i0) → ∣ αJ (surf i j) εJ ∣
                    ; (k = i1) → ∣ αJ (surf i j) εJ ∣ })
           ∣ (αJ (surf i j) εJ) ∣
-}
  helper εJ i = ∣ δJ εJ (~ i) ∣
  helper (αJ x y) = mutualInd' x y
  helper (δJ a i) j = {!!} -- compPath-filler (helper a) (λ i → ∣ δJ a i ∣) i j

-- retrH2 : section amap2back amap2
-- retrH2 εJ = sym (δJ εJ)
-- retrH2 (αJ base x₁) = retrH2 x₁ ∙ δJ x₁
-- retrH2 (αJ (surf i j) εJ) k =
--   hcomp (λ m → λ { (i = i0) → lCancel (δJ εJ) (~ m) k
--                  ; (i = i1) → lCancel (δJ εJ) (~ m) k
--                  ; (j = i0) → lCancel (δJ εJ) (~ m) k
--                  ; (j = i1) → lCancel (δJ εJ) (~ m) k
--                  ; (k = i0) → αJ (surf i j) εJ
--                  ; (k = i1) → αJ (surf i j) εJ })
--         (αJ (surf i j) εJ)
-- retrH2 (αJ (surf i j) (αJ base x)) k =
--   hcomp (λ m → λ { (i = i0) → ((retrH2 x ∙ δJ x) ∙ δnatJ x (~ m)) k
--                  ; (i = i1) → ((retrH2 x ∙ δJ x) ∙ δnatJ x (~ m)) k
--                  ; (j = i0) → ((retrH2 x ∙ δJ x) ∙ δnatJ x (~ m)) k
--                  ; (j = i1) → ((retrH2 x ∙ δJ x) ∙ δnatJ x (~ m)) k
--                  ; (k = i0) → amap2back (amap2 (αJ (surf i j) x))
--                  ; (k = i1) → αJ (surf i j) (αJ base x)})
--         (hcomp (λ m → λ { (k = i0) → amap2back (amap2 (αJ (surf i j) x))
--                          ; (k = i1) → αJ (surf i j) (δJ x m)})
--                (retrH2 (αJ (surf i j) x) k))

-- retrH2 (αJ (surf i i₁) (αJ (surf i₂ i₃) x₁)) k = {!isOfHLevel!} --done
-- retrH2 (αJ (surf i i₁) (δJ x₁ i₂)) k = {!!} --done
-- retrH2 (δJ x i) = compPath-filler (retrH2 x) (δJ x) i

-- -- retrH : section amap2back amap2
-- -- retrH εJ = sym (δJ εJ)
-- -- retrH (αJ base εJ) = refl
-- -- retrH (αJ base (αJ base x₁)) = retrH x₁ ∙∙ δJ x₁ ∙∙ cong (αJ base) (δJ x₁)
-- -- retrH (αJ base (αJ (surf i i₁) x₁)) x = {!!}
-- -- retrH (αJ base (δJ x₁ i)) j = {!!}
-- -- retrH (αJ (surf i j) εJ) k = {!!}
-- -- {-
-- --   hcomp (λ m → λ { (i = i0) → lCancel (δJ εJ) (~ m) k
-- --                   ; (i = i1) → lCancel (δJ εJ) (~ m) k
-- --                   ; (j = i0) → lCancel (δJ εJ) (~ m) k
-- --                   ; (j = i1) → lCancel (δJ εJ) (~ m) k
-- --                   ; (k = i0) → αJ (surf i j) εJ
-- --                   ; (k = i1) → αJ (surf i j) εJ})
-- --        (αJ (surf i j) εJ)
-- -- -}
-- -- retrH (αJ (surf i k) (αJ base εJ)) j =
-- --   hcomp (λ r → λ { (i = i0) → help r j ;
-- --                     (i = i1) → help r j ;
-- --                     (k = i0) → help r j ;
-- --                     (k = i1) → help r j ;
-- --                     (j = i0) → αJ (surf i k) εJ ;
-- --                     (j = i1) → αJ (surf i k) (αJ base εJ) }
-- --                 )
-- --         (αJ (surf i k) (δJ εJ j))
-- --   where
-- --   help : Path (Path (J (S² , base)) _ _) (cong (αJ base) (δJ εJ)) ((λ i₁ → δJ εJ (~ i₁)) ∙∙ δJ εJ ∙∙ cong (αJ base) (δJ εJ))
-- --   help = {!cong (αJ base) (δJ εJ)!}
-- -- {-
-- --   hcomp (λ r → λ {(j = i0) → αJ (surf i k) εJ
-- --                  ; (j = i1) → {!retrH (αJ (surf i k) εJ) i1!}})
-- --         (retrH (αJ (surf i k) εJ) j)
-- -- -}
-- -- retrH (αJ (surf i k) (αJ base (αJ x x₁))) j = {!!}
-- -- retrH (αJ (surf i k) (αJ base (δJ x₁ i₁))) j = {!!}
-- --   where
-- -- retrH (αJ (surf i i₁) (αJ (surf i₂ i₃) x₁)) = {!(cong (cong (λ x → amap2back (amap2 (αJ x x₁)))) surf)!}

-- -- retrH (αJ (surf i i₁) (δJ x₁ i₂)) = {!x₁!}
-- -- retrH (δJ εJ i) j = δJ εJ (~ j ∨ i)
-- -- retrH (δJ (αJ base εJ) i) j = {!!}
-- -- retrH (δJ (αJ base (αJ x x₁)) i) j = {!!}
-- -- retrH (δJ (αJ base (δJ x₁ i₁)) i) j = {!!}
-- -- retrH (δJ (αJ (surf i₁ i₂) x₁) i) = {!!} --not needed
-- -- retrH (δJ (δJ εJ i₁) i) = {!!}
-- -- retrH (δJ (δJ (αJ x x₁) i₁) i) = {!!} -- not needed
-- -- retrH (δJ (δJ (δJ x i₂) i₁) i) = {!!} --not needed
-- -- -- compPath-filler (retrH x) (δJ x) i


-- -- module _ (A : Pointed ℓ) where
-- --   James : ℕ → Type ℓ
-- --   JamesS : ℕ → Type ℓ
-- --   i : (n : ℕ) → James n → JamesS n
-- --   α : (n : ℕ) → typ A → James n → JamesS n
-- --   β : (n : ℕ) (x : James n) → α n (pt A) x ≡ i n x

-- --   James zero = Unit*
-- --   James (suc n) = JamesS n

-- --   JamesS zero = typ A
-- --   JamesS (suc n) = Pushout f g
-- --     module JamesS where
-- --     X : Type ℓ
-- --     X = Pushout {A = James n} {B = typ A × James n} {C = JamesS n}
-- --                 (λ x → (pt A , x)) (i n)

-- --     f : X → typ A × JamesS n
-- --     f (inl (x , y)) = x , (i n y)
-- --     f (inr x) = (pt A) , x
-- --     f (push a i₁) = pt A , i n a

-- --     g : X → JamesS n
-- --     g (inl (x , y)) = α n x y
-- --     g (inr x) = x
-- --     g (push a i₁) = β n a i₁

-- --   i zero x = pt A
-- --   i (suc n) x = inr x

-- --   α zero a _ = a
-- --   α (suc n) a x = inl (a , x)

-- --   β zero _ = refl
-- --   β (suc n) x = push (inr x)


-- -- J+2-elim : {!!}
-- -- J+2-elim = {!!}

