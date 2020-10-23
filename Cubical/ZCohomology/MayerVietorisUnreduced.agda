{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.MayerVietorisUnreduced where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.KcompPrelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₁ ; ∣_∣ to ∣_∣₁)
open import Cubical.Data.Nat
open import Cubical.Data.Prod hiding (_×_)
open import Cubical.Algebra.Group
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3)

open GroupHom

helper' : ∀ {ℓ} {A : Type ℓ} {a0 x y z w : A} {p : a0 ≡ a0} {q : a0 ≡ a0}
       → (f : A → A → A)
       → (pl : (x : A) → f x a0 ≡ x)
       → PathP (λ i → pl a0 i ≡ pl a0 i)
                (cong₂ f p q)
                (p ∙ q)
helper' {a0 = a0} {p = p} {q = q} f pl =
  toPathP (cong (transport (λ i → pl a0 i ≡ pl a0 i)) ((cong₂Funct f _ _) ∙ (cong (_∙ (cong (λ x → f a0 x) q)) (sym helper2)))
       ∙ λ i → transp (λ j → pl a0 (j ∨ i) ≡ pl a0 (j ∨ i)) i ((λ j → pl (pl (p j) (~ j ∨ i)) (i ∨ j)) ∙ λ j → pl {!q j!} i))
  where
  helper2 : (λ i → pl (pl (p i) (~ i)) i) ≡ (cong (λ x → f x a0) p)
  helper2 i j = {!cong pl q!}
{-
    hcomp (λ k → λ { (i = i0) → {!!}
                    ; (i = i1) → {!!}
                    ; (j = i0) → {!!}
                    ; (j = i1) → {!!} })
          {!!}
-}
{-
i = i0 ⊢ pl (pr (p j) (~ j)) j
i = i1 ⊢ cong (λ x₁ → f x₁ a0) p j
j = i0 ⊢ f a0 a0
j = i1 ⊢ f a0 a0
-}


module MV {ℓ ℓ' ℓ''} (A : Type ℓ) (B : Type ℓ') (C : Type ℓ'') (f : C → A) (g : C → B) where
  -- Proof from Brunerie 2016.
  -- We first define the three morphisms involved: i, Δ and d.

  private
    i* : (n : ℕ) → coHom n (Pushout f g) → coHom n A × coHom n B
    i* _ = sRec (isSet× setTruncIsSet setTruncIsSet) λ δ → ∣ (λ x → δ (inl x)) ∣₂ , ∣ (λ x → δ (inr x)) ∣₂

  iIsHom : (n : ℕ) → isGroupHom (coHomGr n (Pushout f g)) (×coHomGr n A B) (i* n)
  iIsHom _ = sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _) λ _ _ → refl

  i : (n : ℕ) → GroupHom (coHomGr n (Pushout f g)) (×coHomGr n A B)
  GroupHom.fun (i n) = i* n
  GroupHom.isHom (i n) = iIsHom n

-- isCommLoopSpace
  private
    distrLem : (n : ℕ) (x y z w : coHomK n) → (x +[ n ]ₖ y) -[ n ]ₖ (z +[ n ]ₖ w) ≡ (x -[ n ]ₖ z) +[ n ]ₖ (y -[ n ]ₖ w)
    distrLem n x y z w =
         cong (ΩKn+1→Kn n)
            ((cong₂ (λ q p → ∙K n q (symK n p)) (+ₖ→∙ n x y) (+ₖ→∙ n z w))
          ∙∙ (cong (∙K n (∙K n (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y))) (symDistr∙K n (Kn→ΩKn+1 n z) (Kn→ΩKn+1 n w)))
          ∙∙ (sym (assoc∙K n (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y) _)
          ∙∙ cong (∙K n (Kn→ΩKn+1 n x)) (assoc∙K n (Kn→ΩKn+1 n y) (symK n (Kn→ΩKn+1 n w)) (symK n (Kn→ΩKn+1 n z)))
          ∙∙ (cong (∙K n (Kn→ΩKn+1 n x)) (isCommLoopSpace n _ _)
          ∙∙ assoc∙K n _ _ _
          ∙∙ cong₂ (∙K n) (sym (Iso.rightInv (Iso-Kn-ΩKn+1 n) (∙K n (Kn→ΩKn+1 n x) (symK n (Kn→ΩKn+1 n z)))))
                          (sym (Iso.rightInv (Iso-Kn-ΩKn+1 n) (∙K n (Kn→ΩKn+1 n y) (symK n (Kn→ΩKn+1 n w))))))))

    Δ' : (n : ℕ) → ⟨ ×coHomGr n A B ⟩ → ⟨ coHomGr n C ⟩
    Δ' n (α , β) = coHomFun n f α -[ n ]ₕ coHomFun n g β

    Δ'-isMorph : (n : ℕ) → isGroupHom (×coHomGr n A B) (coHomGr n C) (Δ' n)
    Δ'-isMorph n =
      prodElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _ )
        λ f' x1 g' x2 i → ∣ (λ x → distrLem n (f' (f x)) (g' (f x)) (x1 (g x)) (x2 (g x)) i) ∣₂

  Δ : (n : ℕ) → GroupHom (×coHomGr n A B) (coHomGr n C)
  GroupHom.fun (Δ n) = Δ' n
  GroupHom.isHom (Δ n) = Δ'-isMorph n

  helper : (n : ℕ) (x : coHomK (suc n)) → Path (coHomK (2 + n)) (0ₖ (2 + n)) (0ₖ (2 + n))
  helper n x = trRec (isOfHLevelTrunc (4 + n) _ _) (cong ∣_∣) (Kn→ΩKn+1 (suc n) x)

  helperLemma : (n : ℕ) (x y : coHomK (suc n)) → helper n (x +[ (suc n) ]ₖ y) ≡ helper n x ∙ helper n y
  helperLemma zero = elim2 {!!} λ a b → {!!}
    where
    helper2 : (a b : S¹) (x : coHomK 1) → ΩKn+1→Kn 1 (∣ ϕ base a ∙ ϕ base b ∣) ≡ x → helper 0 (ΩKn+1→Kn 1 ∣ ϕ base a ∙ ϕ base b ∣) ≡ helper zero ∣ a ∣ ∙ helper zero ∣ b ∣
    helper2 a b = trElim (λ _ → isGroupoidΠ λ _ → isOfHLevelPath' 3 (isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _) _ _) λ c p → cong (helper 0) p
               ∙∙ cong (Iso.inv (PathIdTruncIso 3)) ((sym (cong (Kn→ΩKn+1 1) p)) ∙ (Iso.rightInv (Iso-Kn-ΩKn+1 1) (∣ ϕ base a ∙ ϕ base b ∣)))
               ∙∙ (congFunct ∣_∣ (ϕ base a) (ϕ base b)
               ∙ λ i → (λ j → ∣ ϕ base a j ∣) ∙ λ j → ∣ ϕ base b j ∣)
  helperLemma (suc n) = elim2 {!!} λ a b → helper2 (ΩKn+1→Kn (2 + n) (∣ ϕ north a ∙ ϕ north b ∣)) a b refl
    where
    helper2 : (x : coHomK (2 + n)) (a b : S₊ (2 + n)) → ΩKn+1→Kn (2 + n) (∣ ϕ north a ∙ ϕ north b ∣) ≡ x → helper (suc n) (+ₖ-syntax (suc (suc n)) ∣ a ∣ ∣ b ∣) ≡ helper (suc n) ∣ a ∣ ∙ helper (suc n) ∣ b ∣
    helper2 = trElim {!!} (helper3 n)
      where
      helper3 : (n : ℕ) → (c a b : S₊ (2 + n)) → ΩKn+1→Kn (2 + n) (∣ ϕ north a ∙ ϕ north b ∣) ≡ ∣ c ∣
             → helper (suc n) (+ₖ-syntax (suc (suc n)) ∣ a ∣ ∣ b ∣) ≡ helper (suc n) ∣ a ∣ ∙ helper (suc n) ∣ b ∣
      helper3 n c a b p =
           {!!}
        ∙∙ {!!}
        ∙∙ {!!}

  d-pre : (n : ℕ) → (C → coHomK n) → Pushout f g → coHomK (suc n)
  d-pre n γ (inl x) = 0ₖ (suc n)
  d-pre n γ (inr x) = 0ₖ (suc n)
  d-pre zero γ (push a i) = ∣ Kn→ΩKn+1 zero (γ a) i ∣ -- Kn→ΩKn+1 zero (γ a) i
  d-pre (suc n) γ (push a i) = helper n (γ a) i -- Iso.inv (PathIdTruncIso (3 + n)) (Kn→ΩKn+1 (suc n) (γ a)) i
    where

{-
  dHomHelperPath : (n : ℕ) (h l : C → coHomK n) (a : C) → I → I → coHomK (suc n)
  dHomHelperPath zero h l a i j =
    hcomp (λ k → λ { (i = i0) → lUnitₖ 1 (0ₖ 1) (~ j)
                   ; (i = i1) → lUnitₖ 1 (0ₖ 1) (~ j)
                   ; (j = i0) → +ₖ→∙ 0 (h a) (l a) (~ k) i
                   ; (j = i1) → cong₂Funct (λ x y → x +[ 1 ]ₖ y)
                                           (Kn→ΩKn+1 0 (h a)) (Kn→ΩKn+1 0 (l a)) (~ k) i})
          (bottom i j)
       where
       bottom : I → I → coHomK 1
       bottom i j = hcomp (λ k → λ { (i = i0) → lUnitₖ 1 (0ₖ 1) (~ j)
                                   ; (i = i1) → lUnitₖ 1 (Kn→ΩKn+1 0 (l a) k) (~ j) })
                          (anotherbottom i j)

         where
         anotherbottom : I → I → coHomK 1
         anotherbottom i j =  hcomp (λ k → λ { (i = i0) → rUnitlUnit0 1 k (~ j)
                                             ; (i = i1) → rUnitlUnit0 1 k (~ j)
                                             ; (j = i0) → Kn→ΩKn+1 0 (h a) i
                                             ; (j = i1) → Kn→ΩKn+1 0 (h a) i +[ 1 ]ₖ 0ₖ 1 })
                                    (rUnitₖ 1 (Kn→ΩKn+1 0 (h a) i) (~ j))
  dHomHelperPath (suc n) h l a i j =
    hcomp (λ k → λ { (i = i0) → lUnitₖ (2 + n) (0ₖ (2 + n)) (~ j)
                   ; (i = i1) → lUnitₖ (2 + n) (0ₖ (2 + n)) (~ j)
                   ; (j = i0) → +ₖ→∙ (suc n) (h a) (l a) (~ k) i
                   ; (j = i1) → cong₂Funct (λ x y → x +[ 2 + n ]ₖ y)
                                           (Kn→ΩKn+1 (suc n) (h a)) (Kn→ΩKn+1 (suc n) (l a)) (~ k) i})
          (bottom i j)
      where
      bottom : I → I → coHomK (2 + n)
      bottom i j = hcomp (λ k → λ { (i = i0) → lUnitₖ (2 + n) (0ₖ (2 + n)) (~ j)
                                  ; (i = i1) → lUnitₖ (2 + n) (Kn→ΩKn+1 (suc n) (l a) k) (~ j) })
                         (anotherbottom i j)

        where
        anotherbottom : I → I → coHomK (2 + n)
        anotherbottom i j = hcomp (λ k → λ { (i = i0) → rUnitlUnit0 (2 + n) k (~ j)
                                           ; (i = i1) → rUnitlUnit0 (2 + n) k (~ j)
                                           ; (j = i0) → Kn→ΩKn+1 (suc n) (h a) i
                                           ; (j = i1) → Kn→ΩKn+1 (suc n) (h a) i +[ 2 + n ]ₖ (0ₖ (2 + n)) })
                                  (rUnitₖ (2 + n) (Kn→ΩKn+1 (suc n) (h a) i) (~ j))

  dHomHelper : (n : ℕ) (h l : C → coHomK n) (x : Pushout f g)
             → d-pre n (λ x → h x +[ n ]ₖ l x) x ≡ d-pre n h x +[ suc n ]ₖ d-pre n l x
  dHomHelper n h l (inl x) = sym (lUnitₖ (suc n) (0ₖ (suc n)))
  dHomHelper n h l (inr x) = sym (lUnitₖ (suc n) (0ₖ (suc n)))
  dHomHelper zero h l (push a i) j = dHomHelperPath zero h l a i j
  dHomHelper (suc n) h l (push a i) j = dHomHelperPath (suc n) h l a i j
-}
  dIsHom' : (n : ℕ) → isGroupHom (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (sRec setTruncIsSet λ a → ∣ d-pre n a ∣₂)
  dIsHom' zero = {!!}
  dIsHom' (suc n) =
    sElim2 {!!}
           λ f g → cong ∣_∣₂ (funExt λ { (inl x) → sym (rUnitₖ (2 + n) (0ₖ (2 + n)))
                                       ; (inr x) → sym (lUnitₖ (2 + n) (0ₖ (2 + n)))
                                       ; (push a i) j → {! helper2 a f g j i !}})
    where
    * = ptSn (suc n)

    helper2 : (c : C) → (f g : C → coHomK (suc n))
      → PathP (λ i → (rUnitₖ (2 + n) (0ₖ (2 + n))) (~ i) ≡ (lUnitₖ (2 + n) (0ₖ (2 + n))) (~ i))
                    (helper n (+ₖ-syntax (suc n) (f c) (g c)))
                    (λ i → +ₖ-syntax (2 + n) (helper n (f c) i) (helper n (g c) i))
    helper2 = {!!}
      where
      helper3 : (x y : coHomK (suc n))
              → PathP (λ i → (rUnitₖ (2 + n) (0ₖ (2 + n))) (~ i) ≡ (lUnitₖ (2 + n) (0ₖ (2 + n))) (~ i))
                       (trRec (isOfHLevelTrunc (4 + n) _ _) (cong ∣_∣) (Kn→ΩKn+1 (suc n) (x +[ (suc n) ]ₖ y)))
                       (cong₂ (+ₖ-syntax (2 + n)) (trRec (isOfHLevelTrunc (4 + n) _ _) (cong ∣_∣) (Kn→ΩKn+1 (suc n) x))
                                                  (trRec (isOfHLevelTrunc (4 + n) _ _) (cong ∣_∣) (Kn→ΩKn+1 (suc n) y)))
      helper3 x y i j =
        hcomp (λ k → λ { (i = i0) → trRec (isOfHLevelTrunc (4 + n) _ _) (cong ∣_∣) (Iso.rightInv (Iso-Kn-ΩKn+1 (suc n)) (∙K (suc n) (Kn→ΩKn+1 (suc n) x) (Kn→ΩKn+1 (suc n) y)) (~ k)) j
                        ; (i = i1) → (cong₂Funct (+ₖ-syntax (2 + n)) (trRec (isOfHLevelTrunc (4 + n) _ _) (cong ∣_∣) (Kn→ΩKn+1 (suc n) x))
                                                                 (trRec (isOfHLevelTrunc (4 + n) _ _) (cong ∣_∣) (Kn→ΩKn+1 (suc n) y))) (~ k) j
                        ; (j = i0) → (rUnitₖ (2 + n) (0ₖ (2 + n))) (~ i) 
                        ; (j = i1) → (lUnitₖ (2 + n) (0ₖ (2 + n))) (~ i)})
              (helper4 x y i j)
       where
       helper4 : (x y : coHomK (suc n)) → PathP (λ i → (rUnitₖ (2 + n) (0ₖ (2 + n))) (~ i) ≡ (lUnitₖ (2 + n) (0ₖ (2 + n))) (~ i))
                                                 (trRec (isOfHLevelTrunc (4 + n) _ _) (cong ∣_∣) (∙K (suc n) (Kn→ΩKn+1 (suc n) x) (Kn→ΩKn+1 (suc n) y)))
                                                 (cong (λ x → x +[ (2 + n) ]ₖ (0ₖ (2 + n))) ((trRec (isOfHLevelTrunc (4 + n) _ _) (cong ∣_∣) (Kn→ΩKn+1 (suc n) x)))
                                                   ∙ cong (λ x → (0ₖ (2 + n)) +[ (2 + n) ]ₖ x) ((trRec (isOfHLevelTrunc (4 + n) _ _) (cong ∣_∣) (Kn→ΩKn+1 (suc n) y))))
       helper4 =
         elim2 (λ _ _ → isOfHLevelPathP (3 + n) (isOfHLevelTrunc (4 + n) _ _) _ _)
                λ a b i j → {!!}
         where
         helper5 : (a b : S₊ (suc n)) → PathP (λ i → (rUnitₖ (2 + n) (0ₖ (2 + n))) (~ i) ≡ (lUnitₖ (2 + n) (0ₖ (2 + n))) (~ i))
                                               (cong ∣_∣ (ϕ * a ∙ ϕ * b))
                                               (cong (λ x → x +[ (2 + n) ]ₖ (0ₖ (2 + n))) (cong ∣_∣ (ϕ * a))
                                                 ∙ cong (λ x → (0ₖ (2 + n)) +[ (2 + n) ]ₖ x) (cong ∣_∣ (ϕ * b)))
         helper5 = sphereElim2 n (λ _ _ → isOfHLevelPathP' (suc n) {!isOfHLevelTrunc (4 + n) _ _ _ _!} _ _) {!!}
{-
           hcomp (λ k → λ { (i = i0) → rUnitₖ (2 + n) (0ₖ (2 + n)) (~ j)
                           ; (i = i1) → lUnitₖ (2 + n) {!∣ ? ∣!} (~ j) -- lUnitₖ (2 + n) ∣ ϕ * b k ∣  {!~ j!}
                           ; (j = i0) → ∣ compPath-filler (ϕ * a) (ϕ * b) k i ∣ -- ∣ compPath-filler (ϕ * a) (ϕ * b) k i ∣
                           ; (j = i1) → compPath-filler (cong (λ x → x +[ (2 + n) ]ₖ (0ₖ (2 + n))) (cong ∣_∣ (ϕ * a))) (cong (λ x → (0ₖ (2 + n)) +[ (2 + n) ]ₖ x) (cong ∣_∣ (ϕ * b)))
                                                          k i})
                 {!!}
-}

  dIsHom : (n : ℕ) → isGroupHom (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (sRec setTruncIsSet λ a → ∣ d-pre n a ∣₂)
  dIsHom zero = sElim2 {!!} λ f g → {!!}
  dIsHom (suc zero) = sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _ )
      λ f g →
        cong ∣_∣₂
          (funExt λ { (inl x) → refl
                    ; (inr x) → refl
                    ; (push c i) j → helper2 c f g j i})
    where
    helper2 : (c : C) → (f g : C → hLevelTrunc 3 S¹)
      → helper 0 (+ₖ-syntax 1 (f c) (g c))
      ≡ (λ i → +ₖ-syntax 2 (helper 0 (f c) i) (helper 0 (g c) i))
    helper2 c f g = helper3 (f c) (g c)

      where
      helper3 : (x y : hLevelTrunc 3 S¹)
              → trRec (isOfHLevelTrunc 4 _ _) (cong ∣_∣) (Kn→ΩKn+1 1 (x +[ 1 ]ₖ y))
              ≡ cong₂ (+ₖ-syntax 2) (trRec (isOfHLevelTrunc 4 _ _) (cong ∣_∣) (Kn→ΩKn+1 1 x)) (trRec (isOfHLevelTrunc 4 _ _) (cong ∣_∣) (Kn→ΩKn+1 1 y))
      helper3 x y = cong (trRec (isOfHLevelTrunc 4 _ _) (cong ∣_∣)) (Iso.rightInv (Iso-Kn-ΩKn+1 1) (∙K 1 (Kn→ΩKn+1 1 x) (Kn→ΩKn+1 1 y)))
                  ∙ helper4 x y
        where
        helper4 : (x y : hLevelTrunc 3 S¹) → trRec (isOfHLevelTrunc 4 _ _) (cong ∣_∣) (∙K 1 (Kn→ΩKn+1 1 x) (Kn→ΩKn+1 1 y))
                ≡ cong₂ (+ₖ-syntax 2) (trRec (isOfHLevelTrunc 4 _ _) (cong ∣_∣) (Kn→ΩKn+1 1 x)) (trRec (isOfHLevelTrunc 4 _ _) (cong ∣_∣) (Kn→ΩKn+1 1 y))
        helper4 = elim2 {!!} helper5
          where
          helper5 : (a b : S¹) → cong ∣_∣ (ϕ base a ∙ ϕ base b) ≡ cong₂ (+ₖ-syntax 2) (cong ∣_∣ (ϕ base a)) (cong ∣_∣ (ϕ base b))
          helper5 = wedgeConSn 0 0 (λ _ _ → isOfHLevelTrunc 4 _ _ _ _)
                                   helper6
                                   {!!}
                                   {!!} .fst
            where
            helper6 : (x : S¹) → cong ∣_∣ (ϕ base base ∙ ϕ base x) ≡
                                 cong₂ (+ₖ-syntax 2) (cong ∣_∣ (ϕ base base)) (cong ∣_∣ (ϕ base x))
            helper6 x = (λ i → cong ∣_∣ (rCancel (merid base) i ∙ ϕ base x)) ∙∙ {!!} ∙∙ {!!}
  dIsHom (suc (suc n)) = 
    sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _ )
      λ f g →
        cong ∣_∣₂
          (funExt λ { (inl x) → refl
                    ; (inr x) → refl
                    ; (push c i) j → {!!} }) --helper2 c f g j i})
    where
    {-
    helper2 : (c : C) → (f g : C → coHomK (2 + n))
      → helper (suc n) (λ x → +ₖ-syntax (2 + n) (f x) (g x)) c
      ≡ (λ i → +ₖ-syntax (3 + n) (helper (1 + n) f c i) (helper (suc n) g c i))
    helper2 c f g = elim2 {B = {!!}} {!!} {!!} (f c) (g c) -}

{-
    sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _ )
      λ f g →
        cong ∣_∣₂
          (funExt λ { (inl x) → {!ΩTrunc.decode-fun ∣ north ∣ ∣ north ∣!}
                    ; (inr x) → {!!}
                    ; (push c i) → {!!}})
  -}
  -- sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
     --              λ f g i → ∣ funExt (λ x → dHomHelper (suc n) f g x) i ∣₂

  -- d : (n : ℕ) → GroupHom (coHomGr n C) (coHomGr (suc n) (Pushout f g))
  -- GroupHom.fun (d n) = sRec setTruncIsSet λ a → ∣ d-pre n a ∣₂
  -- GroupHom.isHom (d n) = dIsHom n

  -- -- The long exact sequence
  -- Im-d⊂Ker-i : (n : ℕ) (x : ⟨ (coHomGr (suc n) (Pushout f g)) ⟩)
  --           → isInIm (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (d n) x
  --           → isInKer (coHomGr (suc n) (Pushout f g)) (×coHomGr (suc n) A B) (i (suc n)) x
  -- Im-d⊂Ker-i n = sElim (λ _ → isSetΠ λ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
  --                      λ a → pRec (isOfHLevelPath' 1 (isSet× setTruncIsSet setTruncIsSet) _ _)
  --                              (sigmaElim (λ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
  --                               λ δ b i → sRec (isSet× setTruncIsSet setTruncIsSet)
  --                                              (λ δ → ∣ (λ x → δ (inl x)) ∣₂ , ∣ (λ x → δ (inr x)) ∣₂ ) (b (~ i)))


  -- Ker-i⊂Im-d : (n : ℕ) (x : ⟨ coHomGr (suc n) (Pushout f g) ⟩)
  --            → isInKer (coHomGr (suc n) (Pushout f g)) (×coHomGr (suc n) A B) (i (suc n)) x
  --            → isInIm (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (d n) x
  -- Ker-i⊂Im-d zero =
  --    sElim (λ _ → isSetΠ λ _ → isProp→isSet propTruncIsProp)
  --          λ a p → pRec {A = (λ x → a (inl x)) ≡ λ _ → 0ₖ 1}
  --                       (isProp→ propTruncIsProp)
  --                       (λ p1 → pRec propTruncIsProp λ p2 → ∣ ∣ (λ c → ΩKn+1→Kn 0 (sym (cong (λ F → F (f c)) p1)
  --                                                                                    ∙∙ cong a (push c)
  --                                                                                    ∙∙ cong (λ F → F (g c)) p2)) ∣₂
  --                                                                            , cong ∣_∣₂ (funExt (λ δ → helper a p1 p2 δ)) ∣₁)
  --                                      (Iso.fun PathIdTrunc₀Iso (cong fst p))
  --                                      (Iso.fun PathIdTrunc₀Iso (cong snd p))

  --     where
  --     helper : (F : (Pushout f g) → hLevelTrunc 3 (S₊ 1))
  --              (p1 : Path (_ → hLevelTrunc 3 (S₊ 1)) (λ a₁ → F (inl a₁)) (λ _ → ∣ base ∣))
  --              (p2 : Path (_ → hLevelTrunc 3 (S₊ 1)) (λ a₁ → F (inr a₁)) (λ _ → ∣ base ∣))
  --            → (δ : Pushout f g)
  --            → d-pre 0 (λ c → ΩKn+1→Kn 0 ((λ i₁ → p1 (~ i₁) (f c))
  --                                                    ∙∙ cong F (push c)
  --                                                    ∙∙ cong (λ F → F (g c)) p2)) δ
  --             ≡ F δ
  --     helper F p1 p2 (inl x) = sym (cong (λ f → f x) p1)
  --     helper F p1 p2 (inr x) = sym (cong (λ f → f x) p2)
  --     helper F p1 p2 (push a i) j =
  --       hcomp (λ k → λ { (i = i0) → p1 (~ j) (f a)
  --                      ; (i = i1) → p2 (~ j) (g a)
  --                      ; (j = i0) → Iso.rightInv (Iso-Kn-ΩKn+1 0) ((λ i₁ → p1 (~ i₁) (f a))
  --                                                                      ∙∙ cong F (push a)
  --                                                                      ∙∙ cong (λ F₁ → F₁ (g a)) p2) (~ k) i
  --                       ; (j = i1) → F (push a i)})
  --             (doubleCompPath-filler (sym (cong (λ F → F (f a)) p1)) (cong F (push a)) (cong (λ F → F (g a)) p2) (~ j) i)
  -- Ker-i⊂Im-d (suc n) =
  --   sElim (λ _ → isSetΠ λ _ → isProp→isSet propTruncIsProp)
  --          λ a p → pRec {A = (λ x → a (inl x)) ≡ λ _ → 0ₖ (2 + n)} (isProp→ propTruncIsProp)
  --                       (λ p1 → pRec propTruncIsProp λ p2 → ∣ ∣ (λ c → ΩKn+1→Kn (suc n) (sym (cong (λ F → F (f c)) p1)
  --                                                                                          ∙∙ cong a (push c)
  --                                                                                          ∙∙ cong (λ F → F (g c)) p2)) ∣₂
  --                                                                            , cong ∣_∣₂ (funExt (λ δ → helper a p1 p2 δ)) ∣₁)
  --                                      (Iso.fun PathIdTrunc₀Iso (cong fst p))
  --                                      (Iso.fun PathIdTrunc₀Iso (cong snd p))

  --     where
  --     helper : (F : (Pushout f g) → hLevelTrunc (4 + n) (S₊ (2 + n)))
  --              (p1 : Path (_ → hLevelTrunc (4 + n) (S₊ (2 + n))) (λ a₁ → F (inl a₁)) (λ _ → ∣ north ∣))
  --              (p2 : Path (_ → hLevelTrunc (4 + n) (S₊ (2 + n))) (λ a₁ → F (inr a₁)) (λ _ → ∣ north ∣))
  --            → (δ : (Pushout f g))
  --            → d-pre (suc n) (λ c → ΩKn+1→Kn (suc n) ((λ i₁ → p1 (~ i₁) (f c))
  --                                                    ∙∙ cong F (push c)
  --                                                    ∙∙ cong (λ F → F (g c)) p2)) δ
  --             ≡ F δ
  --     helper F p1 p2 (inl x) = sym (cong (λ f → f x) p1)
  --     helper F p1 p2 (inr x) = sym (cong (λ f → f x) p2)
  --     helper F p1 p2 (push a i) j =
  --       hcomp (λ k → λ { (i = i0) → p1 (~ j) (f a)
  --                      ; (i = i1) → p2 (~ j) (g a)
  --                      ; (j = i0) → Iso.rightInv (Iso-Kn-ΩKn+1 (suc n)) ((λ i₁ → p1 (~ i₁) (f a))
  --                                                                          ∙∙ cong F (push a)
  --                                                                          ∙∙ cong (λ F₁ → F₁ (g a)) p2) (~ k) i
  --                      ; (j = i1) → F (push a i)})
  --             (doubleCompPath-filler (sym (cong (λ F → F (f a)) p1)) (cong F (push a)) (cong (λ F → F (g a)) p2) (~ j) i)

  -- open GroupHom

  -- Im-i⊂Ker-Δ : (n : ℕ) (x : ⟨ ×coHomGr n A B ⟩)
  --           → isInIm (coHomGr n (Pushout f g)) (×coHomGr n A B) (i n) x
  --           → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) x
  -- Im-i⊂Ker-Δ n (Fa , Fb) =
  --   sElim {B = λ Fa → (Fb : _) → isInIm (coHomGr n (Pushout f g)) (×coHomGr n A B) (i n) (Fa , Fb)
  --                              → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) (Fa , Fb)}
  --         (λ _ → isSetΠ2 λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
  --         (λ Fa → sElim (λ _ → isSetΠ λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
  --                       λ Fb → pRec (setTruncIsSet _ _)
  --                                    (sigmaElim (λ x → isProp→isSet (setTruncIsSet _ _))
  --                                               λ Fd p → helper n Fa Fb Fd p))
  --         Fa
  --         Fb
  --   where
  --   helper : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n) (Fd : (Pushout f g) → coHomK n)
  --         → (fun (i n) ∣ Fd ∣₂ ≡ (∣ Fa ∣₂ , ∣ Fb ∣₂))
  --         → (fun (Δ n)) (∣ Fa ∣₂ , ∣ Fb ∣₂) ≡ 0ₕ n
  --   helper zero Fa Fb Fd p = cong (fun (Δ zero)) (sym p)
  --                          ∙∙ (λ i → ∣ (λ x → Fd (inl (f x))) ∣₂ -[ 0 ]ₕ ∣ (λ x → Fd (push x (~ i))) ∣₂ )
  --                          ∙∙ cancelₕ 0 ∣ (λ x → Fd (inl (f x))) ∣₂
  --   helper (suc n) Fa Fb Fd p = cong (fun (Δ (suc n))) (sym p)
  --                             ∙∙ (λ i → ∣ (λ x → Fd (inl (f x))) ∣₂ -[ (suc n) ]ₕ ∣ (λ x → Fd (push x (~ i))) ∣₂)
  --                             ∙∙ cancelₕ (suc n) ∣ (λ x → Fd (inl (f x))) ∣₂

  -- Ker-Δ⊂Im-i : (n : ℕ) (a : ⟨ ×coHomGr n A B ⟩)
  --           → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) a
  --           → isInIm (coHomGr n (Pushout f g)) (×coHomGr n A B) (i n) a
  -- Ker-Δ⊂Im-i n = prodElim (λ _ → isSetΠ (λ _ → isProp→isSet propTruncIsProp))
  --                         (λ Fa Fb p → pRec propTruncIsProp
  --                                           (λ q → ∣ ∣ helpFun Fa Fb q ∣₂ , refl ∣₁)
  --                                           (helper Fa Fb p))
  --   where
  --   helper : (Fa : A → coHomK n) (Fb : B → coHomK n)
  --          → fun (Δ n) (∣ Fa ∣₂ , ∣ Fb ∣₂) ≡ 0ₕ n
  --          → ∥ Path (_ → _) (λ c → Fa (f c)) (λ c → Fb (g c)) ∥₁
  --   helper Fa Fb p = Iso.fun PathIdTrunc₀Iso
  --                              (sym (-+cancelₕ n ∣ (λ c → Fa (f c)) ∣₂ ∣ (λ c → Fb (g c)) ∣₂)
  --                              ∙∙ cong (λ x → x +[ n ]ₕ ∣ (λ c → Fb (g c)) ∣₂) p
  --                              ∙∙ lUnitₕ n _)

  --   helpFun : (Fa : A → coHomK n) (Fb : B → coHomK n)
  --           → ((λ c → Fa (f c)) ≡ (λ c → Fb (g c)))
  --           → Pushout f g → coHomK n
  --   helpFun Fa Fb p (inl x) = Fa x
  --   helpFun Fa Fb p (inr x) = Fb x
  --   helpFun Fa Fb p (push a i) = p i a


  -- private
  --   distrHelper : (n : ℕ) (p q : _)
  --               → ΩKn+1→Kn n p +[ n ]ₖ (-[ n ]ₖ ΩKn+1→Kn n q) ≡ ΩKn+1→Kn n (p ∙ sym q)
  --   distrHelper n p q i =
  --       ΩKn+1→Kn n (Iso.rightInv (Iso-Kn-ΩKn+1 n) p i
  --     ∙ Iso.rightInv (Iso-Kn-ΩKn+1 n) (sym (Iso.rightInv (Iso-Kn-ΩKn+1 n) q i)) i)

  -- Ker-d⊂Im-Δ : (n : ℕ) (a : coHom n C)
  --            → isInKer (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (d n) a
  --            → isInIm (×coHomGr n A B) (coHomGr n C) (Δ n) a
  -- Ker-d⊂Im-Δ zero =
  --   sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
  --         λ Fc p → pRec propTruncIsProp (λ p → ∣ (∣ (λ a → ΩKn+1→Kn 0 (cong (λ f → f (inl a)) p)) ∣₂ ,
  --                                                    ∣ (λ b → ΩKn+1→Kn 0 (cong (λ f → f (inr b)) p)) ∣₂) ,
  --                                                 Iso.inv (PathIdTrunc₀Iso) ∣ funExt (λ c → helper2 Fc p c) ∣₁ ∣₁)
  --                                        (Iso.fun (PathIdTrunc₀Iso) p)

  --   where

  --   helper2 : (Fc : C → coHomK 0)
  --             (p : d-pre 0 Fc ≡ (λ _ → ∣ base ∣)) (c : C)
  --           → ΩKn+1→Kn 0 (λ i₁ → p i₁ (inl (f c))) -[ 0 ]ₖ (ΩKn+1→Kn 0 (λ i₁ → p i₁ (inr (g c)))) ≡ Fc c
  --   helper2 Fc p c = cong₂ (λ x y → ΩKn+1→Kn 0 (x ∙ sym y)) (Iso.rightInv (Iso-Kn-ΩKn+1 0) (λ i₁ → p i₁ (inl (f c))))
  --                                                           (Iso.rightInv (Iso-Kn-ΩKn+1 0) (λ i₁ → p i₁ (inr (g c))))
  --                 ∙∙ cong (ΩKn+1→Kn 0) (sym ((PathP→compPathR (cong (λ f → cong f (push c)) p))
  --                             ∙ (λ i → (λ i₁ → p i₁ (inl (f c)))
  --                                     ∙ (lUnit (sym (λ i₁ → p i₁ (inr (g c)))) (~ i)))))
  --                 ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 zero) (Fc c)
  -- Ker-d⊂Im-Δ (suc n) =
  --   sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
  --         λ Fc p → pRec propTruncIsProp (λ p → ∣ (∣ (λ a → ΩKn+1→Kn (suc n) (cong (λ f → f (inl a)) p)) ∣₂ ,
  --                                                    ∣ (λ b → ΩKn+1→Kn (suc n) (cong (λ f → f (inr b)) p)) ∣₂) ,
  --                                                 Iso.inv (PathIdTrunc₀Iso) ∣ funExt (λ c → helper2 Fc p c) ∣₁ ∣₁)
  --                                        (Iso.fun (PathIdTrunc₀Iso) p)

  --   where

  --   helper2 : (Fc : C → coHomK (suc n))
  --             (p : d-pre (suc n) Fc ≡ (λ _ → ∣ north ∣)) (c : C)
  --           → ΩKn+1→Kn (suc n) (λ i₁ → p i₁ (inl (f c))) -[ (suc n) ]ₖ (ΩKn+1→Kn (suc n) (λ i₁ → p i₁ (inr (g c)))) ≡ Fc c
  --   helper2 Fc p c = cong₂ (λ x y → ΩKn+1→Kn (suc n) (x ∙ sym y)) (Iso.rightInv (Iso-Kn-ΩKn+1 (suc n)) (λ i₁ → p i₁ (inl (f c))))
  --                                                                  (Iso.rightInv (Iso-Kn-ΩKn+1 (suc n)) (λ i₁ → p i₁ (inr (g c))))
  --                 ∙∙ cong (ΩKn+1→Kn (suc n)) (sym ((PathP→compPathR (cong (λ f → cong f (push c)) p))
  --                             ∙ (λ i → (λ i₁ → p i₁ (inl (f c)))
  --                                     ∙ (lUnit (sym (λ i₁ → p i₁ (inr (g c)))) (~ i)))))
  --                 ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 (suc n)) (Fc c)

  -- Im-Δ⊂Ker-d : (n : ℕ) (a : coHom n C)
  --            → isInIm (×coHomGr n A B) (coHomGr n C) (Δ n) a
  --            → isInKer (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (d n) a
  -- Im-Δ⊂Ker-d n =
  --   sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
  --         λ Fc → pRec (isOfHLevelPath' 1 setTruncIsSet _ _)
  --                      (sigmaProdElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
  --                                     λ Fa Fb p → pRec (isOfHLevelPath' 1 setTruncIsSet _ _)
  --                                                       (λ q → ((λ i → fun (d n) ∣ (q (~ i)) ∣₂) ∙ dΔ-Id n Fa Fb))
  --                                                       (Iso.fun (PathIdTrunc₀Iso) p))

  --   where
  --   d-preLeftId : (n : ℕ) (Fa : A → coHomK n)(d : (Pushout f g))
  --               → d-pre n (Fa ∘ f) d ≡ 0ₖ (suc n)
  --   d-preLeftId zero Fa (inl x) = Kn→ΩKn+1 0 (Fa x)
  --   d-preLeftId (suc n) Fa (inl x) = Kn→ΩKn+1 (suc n) (Fa x)
  --   d-preLeftId zero Fa (inr x) = refl
  --   d-preLeftId (suc n) Fa (inr x) = refl
  --   d-preLeftId zero Fa (push a i) j = Kn→ΩKn+1 zero (Fa (f a)) (j ∨ i)
  --   d-preLeftId (suc n) Fa (push a i) j = Kn→ΩKn+1 (suc n) (Fa (f a)) (j ∨ i)

  --   d-preRightId : (n : ℕ) (Fb : B → coHomK n) (d : (Pushout f g))
  --               → d-pre n (Fb ∘ g) d ≡ 0ₖ (suc n)
  --   d-preRightId n Fb (inl x) = refl
  --   d-preRightId zero Fb (inr x) = sym (Kn→ΩKn+1 0 (Fb x))
  --   d-preRightId (suc n) Fb (inr x) = sym (Kn→ΩKn+1 (suc n) (Fb x))
  --   d-preRightId zero Fb (push a i) j = Kn→ΩKn+1 zero (Fb (g a)) (~ j ∧ i)
  --   d-preRightId (suc n) Fb (push a i) j = Kn→ΩKn+1 (suc n) (Fb (g a)) (~ j ∧ i)

  --   dΔ-Id : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n)
  --           → fun (d n) (fun (Δ n) (∣ Fa ∣₂ , ∣ Fb ∣₂)) ≡ 0ₕ (suc n)
  --   dΔ-Id zero Fa Fb = -distrLemma 0 1 (d zero) ∣ Fa ∘ f ∣₂ ∣ Fb ∘ g ∣₂
  --                   ∙∙ (λ i → ∣ (λ x → d-preLeftId zero Fa x i) ∣₂ -[ 1 ]ₕ ∣ (λ x → d-preRightId zero Fb x i) ∣₂)
  --                   ∙∙ cancelₕ 1 (0ₕ 1)
  --   dΔ-Id (suc n) Fa Fb = -distrLemma (suc n) (2 + n) (d (suc n)) ∣ Fa ∘ f ∣₂ ∣ Fb ∘ g ∣₂
  --                   ∙∙ (λ i → ∣ (λ x → d-preLeftId (suc n) Fa x i) ∣₂ -[ (2 + n) ]ₕ ∣ (λ x → d-preRightId (suc n) Fb x i) ∣₂)
  --                   ∙∙ cancelₕ (2 + n) (0ₕ (2 + n))
