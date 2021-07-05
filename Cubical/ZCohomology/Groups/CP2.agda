{-# OPTIONS --safe #-}
module Cubical.ZCohomology.Groups.CP2 where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Int
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Algebra.Group
  renaming (ℤ to ℤGroup) hiding (Unit)

open import Cubical.HITs.Pushout
open import Cubical.HITs.S1 renaming (_·_ to _*_) hiding (decode ; encode)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Hopf
open import Cubical.HITs.Join
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim2 to pElim2 ; ∣_∣ to ∣_∣₁)


open IsGroupHom
open Iso

CP² : Type
CP² = Pushout {A = TotalHopf} fst λ _ → tt

open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec)
CP²' : Type
CP²' = Pushout {A = TotalHopf'} fst λ _ → tt

module M = MV (S₊ 2) Unit TotalHopf' fst (λ _ → tt)
t : coHom 3 TotalHopf' → coHom 4 CP²'
t = fst (M.d 3)

isEq-t : isEquiv t
isEq-t =
  record { equiv-proof = sElim (λ _ → isProp→isSet isPropIsContr)
    λ f → pRec isPropIsContr
     (λ p2 → pRec isPropIsContr
      (λ p → (∣ (λ x → ΩKn+1→Kn _ (sym (funExt⁻ p (fst x)) ∙∙ cong f (push x)  ∙∙ p2)) ∣₂
      , cong ∣_∣₂ (funExt λ { (inl x) → sym (funExt⁻ p x)
               ; (inr x) → sym p2
               ; (push a i) → main f p p2 a i}))
      , uncurry (sElim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 (isSetΣ squash₂ (λ _ → isOfHLevelPath 2 squash₂ _ _)) _ _))
                λ g id → Σ≡Prop (λ _ → squash₂ _ _)
                       (pRec (squash₂ _ _)
                         (λ id2 → pRec (squash₂ _ _)
                                    (λ pp → pRec {!!} {!!}
                                    (main4 f g p2 id2))
                                    (main3 f g p id2))
                         (Iso.fun PathIdTrunc₀Iso id))))
       (help (f ∘ inl))) (help2 (f (inr tt))) }
  where

  main2 : (f : CP²' → coHomK 4) (g : TotalHopf' → coHomK 3) (id2 : M.d-pre _ g ≡ f) (p : (λ x → f (inl x)) ≡ (λ _ → 0ₖ 4)) (p2 : _)
        → PathP (λ i → id2 (~ i) ∘ inl ≡ λ _ → 0ₖ _) p refl
        → PathP (λ i → id2 (~ i) (inr tt) ≡ 0ₖ _) p2 refl
        → (x : _) → ΩKn+1→Kn 3 ((λ i → funExt⁻ p (fst x) (~ i)) ∙∙ cong f (push x) ∙∙ p2) ≡ g x
  main2 f g = {!!}
    where
    help : (p : (M.d-pre 3 g ∘ inl) ≡ (λ _ → 0ₖ 4)) (p2 : _) (x : _)
        → ((λ i → p (~ i) (fst x)) ∙∙ cong (M.d-pre (suc (suc (suc zero))) g) (push x) ∙∙ p2) ≡ Kn→ΩKn+1 (suc (suc (suc zero))) (g x)
    help p p2 x i j = {!!}
    {-
    ———— Boundary ——————————————————————————————————————————————
i = i0 ⊢ ((λ i₁ → funExt⁻ p (fst x) (~ i₁)) ∙∙ cong f (push x) ∙∙
          p2)
         j
i = i1 ⊢ Kn→ΩKn+1 3 (g x) j
j = i0 ⊢ 0ₖ 4
j = i1 ⊢ ∣ ptSn (suc 3) ∣
    -}

  main : (f : CP²' → coHomK 4) (p : (λ x → f (inl x)) ≡ (λ _ → 0ₖ 4)) (p2 : _) (a : _) → PathP (λ i → Kn→ΩKn+1 3
      (ΩKn+1→Kn 3
       ((λ i₁ → funExt⁻ p (fst a) (~ i₁)) ∙∙ (λ i₁ → f (push a i₁)) ∙∙
        p2))
      i ≡ f (push a i)) (sym (funExt⁻ p (fst a))) (sym p2)
  main f p p2 a i j =
    hcomp (λ k → λ { (i = i0) → p (~ j) (fst a)
                    ; (i = i1) → sym p2 j
                    ; (j = i0) → Iso.rightInv (Iso-Kn-ΩKn+1 _) (sym (funExt⁻ p (fst a)) ∙∙ cong f (push a) ∙∙ p2) (~ k) i
                    ; (j = i1) → f (push a i)})
          (doubleCompPath-filler (sym (funExt⁻ p (fst a))) (cong f (push a)) p2 (~ j) i)

  help2 : (x : coHomK 4) → ∥ x ≡ 0ₖ _ ∥
  help2 = trElim (λ _ → isProp→isOfHLevelSuc 5 squash)
            (sphereElim _ (λ _ → isProp→isOfHLevelSuc 3 squash) ∣ refl ∣₁)

  help : (f : S₊ 2 → coHomK 4) → ∥ (f ≡ λ _ → 0ₖ _) ∥
  help f = Iso.fun PathIdTrunc₀Iso (isOfHLevelRetractFromIso 1 (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p))) isPropUnit _ _)

  main4 : (f : CP²' → coHomK 4) (g : TotalHopf' → coHomK 3) (p : f (inr tt) ≡ 0ₖ _) (id2 : M.d-pre 3 g ≡ f)
       → ∥ PathP (λ i → id2 (~ i) (inr tt) ≡ 0ₖ _) p refl ∥
  main4 f g p id2 =
    trRec (isProp→isOfHLevelSuc 2 squash)
      (λ P → ∣ toPathP P ∣₁)
      (Iso.fun (PathIdTruncIso _)
       (isContr→isProp (isConnectedPathKn _ (0ₖ _) (0ₖ _))
        ∣ transport (λ i → id2 (~ i) (inr tt) ≡ 0ₖ _) p ∣ ∣ refl ∣))

  main3 : (f : CP²' → coHomK 4) (g : TotalHopf' → coHomK 3) (p : f ∘ inl ≡ λ _ → 0ₖ _) (id2 : M.d-pre 3 g ≡ f)
       → ∥ PathP (λ i → id2 (~ i) ∘ inl ≡ λ _ → 0ₖ _) p refl ∥
  main3 f g p id2 =
    pRec squash
      (λ P → ∣ {!!} ∣₁)
      {!isConnectedΠ!}

test : coHomRed 4 (CP²' , inr tt) → coHom 3 (TotalHopf')
test = sRec squash₂ λ f → ∣ uncurry (λ x y → {!!}) ∣₂ -- x → ΩKn+1→Kn _ ({!f ∘ inl!} ∙∙ cong (fst f) (push x) ∙∙ {!!})
  where
  Code→Code : (x : _) → Code (suc (suc zero)) x → Code (suc (suc zero)) ∣ north ∣
  Code→Code = trElim {!!} {!!}
  z : isSet (S₊∙ 2 →∙ coHomK-ptd 4)
  z = {!!}
  code↑ : (x : _) → (f : _ → _) → Code zero x → Code (suc (suc zero)) (f x)
  code↑ x f = {!!}
  s : {!f !}
  s = {!!}

-- module M = MV (S₊ 2) Unit TotalHopf fst (λ _ → tt)

-- H²CP²≅ℤ : GroupIso (coHomGr 2 CP²) ℤGroup
-- H²CP²≅ℤ = compGroupIso (BijectionIso→GroupIso bij)
--             (compGroupIso (invGroupIso trivIso) (Hⁿ-Sⁿ≅ℤ 1))
--   where
--   isContrH¹TotalHopf : isContr (coHom 1 TotalHopf)
--   isContrH¹TotalHopf =
--     isOfHLevelRetractFromIso 0 (setTruncIso (domIso (invIso (IsoS³TotalHopf))))
--       (isOfHLevelRetractFromIso 0 ((fst (H¹-Sⁿ≅0 1))) isContrUnit)

--   isContrH²TotalHopf : isContr (coHom 2 TotalHopf)
--   isContrH²TotalHopf =
--     isOfHLevelRetractFromIso 0 (setTruncIso (domIso (invIso (IsoS³TotalHopf))))
--       ((isOfHLevelRetractFromIso 0
--         (fst (Hⁿ-Sᵐ≅0 1 2 λ p → snotz (sym (cong predℕ p)))) isContrUnit))

--   trivIso : GroupIso (coHomGr 2 (Susp S¹)) (×coHomGr 2 (Susp S¹) Unit)
--   fun (fst trivIso) x = x , 0ₕ _
--   inv (fst trivIso) = fst
--   rightInv (fst trivIso) (x , p) =
--     ΣPathP (refl , isContr→isProp (isContrHⁿ-Unit 1) _ _)
--   leftInv (fst trivIso) x = refl
--   snd trivIso = makeIsGroupHom λ _ _ → refl

--   bij : BijectionIso (coHomGr 2 CP²) (×coHomGr 2 (Susp S¹) Unit)
--   BijectionIso.fun bij = M.i 2
--   BijectionIso.inj bij x p =
--     pRec (squash₂ _ _)
--       (uncurry (λ z q
--         → sym q
--         ∙∙ cong (fst (M.d 1)) (isContr→isProp isContrH¹TotalHopf z (0ₕ _))
--         ∙∙ (M.d 1) .snd .pres1))
--       (M.Ker-i⊂Im-d 1 x p)
--     where
--     help : isInIm (M.d 1) x
--     help = M.Ker-i⊂Im-d 1 x p
--   BijectionIso.surj bij y =
--     M.Ker-Δ⊂Im-i 2 y (isContr→isProp isContrH²TotalHopf _ _)

-- H⁴CP²≅ℤ : GroupIso (coHomGr 4 CP²) ℤGroup
-- H⁴CP²≅ℤ = compGroupIso (invGroupIso (BijectionIso→GroupIso bij))
--           (compGroupIso help (Hⁿ-Sⁿ≅ℤ 2))
--   where
--   help : GroupIso (coHomGr 3 TotalHopf) (coHomGr 3 (S₊ 3))
--   help = isoType→isoCohom 3 (invIso IsoS³TotalHopf)

--   bij : BijectionIso (coHomGr 3 TotalHopf) (coHomGr 4 CP²)
--   BijectionIso.fun bij = M.d 3
--   BijectionIso.inj bij x p =
--     pRec (squash₂ _ _)
--          (uncurry (λ z q →
--              sym q
--           ∙∙ cong (M.Δ 3 .fst)
--                 (isOfHLevelΣ 1 (isContr→isProp
--                   (isOfHLevelRetractFromIso 0
--                     (fst (Hⁿ-Sᵐ≅0 2 1 λ p → snotz (cong predℕ p))) isContrUnit))
--                 (λ _ → isContr→isProp (isContrHⁿ-Unit 2))
--                 z (0ₕ _ , 0ₕ _))
--           ∙∙ M.Δ 3 .snd .pres1))
--          (M.Ker-d⊂Im-Δ _ x p)
--   BijectionIso.surj bij y =
--     M.Ker-i⊂Im-d 3 y (isOfHLevelΣ 1
--       (isContr→isProp (isOfHLevelRetractFromIso 0
--         (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p))) isContrUnit))
--         (λ _ → isContr→isProp (isContrHⁿ-Unit _)) _ _)


-- one : coHom 2 CP²
-- one = Iso.inv (fst H²CP²≅ℤ) 1
-- open import Cubical.HITs.Truncation
-- oneDirect' : CP² → coHomK 2
-- oneDirect' = (λ { (inl x) → ∣ x ∣ ; (inr x) → ∣ north ∣
--                  ; (push (x , y) i) → t x y i} )
--   where
--   t : (x : S₊ 2) → (y : HopfSuspS¹ x) → Path (coHomK 2) ∣ x ∣ (0ₖ 2)
--   t north y j = ∣ (merid base ∙ sym (merid y)) j ∣
--   t south y j = ∣ merid y (~ j) ∣
--   t (merid a i) y = h a (~ i) y
--     where
--     eq : (x y : S¹) → ∣ x ∣ +ₖ ∣ y ∣ ≡ ∣ x * y ∣
--     eq = wedgeconFun _ _ (λ _ _ → isOfHLevelTrunc 3 _ _)
--           (λ _ → refl)
--           (λ { base → refl ; (loop i) → refl})
--           refl
--     toho : (x y : S¹) → Kn→ΩKn+1 1 ∣ x * y ∣ ≡ Kn→ΩKn+1 1 ∣ x ∣ ∙ Kn→ΩKn+1 1 ∣ y ∣
--     toho x y = cong (Kn→ΩKn+1 _) (sym (eq x y)) ∙ Kn→ΩKn+1-hom 1 ∣ x ∣ ∣ y ∣
--     y*base : (y : S¹) → y * base ≡ y
--     y*base base = refl
--     y*base (loop i) = refl

--     z : (x y : S¹) → Path (Path (coHomK 2) _ _) (cong ∣_∣ (merid (x * y))) (Kn→ΩKn+1 1 ∣ x ∣ ∙ λ i → ∣ merid y i ∣)
--     z x y = rUnit _
--          ∙∙ (λ i → cong ∣_∣ (compPath-filler (merid (x * y)) (sym (merid base)) i) ∙ λ j → ∣ merid base (~ i ∨ j) ∣)
--          ∙∙ cong (_∙ (cong ∣_∣ (merid base))) (toho x y)
--          ∙∙ sym (assoc (Kn→ΩKn+1 1 ∣ x ∣) (Kn→ΩKn+1 1 ∣ y ∣) (cong ∣_∣ (merid base)))
--          ∙∙ cong (Kn→ΩKn+1 1 ∣ x ∣ ∙_) ((λ k → (λ i → ∣ compPath-filler (merid y) (sym (merid base)) (~ k) i ∣) ∙ λ j → ∣ merid base (j ∨ k) ∣) ∙ sym (rUnit _))
--     h : (x : S¹) → PathP (λ j  → Glue S¹ (Border x (~ j)) → Path (coHomK 2) ∣ merid x (~ j) ∣ (0ₖ 2)) (λ x i → ∣ merid x (~ i) ∣) (λ x i → ∣ (merid base ∙ sym (merid x)) i ∣)
--     h x = toPathP (funExt (λ y → (λ k → transp (λ i → Path (coHomK 2) ∣ merid x (~ i ∧ ~ k) ∣ (0ₖ 2)) k
--                                         λ j → ∣ compPath-filler' (merid x) (sym (merid (x * y))) k j ∣)
--                                         ∙∙ cong-∙ ∣_∣ (merid x) (sym (merid (x * y)))
--                                         ∙∙ cong (cong ∣_∣ (merid x) ∙_) (cong sym (z x y)
--                                           ∙∙ symDistr (Kn→ΩKn+1 1 ∣ x ∣) (cong ∣_∣ (merid y))
--                                           ∙∙ cong (sym (cong ∣_∣ (merid y)) ∙_) (cong (cong ∣_∣) (symDistr (merid x) (sym (merid base)))))
--                                         ∙∙ assoc _ _ _
--                                         ∙∙ isCommΩK 2 ((λ i₁ → ∣ merid x i₁ ∣) ∙ (λ i₁ → ∣ merid y (~ i₁) ∣))
--                                                        (λ i₁ → ∣ (sym (λ i₂ → merid base (~ i₂)) ∙ sym (merid x)) i₁ ∣)
--                                         ∙∙ (λ j → (λ i → ∣ compPath-filler (merid base) (sym (merid x)) (~ j) i ∣)
--                                                  ∙ λ i → compPath-filler' (cong ∣_∣ (merid x)) (cong ∣_∣ (sym (merid y))) (~ j) i)
--                                         ∙∙ sym (congFunct ∣_∣ (merid base) (sym (merid y)))))

-- oneDirect : coHom 2 CP²
-- oneDirect = ∣ oneDirect' ∣₂ 
-- Z : coHom 2 CP² → ℤ
-- Z = Iso.fun (fst H²CP²≅ℤ)


-- theGuy : CP² → coHomK 4
-- theGuy x = oneDirect' x ⌣ₖ oneDirect' x

-- theGuyId : (x : _) → theGuy (inl x) ≡ 0ₖ _
-- theGuyId north = refl
-- theGuyId south = refl
-- theGuyId (merid a i) k = h i k
--   where
--   c : cong (theGuy ∘ inl) (merid a) ≡ refl
--   c = (λ k i → Kn→ΩKn+1 _ (_⌣ₖ_ {n = 1} {m = 2} ∣ a ∣ ∣ merid a i ∣) i)
--    ∙∙ {!!}
--    ∙∙ {!!}
--   open import Cubical.Foundations.Path
--   h : PathP (λ i → theGuy (inl (merid a i)) ≡ 0ₖ 4) refl refl
--   h i j = hcomp (λ k → λ {(i = i0) → 0ₖ 4 ; (i = i1) → 0ₖ 4 ; (j = i0) → c (~ k) i ; (j = i1) → 0ₖ 4})
--                  (0ₖ 4)

-- test : Z oneDirect ≡ 1
-- test = refl

-- two : coHom 4 CP²
-- two = oneDirect ⌣ oneDirect

-- t : coHom 4 CP² → coHom 3 TotalHopf
-- t =
--   sRec squash₂
--     λ f → ∣ (λ x → ΩKn+1→Kn _ ({!!} ∙∙ cong theGuy (push x) ∙∙ {!x!})) ∣₂
--       where
--       ttt : (f : S₊ 2 → coHomK 4) → (f north ≡ 0ₖ _) → (x : _) → f x ≡ 0ₖ _
--       ttt f p north = p
--       ttt f p south = cong f (sym (merid base)) ∙ p
--       ttt f p (merid base i) k = compPath-filler' (cong f (sym (merid base))) p i k
--       ttt f p (merid (loop i) j) k = {!compPath-filler' (λ i₁ → f (merid (loop i) (~ i₁))) p j k!}

-- test2 : Iso.fun (fst H⁴CP²≅ℤ) (oneDirect ⌣ oneDirect) ≡ 1
-- test2 = {!!}

-- three : coHom 4 CP²
-- three = sRec squash₂ (λ f → ∣ (λ x → f x ⌣ₖ f x) ∣₂) one

-- s : coHom 3 (S₊ 3)
-- s = sRec {!!} (λ f → {!!}) two

-- -- Another Brunerie number
-- ℤ→HⁿCP²→ℤ : ℤ → ℤ
-- ℤ→HⁿCP²→ℤ x =
--   Iso.fun (fst H⁴CP²≅ℤ)
--     (Iso.inv (fst H²CP²≅ℤ) x ⌣ Iso.inv (fst H²CP²≅ℤ) x)

-- brunerie2 : ℤ
-- brunerie2 = ℤ→HⁿCP²→ℤ 1

-- {-
-- |brunerie2|≡1 : abs (ℤ→HⁿCP²→ℤ 1) ≡ 1
-- |brunerie2|≡1 = refl
-- -}

