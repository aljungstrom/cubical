{-# OPTIONS --safe --experimental-lossy-unification #-}
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
open import Cubical.HITs.S1
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

charaFSpace : (n : ℕ)
  → Iso (coHom n CP²)
      ∥ (Σ[ x ∈ coHomK n ]
        ∥ (Σ[ f ∈ (S₊ 2 → coHomK n) ] ∥ (((a : TotalHopf) → f (fst a) ≡ x)) ∥₂) ∥₂) ∥₂
fun (charaFSpace n) = sMap λ f → (f (inr tt)) , ∣ (f ∘ inl) , ∣ (λ a → cong f (push a)) ∣₂ ∣₂
inv (charaFSpace n) =
  sRec squash₂
    (uncurry
      λ a₀ → sRec squash₂
        (uncurry λ f → sRec squash₂
          λ p → ∣ (λ { (inl x) → f x ; (inr x) → a₀ ; (push a i) → p a i}) ∣₂))
rightInv (charaFSpace n) =
  sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
    (uncurry λ _ →
      sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
        (uncurry λ _ → sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
          λ _ → refl))
leftInv (charaFSpace n) =
  sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
    λ _ → cong ∣_∣₂ (funExt λ { (inl x) → refl
                              ; (inr x) → refl
                              ; (push a i) → refl})

open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec ; map to trMap)
open import Cubical.Homotopy.Loopspace

wah : hLevelTrunc 3 (S₊ 2 → coHomK 4) → TypeOfHLevel ℓ-zero 2
wah = trRec (isOfHLevelTypeOfHLevel 2) λ f → ∥ ((a : TotalHopf) → f (fst a) ≡ 0ₖ 4) ∥₂ , squash₂

charaFSpace2 : Iso
      ∥ (Σ[ x ∈ coHomK 4 ]
        ∥ (Σ[ f ∈ (S₊ 2 → coHomK 4) ] ∥ (((a : TotalHopf) → f (fst a) ≡ x)) ∥₂) ∥₂) ∥₂
     ∥ Σ (hLevelTrunc 3 (S₊ 2 → coHomK 4)) (fst ∘ wah) ∥₂
fun charaFSpace2 =
  sRec squash₂ (uncurry (coHomK-elim _ (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelSuc 3 (isOfHLevelSuc 2 squash₂))
    (sRec squash₂ λ f → ∣ ∣ fst f ∣ , snd f ∣₂)))
inv charaFSpace2 =
  sRec squash₂
    (uncurry (trElim (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelSuc 2 squash₂)
      λ f p → ∣ (0ₖ _) , ∣ f , p ∣₂ ∣₂))
rightInv charaFSpace2 =
  sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
    (uncurry (trElim (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelSuc 2 (isOfHLevelPath 2 squash₂ _ _))
      λ _ _ → refl))
leftInv charaFSpace2 =
  sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
    (uncurry (coHomK-elim _ (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelSuc 3 (isOfHLevelSuc 2 (isOfHLevelPath 2 squash₂ _ _)))
      (sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
        λ _ → refl)))





test12 : isContr ((hLevelTrunc 3 (S₊ 2 → coHomK 4)))
test12 = isOfHLevelRetractFromIso 0 (compIso (mapCompIso t4') (compIso t6 (compIso t5 (compIso (mapCompIso t2) t7))))
           final
  where
  t4' : Iso (S₊ 2 → coHomK 4) (Σ[ x ∈ coHomK 4 ] Σ[ y ∈ coHomK 4 ] (S¹ → x ≡ y))
  fun t4' f = (f north) , ((f south) , (λ a → cong f (merid a) ))
  inv t4' (x , y , f) north = x
  inv t4' (x , y , f) south = y
  inv t4' (x , y , f) (merid a i) = f a i
  rightInv t4' _ = refl
  leftInv t4' f = funExt λ { north → refl ; south → refl ; (merid a i) → refl}

  t4 : Iso (S₊ 2 → coHomK 4) (Σ[ x ∈ coHomK 4 ] Σ[ y ∈ coHomK 4 ] Σ[ p ∈ x ≡ y ] (p ≡ p))
  fun t4 f = f north , f south , cong f (merid base) , λ i j → f (merid (loop i) j)
  inv t4 (x , y , p , P) north = x
  inv t4 (x , y , p , P) south = y
  inv t4 (x , y , p , P) (merid base i) = p i
  inv t4 (x , y , p , P) (merid (loop i₁) i) = P i₁ i
  rightInv t4 _ = refl
  leftInv t4 f = funExt λ { north → refl
                          ; south → refl
                          ; (merid base i) → refl
                          ; (merid (loop i₁) i) → refl}

  t6 : Iso (hLevelTrunc 3 (Σ[ x ∈ coHomK 4 ] Σ[ y ∈ coHomK 4 ] (S¹ → x ≡ y))) (hLevelTrunc 3 (S¹ → 0ₖ 4 ≡ 0ₖ 4))
  fun t6 = trRec (isOfHLevelTrunc 3)
             (uncurry (coHomK-elim _ (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelSuc 3 (isOfHLevelTrunc 3))
               (uncurry (coHomK-elim _ (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelSuc 3 (isOfHLevelTrunc 3))
                 ∣_∣))))
  inv t6 = trMap λ f → 0ₖ _ , 0ₖ _ , f
  rightInv t6 =
    trElim (λ _ → isOfHLevelTruncPath {n = 3}) λ _ → refl
  leftInv t6 =
    trElim (λ _ → isOfHLevelTruncPath {n = 3})
      (uncurry (coHomK-elim _ (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelSuc 3 (isOfHLevelTruncPath {n = 3}))
        (uncurry (coHomK-elim _ (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelSuc 3 (isOfHLevelTruncPath {n = 3}))
          λ f → refl))))

  t5 : Iso (hLevelTrunc 3 (S¹ → 0ₖ 4 ≡ 0ₖ 4)) (hLevelTrunc 3 (S₊ 1 → coHomK 3))
  t5 = mapCompIso (codomainIso (invIso (Iso-Kn-ΩKn+1 3)))

  t2 : Iso (S¹ → coHomK 3) (Σ[ x ∈ coHomK 3 ] x ≡ x)
  fun t2 f = f base , cong f loop
  inv t2 (x , p) base = x
  inv t2 (x , p) (loop i) = p i
  rightInv t2 z = refl
  leftInv t2 f = funExt λ { base → refl ; (loop i) → refl}

  t7 : Iso (hLevelTrunc 3 (Σ[ x ∈ coHomK 3 ] x ≡ x)) (hLevelTrunc 3 (0ₖ 3 ≡ 0ₖ 3))
  fun t7 = trRec (isOfHLevelTrunc 3) (uncurry (coHomK-elim _ (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelTrunc 3)
             ∣_∣))
  inv t7 = trRec (isOfHLevelTrunc 3) λ p → ∣ _ , p ∣
  rightInv t7 = trElim (λ _ → isOfHLevelTruncPath {n = 3}) λ _ → refl
  leftInv t7 = trElim (λ _ → isOfHLevelTruncPath {n = 3})
                 (uncurry (coHomK-elim _ (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelTruncPath {n = 3})
                   λ _ → refl))

  final : isContr ((hLevelTrunc 3 (0ₖ 3 ≡ 0ₖ 3)))
  final = isOfHLevelRetractFromIso 0 (mapCompIso (invIso (Iso-Kn-ΩKn+1 2)))
            (isConnectedKn 1)

charaFSpace3' : Iso ∥ Σ (hLevelTrunc 3 (S₊ 2 → coHomK 4)) (fst ∘ wah) ∥₂ (coHom 3 TotalHopf)
charaFSpace3' = compIso is (setTruncIso (codomainIso (invIso (Iso-Kn-ΩKn+1 3))))
  where
  mainF : _ → _
  mainF = sRec squash₂
      (uncurry (trElim (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelSuc 2 squash₂)
        λ f → sRec squash₂
                λ P → trRec squash₂
                        (λ p → ∣ (λ x → sym (funExt⁻ p (fst x)) ∙ P x) ∣₂)
                        (Iso.fun (PathIdTruncIso _) (isContr→isProp test12 ∣ f ∣ (∣ (λ _ → 0ₖ _) ∣)))))

  t : (f : _) → mainF ∣ ∣ (λ _ → 0ₖ 4) ∣ , ∣ f ∣₂ ∣₂ ≡ ∣ f ∣₂
  t f = (λ i → trRec squash₂ (λ p → ∣ (λ x → sym (funExt⁻ p (fst x)) ∙ f x) ∣₂) (h i))
      ∙ (λ i → ∣ (λ x → lUnit (f x) (~ i)) ∣₂)
    where
    h : (Iso.fun (PathIdTruncIso _) (isContr→isProp test12 (∣ (λ _ → 0ₖ _) ∣) (∣ (λ _ → 0ₖ _) ∣))) ≡ ∣ refl ∣
    h = cong (Iso.fun (PathIdTruncIso _)) (isProp→isSet (isContr→isProp test12) _ _ (isContr→isProp test12 ∣ (λ _ → 0ₖ 4) ∣ ∣ (λ _ → 0ₖ 4) ∣) refl)
      ∙ transportRefl ∣ refl ∣

  is : Iso _ _
  fun is = mainF
    
  inv is = sMap λ f → ∣ (λ _ → 0ₖ _) ∣ , ∣ f ∣₂
  rightInv is =
    sElim (λ _ → isOfHLevelPath 2 squash₂ _ _) t
  leftInv is = sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
    (uncurry (trElim (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 squash₂) _ _)
     λ f → transport (λ i → (y : (fst ∘ wah) (h f (~ i))) → inv is (fun is ∣ h f (~ i) , y ∣₂) ≡ ∣ h f (~ i) , y ∣₂)
       {!λ !}))
       where
       h : (f : S₊ 2 → coHomK 4) → Path (hLevelTrunc 3 _) ∣ f ∣ₕ ∣ (λ _ → 0ₖ 4) ∣
       h = {!!}

charaFSpace3 : Iso ∥ Σ (hLevelTrunc 3 (S₊ 2 → coHomK 4)) (fst ∘ wah) ∥₂ (coHom 3 TotalHopf)
charaFSpace3 =
  compIso
    is
   (setTruncIso (codomainIso (invIso (Iso-Kn-ΩKn+1 3))))
  where
  is : Iso ∥ Σ (hLevelTrunc 3 (S₊ 2 → coHomK 4)) (fst ∘ wah) ∥₂ ∥ (TotalHopf → 0ₖ 4 ≡ 0ₖ 4) ∥₂
  fun is =
    sRec squash₂
      λ x → transport (λ i → wah (isContr→isProp test12 (fst x) (∣ (λ _ → 0ₖ _) ∣) i) .fst) (snd x)
  inv is = sMap λ f → ∣ (λ _ → 0ₖ _) ∣ , ∣ f ∣₂
  rightInv is =
    sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
      λ f → (λ i → subst (fst ∘ wah)
                     (isProp→isSet (isContr→isProp test12) _ _
                      (isContr→isProp test12 (∣ (λ _ → 0ₖ _) ∣) (∣ (λ _ → 0ₖ _) ∣)) refl i) ∣ f ∣₂)
            ∙ transportRefl ∣ f ∣₂
  leftInv is =
    sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
      (uncurry λ x y → hen x (isContr→isProp test12 ∣ (λ _ → 0ₖ 4) ∣ x) y)
     where
     hen : (x : hLevelTrunc 3 (S₊ 2 → coHomK 4)) → (p : ∣ (λ _ → 0ₖ _) ∣ ≡ x)
       → (y : (fst ∘ wah) x) → sMap (λ f → ∣ (λ _ → 0ₖ 4) ∣ , ∣ f ∣₂)
      (transport
       (λ i → wah (isContr→isProp test12 x ∣ (λ _ → 0ₖ 4) ∣ i) .fst) y)
      ≡ ∣ x , y ∣₂
     hen x = J (λ x p → ((y : (fst ∘ wah) x) → sMap (λ f → ∣ (λ _ → 0ₖ 4) ∣ , ∣ f ∣₂)
      (transport
       (λ i → wah (isContr→isProp test12 x ∣ (λ _ → 0ₖ 4) ∣ i) .fst) y)
      ≡ ∣ x , y ∣₂)) (sElim (λ _ → isOfHLevelPath 2 squash₂ _ _)
        λ f → cong (sMap (λ f → ∣ (λ _ → 0ₖ 4) ∣ , ∣ f ∣₂)) ((λ i → subst (fst ∘ wah)
                     (isProp→isSet (isContr→isProp test12) _ _
                      (isContr→isProp test12 (∣ (λ _ → 0ₖ _) ∣) (∣ (λ _ → 0ₖ _) ∣)) refl i) ∣ f ∣₂) ∙ transportRefl ∣ f ∣₂))

characFSpace4 : Iso (coHom 3 TotalHopf) ℤ
characFSpace4 = compIso (setTruncIso (domIso (invIso IsoS³TotalHopf))) (fst (Hⁿ-Sⁿ≅ℤ 2))

finalIso : Iso (coHom 4 CP²) ℤ
finalIso = compIso (compIso (compIso (charaFSpace 4) charaFSpace2) charaFSpace3') characFSpace4

test16 : Iso.fun finalIso (0ₕ _) ≡ 0
test16 = {!refl!}

-- t : Iso
--       ∥ (Σ[ x ∈ coHomK 4 ]
--         ∥ (Σ[ f ∈ (S₊ 2 → coHomK 4) ] ∥ (((a : TotalHopf) → f (fst a) ≡ x)) ∥₂) ∥₂) ∥₂
--       {!!}
-- t = {!!}

-- myFib : ∥ (S₊ 2 → coHomK 4) ∥₂ → TypeOfHLevel ℓ-zero 2
-- myFib =
--   rec→Gpd.fun
--     (isOfHLevelTypeOfHLevel 2)
--     (λ f → ∥ ((a : TotalHopf) → f (fst a) ≡ 0ₖ _) ∥₂ , squash₂)
--     λ a b p q → {!!} -- zz (λ _ → isPropIsOfHLevel 2) _ _ (main-fst a b p q)
--       where
--       zz : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → ((x : A) → isProp (B x))
--         → {x y : Σ A B} (p q : x ≡ y)
--         → cong fst p ≡ cong fst q
--         → p ≡ q
--       fst (zz prop p q P i j) = P i j
--       snd (zz {B = B} prop {x = x} {y = y} p q P i j) = help i j
--         where
--         help : SquareP (λ i j → B (P i j)) (cong snd p) (cong snd q) (λ _ → snd x) λ _ → snd y 
--         help = toPathP (isOfHLevelPathP' 1 (isProp→isSet (prop _)) _ _ _ _)

--       help : (f : Susp S¹ → _) → isProp (∥ ((a : TotalHopf) → f (fst a) ≡ 0ₖ 4) ∥₂) 
--       help f = pRec isPropIsProp (λ p → subst isProp (λ i → ∥ ((a : TotalHopf) → p (~ i) a ≡ 0ₖ 4) ∥₂)
--                     (subst isProp (λ i → ∥ ((a : TotalHopf) → isoToPath (Iso-Kn-ΩKn+1 3) i) ∥₂)
--                       {!!})) {!!}
--         where
--         help' : ∥ (Σ[ p ∈ (f ∘ fst ≡ (λ _ → 0ₖ _)) ] {!p ≡ !}) ∥
--         help' = {!!}

--       ΩProp : ∀ {ℓ} {A : Type ℓ} → isProp A → isProp (A ≡ A)
--       ΩProp p = isOfHLevelRetract 1 (univalence .fst) (invEq univalence) (retEq univalence)
--         (isOfHLevel≃ 1 p p)

--       main-fst : (a b : S₊ 2 → coHomK 4) (p q : a ≡ b)
--         → cong (λ f → ∥ ((a₁ : TotalHopf) → f (fst a₁) ≡ 0ₖ 4) ∥₂) p
--         ≡
--         cong (λ f → ∥ ((a₁ : TotalHopf) → f (fst a₁) ≡ 0ₖ 4) ∥₂) q
--       main-fst a b p q = sRec ({!λ P Q R S → cong fst (isOfHLevelTypeOfHLevel 1 _ _ ? ? _ _ )!}) {!cong (λ f → ∥ ((a₁ : TotalHopf) → f (fst a₁) ≡ 0ₖ 4) ∥₂) p!} {!!}
--       {- J (λ b p → (q : a ≡ b) →
--             cong (λ f → ∥ ((a₁ : TotalHopf) → f (fst a₁) ≡ 0ₖ 4) ∥₂) p ≡
--             cong (λ f → ∥ ((a₁ : TotalHopf) → f (fst a₁) ≡ 0ₖ 4) ∥₂) q)
--               {!λ q → ?!} -}
--         where
--         help' : (q : a ≡ a) → ∥ q ≡ refl ∥₂
--         help' q = sRec squash₂ (λ qrefl → ∣ (λ i j x → qrefl i x j ) ∣₂) q'refl
--           where
          
--           t3 : isContr (hLevelTrunc 3 (S₊ 2 → coHomK 3))
--           t3 = {!!}

--           q' = funExt⁻ q

--           open import Cubical.Foundations.Pointed.Homogeneous
--           open import Cubical.Homotopy.Loopspace
--           q'refl : ∥ q' ≡ (λ x → refl) ∥₂
--           q'refl =
--             Iso.inv setTruncTrunc2Iso
--               (Iso.fun (PathIdTruncIso 2)
--                 (subst isProp (λ i → hLevelTrunc 3 (((x : Susp S¹) → typ (Ω (isHomogeneousKn 4 (a x) i)))))
--                   (subst isProp (λ i → hLevelTrunc 3 (((x : Susp S¹) → isoToPath (Iso-Kn-ΩKn+1 3) i)))
--                     {!!}) _ _))

--       main-snd : (a b : S₊ 2 → coHomK 4) (p q : a ≡ b)
--         → PathP (λ i → PathP (λ j → isOfHLevel 2 (main-fst a b p q i j)) {!!} {!!})
--              {!!}
--              {!!}
--       main-snd = {!!}

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
