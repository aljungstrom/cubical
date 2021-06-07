{-# OPTIONS --safe #-}
module Cubical.ZCohomology.Groups.CP2 where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Prelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc) hiding (_+'_)
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_)
open import Cubical.Data.Unit
open import Cubical.Algebra.Group renaming (Int to IntGroup ; Bool to BoolGroup ; Unit to UnitGroup)

open import Cubical.HITs.Pushout
open import Cubical.HITs.S1 renaming (_·_ to _·''_)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2) hiding (map)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim2 to pElim2 ; ∣_∣ to ∣_∣₁) hiding (map)
open import Cubical.HITs.Nullification
open import Cubical.HITs.Truncation renaming (elim to trElim ; elim2 to trElim2 ; map to trMap ; rec to trRec)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

open import Cubical.ZCohomology.RingStructure.CupProduct

open IsGroupHom
open Iso

open import Cubical.HITs.Hopf

open import Cubical.HITs.Join

CP² : Type
CP² = Pushout {A = TotalHopf} fst λ _ → tt

CP' : Type
CP' = Pushout {A = join S¹ S¹} (fst ∘ JoinS¹S¹→TotalHopf) λ _ → tt

characFunSpace : ∀ {ℓ} {A : Type ℓ} →
  (Σ[ f ∈ (S₊ 2 → A) ]
    (Σ[ pt ∈ A ]
      Σ[ g ∈ (S₊ 1 → f north ≡ pt) ]
        Σ[ h ∈ (S₊ 1 → f south ≡ pt) ]
          ((a b : S¹) → PathP (λ i → f (merid (invLooper a ·'' b) i) ≡ pt) (g a) (h b)))) → CP' → A
characFunSpace (f , pt , _) (inl x) = f x
characFunSpace (f , pt , _) (inr x) = pt
characFunSpace (f , pt , g , h , _) (push (inl x) i) = g x i
characFunSpace (f , pt , g , h , _) (push (inr x) i) = h x i
characFunSpace (f , pt , g , h , p) (push (push a b j) i) = p a b j i

characFunSpace2 : ∀ {ℓ} {A : Type ℓ} →
  (Σ[ x ∈ A ]
    (Σ[ y ∈ A ]
      Σ[ z ∈ A ]
        Σ[ g ∈ (S₊ 1 → x ≡ z) ]
          Σ[ h ∈ (S₊ 1 → y ≡ z) ]
            Σ[ m ∈ (S₊ 1 → x ≡ y) ]
              (((a b : S¹) → PathP (λ i → m (invLooper a ·'' b) i ≡ z) (g a) (h b))))) → CP' → A
characFunSpace2 (x , y , z , g , h , m , p) (inl north) = x
characFunSpace2 (x , y , z , g , h , m , p) (inl south) = y
characFunSpace2 (x , y , z , g , h , m , p) (inl (merid a i)) = m a i
characFunSpace2 (x , y , z , g , h , m , p) (inr x₁) = z
characFunSpace2 (x , y , z , g , h , m , p) (push (inl x₁) i) = g x₁ i
characFunSpace2 (x , y , z , g , h , m , p) (push (inr x₁) i) = h x₁ i
characFunSpace2 (x , y , z , g , h , m , p) (push (push a b i₁) i) = p a b i₁ i

t : ∥ (Σ[ x ∈ coHomK 2 ]
    (Σ[ y ∈ coHomK 2 ]
      Σ[ z ∈ coHomK 2 ]
        Σ[ g ∈ (S₊ 1 → x ≡ z) ]
          Σ[ h ∈ (S₊ 1 → y ≡ z) ]
            Σ[ m ∈ (S₊ 1 → x ≡ y) ]
              (((a b : S¹) → PathP (λ i → m (invLooper a ·'' b) i ≡ z) (g a) (h b))))) ∥₂
    → ∥ (Σ[ g ∈ (S₊ 1 → 0ₖ 2 ≡ 0ₖ 2) ]
          Σ[ h ∈ (S₊ 1 → 0ₖ 2 ≡ 0ₖ 2) ]
            Σ[ m ∈ (S₊ 1 → 0ₖ 2 ≡ 0ₖ 2) ]
              (((a b : S¹) → PathP (λ i → m (invLooper a ·'' b) i ≡ 0ₖ 2) (g a) (h b)))) ∥₂
t =
  sRec squash₂
    (uncurry
      (trElim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelPlus {n = 2} 2 squash₂)
        (sphereElim 1 (λ _ → isSetΠ λ _ → squash₂)
          (uncurry (trElim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelPlus {n = 2} 2 squash₂)
          (sphereElim 1 (λ _ → isSetΠ λ _ → squash₂)
            (uncurry (trElim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelPlus {n = 2} 2 squash₂)
          (sphereElim 1 (λ _ → isSetΠ λ _ → squash₂)
            ∣_∣₂)))))))))

t' : (b : S¹) → {!!}
t' = {!!}


S3->S1*S1 : S₊ 3 → join S¹ S¹
S3->S1*S1 north = inl base
S3->S1*S1 south = inr base
S3->S1*S1 (merid north i) = push base base i
S3->S1*S1 (merid south i) = push base base i
S3->S1*S1 (merid (merid base j) i) = push base base i
S3->S1*S1 (merid (merid (loop k) j) i) =
  hcomp (λ r → λ {(i = i0) → inl (loop (k ∨ r))
                 ; (i = i1) → inr (loop (j ∨ r))
                 ; (j = i0) → push (loop (k ∨ r)) (loop r) i
                 ; (j = i1) → push (loop (k ∨ r)) base i
                 ; (k = i0) → push (loop r) (loop (j ∨ r)) i
                 ; (k = i1) → push base (loop (j ∨ r)) i})
        (push (loop k) (loop j) i)

back' : join S¹ S¹ → S₊ 3
back' (inl x) = north
back' (inr x) = south
back' (push base base i) = merid north i
back' (push base (loop k) i) = (merid ((merid base ∙ sym (merid base)) k)) i
back' (push (loop j) base i) = merid north i
back' (push (loop j) (loop k) i) = merid ((merid (loop j) ∙ sym (merid base)) k) i

back : join S¹ S¹ → S₊ 3
back (inl a) = north
back (inr a) = north
back (push base base i) = (merid north ∙ sym (merid north)) i
back (push base (loop k) i) = (merid ((merid base ∙ sym (merid base)) k) ∙ sym (merid north)) i
back (push (loop j) base i) = (merid north ∙ sym (merid north)) i
back (push (loop j) (loop k) i) = (merid ((merid (loop j) ∙ sym (merid base)) k) ∙ sym (merid north)) i

s1 : (x : join S¹ S¹) → S3->S1*S1 (back x) ≡ x
s1 (inl base) = {!!}
s1 (inl (loop i)) = {!!}
s1 (inr x) = {!x!}
s1 (push a b i) = {!!}


hopf : S₊ 3 → S₊ 2
hopf north = north
hopf south = north
hopf (merid north i) = north
hopf (merid south i) = north
hopf (merid (merid base j) i) = north
hopf (merid (merid (loop k) j) i) = help i j k
  where
  help : Path (typ ((Ω^ 2) (S₊∙ 2))) refl refl
  help i j k =
    hcomp (λ r → λ {(i = i0) → {!!} -- north
                   ; (i = i1) → {!!} -- north
                   ; (j = i0) → {!!}
                   ; (j = i1) → {!!}
                   ; (k = i0) → {!compPath-filler (merid (loop j)) (sym (merid base)) (~ i1) i!}
                   ; (k = i1) → (merid ((loop ∙ loop) j) ∙ sym (merid base)) (i ∨ r)})
          ((merid (compPath-filler loop loop k j)
          ∙ sym (merid base)) i)

-- module M = MV (S₊ 2) Unit TotalHopf fst (λ _ → tt)

-- H²CP²≅ℤ : GroupIso (coHomGr 2 CP²) IntGroup
-- H²CP²≅ℤ = compGroupIso (BijectionIso→GroupIso bij) (compGroupIso (invGroupIso trivIso) (Hⁿ-Sⁿ≅ℤ 1))
--   where
--   isContrH¹TotalHopf : isContr (coHom 1 TotalHopf)
--   isContrH¹TotalHopf =
--     isOfHLevelRetractFromIso 0 (setTruncIso (domIso (invIso (IsoS³TotalHopf))))
--       (isOfHLevelRetractFromIso 0 ((fst (H¹-Sⁿ≅0 1))) isContrUnit)

--   isContrH²TotalHopf : isContr (coHom 2 TotalHopf)
--   isContrH²TotalHopf =
--     isOfHLevelRetractFromIso 0 (setTruncIso (domIso (invIso (IsoS³TotalHopf))))
--       ((isOfHLevelRetractFromIso 0 (fst (Hⁿ-Sᵐ≅0 1 2 λ p → snotz (sym (cong predℕ p)))) isContrUnit))

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
--     pRec (setTruncIsSet _ _)
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

-- H⁴CP²≅ℤ : GroupIso (coHomGr 4 CP²) IntGroup
-- H⁴CP²≅ℤ = compGroupIso (invGroupIso (BijectionIso→GroupIso bij))
--           (compGroupIso help (Hⁿ-Sⁿ≅ℤ 2)) -- (subst (λ x → GroupIso (coHomGr 3 x) IntGroup) (isoToPath IsoS³TotalHopf) (Hⁿ-Sⁿ≅ℤ 2))
--   where
--   help : GroupIso (coHomGr 3 TotalHopf) (coHomGr 3 (S₊ 3))
--   fst help = setTruncIso (domIso (invIso IsoS³TotalHopf))
--   snd help = {!!}

--   bij : BijectionIso (coHomGr 3 TotalHopf) (coHomGr 4 CP²)
--   BijectionIso.fun bij = M.d 3
--   BijectionIso.inj bij x p =
--     pRec (setTruncIsSet _ _)
--          (uncurry (λ z q →
--              sym q
--           ∙∙ cong (M.Δ 3 .fst)
--                 (isOfHLevelΣ 1 (isContr→isProp
--                   (isOfHLevelRetractFromIso 0 (fst (Hⁿ-Sᵐ≅0 2 1 λ p → snotz (cong predℕ p))) isContrUnit))
--                 (λ _ → isContr→isProp (isContrHⁿ-Unit 2))
--                 z (0ₕ _ , 0ₕ _))
--           ∙∙ M.Δ 3 .snd .pres1))
--          (M.Ker-d⊂Im-Δ _ x p)
--   BijectionIso.surj bij y =
--     M.Ker-i⊂Im-d 3 y (isOfHLevelΣ 1
--       (isContr→isProp (isOfHLevelRetractFromIso 0
--         (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p))) isContrUnit))
--         (λ _ → isContr→isProp (isContrHⁿ-Unit _)) _ _)

-- open import Cubical.HITs.S3
-- s : S₊ 3 → S³
-- s north = base
-- s south = base
-- s (merid north i) = base
-- s (merid south i) = base
-- s (merid (merid base i₁) i) = base
-- s (merid (merid (loop k) j) i) = surf i j k

-- hopf₁ : S₊ 3 → S₊ 2
-- hopf₁ north = north
-- hopf₁ south = north
-- hopf₁ (merid north i) = north
-- hopf₁ (merid south i) = north
-- hopf₁ (merid (merid a j) i) = {!!}
--   where

--   t : (a : S¹) → typ ((Ω^ 2) (S₊∙ 2))
--   t a i j =
--     hcomp {!!}
--           (merid (trRec (isGroupoidS¹) (λ p → p) (∣ a ∣ +ₖ ∣ a ∣)) j)

-- test : coHom 4 CP² → Int
-- test = Iso.fun (fst H⁴CP²≅ℤ)

-- one : coHom 2 CP²
-- one = ∣ (λ { (inl x) → ∣ x ∣
--           ; (inr x) → 0ₖ _
--           ; (push a i) → help (fst a) (snd a) i }) ∣₂
--   where
--   help : (a : S₊ 2) (b : HopfSuspS¹ a) → ∣ a ∣ ≡ 0ₖ 2
--   help north b = Kn→ΩKn+1 1 ∣ b ∣
--   help south b = cong ∣_∣ₕ (sym (merid b))
--   help (merid a i) = ok i
--     where
--     ok : PathP (λ i → HopfSuspS¹ (merid a i) → ∣ merid a i ∣ ≡ 0ₖ 2) (λ b → Kn→ΩKn+1 1 ∣ b ∣) λ b → cong ∣_∣ₕ (sym (merid b))
--     ok = toPathP (funExt
--       λ x → cong (transport (λ i₁ → ∣ merid a i₁ ∣ ≡ 0ₖ 2)) (cong (Kn→ΩKn+1 1 ∘ ∣_∣ₕ) (transportRefl (invEq (_ , rotIsEquiv a) x)))
--           ∙∙ (λ i → transp {!!} {!!} {!!})
--           ∙∙ {!!})


-- test2 : test (one ⌣ one) ≡ 1
-- test2 = {!refl!}
