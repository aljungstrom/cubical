{-# OPTIONS --safe --lossy-unification #-}

{-
This file contains
1. The Thom isomorphism (various related forms of it)
2. The Gysin sequence
-}

module Cubical.Cohomology.EilenbergMacLane.Rings.RPinf where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.Gysin

open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.GradedCommTensor
  hiding (⌣ₖ-comm)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import Cubical.Functions.Morphism
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.EilenbergMacLane1.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.S1

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order hiding (eq)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_≤_)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.Group.Instances.IntMod

open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Fin.Base


open RingStr renaming (_+_ to _+r_)
open PlusBis


EM→-charac : ∀ {ℓ ℓ'} {A : Pointed ℓ} {G : AbGroup ℓ'} (n : ℕ)
  → Iso (fst A → EM G n) ((A →∙ EM∙ G n) × EM G n)
Iso.fun (EM→-charac {A = A} n) f =
  ((λ x → f x -ₖ f (pt A)) , rCancelₖ n (f (pt A))) , f (pt A)
Iso.inv (EM→-charac n) (f , a) x = fst f x +ₖ a
Iso.rightInv (EM→-charac {A = A} n) ((f , p) , a) =
  ΣPathP (→∙Homogeneous≡ (isHomogeneousEM _)
    (funExt (λ x → (λ i → (f x +ₖ a) -ₖ (cong (_+ₖ a) p ∙ lUnitₖ n a) i)
                  ∙ sym (assocₖ n (f x) a (-ₖ a))
                  ∙ cong (f x +ₖ_) (rCancelₖ n a)
                  ∙ rUnitₖ n (f x)))
  , cong (_+ₖ a) p ∙ lUnitₖ n a)
Iso.leftInv (EM→-charac {A = A} n) f =
  funExt λ x → sym (assocₖ n (f x) (-ₖ f (pt A)) (f (pt A)))
    ∙∙ cong (f x +ₖ_) (lCancelₖ n (f (pt A)))
    ∙∙ rUnitₖ n (f x)

EquivPresId : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) {x y : A} → fst e x ≡ fst e y → x ≡ y
EquivPresId e p = sym (retEq e _) ∙∙ cong (invEq e) p ∙∙ retEq e _

private
  hlev : (b : EM (Ring→AbGroup ℤ/2Ring) 1)
    → isOfHLevel 2 (Susp∙ (embase ≡ b) →∙ EM∙ (CommRing→AbGroup ℤ/2CommRing) 1)
  hlev = EM→Prop _ 0 (λ _ → isPropIsOfHLevel 2)
    (subst isSet (cong ((ℤ/2Ring .fst , fzero) →∙_)
              (EM≃ΩEM+1∙ 0)
      ∙ isoToPath (ΩSuspAdjointIso {A = ℤ/2Ring .fst , fzero})
      ∙ cong (_→∙ EM∙ (CommRing→AbGroup ℤ/2CommRing) 1)
      (cong Susp∙ (isoToPath  (Iso-EM-ΩEM+1 0))))
      (subst isSet
        (cong (λ x → x →∙ x)
          (ua∙ {A = _ , true} (isoToEquiv (Bool≅ℤGroup/2 .fst)) refl))
        (isOfHLevel→∙ 2 isSetBool)))

  eule : (x : EM (Ring→AbGroup ℤ/2Ring) 1) → embase ≡ x → Ω (EM∙ (CommRing→AbGroup ℤ/2CommRing) 1) .fst
  eule = EM-raw'-elim _ 1 (λ _ → isOfHLevelΠ 2 (λ _ → hLevelEM _ 1 _ _))
    λ { embase-raw → idfun _
      ; (emloop-raw g i) z → {!!}}
      where
      h : (g : fst ℤ/2Ring)
        → PathP (λ i → embase ≡ emloop g i → Ω (EM∙ (CommRing→AbGroup ℤ/2CommRing) 1) .fst)
                 (λ z → z) (λ z → z)
      h = ℤ/2-elim (toPathP (funExt (λ p → {!!})))
                   (toPathP (funExt λ p → {!!}))


  open import Cubical.Data.Empty as ⊥
  open import Cubical.Relation.Nullary

  myType : (b : EM (Ring→AbGroup ℤ/2Ring) 1) → Type _
  myType b =  (Σ[ F ∈ Susp∙ (embase ≡ b) →∙ EM∙ (CommRing→AbGroup ℤ/2CommRing) 1 ]
             ¬ F ≡ const∙ _ _)

  Iso1 : Iso (Susp∙ (Ω (EM∙ (CommRing→AbGroup ℤ/2CommRing) 1) .fst) →∙ EM∙ (CommRing→AbGroup ℤ/2CommRing) 1)
             ((Bool , true) →∙ (Bool , true))
  Iso1 =
    compIso (invIso (ΩSuspAdjointIso {A = Ω (EM∙ (CommRing→AbGroup ℤ/2CommRing) 1)}) )
            (compIso
              (post∘∙equiv (help , refl))
              (pre∘∙equiv (help , refl)))
    where
    help = (isoToEquiv (compIso (invIso (Iso-EM-ΩEM+1 {G = CommRing→AbGroup ℤ/2CommRing} 0))
            (invIso (Bool≅ℤGroup/2 .fst))))

  open import Cubical.Foundations.Univalence
  ΣIs : ∀ {ℓ} {B A : Type ℓ}
    → (e : A ≃ B)
    → {x : A}
    → Iso (Σ[ y ∈ A ] ¬ y ≡ x)
           (Σ[ y ∈ B ] ¬ y ≡ fst e x)
  ΣIs {B = B} = EquivJ (λ A e → {x : A}
    → Iso (Σ[ y ∈ A ] ¬ y ≡ x)
           (Σ[ y ∈ B ] ¬ y ≡ fst e x)) idIso

  iso2Inv : Bool → (Bool , true) →∙ (Bool , true)
  iso2Inv false = idfun∙ _
  iso2Inv true = const∙ _ _
  iso2 : Iso ((Bool , true) →∙ (Bool , true)) Bool
  Iso.fun iso2 f = fst f false
  Iso.inv iso2 = iso2Inv
  Iso.rightInv iso2 false = refl
  Iso.rightInv iso2 true = refl
  Iso.leftInv iso2 f = Σ≡Prop (λ _ → isSetBool _ _) (help _ refl)
    where
    help : (x : Bool) → fst f false ≡ x → iso2Inv (fst f false) .fst ≡ f .fst
    help false p = funExt λ { false → (λ j → iso2Inv (p j) .fst false) ∙ sym p
                             ; true → (λ j → iso2Inv (p j) .fst true) ∙ sym (snd f)}
    help true p = (λ j → iso2Inv (p j) .fst) ∙ funExt λ { false → sym p ; true → sym (snd f)}

  myTYIso : Iso (myType embase) (Σ[ F ∈ Bool ] ¬ F ≡ true)
  myTYIso = ΣIs (isoToEquiv (compIso Iso1 iso2))

  isProp-T : (b : EM (Ring→AbGroup ℤ/2Ring) 1) → isProp (myType b)
  isProp-T = EM→Prop _ 0 (λ _ → isPropIsProp)
           (isOfHLevelRetractFromIso 1 myTYIso
             (isContr→isProp ((false , true≢false ∘ sym)
                            , λ { (false , p) → Σ≡Prop (λ _ → isProp¬ _) refl  
                                ; (true , p) → ⊥.rec (p refl)})))

  euler-f : Susp∙ (Ω (EM∙ (CommRing→AbGroup ℤ/2CommRing) 1) .fst) →∙ EM∙ (CommRing→AbGroup ℤ/2CommRing) 1
  fst euler-f north = embase
  fst euler-f south = embase
  fst euler-f (merid a i) = a i
  snd euler-f = refl

  euler : myType embase
  fst euler = euler-f
  snd euler p = true≢false true≡false
    where
    true≡false : true ≡ false
    true≡false i = Iso.fun (compIso Iso1 iso2) (p (~ i))

  euler-full : (b : EM (Ring→AbGroup ℤ/2Ring) 1) → myType b
  euler-full = EM→Prop _ 0 isProp-T euler

  module ThomRP∞ = Thom (EM∙ (Ring→AbGroup ℤ/2Ring) 1) (0ₖ 1 ≡_) refl -- (isConnectedEM 1)
                   (isConnectedEM 1) -- ℤ/2CommRing
                   ℤ/2CommRing


  open ThomRP∞
  isContrE : isContr E
  isContrE = isContrSingl _

  module conRP∞ =
    con 0 (((compEquiv (isoToEquiv (invIso (Iso-EM-ΩEM+1 0)))
                     (isoToEquiv (invIso (fst Bool≅ℤGroup/2))))) , refl)
          (λ b → euler-full b .fst)
          (EquivPresId (isoToEquiv (compIso Iso1 iso2)) λ i → false)
  open conRP∞
  test : (n : ℕ) → ((fst (EM∙ (Ring→AbGroup ℤ/2Ring) 1) → EM (Ring→AbGroup ℤ/2Ring) n))
                   ≃ (EM∙ (Ring→AbGroup ℤ/2Ring) 1 →∙ EM∙ (Ring→AbGroup ℤ/2Ring) (n +' 1))
  test n = ϕ-raw-contr n isContrE

  open import Cubical.Algebra.AbGroup.TensorProduct
  ⌣RP∞ : (n : ℕ) → (fst (EM∙ (Ring→AbGroup ℤ/2Ring) 1) → EM (Ring→AbGroup ℤ/2Ring) n)
                  → EM∙ (Ring→AbGroup ℤ/2Ring) 1 →∙ EM∙ (Ring→AbGroup ℤ/2Ring) (n +' 1)
  fst (⌣RP∞ n f) x = (f x) ⌣ₖ x
  snd (⌣RP∞ n f) = ⌣ₖ-0ₖ _ _ (f (0ₖ 1))

  ⌣RP∞IsEq : (n : ℕ) → isEquiv (⌣RP∞ n)
  ⌣RP∞IsEq n =
    subst isEquiv
      (funExt (λ f → →∙Homogeneous≡ (isHomogeneousEM _)
        (λ i x → f x ⌣ₖ (euler-full-lem x i))))
        (test n .snd)
    where
    help : (g : _) → (λ i → euler-full (emloop g i) .fst .fst south) ≡ emloop g
    help g j i = hcomp (λ k → λ {(i = i0) → embase
                                ; (i = i1) → emloop g k
                                ; (j = i0) → euler-full (emloop g i) .fst .fst (merid (λ w → emloop g (i ∧ w)) k)
                                ; (j = i1) → emloop g (i ∧ k)})
                       (euler-full (emloop g i) .fst .snd j)

    euler-full-lem : (x : _) → euler-full x .fst .fst south ≡ x
    euler-full-lem = EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
      λ { embase-raw → refl ; (emloop-raw g i) j → help g j i }

  ⌣RP∞Equiv : (n : ℕ) → (fst (EM∙ (Ring→AbGroup ℤ/2Ring) 1) → EM (Ring→AbGroup ℤ/2Ring) n)
                        ≃ (EM∙ (Ring→AbGroup ℤ/2Ring) 1 →∙ EM∙ (Ring→AbGroup ℤ/2Ring) (n +' 1))
  ⌣RP∞Equiv n = ⌣RP∞ n , ⌣RP∞IsEq n


  RP→Charac₀ : Iso (EM (Ring→AbGroup ℤ/2Ring) 1 → ℤ/2Ring .fst)
                (ℤ/2Ring .fst)
  Iso.fun RP→Charac₀ f = f embase
  Iso.inv RP→Charac₀ a = λ _ → a
  Iso.rightInv RP→Charac₀ a = refl
  Iso.leftInv RP→Charac₀ f = funExt (EM→Prop _ 0 (λ _ → is-set (snd ℤ/2Ring) _ _) refl)

  _ˣ_ : ∀ {ℓ} (A : ℕ → Type ℓ) (n : ℕ) → Type ℓ
  A ˣ zero = A zero
  A ˣ suc n = (A ˣ n) × A (suc n)

  triv : (n : ℕ) (x : EM _ n) → ⌣RP∞Equiv n .fst (λ _ → x) ≡ ((λ y → x ⌣ₖ y) , ⌣ₖ-0ₖ _ 1 _)
  triv n x = →∙Homogeneous≡ (isHomogeneousEM _) refl

  
  RP→Charac : (n : ℕ)
    → Iso (fst (EM∙ (Ring→AbGroup ℤ/2Ring) 1) → EM (Ring→AbGroup ℤ/2Ring) n)
           ((EM (Ring→AbGroup ℤ/2Ring)) ˣ n)
  RP→Charac zero = RP→Charac₀
  RP→Charac (suc n) =
    compIso (EM→-charac {A = EM∙ (Ring→AbGroup ℤ/2Ring) 1} (suc n))
     (Σ-cong-iso-fst
       (compIso {!!} (RP→Charac n)))
  module GysinRP∞ = Gysin (EM∙ (Ring→AbGroup ℤ/2Ring) 1) (0ₖ 1 ≡_) (isConnectedEM 1)
                   ℤ/2CommRing
                   0
                   ((compEquiv (isoToEquiv (invIso (Iso-EM-ΩEM+1 0)))
                     (isoToEquiv (invIso (fst Bool≅ℤGroup/2)))))
                   (λ b → euler-full b .fst)
                   (EquivPresId (isoToEquiv (compIso Iso1 iso2)) λ i → false)


