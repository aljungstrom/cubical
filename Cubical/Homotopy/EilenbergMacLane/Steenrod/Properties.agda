{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Homotopy.EilenbergMacLane.Steenrod.Properties where

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.FibreDelooping
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.Order2
open import Cubical.Homotopy.EilenbergMacLane.Steenrod.Base

open import Cubical.Cohomology.EilenbergMacLane.Base

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.CommRing.Instances.IntMod

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic

open import Cubical.HITs.SetTruncation as ST

open CommRingStr renaming (_+_ to _+R_)
open IsCommRing
open IsMonoid
open IsSemigroup
open IsRing
open AbGroupStr renaming (_+_ to _+G_)

open import Cubical.Data.Nat.Order

open Iso
open PlusBis

private
  cupℤ/2 : (n m : ℕ) → Kℤ/2 n → Kℤ/2 m → Kℤ/2 (n +' m)
  cupℤ/2 n m = _⌣ₖ_

open EM-subst ℤ/2

Sqₖ⁰≡id : {n : ℕ} (x : Kℤ/2 n) → Sqₖ 0 x ≡ x
Sqₖ⁰≡id {n = zero} x = refl
Sqₖ⁰≡id {n = suc n} x = refl

Sqₖ≡⌣ₖ : {n : ℕ} (x : Kℤ/2 n) → Sqₖ n x ≡ cupℤ/2 n n x x
Sqₖ≡⌣ₖ {n = zero} = ℤ/2-elim refl refl
Sqₖ≡⌣ₖ {n = suc n} x =
     (λ i → Sqₖ∙-gen (suc n) (suc n)
              (isPropTrichotomy (suc n ≟ suc n)
              (eq refl) i) .fst x)
  ∙ transportRefl _

Sqₖ-triv : {n : ℕ} (i : ℕ) → i > n → (x : Kℤ/2 n) → Sqₖ i x ≡ 0ₖ (i +' n)
Sqₖ-triv {n = zero} zero p x = ⊥.rec (¬m<m p)
Sqₖ-triv {n = zero} (suc i) p x = refl
Sqₖ-triv {n = suc n} zero p x = ⊥.rec (snotz (sym (+-suc _ _) ∙ snd p))
Sqₖ-triv {n = suc n} (suc i) p x j =
  Sqₖ∙-gen (suc n) (suc i)
   (isPropTrichotomy (suc i ≟ suc n) (gt p) j) .fst x

ΩSqFun : (n i : ℕ) → Ω (EM∙ ℤ/2 (suc n)) →∙ Ω (EM∙ ℤ/2 (i +' suc n))
fst (ΩSqFun n i) x =
  substΩEM (+'-suc' i n) .fst
   (EM→ΩEM+1 (i +' n) (Sqₖ {n = n} i (ΩEM+1→EM n x)))
snd (ΩSqFun n i) =
      cong (substΩEM (+'-suc' i n) .fst)
         (cong (EM→ΩEM+1 (i +' n))
           (cong (Sqₖ i)
             (ΩEM+1→EM-refl n)
          ∙ Sqₖ∙ i .snd)
        ∙ EM→ΩEM+1-0ₖ (i +' n))
  ∙ substΩEM (+'-suc' i n) .snd


-- some tehcnical lemmas
private
  wrap-id : (n : ℕ) {x : Kℤ/2 n} (r q1 q2 : x ≡ x)
    → q1 ≡ q2 → q1 ≡ sym r ∙∙ q2 ∙∙ r
  wrap-id zero {x = x} r _ _ _ = hLevelEM _ 0 _ _ _ _
  wrap-id (suc n) {x = x} r q1 =
    J> (lUnit q1
    ∙ cong (_∙ q1) (sym (lCancel r))
    ∙ sym (assoc _ _ _)
    ∙ (cong (sym r ∙_) (isCommΩEM-base n x r q1)))
    ∙ sym (doubleCompPath≡compPath _ _ _)

  module _ {i n : ℕ} where
    ℕP = (+'-comm (suc i) (suc (suc n)) ∙
          (λ i₂ → +'-suc (suc n) (suc i) (~ i₂)))
         ∙ (λ i₂ → suc (+'-comm (suc n) (suc i) i₂))

    helplem : (x : _)
      → substΩEM (sym ℕP) .fst
           (EM→ΩEM+1 (suc (suc (i + n))) x)
       ≡ EM→ΩEM+1 (suc (i + suc n))
           (substEM (cong suc (sym (+-suc i n))) .fst x)
    helplem x =
        substℕSwap {B = λ n → Ω (Kℤ/2∙ n) .fst}
                    (sym ℕP) (sym (cong (2 +_) (+-suc i n)))
                    (EM→ΩEM+1 (suc (suc (i + n))) x)
      ∙ substCommSlice Kℤ/2 (λ n → fst (Ω (Kℤ/2∙ (suc n))))
          EM→ΩEM+1 (cong suc (sym (+-suc i n))) x


cong₂-cupℤ/2 : (n : ℕ) (q : 0ₖ n ≡ 0ₖ n) → cong₂ (cupℤ/2 n n) q q ≡ refl
cong₂-cupℤ/2 = cong₂-⌣ₖ ℤ/2Ring

preΩSqₖ∙ : (n i : ℕ) → Trichotomy i n
  → ΩSqFun n i ≡ Ω→ (Sqₖ∙ {n = suc n} i)
preΩSqₖ∙ zero zero p =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
     (funExt λ x → cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' zero zero))
       (Iso.rightInv (Iso-EM-ΩEM+1 zero) x)
     ∙ transportRefl x
     ∙ wrap-id 1 refl x _ refl)
preΩSqₖ∙ zero (suc i) (lt x) = ⊥.rec (snotz (sym (+-suc _ _) ∙ x .snd))
preΩSqₖ∙ zero (suc i) (eq p) = ⊥.rec (snotz p)
preΩSqₖ∙ zero (suc i) (gt (zero , p)) =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
        (funExt main
       ∙ sym (cong fst Ω→-triv))
  ∙ cong (Ω→ ∘ Sqₖ∙-gen 1 (suc i))
         (isPropTrichotomy (eq (sym p)) (suc i ≟ 1))
  where
  cong₂-lem : (q : snd (Kℤ/2∙ 1) ≡ snd (Kℤ/2∙ 1))
     → cong (substEM (cong (_+' 1) p) .fst)
             (cong₂ (cupℤ/2 1 1) q q)
      ≡ refl
  cong₂-lem q = cong (cong (substEM (cong (_+' 1) p) .fst)) (cong₂-cupℤ/2 1 q)

  Ω→-triv : Ω→ (Sqₖ∙-gen 1 (suc i) (eq (sym p))) ≡ ((λ _ → refl) , refl)
  Ω→-triv = →∙Homogeneous≡ (isHomogeneousPath _ _)
       (funExt λ q → cong₂ (λ x y → sym x ∙∙ y ∙∙ x) refl (cong₂-lem q)
                    ∙ ∙∙lCancel _)

  main : (x : _) → ΩSqFun zero (suc i) .fst x ≡ refl
  main x = cong (subst (λ x₁ → fst (Ω (EM∙ ℤ/2 x₁))) (+'-suc' (suc i) zero))
                (cong (EM→ΩEM+1 (suc i))
                  (λ j → Sqₖ∙-gen 0 (suc i)
                         (isPropTrichotomy (suc i ≟ 0)
                         (gt (i , +-comm i 1)) j) .fst (ΩEM+1→EM zero x))
               ∙ EM→ΩEM+1-0ₖ (suc i))
         ∙ substΩEM (+'-suc' (suc i) zero) .snd
preΩSqₖ∙ zero (suc i) (gt (suc x , p)) =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt (λ q
      → cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' (suc i) zero))
              (cong (EM→ΩEM+1 (suc i))
                ((λ j → Sqₖ∙-gen zero (suc i) (isPropTrichotomy (suc i ≟ zero)
                  (gt (i , +-comm i 1)) j) .fst (ΩEM+1→EM zero q))))
       ∙ cong (substΩEM (+'-suc' (suc i) zero) .fst) (EM→ΩEM+1-0ₖ _)
       ∙ substΩEM (+'-suc' (suc i) zero) .snd))
  ∙ sym (Ω^→const 1)
  ∙ cong (Ω→ ∘ Sqₖ∙-gen 1 (suc i))
         (isPropTrichotomy (gt (x , +-suc x 1 ∙ p)) (suc i ≟ 1))
preΩSqₖ∙ (suc n) zero p =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q →
         substℕSwap {B = fst ∘ Ω ∘ Kℤ/2∙} (+'-suc' zero (suc n)) refl _
       ∙ transportRefl _
       ∙ cong (EM→ΩEM+1 (suc n))
            ((λ j → Sqₖ∙-gen (suc n) zero
              (isPropTrichotomy (lt (n , +-comm n 1)) (zero ≟ suc n) j)
               .fst (ΩEM+1→EM (suc n) q)))
       ∙ Iso.rightInv (Iso-EM-ΩEM+1 (suc n)) q))
  ∙ sym Ω→id
  ∙ cong (Ω→ ∘ Sqₖ∙-gen (suc (suc n)) zero)
      (isPropTrichotomy
        (lt (suc n , +-comm (suc n) 1))
        (zero ≟ (suc (suc n))))
preΩSqₖ∙ (suc n) (suc i) (lt (zero , p)) =
     →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q →
        substℕSwap {B = λ n → Ω (Kℤ/2∙ n) .fst}
          (+'-suc' (suc i) (suc n)) (sym (cong (2 +_) (+-suc i n)))
          (EM→ΩEM+1 (suc (suc (i + n))) (Sqₖ (suc i) (ΩEM+1→EM (suc n) q)))
            ∙ substCommSlice Kℤ/2 (λ n → fst (Ω (Kℤ/2∙ (suc n))))
                             EM→ΩEM+1 (cong suc (sym (+-suc i n)))
                             (Sqₖ (suc i) (ΩEM+1→EM (suc n) q))
           ∙ cong (EM→ΩEM+1 (suc (i + suc n)))
               (cong (subst Kℤ/2 (cong suc (sym (+-suc i n))))
                 λ k → Sqₖ∙-gen (suc n) (suc i)
                           (isPropTrichotomy (suc i ≟ suc n)
                            (lt (0 , p)) k) .fst (ΩEM+1→EM (suc n) q))))
  ∙ (sym (secEq (deloopKℤ/2FunIso (suc n) (suc i) (0 , p)) _)
  ∙ cong Ω→ (sym help))
  ∙ cong Ω→ λ j → Sqₖ∙-gen (suc (suc n)) (suc i)
            (isPropTrichotomy (lt (1 , cong suc p)) (suc i ≟ suc (suc n)) j)
  where
  help : Sqₖ∙-gen (suc (suc n)) (suc i) (lt (1 , cong suc p))
       ≡ invEq (deloopKℤ/2FunIso (suc n) (suc i) (0 , p))
               ((EM→ΩEM+1∙ ((suc (i + suc n))))
               ∘∙ ((substEM (cong suc (sym (+-suc i n)))
                ∘∙ Sqₖ∙-gen (suc n) (suc i) (lt (0 , p)))
                ∘∙ (ΩEM+1→EM∙ (suc n))))
  help = cong (invEq (deloopKℤ/2FunIso (suc n) (suc i) (0 , p)))
         (→∙Homogeneous≡ (isHomogeneousPath _ _)
           (funExt (λ q →
              helplem (substEM (cong (_+' suc n) (cong predℕ (sym p))) .fst
              (fib-deloop n .fst .fst (ΩEM+1→EM (suc n) q))))))
preΩSqₖ∙ (suc n) (suc i) (lt (suc x , p)) =
   →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q →
          substℕSwap {B = λ n → Ω (Kℤ/2∙ n) .fst}
             (+'-suc' (suc i) (suc n))
             (sym (cong (suc ∘ suc) (+-suc i n)))
             (EM→ΩEM+1 (suc (suc (i + n)))
             (Sqₖ (suc i) (ΩEM+1→EM (suc n) q)))
       ∙∙ substCommSlice Kℤ/2 (λ n → fst (Ω (Kℤ/2∙ (suc n))))
             EM→ΩEM+1 (cong suc (sym (+-suc i n)))
              (Sqₖ (suc i) (ΩEM+1→EM (suc n) q))
       ∙∙ cong (EM→ΩEM+1 (suc (i + suc n)))
           (cong (fst (substEM (cong suc (sym (+-suc i n)))))
             λ k → Sqₖ∙-gen (suc n) (suc i)
               (isPropTrichotomy (suc i ≟ suc n) (lt (suc x , p)) k)
               .fst (ΩEM+1→EM (suc n) q))))
  ∙ sym (secEq (deloopKℤ/2FunIso (suc n) (suc i) (suc x , p)) guy)
  ∙ cong Ω→ (sym help)
  ∙ cong Ω→ λ j → Sqₖ∙-gen (suc (suc n)) (suc i)
            (isPropTrichotomy (lt (suc (suc x) ,  cong suc p))
            (suc i ≟ suc (suc n)) j)
  where
  guy = (EM→ΩEM+1 ((suc (i + suc n))) , EM→ΩEM+1-0ₖ (suc (i + suc n)))
               ∘∙ ((substEM (cong suc (sym (+-suc i n)))
                ∘∙ Sqₖ∙-gen (suc n) (suc i) (lt (((suc x)) , p)))
                ∘∙ (ΩEM+1→EM∙ (suc n)))

  help : Sqₖ∙-gen (suc (suc n)) (suc i) (lt (2 + x , cong suc p))
      ≡ invEq (deloopKℤ/2FunIso (suc n) (suc i) (suc x , p)) guy
  help = cong (invEq (deloopKℤ/2FunIso (suc n) (suc i) (suc x , p)))
              (→∙Homogeneous≡ (isHomogeneousPath _ _)
                (funExt λ q
                 → cong (substΩEM (sym ℕP) .fst)
                         (λ _ → EM→ΩEM+1 (suc (suc (i + n)))
                           (Sqₖ∙-gen (suc n) (suc i)
                              (lt (suc x , p)) .fst (ΩEM+1→EM (suc n) q)))
                  ∙ helplem (Sqₖ∙-gen (suc n) (suc i)
                       (lt (suc x , p)) .fst (ΩEM+1→EM (suc n) q))))

preΩSqₖ∙ (suc n) (suc i) (eq p) =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q →
        cong (substΩEM (+'-suc' (suc i) (suc n)) .fst)
             (cong (EM→ΩEM+1 (suc (suc (i + n))))
               (λ j → Sqₖ∙-gen (suc n) (suc i)
                        (isPropTrichotomy
                        (suc i ≟ suc n) (eq p) j) .fst
                        (ΩEM+1→EM (suc n) q))
           ∙ sym (substCommSlice Kℤ/2 (fst ∘ Ω ∘ Kℤ/2∙ ∘ suc) EM→ΩEM+1
               (cong (_+' suc n) (sym p))
               (cupℤ/2 (suc n) (suc n)
                 (ΩEM+1→EM (suc n) q) (ΩEM+1→EM (suc n) q))))
       ∙ sym (substComposite (fst ∘ Ω ∘ Kℤ/2∙)
          (λ i₁ → suc (p (~ i₁) +' suc n)) (+'-suc' (suc i) (suc n)) _)
       ∙ substℕSwap _ _ _
       ∙ substComposite (fst ∘ Ω ∘ Kℤ/2∙)
          (+'-suc' (suc n) (suc n)) (λ i₁ → sym p i₁ +' suc (suc n)) _
       ∙ sym (Ω→H≡ (⌣-deloop (suc n) .fst q))))
  ∙ (λ i → Ω→ H ∘∙ (fib-deloop (suc n) .snd (~ i)))
  ∙ sym (Ω→∘∙ H (fib-deloop (suc n) .fst))
  ∙ cong Ω→ (sym help)
  ∙ cong Ω→ λ j → Sqₖ∙-gen (suc (suc n)) (suc i)
     (isPropTrichotomy (lt (zero , cong suc p)) (suc i ≟ suc (suc n)) j)
  where
  H : Kℤ/2∙ (suc (suc (n + suc n))) →∙ Kℤ/2∙ (suc (suc (i + suc n)))
  H = substEM (cong (_+' suc (suc n)) (sym p))

  Ω→H≡  : (x : _)
    → Ω→ H .fst x
     ≡ substΩEM (λ i → ((sym p i) +' suc (suc n))) .fst x
  Ω→H≡ x i = substΩEM≡ (λ i → ((sym p i) +' suc (suc n))) (~ i) .fst x

  help : Sqₖ∙-gen (suc (suc n)) (suc i) (lt (0 , cong suc p))
       ≡ H ∘∙ fib-deloop (suc n) .fst
  help = →∙Homogeneous≡ (isHomogeneousEM (suc (suc (i + suc n)))) refl

preΩSqₖ∙ (suc n) (suc i) (gt (zero , p)) =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q →
        cong (substΩEM (+'-suc' (suc i) (suc n)) .fst)
                 (cong (EM→ΩEM+1 (suc (suc (i + n))))
                   (λ j → Sqₖ∙-gen (suc n) (suc i)
                           (isPropTrichotomy (suc i ≟ suc n)
                             (gt (0 , p)) j) .fst (ΩEM+1→EM (suc n) q))
                ∙ EM→ΩEM+1-0ₖ (suc (suc (i + n))))
  ∙∙ (substΩEM (+'-suc' (suc i) (suc n)) .snd
               ∙ sym (∙∙lCancel _))
  ∙∙ cong₂ (λ x y → sym x ∙∙ y ∙∙ x) refl
       (sym (cong (cong (subst (λ m → Kℤ/2 m) (cong (_+' suc (suc n)) p)))
         (cong₂-cupℤ/2 (suc (suc n)) q)))))
  ∙ cong (Ω→ ∘ Sqₖ∙-gen (suc (suc n)) (suc i))
      (isPropTrichotomy
        (eq (sym p))
        (suc i ≟ suc (suc n)))
preΩSqₖ∙ (suc n) (suc i) (gt (suc x , p)) =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt (λ q →
      cong (substΩEM (+'-suc' (suc i) (suc n)) .fst)
       (cong (EM→ΩEM+1 (suc (suc (i + n))))
         (λ j → Sqₖ∙-gen (suc n) (suc i)
            (isPropTrichotomy (suc i ≟ suc n) (gt (suc x , p)) j) .fst
              (ΩEM+1→EM (suc n) q))
       ∙ EM→ΩEM+1-0ₖ (suc (suc (i + n))))
    ∙ substΩEM (+'-suc' (suc i) (suc n)) .snd))
  ∙ sym Ω→const
  ∙ cong Ω→ (cong (Sqₖ∙-gen (suc (suc n)) (suc i))
     (isPropTrichotomy (gt (x , +-suc x (2 + n) ∙ p)) (suc i ≟ suc (suc n))))

ΩSqₖ∙ : (n i : ℕ) → ΩSqFun n i ≡ Ω→ (Sqₖ∙ {n = suc n} i)
ΩSqₖ∙ n i = preΩSqₖ∙ n i (i ≟ n)

ΩSqₖ : (n i : ℕ) → substΩEM (+'-suc' i n) .fst
                   ∘ EM→ΩEM+1 (i +' n)
                   ∘ Sqₖ {n = n} i
                   ∘ ΩEM+1→EM n
                   ≡ Ω→ (Sqₖ∙ {n = suc n} i) .fst
ΩSqₖ n i = cong fst (ΩSqₖ∙ n i)

⌣∘Sq∙ : (n m i : ℕ) → Kℤ/2 n → Kℤ/2∙ m →∙ Kℤ/2∙ (i +' (n +' m))
fst (⌣∘Sq∙ n m i x) y = Sqₖ i (x ⌣ₖ y)
snd (⌣∘Sq∙ n m i x) = cong (Sqₖ i) (⌣ₖ-0ₖ n m x) ∙ Sqₖ∙ i .snd

⌣∘Sq∙∙ : (n m i : ℕ) → Kℤ/2∙ n →∙ (Kℤ/2∙ m →∙ Kℤ/2∙ (i +' (n +' m)) ∙)
fst (⌣∘Sq∙∙ n m i) = ⌣∘Sq∙ n m i
snd (⌣∘Sq∙∙ n m i) = help
  where
  abstract
    help : ⌣∘Sq∙ n m i (0ₖ n) ≡ const∙ _ _
    help = →∙Homogeneous≡ (isHomogeneousEM _)
             (funExt λ y → cong (Sqₖ i) (0ₖ-⌣ₖ n m y)
                          ∙ Sqₖ∙ i .snd)

Ω→∙∙ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  → (A →∙ (B →∙ C ∙))
  → Ω A →∙ (B →∙ Ω C ∙)
fst (fst (Ω→∙∙ f) p) b i = Ω→ f .fst p i .fst b
snd (fst (Ω→∙∙ f) p) j i = Ω→ f .fst p i .snd j
fst (snd (Ω→∙∙ f) k) b i = Ω→ f .snd k i .fst b 
snd (snd (Ω→∙∙ f) k) j i = Ω→ f .snd k i .snd j


ℕP2 : (n m i : ℕ) → _ ≡ _
ℕP2 n m i = (cong (i +'_) (sym (+'-suc n m))
                                 ∙ sym (+'-suc' i (n +' m)))

delFst : (n m i : ℕ)
  → Kℤ/2∙ (suc n) →∙ (Kℤ/2∙ m →∙ Kℤ/2∙ (i +' (suc n +' m)) ∙)
  → Kℤ/2∙ n →∙ (Kℤ/2∙ m →∙ Kℤ/2∙ (i +' (n +' m)) ∙)
delFst n m i f = post∘∙ _ (ΩEM+1→EM∙ (i +' (n +' m))
                       ∘∙ substΩEM (ℕP2 n m i))
                       ∘∙ (Ω→∙∙ f ∘∙ EM→ΩEM+1∙ n)

cuper : (n m i : ℕ) → Kℤ/2∙ n →∙ (Kℤ/2∙ m →∙ Kℤ/2∙ (i +' (n +' m)) ∙)
fst (fst (cuper n m i) x) y = Sqₖ i (x ⌣ₖ y)
snd (fst (cuper n m i) x) = cong (Sqₖ i) (⌣ₖ-0ₖ n m x) ∙ Sqₖ∙ i .snd
snd (cuper n m i) =
  →∙Homogeneous≡ (isHomogeneousEM _) (funExt λ y → cong (Sqₖ i) (0ₖ-⌣ₖ n m y) ∙ Sqₖ∙ i .snd)

cool : (n m i : ℕ) → (suc n) +' m < i
  → delFst n m i (cuper (suc n) m i) ≡ cuper n m i 
cool n m i p =
  →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
    (funExt λ x → →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ y → cong (ΩEM+1→EM (i +' (n +' m)))
                      (cong (substΩEM (ℕP2 n m i) .fst)
                        (lem x y))
                    ∙ cong (ΩEM+1→EM (i +' (n +' m)))
                           (substSubst⁻ (λ n → Ω (EM∙ ℤ/2 n) .fst)
                             (ℕP2 n m i) (EM→ΩEM+1 (i +' (n +' m)) (Sqₖ i (x ⌣ₖ y)))) -- (transportTransport⁻ _ _)
                    ∙ {!so!}))
  where
  lem : (x : _) (y : _) → fst (fst (Ω→∙∙ (cuper (suc n) m i) ∘∙ EM→ΩEM+1∙ n) x) y
                        ≡ substΩEM (sym (ℕP2 n m i)) .fst
                                   (EM→ΩEM+1 _ (Sqₖ i (x ⌣ₖ y)))
  lem x y = {!ΩSqₖ n i!}
          ∙ {!!}
