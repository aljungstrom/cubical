{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Homotopy.EilenbergMacLane.Steenrod.Base where

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.FibreDelooping
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.Order2

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

isProp-fiberΩ→ : (n : ℕ)
     (g : (Ω (Kℤ/2∙ (suc n)) →∙ Ω (Kℤ/2∙ (n +' (suc n)))))
  → (isProp (fiber Ω→ g))
   × ((x : _) → isProp (Σ[ y ∈ _ ] (pre-alt-fibΩ x y g)))
isProp-fiberΩ→ n g = isOfHLevel-fiberΩ→ n 1 g (isConnectedEM (suc n))
         (subst (λ m → isOfHLevel m (Kℤ/2 (n +' suc n)))
           ℕlem
           (hLevelEM (Ring→AbGroup ℤ/2Ring) (n +' suc n)))
       , isOfHLevel-Total-pre-alt-fibΩ n 1 g (isConnectedEM (suc n))
         (subst (λ m → isOfHLevel m (Kℤ/2 (n +' suc n)))
           ℕlem
           (hLevelEM (Ring→AbGroup ℤ/2Ring) (n +' suc n)))
  where
  ℕlem : (2 + (n +' suc n)) ≡ suc (suc (n + n + 1))
  ℕlem = cong (suc ∘ suc) (+'≡+ n (suc n)
                        ∙ +-suc n n
                        ∙ +-comm 1 (n + n))

-- Ω K(n + 1,ℤ/2) ≃ K(n,ℤ/2) --ᶠ→ K(2n,ℤ/2) ≃ Ω K(2n + 1,ℤ/2)
-- where f := ⌣ₖ ∘ Δ
⌣-deloop : (n : ℕ)
  → (Ω (Kℤ/2∙ (suc n)) →∙ Ω (Kℤ/2∙ (n +' (suc n))))
fst (⌣-deloop n) x =
  subst (λ m → fst (Ω (Kℤ/2∙ m))) (+'-suc' n n)
       (EM→ΩEM+1 (n +' n) (cupℤ/2 n n (ΩEM+1→EM n x) (ΩEM+1→EM n x)))
snd (⌣-deloop n) =
  cong (subst (λ m → fst (Ω (Kℤ/2∙ m))) (+'-suc' n n))
       (cong (EM→ΩEM+1 (n +' n))
         (cong (λ x → cupℤ/2 n n x x) (ΩEM+1→EM-refl n) ∙ ⌣ₖ-0ₖ n n (0ₖ n))
         ∙ EM→ΩEM+1-0ₖ (n +' n))
     ∙ substΩEM-refl (+'-suc' n n)

fib-deloop : (n : ℕ) → fiber Ω→ (⌣-deloop n)
fib-deloop n = fib-deloop'
  where
  substResp· : {n : ℕ} (m : ℕ) (t : n ≡ m) (p q : _)
    → subst (λ m → fst (Ω (Kℤ/2∙ m))) t (p ∙ q)
     ≡ subst (λ m → fst (Ω (Kℤ/2∙ m))) t p
     ∙ subst (λ m → fst (Ω (Kℤ/2∙ m))) t q
  substResp· =
    J> λ p q → transportRefl _
              ∙ sym (cong₂ _∙_ (transportRefl p)
                               (transportRefl q))

  distrLem : (p q : EM ℤ/2 n)
    → cupℤ/2 n n p p +ₖ cupℤ/2 n n (p +ₖ q) (p +ₖ q)
     ≡ cupℤ/2 n n q q
  distrLem p q =
      cong (+ₖ-syntax (n +' n) (cupℤ/2 n n p p))
           cupℤ/2ΔDistr
     ∙ assocₖ (n +' n) _ _ _
     ∙ cong (_+ₖ cupℤ/2 n n q q) (+ₖ≡id-ℤ/2 (n +' n) _)
     ∙ lUnitₖ (n +' n) (cupℤ/2 n n q q)
    where
    cupℤ/2ΔDistr : cupℤ/2 n n (p +ₖ q) (p +ₖ q)
                 ≡ cupℤ/2 n n p p +ₖ cupℤ/2 n n q q
    cupℤ/2ΔDistr = distrR⌣ₖ n n p q (p +ₖ q)
         ∙ cong₂ _+ₖ_ (distrL⌣ₖ n n p p q) (distrL⌣ₖ n n q p q)
         ∙ sym (assocₖ (n +' n) _ _ _)
         ∙ cong (+ₖ-syntax (n +' n) (cupℤ/2 n n p p))
                (assocₖ (n +' n) _ _ _
               ∙ cong (λ z → z +ₖ cupℤ/2 n n q q)
                      (cong (+ₖ-syntax (n +' n) (p ⌣ₖ q))
                        (⌣ₖ-commℤ/2 n n q p
                      ∙ (λ i → subst (EM ℤ/2)
                           (isSetℕ _ _ (+'-comm n n) refl i)
                           (cupℤ/2 n n p q))
                      ∙ transportRefl (cupℤ/2 n n p q))
                    ∙ +ₖ≡id-ℤ/2 (n +' n) _)
               ∙ lUnitₖ (n +' n) (cupℤ/2 n n q q))
  abstract
    fib-deloop' : fiber Ω→ (⌣-deloop n)
    fib-deloop' = Iso.fun (Iso/alt-fibΩ/fibΩ→ (⌣-deloop n))
        (EM→Prop _ n (λ _ → isProp-fiberΩ→ n (⌣-deloop n) .snd _)
          (0ₖ (n +' suc n)
        , (⌣-deloop n .fst)
        , λ p → →∙Homogeneous≡ (isHomogeneousPath _ _)
        (funExt λ q →
          sym (substResp· _ (+'-suc' n n) _ _)
        ∙ cong (subst (λ m → fst (Ω (Kℤ/2∙ m))) (+'-suc' n n))
               (cong₂ _∙_ (sym (EM→ΩEM+1-sym (n +' n) _)
                        ∙ cong (EM→ΩEM+1 (n +' n))
                           (-ₖConst-ℤ/2-gen (n +' n)
                             (cupℤ/2 n n (ΩEM+1→EM n p) (ΩEM+1→EM n p))))
                        (cong (EM→ΩEM+1 (n +' n))
                          (cong₂ (cupℤ/2 n n)
                            (ΩEM+1→EM-hom n p q)
                            (ΩEM+1→EM-hom n p q)))
              ∙ sym (EM→ΩEM+1-hom (n +' n) _ _)
              ∙ cong (EM→ΩEM+1 (n +' n))
                 (distrLem _ _)))))

-- equivalence K(n,ℤ/2) →∙ K(i + n,ℤ/2)
-- with ΩK(n,ℤ/2) →∙ ΩK(i + n,ℤ/2)
-- for i < n - 1 and n ≥ 1
deloopKℤ/2FunIso : (n i : ℕ) → (i < n)
  → Kℤ/2∙ (suc n) →∙ Kℤ/2∙ (i +' (suc n))
  ≃ Ω (Kℤ/2∙ (suc n)) →∙ Ω (Kℤ/2∙ (i +' (suc n)))
fst (deloopKℤ/2FunIso n i p) = Ω→
snd (deloopKℤ/2FunIso zero i p) =
  ⊥.rec (snotz (+-comm (suc i) (fst p) ∙ snd p))
snd (deloopKℤ/2FunIso (suc n) i (x , p)) = record { equiv-proof = isEq-deloop }
  where
  ℕPath : 2 + (i +' suc (x + suc i)) + x
         ≡ suc (suc (suc n + suc n + 0))
  ℕPath =
    (cong suc
        (cong suc
           (cong (_+ x) (+'≡+ i (suc (x + suc i)))
          ∙ (sym (+-assoc i (suc (x + suc i)) x)
          ∙ cong (λ z → i + suc z)
                 (sym (+-assoc x (suc i) x)
               ∙ cong (x +_) (cong suc (+-comm i x)
                            ∙ sym (+-suc x i)))
          ∙ +-suc i (x + (x + suc i))
          ∙ +-assoc (suc i) x (x + suc i)
          ∙ cong (_+ (x + suc i))
               (+-comm (suc i) x))
          ∙ sym (+'≡+ (x + suc i) (x + suc i)))
         ∙ (+'-suc (x + suc i) (x + suc i))
         ∙ +'-comm (suc (x + suc i)) (x + suc i))
     ∙ cong suc (cong₂ _+'_ p (cong suc p))
     ∙ cong (suc ∘ suc ∘ suc) (+-comm 0 (n + suc n)))

  abstract
    isEq-deloop :
      (g : Ω (Kℤ/2∙ (suc (suc n))) →∙ Ω (Kℤ/2∙ (i +' suc (suc n))))
      → isContr (fiber Ω→ g)
    isEq-deloop g =
      isOfHLevel-fiberΩ→ (suc n) 0 g (isConnectedEM (suc (suc n)))
       (subst2 (λ m n → isOfHLevel m (Kℤ/2 (i +' suc n)))
         ℕPath
         p
         (isOfHLevelPlus' {n = x} (2 + (i +' suc (x + suc i)))
           (hLevelEM (Ring→AbGroup ℤ/2Ring) (i +' suc (x + suc i)))))
-- deloopKℤ/2FunIso

ΩKℤ/2→Kℤ/2-FunSpaceIso : (n i : ℕ)
  → ((Ω (Kℤ/2∙ (suc n)) →∙ Ω (Kℤ/2∙ (i +' (suc n)))))
   ≃ (Kℤ/2∙ n →∙ Kℤ/2∙ (i +' n))
ΩKℤ/2→Kℤ/2-FunSpaceIso n i =
  isoToEquiv
   (compIso
    (post∘∙equiv ((isoToEquiv (invIso (Iso-EM-ΩEM+1 n))) , ΩEM+1→EM-refl n))
      (pre∘∙equiv
        (compEquiv∙ ((substEquiv' (λ x → fst (Ω (Kℤ/2∙ x)))
          ((+'-comm i (suc n) ∙ sym (+'-suc n i)) ∙ cong suc (+'-comm n i)))
          , substΩEM-refl ((+'-comm i (suc n) ∙ sym (+'-suc n i))
                       ∙ cong suc (+'-comm n i)))
      ((isoToEquiv (invIso (Iso-EM-ΩEM+1 (i +' n))))
      , ΩEM+1→EM-refl (i +' n)))))

Kℤ/2-FunSpaceIso↑ : (n i : ℕ) → (i < n)
  → (Kℤ/2∙ (suc n) →∙ Kℤ/2∙ (i +' (suc n)))
   ≃ (Kℤ/2∙ n →∙ Kℤ/2∙ (i +' n))
Kℤ/2-FunSpaceIso↑ n i p =
  compEquiv
    (deloopKℤ/2FunIso n i p)
    (ΩKℤ/2→Kℤ/2-FunSpaceIso n i)

-- Steenrod squares, by case distinction on i < n, i = n, i > n
Sqₖ∙-gen : (n i : ℕ) → Trichotomy i n → Kℤ/2∙ n →∙ Kℤ/2∙ (i +' n)
Sqₖ∙-gen zero zero p = id∙ _
Sqₖ∙-gen zero (suc i) p = (λ _ → 0ₖ (suc i)) , refl
Sqₖ∙-gen (suc n) zero p = id∙ _
fst (Sqₖ∙-gen (suc n) (suc i) (lt (zero , p))) x =
  substEM (cong (_+' (suc n)) (sym (cong predℕ p))) .fst
    (fib-deloop n .fst .fst x)
snd (Sqₖ∙-gen (suc n) (suc i) (lt (zero , p))) =
    cong (substEM (cong (_+' (suc n)) (sym (cong predℕ p))) .fst)
         (fib-deloop n .fst .snd)
  ∙ substEM0ₖ _
Sqₖ∙-gen (suc n) (suc i) (lt (suc x , p)) =
  invEq (Kℤ/2-FunSpaceIso↑ n (suc i) (x , cong predℕ p))
    (Sqₖ∙-gen n (suc i) (lt (x , cong predℕ p)))
fst (Sqₖ∙-gen (suc n) (suc i) (eq q)) x =
  substEM (cong (_+' (suc n))  (sym q)) .fst (cupℤ/2 (suc n) (suc n) x x)
snd (Sqₖ∙-gen (suc n) (suc i) (eq q)) =
    cong (substEM (cong (_+' (suc n))  (sym q)) .fst)
         (0ₖ-⌣ₖ (suc n) (suc n) (0ₖ (suc n)))
  ∙ substEM0ₖ _
Sqₖ∙-gen (suc n) (suc i) (gt q) = (λ _ → 0ₖ (suc (suc (i + n)))) , refl

-- Steenrod squares
Sqₖ∙ : {n : ℕ} (i : ℕ) → Kℤ/2∙ n →∙ Kℤ/2∙ (i +' n)
Sqₖ∙ {n = n} i = Sqₖ∙-gen n i (i ≟ n)

Sqₖ : {n : ℕ} (i : ℕ) → Kℤ/2 n → Kℤ/2 (i +' n)
Sqₖ i = Sqₖ∙ i .fst

-- On cohomology (TODO: move to cohomology folder)
Sq : ∀ {ℓ} {A : Type ℓ} {n : ℕ} (i : ℕ)
  → coHom n ℤ/2 A → coHom (i +' n) ℤ/2 A
Sq i = ST.map λ f x → Sqₖ i (f x)

Sq-nat : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) {n : ℕ} (i : ℕ)
  → (x : coHom n ℤ/2 B)
  → (f *H) (Sq i x) ≡ Sq i ((f *H) x)
Sq-nat f i = ST.elim (λ _ → isSetPathImplicit) λ f → refl
{-
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
fst (ΩSqFun n i) x = subst (λ n → fst (Ω (EM∙ ℤ/2 n)))
                        (+'-suc' i n)
                        (EM→ΩEM+1 (i +' n) (Sqₖ {n = n} i (ΩEM+1→EM n x)))
snd (ΩSqFun n i) =
      cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' i n))
         (cong (EM→ΩEM+1 (i +' n))
           (cong (Sqₖ i)
             (ΩEM+1→EM-refl n)
          ∙ Sqₖ∙ i .snd)
        ∙ EM→ΩEM+1-0ₖ (i +' n))
  ∙ λ j → transp (λ k → fst (Ω (EM∙ ℤ/2 (+'-suc' i n (j ∨ k))))) j refl

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

cong₂-cupℤ/2 : (n : ℕ) (q : 0ₖ n ≡ 0ₖ n) → cong₂ (cupℤ/2 n n) q q ≡ refl
cong₂-cupℤ/2 = cong₂-⌣ₖ ℤ/2Ring

substRefl-lem : {n : ℕ} (m : ℕ) (p : n ≡ m) →
  subst (λ n₁ → fst (Ω (EM∙ ℤ/2 n₁))) p refl ≡ refl
substRefl-lem = J> (transportRefl refl)

Ω-Sq' : (n i : ℕ) → Trichotomy i n
  → ΩSqFun n i ≡ Ω→ (Sqₖ∙ {n = suc n} i)
Ω-Sq' zero zero p =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt λ x → cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' zero zero))
      (Iso.rightInv (Iso-EM-ΩEM+1 zero) x)
    ∙ transportRefl x
    ∙ wrap-id 1 refl x _ refl)
Ω-Sq' zero (suc i) (lt x) = ⊥.rec (snotz (sym (+-suc _ _) ∙ x .snd))
Ω-Sq' zero (suc i) (eq p) = ⊥.rec (snotz p)
Ω-Sq' zero (suc i) (gt (zero , p)) =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q →   cong (substΩEM (+'-suc' (suc i) zero) .fst)
                       (cong (EM→ΩEM+1 (suc i))
                         (λ j → Sqₖ∙-gen 0 (suc i)
                         (isPropTrichotomy (suc i ≟ 0) (gt (i , +-comm i 1)) j) .fst (ΩEM+1→EM zero q))
                      ∙ EM→ΩEM+1-0ₖ (suc i))
                    ∙ substΩEM (+'-suc' (suc i) zero) .snd
                    ∙ sym (funExt⁻ (cong fst h) q)))
  ∙ cong Ω→ (cong (Sqₖ∙-gen 1 (suc i)) (isPropTrichotomy (eq (sym p)) (suc i ≟ 1)))
  where
  pr : (q : snd (Kℤ/2∙ 1) ≡ snd (Kℤ/2∙ 1))
     → cong (subst (λ m → Kℤ/2 (m +' 1)) p)
           (cong₂ (cupℤ/2 1 1) q q)
     ≡ refl
  pr q = cong (cong (subst (λ m → Kℤ/2 (m +' 1)) p)) (cong₂-cupℤ/2 1 q)

  h : Ω→ (Sqₖ∙-gen 1 (suc i) (eq (sym p))) ≡ ((λ _ → refl) , refl)
  h = →∙Homogeneous≡ (isHomogeneousPath _ _)
       (funExt λ q → cong₂ (λ x y → sym x ∙∙ y ∙∙ x) refl (pr q)
                    ∙ ∙∙lCancel _)

Ω-Sq' zero (suc i) (gt (suc x , p)) =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt (λ q → cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' (suc i) zero))
                         (cong (EM→ΩEM+1 (suc i))
                           ((λ j → Sqₖ∙-gen zero (suc i) (isPropTrichotomy (suc i ≟ zero)
                             (gt (i , +-comm i 1)) j) .fst (ΩEM+1→EM zero q))))
                  ∙ cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' (suc i) zero)) (EM→ΩEM+1-0ₖ _)
                  ∙ substΩEM (+'-suc' (suc i) zero) .snd))
  ∙ sym (Ω^→const 1)
  ∙ cong Ω→ (cong (Sqₖ∙-gen 1 (suc i)) (isPropTrichotomy (gt (x , +-suc x 1 ∙ p)) (suc i ≟ 1)))
Ω-Sq' (suc n) zero p =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q → substℕSwap {B = fst ∘ Ω ∘ Kℤ/2∙} (+'-suc' zero (suc n)) refl _
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
Ω-Sq' (suc n) (suc i) (lt (zero , p)) =
     →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q → substℕSwap {B = λ n → Ω (Kℤ/2∙ n) .fst} (+'-suc' (suc i) (suc n)) (sym (cong (2 +_) (+-suc i n)))
                         (EM→ΩEM+1 (suc (suc (i + n))) (Sqₖ (suc i) (ΩEM+1→EM (suc n) q)))
            ∙ substCommSlice Kℤ/2 (λ n → fst (Ω (Kℤ/2∙ (suc n)))) EM→ΩEM+1 (cong suc (sym (+-suc i n)))
                         (Sqₖ (suc i) (ΩEM+1→EM (suc n) q))
           ∙ cong (EM→ΩEM+1 (suc (i + suc n)))
               (cong (subst Kℤ/2 (cong suc (sym (+-suc i n))))
                 λ k → Sqₖ∙-gen (suc n) (suc i)
                           (isPropTrichotomy (suc i ≟ suc n) (lt (0 , p)) k) .fst (ΩEM+1→EM (suc n) q))))
  ∙ (sym (secEq (deloopKℤ/2FunIso (suc n) (suc i) (0 , p)) _)
  ∙ cong Ω→ (sym help))
  ∙ cong Ω→ λ j → Sqₖ∙-gen (suc (suc n)) (suc i)
            (isPropTrichotomy (lt (1 , cong suc p)) (suc i ≟ suc (suc n)) j)
  where
  ℕP = (+'-comm (suc i) (suc (suc n)) ∙
      (λ i₂ → +'-suc (suc n) (suc i) (~ i₂)))
     ∙ (λ i₂ → suc (+'-comm (suc n) (suc i) i₂))

  helplem : (x : _) → substΩEM (sym ℕP) .fst (EM→ΩEM+1 (suc (suc (i + n))) x)
                     ≡ EM→ΩEM+1 (suc (i + suc n)) (substEM (cong suc (sym (+-suc i n))) .fst x)
  helplem x = substℕSwap {B = λ n → Ω (Kℤ/2∙ n) .fst} (sym ℕP) (sym (cong (2 +_) (+-suc i n)))
                         (EM→ΩEM+1 (suc (suc (i + n))) x)
            ∙ substCommSlice Kℤ/2 (λ n → fst (Ω (Kℤ/2∙ (suc n)))) EM→ΩEM+1 (cong suc (sym (+-suc i n))) x

  help : Sqₖ∙-gen (suc (suc n)) (suc i) (lt (1 , cong suc p))
       ≡ invEq (deloopKℤ/2FunIso (suc n) (suc i) (0 , p))
               ((EM→ΩEM+1 ((suc (i + suc n))) , EM→ΩEM+1-0ₖ (suc (i + suc n)))
               ∘∙ ((substEM (cong suc (sym (+-suc i n)))
                ∘∙ Sqₖ∙-gen (suc n) (suc i) (lt (0 , p)))
                ∘∙ (ΩEM+1→EM∙ (suc n))))
  help = cong (invEq (deloopKℤ/2FunIso (suc n) (suc i) (0 , p)))
         (→∙Homogeneous≡ (isHomogeneousPath _ _)
           (funExt (λ q →
              helplem (subst (λ m → Kℤ/2 (m +' suc n)) (λ i₁ → predℕ (p (~ i₁)))
              (fib-deloop n .fst .fst (ΩEM+1→EM (suc n) q))))))
Ω-Sq' (suc n) (suc i) (lt (suc x , p)) =
   →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q → substℕSwap {B = λ n → Ω (Kℤ/2∙ n) .fst}
                         (+'-suc' (suc i) (suc n))  (sym (cong (suc ∘ suc) (+-suc i n)))
                         (EM→ΩEM+1 (suc (suc (i + n))) (Sqₖ (suc i) (ΩEM+1→EM (suc n) q)))
                   ∙∙ substCommSlice Kℤ/2 (λ n → fst (Ω (Kℤ/2∙ (suc n))))
                         EM→ΩEM+1 (cong suc (sym (+-suc i n)))
                          (Sqₖ (suc i) (ΩEM+1→EM (suc n) q))
                   ∙∙ cong (EM→ΩEM+1 (suc (i + suc n)))
                       (cong (fst HH)
                         λ k → Sqₖ∙-gen (suc n) (suc i)
                           (isPropTrichotomy (suc i ≟ suc n) (lt (suc x , p)) k)
                           .fst (ΩEM+1→EM (suc n) q))))
  ∙ sym (secEq (deloopKℤ/2FunIso (suc n) (suc i) (suc x , p))
      ((EM→ΩEM+1 ((suc (i + suc n))) , EM→ΩEM+1-0ₖ (suc (i + suc n)))
               ∘∙ ((HH
                ∘∙ Sqₖ∙-gen (suc n) (suc i) (lt ((suc x) , p)))
                ∘∙ (ΩEM+1→EM∙ (suc n)))))
  ∙ cong Ω→ (sym help)
  ∙ cong Ω→ λ j → Sqₖ∙-gen (suc (suc n)) (suc i)
            (isPropTrichotomy (lt (suc (suc x) ,  cong suc p))
            (suc i ≟ suc (suc n)) j)
  where
  HH : Kℤ/2∙ (suc (suc (i + n))) →∙ Kℤ/2∙ (suc (i + (suc n)))
  HH = substEM (cong suc (sym (+-suc i n)))

  ℕP = (+'-comm (suc i) (suc (suc n)) ∙
        (λ i₂ → +'-suc (suc n) (suc i) (~ i₂)))
       ∙ (λ i₂ → suc (+'-comm (suc n) (suc i) i₂))
  ℕP≡ : ℕP ≡ cong (2 +_) (+-suc i n)
  ℕP≡ = isSetℕ _ _ _ _

  helplem : (x : _) → substΩEM (sym ℕP) .fst (EM→ΩEM+1 (suc (suc (i + n))) x)
                     ≡ EM→ΩEM+1 (suc (i + suc n)) (substEM (cong suc (sym (+-suc i n))) .fst x)
  helplem x = substℕSwap {B = λ n → Ω (Kℤ/2∙ n) .fst} (sym ℕP) (sym (cong (2 +_) (+-suc i n)))
                         (EM→ΩEM+1 (suc (suc (i + n))) x)
            ∙ substCommSlice Kℤ/2 (λ n → fst (Ω (Kℤ/2∙ (suc n)))) EM→ΩEM+1 (cong suc (sym (+-suc i n))) x

  help : Sqₖ∙-gen (suc (suc n)) (suc i) (lt (2 + x , cong suc p))
      ≡ invEq (deloopKℤ/2FunIso (suc n) (suc i) (suc x , p))
               ((EM→ΩEM+1 ((suc (i + suc n))) , EM→ΩEM+1-0ₖ (suc (i + suc n)))
               ∘∙ ((HH
                ∘∙ Sqₖ∙-gen (suc n) (suc i) (lt (((suc x)) , p)))
                ∘∙ (ΩEM+1→EM∙ (suc n))))
  help = cong (invEq (deloopKℤ/2FunIso (suc n) (suc i) (suc x , p)))
              (→∙Homogeneous≡ (isHomogeneousPath _ _)
                (funExt λ q → cong (substΩEM (sym ℕP) .fst)
                                    (λ _ → EM→ΩEM+1 (suc (suc (i + n)))
                                      (Sqₖ∙-gen (suc n) (suc i)
                                         (lt (suc x , p)) .fst (ΩEM+1→EM (suc n) q)))
                             ∙ helplem (Sqₖ∙-gen (suc n) (suc i)
                                  (lt (suc x , p)) .fst (ΩEM+1→EM (suc n) q))))

Ω-Sq' (suc n) (suc i) (eq p) =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q → cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' (suc i) (suc n)))
                          (cong (EM→ΩEM+1 (suc (suc (i + n))))
                            (λ j → Sqₖ∙-gen (suc n) (suc i)
                                     (isPropTrichotomy
                                     (suc i ≟ suc n) (eq p) j) .fst
                                     (ΩEM+1→EM (suc n) q))
                        ∙ sym (substCommSlice Kℤ/2 (fst ∘ Ω ∘ Kℤ/2∙ ∘ suc) EM→ΩEM+1
                            (cong (_+' suc n) (sym p))
                            (cupℤ/2 (suc n) (suc n) (ΩEM+1→EM (suc n) q) (ΩEM+1→EM (suc n) q))))
                    ∙ sym (substComposite (fst ∘ Ω ∘ Kℤ/2∙)
                       (λ i₁ → suc (p (~ i₁) +' suc n)) (+'-suc' (suc i) (suc n)) _)
                    ∙ substℕSwap _ _ _
                    ∙ substComposite (fst ∘ Ω ∘ Kℤ/2∙)
                       (+'-suc' (suc n) (suc n)) (λ i₁ → sym p i₁ +' suc (suc n)) _
                    ∙ sym (Ω→H≡ (⌣-deloop (suc n) .fst q))))
  ∙ (refl
  ∙ (λ i → Ω→ H ∘∙ (fib-deloop (suc n) .snd (~ i))))
  ∙ sym (Ω→∘∙ H (fib-deloop (suc n) .fst))
  ∙ cong Ω→ (sym help)
  ∙ cong Ω→ λ j → Sqₖ∙-gen (suc (suc n)) (suc i)
     (isPropTrichotomy (lt (zero , cong suc p)) (suc i ≟ suc (suc n)) j)
  where
  H : Kℤ/2∙ (suc (suc (n + suc n))) →∙ Kℤ/2∙ (suc (suc (i + suc n)))
  fst H = subst (λ m → Kℤ/2 (m +' suc (suc n))) (sym p)
  snd H = substEM0ₖ _

  Ω→H≡  : (x : _) → Ω→ H .fst x
                   ≡ subst (fst ∘ Ω ∘ Kℤ/2∙)
                     (λ i → ((sym p i) +' suc (suc n))) x
  Ω→H≡ x = funExt⁻ (cong fst (sym (substΩEM≡ (λ i → ((sym p i) +' suc (suc n)))))) x


  help : Sqₖ∙-gen (suc (suc n)) (suc i) (lt (0 , cong suc p))
       ≡ (H
       ∘∙ fib-deloop (suc n) .fst)
  help = →∙Homogeneous≡ (isHomogeneousEM (suc (suc (i + suc n)))) refl
Ω-Sq' (suc n) (suc i) (gt (zero , p)) =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q →
        cong (substΩEM (+'-suc' (suc i) (suc n)) .fst)
                 (cong (EM→ΩEM+1 (suc (suc (i + n))))
                   (λ j → Sqₖ∙-gen (suc n) (suc i)
                           (isPropTrichotomy (suc i ≟ suc n)
                             (gt (0 , p)) j) .fst (ΩEM+1→EM (suc n) q))
                ∙ EM→ΩEM+1-0ₖ (suc (suc (i + n))))
  ∙∙ (substRefl-lem _ (+'-suc' (suc i) (suc n))
               ∙ sym (∙∙lCancel _))
  ∙∙ cong₂ (λ x y → sym x ∙∙ y ∙∙ x) refl
       (sym (cong (cong (subst (λ m → Kℤ/2 m) (cong (_+' suc (suc n)) p)))
         (cong₂-cupℤ/2 (suc (suc n)) q)))))
  ∙ cong (Ω→ ∘ Sqₖ∙-gen (suc (suc n)) (suc i))
      (isPropTrichotomy
        (eq (sym p))
        (suc i ≟ suc (suc n)))
Ω-Sq' (suc n) (suc i) (gt (suc x , p)) =
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
-}

open import Cubical.HITs.EilenbergMacLane1
_^ : Kℤ/2 1 → Kℤ/2 1
_^ = elimGroupoid (AbGroup→Group ℤ/2)
       (λ _ → emsquash)
       {!!}
       {!!}
       {!!}

open import Cubical.HITs.SmashProduct

asd : (n : ℕ) (A B : Pointed₀)
  → Iso ((Smash A B , proj (pt A) (pt B)) →∙ (Kℤ/2∙ n))
         ((typ A × typ B , pt A , pt B) →∙ (Kℤ/2∙ n))
fst (fun (asd n A B) f) x = fst f (proj (fst x) (snd x))
snd (fun (asd n A B) f) = snd f
fst (inv (asd n A B) f) basel = fst f (pt A , pt B)
fst (inv (asd n A B) f) baser = fst f (pt A , pt B)
fst (inv (asd n A B) f) (proj x y) = ((fst f (x , y)) -ₖ fst f (x , pt B)) -ₖ fst f (pt A , y)
fst (inv (asd n A B) f) (gluel a i) = {!fst f (pt A , pt B)!}
fst (inv (asd n A B) f) (gluer b i) = {!cong₂ (λ x y → x -ₖ y) ? ? ∙ ?!}
snd (inv (asd n A B) f) = cong₂ (λ x y → x -ₖ y) (rCancelₖ n (fst f (pt A , pt B))) (snd f) ∙ rCancelₖ n (0ₖ n)
rightInv (asd n A B) (f , p) = →∙Homogeneous≡ (isHomogeneousEM _) (funExt λ {(x , y) → {!!}})
leftInv (asd n A B) = {!!}


asd' : (n : ℕ) (A B : Pointed₀) → Smash (Ω A) B → typ (Ω (Smash A B , proj (pt A) (pt B)))
asd' n A B basel = refl
asd' n A B baser = refl
asd' n A B (proj x y) = (sym (gluer y ∙ sym (gluer (pt B))) ∙∙ cong (λ x → proj x y) x ∙∙ (gluer y ∙ sym (gluer (pt B)))) -- proj (x i) (pt B)
asd' n A B (gluel a i) j = {!!}
asd' n A B (gluer b i) = {!!}

incl : (A B : Pointed₀) (x : Smash A B) → Path (Smash A B) (proj (pt A) (pt B)) x → Smash (Ω A) B
incl A B basel p = {!p!}
incl A B baser p = {!!}
incl A B (proj x y) q = {!q!}
incl A B (gluel a i) = {!!}
incl A B (gluer b i) = {!!}

asd'' : (n : ℕ) (A B : Pointed₀) → typ (Ω (Smash A B , proj (pt A) (pt B))) → Smash (Ω A) B
asd'' n A B = {!!}

module _ (A B : Pointed₀)
         (rA : (a : typ A) → Ω A ≃∙ Ω (typ A , a))
         (rB : (b : typ B) → B ≃∙ fst B , b) where
  looper : Smash A B → Type
  looper basel = Smash (Ω A) B
  looper baser = Smash (Ω A) B
  looper (proj x y) = Smash ((x ≡ x) , refl) ((typ B , y))
  looper (gluel a i) = Smash (ua∙ (invEquiv∙ (rA a) .fst) (invEquiv∙ (rA a) .snd) i) B
  looper (gluer b i) = Smash (Ω A) (ua∙ (invEquiv∙ (rB b) .fst) (invEquiv∙ (rB b) .snd) i)

  br : (x : Smash A B) (p : proj (pt A) (pt B) ≡ x) → looper x
  br = J> proj refl (pt B)

  tst : (p : proj (pt A) (pt B) ≡ proj (pt A) (pt B)) → Smash (Ω A) B
  tst p = br _ p

  inn : looper basel → Path (Smash A B) (proj (pt A) (pt B)) basel
  inn basel = gluel (pt A)
  inn baser = gluel (pt A)
  inn (proj x y) = {!!} ∙∙ (cong (λ x → proj x y) x) ∙∙ (gluer y ∙ {!!})
  inn (gluel a i) = {!!}
  inn (gluer b i) = {!!}

  looper⁻ : (x : Smash A B) → looper x → proj (pt A) (pt B) ≡ x
  looper⁻ basel p = {!!}
  looper⁻ baser p = {!!}
  looper⁻ (proj x y) p = {!p!}
  looper⁻ (gluel a i) p = {!!}
  looper⁻ (gluer b i) p = {!!}

open import Cubical.Foundations.Path

pointedEq : (A B : Pointed₀) (f g : A →∙ B)
  → isHomogeneous B
  → Iso (f ≡ g)
         ((a : typ A)
         → Σ[ p ∈ fst f a ≡ fst g a ]
              ((q : pt A ≡ a) → PathP (λ j → (cong (fst f) q ∙∙ p ∙∙ cong (fst g) (sym q)) j ≡ pt B) (snd f) (snd g)))
fst (fun (pointedEq A B f g hom) p a) i = p i .fst a
snd (fun (pointedEq A B f g hom) p a) =
  J (λ a q → PathP
      (λ j →
         (cong (fst f) q ∙∙ (λ i → p i .fst a) ∙∙ cong (fst g) (sym q)) j ≡
         pt B)
      (snd f) (snd g))
      (flipSquare (sym (rUnit (λ i → p i .fst (snd A))) ◁ flipSquare (cong snd p)))
{-
  hcomp (λ k → λ {(i = i0) → {!snd f j!}
                 ; (i = i1) → {!!}
                 ; (j = i0) → doubleCompPath-filler (cong (fst f) q) (λ i → p i .fst a) (cong (fst g) (sym q)) k i
                 ; (j = i1) → {!!}})
        {!p i .snd j!}
  where
  help : {!———— Boundary ——————————————————————————————————————————————
i = i0 ⊢ snd f j
i = i1 ⊢ snd g j
j = i0 ⊢ (cong (fst f) q ∙∙ fst (fun (pointedEq A B f g hom) p a)
          ∙∙ cong (fst g) (sym q))
         i
j = i1 ⊢ pt B!} -- (q : _) → s (pt A) .fst ≡ ((cong (fst f) q) ∙∙ fst (s (pt A)) ∙∙ cong (fst g) (sym q))
  help = {!!} -- rUnit _ ∙ λ j → (λ i → fst f (q (j ∧ i))) ∙∙ s (q j) .fst ∙∙ λ i → fst g (q (j ∧ ~ i)) -}
inv (pointedEq A B f g hom) s = ΣPathP ((funExt (λ a → s a .fst))
  , flipSquare (rUnit _ ◁ flipSquare (s (pt A) .snd refl)))
rightInv (pointedEq A B f g hom) s = funExt (λ a → ΣPathP (refl , {!refl!}))
leftInv (pointedEq A B f g hom) = {!!}

isOfHLevelΠ↓ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} (n : ℕ)
  → isOfHLevel n ((x : A) → B x)
  → (x : A) → isOfHLevel n (B x) 
isOfHLevelΠ↓ zero hlev x = (fst hlev x) , (λ y → {!snd hle !})
isOfHLevelΠ↓ (suc zero) hlev x = {!hlev!}
isOfHLevelΠ↓ (suc (suc zero)) hlev x y z = {!hlev !}
isOfHLevelΠ↓ (suc (suc (suc n))) hlev x = {!!}
