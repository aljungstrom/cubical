{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.HITs.Truncation.Properties where
open import Cubical.Data.NatMinusOne
open import Cubical.HITs.Truncation.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.PathSplit
open isPathSplitEquiv
open import Cubical.Modalities.Modality
open Modality

open import Cubical.Data.Empty.Base as ⊥ renaming (rec to ⊥rec ; elim to ⊥elim)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification as Null hiding (rec; elim)

open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (∥_∥ to ∥_∥₁; ∣_∣ to ∣_∣₁; squash to squash₁) using ()
open import Cubical.HITs.SetTruncation       as SetTrunc  using (∥_∥₂; ∣_∣₂; squash₂)
open import Cubical.HITs.GroupoidTruncation  as GpdTrunc  using (∥_∥₃; ∣_∣₃; squash₃)
open import Cubical.HITs.2GroupoidTruncation as 2GpdTrunc using (∥_∥₄; ∣_∣₄; squash₄)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

sphereFill : (n : ℕ) (f : S₊ n → A) → Type _
sphereFill {A = A} n f = Σ[ top ∈ A ] ((x : S₊ n) → top ≡ f x)

isSphereFilled : ℕ → Type ℓ → Type ℓ
isSphereFilled n A = (f : S₊ n → A) → sphereFill n f

isSphereFilled∥∥ : {n : ℕ} → isSphereFilled n (HubAndSpoke A n)
isSphereFilled∥∥ f = (hub f) , (spoke f)

isSphereFilled→isOfHLevel : (n : ℕ) → isSphereFilled n A → isOfHLevel (suc n) A
isSphereFilled→isOfHLevel {A = A} zero h x y = sym (snd (h f) true) ∙ snd (h f) false
  where
    f : Bool → A
    f true = x
    f false = y
isSphereFilled→isOfHLevel {A = A} (suc zero) h x y =
  J (λ y q → (p : x ≡ y) → q ≡ p) (helper x)
  where
  helper : (x : A) (p : x ≡ x) → refl ≡ p
  helper x p i j =
    hcomp (λ k → λ { (i = i0) → h S¹→A .snd base k
                   ; (i = i1) → p j
                   ; (j = i0) → h S¹→A .snd base (i ∨ k)
                   ; (j = i1) → h S¹→A .snd base (i ∨ k)})
          (h S¹→A .snd (loop j) i)
    where
    S¹→A : S¹ → A
    S¹→A base = x
    S¹→A (loop i) = p i
isSphereFilled→isOfHLevel {A = A} (suc (suc n)) h x y =
  isSphereFilled→isOfHLevel (suc n) (helper h x y)
  where
    helper : {n : ℕ} → isSphereFilled (suc (suc n)) A → (x y : A) → isSphereFilled (suc n) (x ≡ y)
    helper {n = n} h x y f = sym (snd (h f') north) ∙ (snd (h f') south) , r
      where
        f' : Susp (S₊ (suc n)) → A
        f' north = x
        f' south = y
        f' (merid u i) = f u i

        r : (s : S₊ (suc n)) → sym (snd (h f') north) ∙ (snd (h f') south) ≡ f s
        r s i j = hcomp
                    (λ k →
                       λ { (i = i1) → snd (h f') (merid s j) k
                         ; (j = i0) → snd (h f') north (k ∨ (~ i))
                         ; (j = i1) → snd (h f') south k
                         })
                  (snd (h f') north (~ i ∧ ~ j))

isOfHLevel→isSphereFilled : (n : ℕ) → isOfHLevel (suc n) A → isSphereFilled n A
isOfHLevel→isSphereFilled zero h f = (f true) , (λ _ → h _ _)
isOfHLevel→isSphereFilled {A = A} (suc zero) h f = (f base) , toPropElim (λ _ → h _ _) refl
isOfHLevel→isSphereFilled {A = A} (suc (suc n)) h =
  helper λ x y → isOfHLevel→isSphereFilled (suc n) (h x y)
  where
    helper : {n : ℕ} → ((x y : A) → isSphereFilled (suc n) (x ≡ y))
                     → isSphereFilled (suc (suc n)) A
    helper {n = n} h f = f north , r
      where
      r : (x : S₊ (suc (suc n))) → f north ≡ f x
      r north = refl
      r south = h (f north) (f south) (λ x → cong f (merid x)) .fst
      r (merid x i) j = hcomp (λ k → λ { (i = i0) → f north
                                       ; (i = i1) → h (f north) (f south) (λ x → cong f (merid x)) .snd x (~ k) j
                                       ; (j = i0) → f north
                                       ; (j = i1) → f (merid x i) }) (f (merid x (i ∧ j)))

isOfHLevelTrunc : (n : ℕ) → isOfHLevel n (∥ A ∥ n)
isOfHLevelTrunc zero = isOfHLevelUnit* 0
isOfHLevelTrunc (suc n) = isSphereFilled→isOfHLevel n isSphereFilled∥∥

rec : {n : HLevel}
      {B : Type ℓ'} →
      isOfHLevel (suc n) B →
      (A → B) →
      hLevelTrunc (suc n) A →
      B
rec h g ∣ x ∣ = g x
rec {n = n} {B = B} hB g (hub f) = isOfHLevel→isSphereFilled n hB (λ x → rec hB g (f x)) .fst
rec {n = n} hB g (spoke f x i) =
  isOfHLevel→isSphereFilled n hB (λ x → rec hB g (f x)) .snd x i

rec2 : {n : HLevel}
       {B : Type ℓ'} →
       {C : Type ℓ''} →
       isOfHLevel (suc n) C →
       (A → B → C) →
       hLevelTrunc (suc n) A →
       hLevelTrunc (suc n) B →
       C
rec2 h g ∣ x ∣ ∣ y ∣ = g x y
rec2 h g ∣ x ∣ (hub f) =
  isOfHLevel→isSphereFilled _ h (λ y → rec2 h g ∣ x ∣ (f y)) .fst
rec2 h g ∣ x ∣ (spoke f z i) =
  isOfHLevel→isSphereFilled _ h (λ y → rec2 h g ∣ x ∣ (f y)) .snd z i
rec2 h g (hub f) z =
  isOfHLevel→isSphereFilled _ h (λ y → rec2 h g (f y) z) .fst
rec2 h g (spoke f x i) z =
  isOfHLevel→isSphereFilled _ h (λ y → rec2 h g (f y) z) .snd x i

elim : {n : ℕ}
      {B : ∥ A ∥ (suc n) → Type ℓ'}
      (hB : (x : ∥ A ∥ (suc n)) → isOfHLevel (suc n) (B x))
      (g : (a : A) → B (∣ a ∣))
      (x : ∥ A ∥ (suc n)) →
      B x
elim hB g (∣ a ∣ ) = g a
elim {B = B} hB g (hub f) =
  isOfHLevel→isSphereFilled _ (hB (hub f)) (λ x → subst B (sym (spoke f x)) (elim hB g (f x)) ) .fst
elim {B = B} hB g (spoke f x i) =
  toPathP {A = λ i → B (spoke f x (~ i))}
    (sym (isOfHLevel→isSphereFilled _ (hB (hub f)) (λ x → subst B (sym (spoke f x)) (elim hB g (f x))) .snd x))
    (~ i)

elim2 : {n : ℕ}
       {B : ∥ A ∥ (suc n) → ∥ A ∥ (suc n) → Type ℓ'}
       (hB : ((x y : ∥ A ∥ (suc n)) → isOfHLevel (suc n) (B x y)))
       (g : (a b : A) → B ∣ a ∣ ∣ b ∣)
       (x y : ∥ A ∥ (suc n)) →
       B x y
elim2 {n = n} hB g = elim (λ _ → isOfHLevelΠ (suc n) (λ _ → hB _ _)) λ a →
                    elim (λ _ → hB _ _) (λ b → g a b)

elim3 : {n : ℕ}
       {B : (x y z : ∥ A ∥ (suc n)) → Type ℓ'}
       (hB : ((x y z : ∥ A ∥ (suc n)) → isOfHLevel (suc n) (B x y z)))
       (g : (a b c : A) → B (∣ a ∣) ∣ b ∣ ∣ c ∣)
       (x y z : ∥ A ∥ (suc n)) →
       B x y z
elim3 {n = n} hB g = elim2 (λ _ _ → isOfHLevelΠ (suc n) (hB _ _)) λ a b →
                    elim (λ _ → hB _ _ _) (λ c → g a b c)

isOfHLevelMin→isOfHLevel : {n m : ℕ} → isOfHLevel (min n m) A → isOfHLevel n A × isOfHLevel m A
isOfHLevelMin→isOfHLevel {n = zero} {m = m} h = h , isContr→isOfHLevel m h
isOfHLevelMin→isOfHLevel {n = suc n} {m = zero} h = (isContr→isOfHLevel (suc n) h) , h
isOfHLevelMin→isOfHLevel {A = A} {n = suc n} {m = suc m} h =
    subst (λ x → isOfHLevel x A) (helper n m)
          (isOfHLevelPlus (suc n ∸ (suc (min n m))) h)
  , subst (λ x → isOfHLevel x A) ((λ i → m ∸ (minComm n m i) + suc (minComm n m i)) ∙ helper m n)
          (isOfHLevelPlus (suc m ∸ (suc (min n m))) h)
  where
  helper : (n m : ℕ) → n ∸ min n m + suc (min n m) ≡ suc n
  helper zero zero = refl
  helper zero (suc m) = refl
  helper (suc n) zero = cong suc (+-comm n 1)
  helper (suc n) (suc m) = +-suc _ _ ∙ cong suc (helper n m)

ΣTruncElim : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {n m : ℕ}
              {B : (x : ∥ A ∥ (suc n)) → Type ℓ'}
              {C : (Σ[ a ∈ (∥ A ∥ (suc n)) ] (∥ B a ∥ (suc m))) → Type ℓ''}
            → ((x : (Σ[ a ∈ (∥ A ∥ (suc n)) ] (∥ B a ∥ (suc m)))) → isOfHLevel (min (suc n) (suc m)) (C x))
            → ((a : A) (b : B (∣ a ∣)) → C (∣ a ∣ , ∣ b ∣))
            → (x : (Σ[ a ∈ (∥ A ∥ (suc n)) ] (∥ B a ∥ (suc m)))) → (C x)
ΣTruncElim {n = n} {m = m} {B = B} {C = C} hB g (a , b) =
  elim {B = λ a → (b :  (∥ B a ∥ (suc m))) → C (a , b)}
       (λ x → isOfHLevelΠ (suc n) λ b → isOfHLevelMin→isOfHLevel (hB (x , b)) .fst )
       (λ a → elim (λ _ → isOfHLevelMin→isOfHLevel (hB (∣ a ∣ , _)) .snd) λ b → g a b)
       a b

truncIdempotentIso : (n : ℕ) → isOfHLevel n A → Iso (∥ A ∥ n) A
truncIdempotentIso zero hA = isContr→Iso (isOfHLevelUnit* 0) hA
Iso.fun (truncIdempotentIso (suc n) hA) = rec hA λ a → a
Iso.inv (truncIdempotentIso (suc n) hA) = ∣_∣
Iso.rightInv (truncIdempotentIso (suc n) hA) _ = refl
Iso.leftInv (truncIdempotentIso (suc n) hA) = elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ _ → refl

truncIdempotent≃ : (n : ℕ) → isOfHLevel n A → ∥ A ∥ n ≃ A
truncIdempotent≃ n hA = isoToEquiv (truncIdempotentIso n hA)

truncIdempotent : (n : ℕ) → isOfHLevel n A → ∥ A ∥ n ≡ A
truncIdempotent n hA = ua (truncIdempotent≃ n hA)

HLevelTruncModality : ∀ {ℓ} (n : HLevel) → Modality ℓ
isModal       (HLevelTruncModality n) = isOfHLevel n
isModalIsProp (HLevelTruncModality n) = isPropIsOfHLevel n
◯             (HLevelTruncModality n) = hLevelTrunc n
◯-isModal     (HLevelTruncModality n) = isOfHLevelTrunc n
η (HLevelTruncModality zero) _ = tt*
η (HLevelTruncModality (suc n)) = ∣_∣
◯-elim (HLevelTruncModality zero) cB _ tt* = cB tt* .fst
◯-elim (HLevelTruncModality (suc n)) = elim
◯-elim-β (HLevelTruncModality zero) cB f a = cB tt* .snd (f a)
◯-elim-β (HLevelTruncModality (suc n)) = λ _ _ _ → refl
◯-=-isModal (HLevelTruncModality zero) x y = (isOfHLevelUnit* 1 x y) , (isOfHLevelUnit* 2 x y _)
◯-=-isModal (HLevelTruncModality (suc n)) = isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n))

-- universal property

univTrunc : ∀ {ℓ} (n : HLevel) {B : TypeOfHLevel ℓ n} → Iso (hLevelTrunc n A → B .fst) (A → B .fst)
univTrunc zero {B , lev} = isContr→Iso (isOfHLevelΠ 0 (λ _ → lev)) (isOfHLevelΠ 0 λ _ → lev)
Iso.fun (univTrunc (suc n) {B , lev}) g a = g ∣ a ∣
Iso.inv (univTrunc (suc n) {B , lev}) = rec lev
Iso.rightInv (univTrunc (suc n) {B , lev}) b = refl
Iso.leftInv (univTrunc (suc n) {B , lev}) b = funExt (elim (λ x → isOfHLevelPath _ lev _ _)
                                                            λ a → refl)

-- functorial action

map : {n : HLevel} {B : Type ℓ'} (g : A → B)
  → hLevelTrunc n A → hLevelTrunc n B
map {n = zero} g = λ _ → tt*
map {n = suc n} g = rec (isOfHLevelTrunc _) (λ a → ∣ g a ∣)

map2 : {n : HLevel} {B : Type ℓ'} {C : Type ℓ''} (g : A → B → C)
  → hLevelTrunc n A → hLevelTrunc n B → hLevelTrunc n C
map2 {n = zero} g = λ _ _ → tt*
map2 {n = suc n} g = rec2 (isOfHLevelTrunc _) (λ a b → ∣ g a b ∣)

mapCompIso : {n : HLevel} {B : Type ℓ'} → (Iso A B) → Iso (hLevelTrunc n A) (hLevelTrunc n B)
mapCompIso {n = zero} {B} _ = isContr→Iso (isOfHLevelUnit* 0) (isOfHLevelUnit* 0)
Iso.fun (mapCompIso {n = (suc n)} g) = map (Iso.fun g)
Iso.inv (mapCompIso {n = (suc n)} g) = map (Iso.inv g)
Iso.rightInv (mapCompIso {n = (suc n)} g) = elim (λ x → isOfHLevelPath _ (isOfHLevelTrunc _) _ _) λ b → cong ∣_∣ (Iso.rightInv g b)
Iso.leftInv (mapCompIso {n = (suc n)} g) = elim (λ x → isOfHLevelPath _ (isOfHLevelTrunc _) _ _) λ a → cong ∣_∣ (Iso.leftInv g a)

mapId : {n : HLevel} → ∀ t → map {n = n} (idfun A) t ≡ t
mapId {n = 0} tt* = refl
mapId {n = (suc n)} =
  elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) (λ _ → refl)

-- equivalences to prop/set/groupoid truncations

propTruncTrunc1Iso : Iso ∥ A ∥₁ (∥ A ∥ 1)
Iso.fun propTruncTrunc1Iso = PropTrunc.rec (isOfHLevelTrunc 1) ∣_∣
Iso.inv propTruncTrunc1Iso = rec squash₁ ∣_∣₁
Iso.rightInv propTruncTrunc1Iso = elim (λ _ → isOfHLevelPath 1 (isOfHLevelTrunc 1) _ _) (λ _ → refl)
Iso.leftInv propTruncTrunc1Iso = PropTrunc.elim (λ _ → isOfHLevelPath 1 squash₁ _ _) (λ _ → refl)

propTrunc≃Trunc1 : ∥ A ∥₁ ≃ ∥ A ∥ 1
propTrunc≃Trunc1 = isoToEquiv propTruncTrunc1Iso

propTrunc≡Trunc1 : ∥ A ∥₁ ≡ ∥ A ∥ 1
propTrunc≡Trunc1 = ua propTrunc≃Trunc1


setTruncTrunc2Iso : Iso ∥ A ∥₂ (∥ A ∥ 2)
Iso.fun setTruncTrunc2Iso = SetTrunc.rec (isOfHLevelTrunc 2) ∣_∣
Iso.inv setTruncTrunc2Iso = rec squash₂ ∣_∣₂
Iso.rightInv setTruncTrunc2Iso = elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _) (λ _ → refl)
Iso.leftInv setTruncTrunc2Iso = SetTrunc.elim (λ _ → isOfHLevelPath 2 squash₂ _ _) (λ _ → refl)

setTrunc≃Trunc2 : ∥ A ∥₂ ≃ ∥ A ∥ 2
setTrunc≃Trunc2 = isoToEquiv setTruncTrunc2Iso

propTrunc≡Trunc2 : ∥ A ∥₂ ≡ ∥ A ∥ 2
propTrunc≡Trunc2 = ua setTrunc≃Trunc2

groupoidTruncTrunc3Iso : Iso ∥ A ∥₃ (∥ A ∥ 3)
Iso.fun groupoidTruncTrunc3Iso = GpdTrunc.rec (isOfHLevelTrunc 3) ∣_∣
Iso.inv groupoidTruncTrunc3Iso = rec squash₃ ∣_∣₃
Iso.rightInv groupoidTruncTrunc3Iso = elim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) (λ _ → refl)
Iso.leftInv groupoidTruncTrunc3Iso = GpdTrunc.elim (λ _ → isOfHLevelPath 3 squash₃ _ _) (λ _ → refl)

groupoidTrunc≃Trunc3 : ∥ A ∥₃ ≃ ∥ A ∥ 3
groupoidTrunc≃Trunc3 = isoToEquiv groupoidTruncTrunc3Iso

groupoidTrunc≡Trunc3 : ∥ A ∥₃ ≡ ∥ A ∥ 3
groupoidTrunc≡Trunc3 = ua groupoidTrunc≃Trunc3

2GroupoidTruncTrunc4Iso : Iso ∥ A ∥₄ (∥ A ∥ 4)
Iso.fun 2GroupoidTruncTrunc4Iso = 2GpdTrunc.rec (isOfHLevelTrunc 4) ∣_∣
Iso.inv 2GroupoidTruncTrunc4Iso = rec squash₄ ∣_∣₄
Iso.rightInv 2GroupoidTruncTrunc4Iso = elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _) (λ _ → refl)
Iso.leftInv 2GroupoidTruncTrunc4Iso = 2GpdTrunc.elim (λ _ → isOfHLevelPath 4 squash₄ _ _) (λ _ → refl)

2GroupoidTrunc≃Trunc4 : ∥ A ∥₄ ≃ ∥ A ∥ 4
2GroupoidTrunc≃Trunc4 = isoToEquiv 2GroupoidTruncTrunc4Iso

2GroupoidTrunc≡Trunc4 : ∥ A ∥₄ ≡ ∥ A ∥ 4
2GroupoidTrunc≡Trunc4 = ua 2GroupoidTrunc≃Trunc4

isContr→isContrTrunc : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A → isContr (hLevelTrunc n A)
isContr→isContrTrunc zero contr = isOfHLevelUnit* 0
isContr→isContrTrunc (suc n) contr =
  ∣ fst contr ∣ , (elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ a → cong ∣_∣ (snd contr a))

truncOfProdIso : (n : ℕ) → Iso (hLevelTrunc n (A × B)) (hLevelTrunc n A × hLevelTrunc n B)
truncOfProdIso 0 = isContr→Iso (isOfHLevelUnit* 0) (isOfHLevel× 0 (isOfHLevelUnit* 0) (isOfHLevelUnit* 0))
Iso.fun (truncOfProdIso (suc n)) = rec (isOfHLevelΣ (suc n) (isOfHLevelTrunc (suc n)) (λ _ → isOfHLevelTrunc (suc n))) λ {(a , b) → ∣ a ∣ , ∣ b ∣}
Iso.inv (truncOfProdIso (suc n)) (a , b) = rec (isOfHLevelTrunc (suc n))
                                          (λ a → rec (isOfHLevelTrunc (suc n))
                                                      (λ b → ∣ a , b ∣)
                                                       b)
                                          a
Iso.rightInv (truncOfProdIso (suc n)) (a , b) =
  elim {B = λ a → Iso.fun (truncOfProdIso (suc n)) (Iso.inv (truncOfProdIso (suc n)) (a , b)) ≡ (a , b)}
       (λ _ → isOfHLevelPath (suc n) (isOfHLevelΣ (suc n) (isOfHLevelTrunc (suc n)) (λ _ → isOfHLevelTrunc (suc n))) _ _)
       (λ a → elim {B = λ b → Iso.fun (truncOfProdIso (suc n)) (Iso.inv (truncOfProdIso (suc n)) (∣ a ∣ , b)) ≡ (∣ a ∣ , b)}
                    (λ _ → isOfHLevelPath (suc n) (isOfHLevelΣ (suc n) (isOfHLevelTrunc (suc n)) (λ _ → isOfHLevelTrunc (suc n))) _ _)
                    (λ b → refl) b) a
Iso.leftInv (truncOfProdIso (suc n)) = elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ a → refl

---- ∥ Ω A ∥ ₙ ≡ Ω ∥ A ∥ₙ₊₁  ----


  {- Proofs of Theorem 7.3.12. and Corollary 7.3.13. in the HoTT book  -}

module ΩTrunc where
  {- We define the fibration P to show a more general result  -}
  P : {X : Type ℓ} {n : HLevel} → ∥ X ∥ (2 + n) → ∥ X ∥ (2 + n) → Type ℓ
  P {n = n} x y =  elim2 (λ _ _  → isOfHLevelTypeOfHLevel (suc n))
                         (λ a b → ∥ a ≡ b ∥ (suc n) , isOfHLevelTrunc (suc n)) x y .fst

  {- We will need P to be of hLevel n + 3  -}
  hLevelP : {X : Type ℓ} {n : HLevel} (a b : ∥ X ∥ (2 + n)) → isOfHLevel ((2 + n)) (P a b)
  hLevelP {n = n} =
    elim2 (λ x y → isProp→isOfHLevelSuc (suc n) (isPropIsOfHLevel (2 + n)))
          (λ a b → isOfHLevelSuc (suc n) (isOfHLevelTrunc (suc n)))

  {- decode function from P x y to x ≡ y -}
  decode-fun : {X : Type ℓ} {n : HLevel} (x y : ∥ X ∥ (2 + n)) → P x y → x ≡ y
  decode-fun {n = n} =
    elim2 (λ u v → isOfHLevelΠ (2 + n)
                                (λ _ → isOfHLevelSuc (2 + n) (isOfHLevelTrunc (2 + n)) u v))
          decode*
      where
      decode* : ∀ {n : HLevel} (u v : B)
              → P {n = n} ∣ u ∣ ∣ v ∣ → Path (∥ B ∥ (2 + n)) ∣ u ∣ ∣ v ∣
      decode* {B = B} {n = zero} u v = rec (isOfHLevelTrunc 2 _ _) (cong ∣_∣)
      decode* {n = suc n} u v =
        rec (isOfHLevelTrunc (3 + n) ∣ u ∣ ∣ v ∣) (cong ∣_∣)

  {- auxiliary function r used to define encode -}
  r : {X : Type ℓ} {n : HLevel} (u : ∥ X ∥ (2 + n)) → P u u
  r = elim (λ x → hLevelP x x) (λ a → ∣ refl ∣)

  {- encode function from x ≡ y to P x y -}
  encode-fun : {X : Type ℓ} {n : HLevel} (x y : ∥ X ∥ (2 + n)) → x ≡ y → P x y
  encode-fun x y p = subst (P x) p (r x)

  {- We need the following two lemmas on the functions behaviour for refl -}
  dec-refl : {X : Type ℓ} {n : HLevel} (x : ∥ X ∥ (2 + n)) → decode-fun x x (r x) ≡ refl
  dec-refl {n = zero} =
    elim (λ _ → isOfHLevelSuc 2 (isOfHLevelSuc 1 (isOfHLevelTrunc 2 _ _)) _ _) λ _ → refl
  dec-refl {n = suc n} =
    elim (λ x → isOfHLevelSuc (2 + n)
                  (isOfHLevelSuc (2 + n)
                     (isOfHLevelTrunc (3 + n) x x)
                     (decode-fun x x (r x)) refl))
         (λ _ → refl)

  enc-refl : {X : Type ℓ} {n : HLevel} (x : ∥ X ∥ (2 + n)) → encode-fun x x refl ≡ r x
  enc-refl x j = transp (λ _ → P x x) j (r x)

  {- decode-fun is a right-inverse -}
  P-rinv : {X : Type ℓ} {n : HLevel} (u v : ∥ X ∥ (2 + n)) (x : Path (∥ X ∥ (2 + n)) u v)
         → decode-fun u v (encode-fun u v x) ≡ x
  P-rinv u v = J (λ y p → decode-fun u y (encode-fun u y p) ≡ p)
                 (cong (decode-fun u u) (enc-refl u) ∙ dec-refl u)

  {- decode-fun is a left-inverse -}
  P-linv : {X : Type ℓ} {n : HLevel} (u v : ∥ X ∥ (2 + n)) (x : P u v)
         → encode-fun u v (decode-fun u v x) ≡ x
  P-linv {n = n} =
    elim2 (λ x y → isOfHLevelΠ (2 + n)
                               (λ z → isOfHLevelSuc (2 + n) (hLevelP x y) _ _))
          helper
    where
    helper : {X : Type ℓ} {n : HLevel} (a b : X) (p : P {n = n} ∣ a ∣ ∣ b ∣)
           → encode-fun _ _ (decode-fun ∣ a ∣ ∣ b ∣ p) ≡ p
    helper {n = zero} a b =
      elim (λ _ → isOfHLevelPath 1 (isOfHLevelTrunc 1) _ _)
           (J (λ y p → encode-fun ∣ a ∣ ∣ y ∣ (decode-fun _ _ ∣ p ∣) ≡ ∣ p ∣)
              (enc-refl ∣ a ∣))
    helper {n = suc n} a b =
      elim (λ x → hLevelP {n = suc n} ∣ a ∣ ∣ b ∣ _ _)
           (J (λ y p → encode-fun {n = (suc n)} ∣ a ∣ ∣ y ∣ (decode-fun _ _ ∣ p ∣) ≡ ∣ p ∣)
              (enc-refl ∣ a ∣))

  {- The final Iso established -}
  IsoFinal : {B : Type ℓ} (n : HLevel) (x y : ∥ B ∥ (2 + n)) → Iso (x ≡ y) (P x y)
  Iso.fun (IsoFinal _ x y) = encode-fun x y
  Iso.inv (IsoFinal _ x y) = decode-fun x y
  Iso.rightInv (IsoFinal _ x y) = P-linv x y
  Iso.leftInv (IsoFinal _ x y) = P-rinv x y

PathIdTruncIso : {a b : A} (n : HLevel) → Iso (Path (∥ A ∥ (suc n)) ∣ a ∣ ∣ b ∣) (∥ a ≡ b ∥ n)
PathIdTruncIso zero = isContr→Iso ((isOfHLevelTrunc 1 _ _)
                    , isOfHLevelPath 1 (isOfHLevelTrunc 1) ∣ _ ∣ ∣ _ ∣ _) (isOfHLevelUnit* 0)
PathIdTruncIso (suc n) = ΩTrunc.IsoFinal n ∣ _ ∣ ∣ _ ∣

PathIdTrunc : {a b : A} (n : HLevel) → (Path (∥ A ∥ (suc n)) ∣ a ∣ ∣ b ∣) ≡ (∥ a ≡ b ∥ n)
PathIdTrunc n = isoToPath (PathIdTruncIso n)

PathΩ : {a : A} (n : HLevel) → (Path (∥ A ∥ (suc n)) ∣ a ∣ ∣ a ∣) ≡ (∥ a ≡ a ∥ n)
PathΩ n = PathIdTrunc n

{- Special case using direct defs of truncations -}
PathIdTrunc₀Iso : {a b : A} → Iso (∣ a ∣₂ ≡ ∣ b ∣₂) ∥ a ≡ b ∥₁
PathIdTrunc₀Iso = compIso (congIso setTruncTrunc2Iso)
                    (compIso (ΩTrunc.IsoFinal _ ∣ _ ∣ ∣ _ ∣)
                             (invIso propTruncTrunc1Iso))

-------------------------

truncOfTruncIso : (n m : HLevel) → Iso (hLevelTrunc n A) (hLevelTrunc n (hLevelTrunc (m + n) A))
truncOfTruncIso zero m = isContr→Iso (isOfHLevelUnit* 0) (isOfHLevelUnit* 0)
Iso.fun (truncOfTruncIso (suc n) zero) = rec (isOfHLevelTrunc (suc n)) λ a → ∣ ∣ a ∣ ∣
Iso.fun (truncOfTruncIso (suc n) (suc m)) = rec (isOfHLevelTrunc (suc n)) λ a → ∣ ∣ a ∣ ∣
Iso.inv (truncOfTruncIso (suc n) zero) =  rec (isOfHLevelTrunc (suc n))
                                               (rec (isOfHLevelTrunc (suc n))
                                                     λ a → ∣ a ∣)
Iso.inv (truncOfTruncIso (suc n) (suc m)) =  rec (isOfHLevelTrunc (suc n))
                                                  (rec (isOfHLevelPlus (suc m) (isOfHLevelTrunc (suc n)))
                                                        λ a → ∣ a ∣)
Iso.rightInv (truncOfTruncIso (suc n) zero) =
  elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _ )
       (elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _ )
              λ a → refl)
Iso.rightInv (truncOfTruncIso (suc n) (suc m)) =
  elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _ )
               (elim (λ x → isOfHLevelPath ((suc m) + (suc n)) (isOfHLevelPlus (suc m) (isOfHLevelTrunc (suc n))) _ _ )
                      λ a → refl)
Iso.leftInv (truncOfTruncIso (suc n) zero) = elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ a → refl
Iso.leftInv (truncOfTruncIso (suc n) (suc m)) = elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ a → refl

truncOfTruncEq : (n m : ℕ) → (hLevelTrunc n A) ≃ (hLevelTrunc n (hLevelTrunc (m + n) A))
truncOfTruncEq n m = isoToEquiv (truncOfTruncIso n m)

truncOfΣIso : ∀ {ℓ ℓ'} (n : HLevel) {A : Type ℓ} {B : A → Type ℓ'}
       → Iso (hLevelTrunc n (Σ A B)) (hLevelTrunc n (Σ A λ x → hLevelTrunc n (B x)))
truncOfΣIso zero = idIso
Iso.fun (truncOfΣIso (suc n)) = map λ {(a , b) → a , ∣ b ∣}
Iso.inv (truncOfΣIso (suc n)) =
  rec (isOfHLevelTrunc (suc n))
        (uncurry λ a → rec (isOfHLevelTrunc (suc n)) λ b → ∣ a , b ∣)
Iso.rightInv (truncOfΣIso (suc n)) =
  elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
         (uncurry λ a → elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
         λ b → refl)
Iso.leftInv (truncOfΣIso (suc n)) =
  elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ {(a , b) → refl}


open import Cubical.Foundations.GroupoidLaws
hLevelS : ∀ {ℓ} (n : ℕ) {A : (S₊ (suc n)) → Type ℓ} → ((x : S₊ (suc n)) → isOfHLevel (suc n) (A x))
          → A (ptSn (suc n))
          → (x : S₊ (suc n)) → A x
hLevelS zero hlev pt = toPropElim hlev pt
hLevelS (suc n) hlev pt north = pt
hLevelS (suc n) {A = A} hlev pt south = subst A (merid (ptSn (suc n))) pt
hLevelS (suc n) {A = A} hlev pt (merid a i) = helper i
  where
  helper : PathP (λ i → A (merid a i)) pt (subst A (merid (ptSn (suc n))) pt)
  helper = hLevelS n {A = λ a → PathP (λ i → A (merid a i)) pt (subst A (merid (ptSn (suc n))) pt)}
                     (λ a → isOfHLevelPathP' (suc n) (hlev south) _ _)
                     (λ i → transp (λ j → A (merid (ptSn (suc n)) (i ∧ j))) (~ i) pt)
                     a

hLevelS2' : ∀ {ℓ} (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
          → ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y))
          → (f : (x : _) → A (ptSn (suc n)) x)
          → (g : (x : _) → A x (ptSn (suc m)))
          → (g (ptSn (suc n)) ≡ f (ptSn (suc m)))
          → (x : S₊ (suc n)) (y : S₊ (suc m)) → A x y
hLevelS2'Id : ∀ {ℓ} (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
          → (hLev : ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y)))
          → (f : (x : _) → A (ptSn (suc n)) x)
          → (g : (x : _) → A x (ptSn (suc m)))
          → (hom : (g (ptSn (suc n)) ≡ f (ptSn (suc m))))
          → ((y : S₊ (suc m)) → hLevelS2' n m hLev f g hom (ptSn (suc n)) y ≡ f y)
hLevelS2' zero zero hlev f g hom base y = f y
hLevelS2' zero zero hlev f g hom (loop i) base = hcomp (λ k → λ {(i = i0) → hom k
                                                               ; (i = i1) → hom k})
                                                       (g (loop i))
hLevelS2' zero zero {A = A} hlev f g hom (loop i) (loop j) = helper i j
  where
  helper : SquareP (λ i j → A (loop i) (loop j)) (cong f loop) (cong f loop)
                        (λ i → hcomp (λ k → λ {(i = i0) → hom k
                                               ; (i = i1) → hom k})
                                      (g (loop i)))
                         λ i → hcomp (λ k → λ { (i = i0) → hom k
                                                ; (i = i1) → hom k})
                                       (g (loop i))
  helper = transport (sym (PathP≡Path _ _ _))
                     (isOfHLevelPathP' 1 (hlev base base) _ _ _ _)
hLevelS2' (suc n) zero {A = A} hlev f g hom north y = f y
hLevelS2' (suc n) zero {A = A} hlev f g hom south y = subst (λ x → A x y) (merid (ptSn (suc n))) (f y)
hLevelS2' (suc n) zero {A = A} hlev f g hom (merid a i) y = helper i
  where
  helper : PathP (λ i → A (merid a i) y) (f y) (transport (λ i → A (merid (ptSn (suc n)) i) y) (f y))
  helper = hLevelS2' n zero {A = λ a y → PathP (λ i → A (merid a i) y) (f y)
                                                (transport (λ i → A (merid (ptSn (suc n)) i) y) (f y))}
                            (λ a y → isOfHLevelPathP' _ (hlev south y) _ _)
                            (λ a i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) a) (~ i) (f a))
                            merid-a
                            merid-aId
                            a y
    where
    helper2 : (x : S₊ (suc n)) → transport (λ i₁ → A (merid x i₁) base) (f base) ≡ g south
    helper2 x = cong (transport (λ i₁ → A (merid x i₁) base)) (sym hom)
              ∙ (λ i → transp (λ j → A (merid x (i ∨ j)) base) i (g (merid x i)))
    merid-a : (x : S₊ (suc n)) → PathP (λ i₁ → A (merid x i₁) base) (f base)
                                        (transport (λ i₁ → A (merid (ptSn (suc n)) i₁) base) (f base))
    merid-a x i = hcomp (λ k → λ { (i = i0) → f base
                                  ; (i = i1) → (helper2 x ∙ sym (helper2 (ptSn (suc n)))) k})
                        (transp (λ i₁ → A (merid x (i₁ ∧ i)) base) (~ i) (f base))

    merid-aId : merid-a (ptSn (suc n)) ≡ λ i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) base) (~ i) (f base)
    merid-aId =
        (λ j i → hcomp (λ k → λ {(i = i0) → f base
                                ; (i = i1) → rCancel (helper2 (ptSn (suc n))) j k})
                       (transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) base) (~ i) (f base)))
      ∙ λ j i → hfill (λ k → λ { (i = i0) → f base
                                 ; (i = i1) → transport (λ i₁ → A (merid (ptSn (suc n)) i₁) base) (f base)})
                       (inS (transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) base) (~ i) (f base))) (~ j)

hLevelS2' n (suc m) hlev f g hom x north = g x
hLevelS2' n (suc m) {A = A} hlev f g hom x south =
  transport (λ i → A x (merid (ptSn (suc m)) i)) (g x)
hLevelS2' n (suc m) {A = A} hlev f g hom x (merid a i) = helper i
  where
  helper : PathP (λ i → A x (merid a i)) (g x) (transport (λ i → A x (merid (ptSn (suc m)) i)) (g x))
  helper = hLevelS2' n m
                    {A = λ x a → PathP (λ i → A x (merid a i)) (g x)
                                        (transport (λ i → A x (merid (ptSn (suc m)) i)) (g x))}
                    (λ _ _ → isOfHLevelPathP' (1 + (n + (suc m))) (hlevHelper _) _ _)
                    merid-a
                    (λ x i → transp (λ i₁ → A x (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g x))
                    (sym (merid-aId))
                    x a
    where
    hlevHelper : (x : _) → isOfHLevel (2 + (n + suc m)) (A x south)
    hlevHelper x = subst (λ n → isOfHLevel n (A x south)) (cong suc (+-suc n (suc m))) (hlev x south)

    helper2 : (x : S₊ (suc m)) → transport (λ i₁ → A (ptSn (suc n)) (merid x i₁)) (g (ptSn (suc n))) ≡ f south
    helper2 x = cong (transport (λ i₁ → A (ptSn (suc n)) (merid x i₁))) hom
              ∙ (λ i → transp (λ j → A (ptSn (suc n)) (merid x (i ∨ j))) i (f (merid x i)))
    merid-a : (a : S₊ (suc m)) → PathP (λ i₁ → A (ptSn (suc n)) (merid a i₁)) (g (ptSn (suc n)))
                                        (transport (λ i₁ → A (ptSn (suc n)) (merid (ptSn (suc m)) i₁))
                                        (g (ptSn (suc n))))
    merid-a a i = hcomp (λ k → λ { (i = i0) → g (ptSn (suc n))
                                  ; (i = i1) → (helper2 a ∙ sym (helper2 (ptSn (suc m)))) k})
                        (transp (λ i₁ → A (ptSn (suc n)) (merid a (i₁ ∧ i))) (~ i) (g (ptSn (suc n))))

    merid-aId : merid-a (ptSn (suc m)) ≡ λ i → transp (λ i₁ → A (ptSn (suc n)) (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g (ptSn (suc n)))
    merid-aId =
       (λ j i → hcomp (λ k → λ {(i = i0) → g (ptSn (suc n))
                                ; (i = i1) → rCancel (helper2 (ptSn (suc m))) j k})
                       (transp (λ i₁ → A (ptSn (suc n)) (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g (ptSn (suc n)))))
     ∙ λ j i → hfill (λ k → λ { (i = i0) → g (ptSn (suc n))
                                ; (i = i1) → transport (λ i₁ → A (ptSn (suc n)) (merid (ptSn (suc m)) i₁)) (g (ptSn (suc n)))})
                       (inS (transp (λ i₁ → A (ptSn (suc n)) (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g (ptSn (suc n))))) (~ j)
hLevelS2'Id zero zero hlev f g hom _ = refl
hLevelS2'Id (suc n) zero hlev f g hom _ = refl
hLevelS2'Id zero (suc m) hlev f g hom north = hom
hLevelS2'Id zero (suc m) {A = A} hlev f g hom south =
    cong (transport (λ i → A base (merid (ptSn (suc m)) i))) hom
  ∙∙ (λ i → transp (λ j → A base (merid (ptSn (suc m)) (i ∨ j))) i (f (merid (ptSn (suc m)) i))) ∙∙ refl
hLevelS2'Id zero (suc m) hlev f g hom (merid a i) j =
  hcomp (λ k → λ {(i = i0) → hom (j ∧ k)
                 ; (j = i0) → {!hLevelS2' zero (suc m) hlev f g hom base (merid a (k ∧ i))!}
                 ; (j = i1) → {!f (merid a i)!}})
        {!!}
  where
  helper : (a : _) (b : _) → PathP {!!} (hLevelS2' zero (suc m) hlev f g hom a b) (hLevelS2' (suc m) zero {!!} g f (sym hom) b a)
  helper = {!Goal: A base (merid a i)
———— Boundary ——————————————————————————————————————————————
i = i0 ⊢ hom j
i = i1 ⊢ ((λ i₁ →
             transport (λ i₂ → A base (merid (ptSn (suc m)) i₂)) (hom i₁))
          ∙
          (λ i₁ →
             transp (λ j₁ → A base (merid (ptSn (suc m)) (i₁ ∨ j₁))) i₁
             (f (merid (ptSn (suc m)) i₁))))
         j
j = i0 ⊢ Cubical.HITs.Truncation.Properties.helper m zero hlev f g
         hom base a i i
j = i1 ⊢ f (merid a i)!}
hLevelS2'Id (suc n) (suc m) hlev f g hom x = {!!}


-- hLevelS2 : ∀ {ℓ} (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
--           → ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y))
--           → (f : (x : _) → A (ptSn (suc n)) x)
--           → (g : (x : _) → A x (ptSn (suc m)))
--           → (g (ptSn (suc n)) ≡ f (ptSn (suc m)))
--           → (x : S₊ (suc n)) (y : S₊ (suc m)) → A x y
-- hLevelS2 zero zero hlev f g hom base y = f y
-- hLevelS2 zero zero hlev f g hom (loop i) base = hcomp (λ k → λ {(i = i0) → hom k
--                                                                ; (i = i1) → hom k})
--                                                       (g (loop i))
-- hLevelS2 zero zero {A = A} hlev f g hom (loop i) (loop j) = helper i j
--   where
--   helper : SquareP (λ i j → A (loop i) (loop j)) (cong f loop) (cong f loop)
--                         (λ i → hcomp (λ k → λ {(i = i0) → hom k
--                                                ; (i = i1) → hom k})
--                                       (g (loop i)))
--                          λ i → hcomp (λ k → λ { (i = i0) → hom k
--                                                 ; (i = i1) → hom k})
--                                        (g (loop i))
--   helper = transport (sym (PathP≡Path _ _ _))
--                      (isOfHLevelPathP' 1 (hlev base base) _ _ _ _)
-- hLevelS2 zero (suc m) hlev f g hom x north = g x
-- hLevelS2 zero (suc m) {A = A} hlev f g hom x south =
--   transport (λ i → A x (merid (ptSn (suc m)) i)) (g x)
-- hLevelS2 zero (suc m) {A = A} hlev f g hom x (merid a i) = helper i
--   where
--   helper : PathP (λ i → A x (merid a i)) (g x) (transport (λ i → A x (merid (ptSn (suc m)) i)) (g x))
--   helper = hLevelS2 zero m
--                     {A = λ x a → PathP (λ i → A x (merid a i)) (g x)
--                                         (transport (λ i → A x (merid (ptSn (suc m)) i)) (g x))}
--                     (λ _ _ → isOfHLevelPathP' (2 + m) (hlev _ _) _ _)
--                     merid-a
--                     (λ x i → transp (λ i₁ → A x (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g x))
--                     (sym (merid-aId))
--                     x a
--     where
--     helper2 : (x : S₊ (suc m)) → transport (λ i₁ → A base (merid x i₁)) (g base) ≡ f south
--     helper2 x = cong (transport (λ i₁ → A base (merid x i₁))) hom
--               ∙ (λ i → transp (λ j → A base (merid x (i ∨ j))) i (f (merid x i)))
--     merid-a : (a : S₊ (suc m)) → PathP (λ i₁ → A base (merid a i₁)) (g base)
--                                         (transport (λ i₁ → A base (merid (ptSn (suc m)) i₁))
--                                         (g base))
--     merid-a a i = hcomp (λ k → λ { (i = i0) → g base
--                                   ; (i = i1) → (helper2 a ∙ sym (helper2 (ptSn (suc m)))) k})
--                         (transp (λ i₁ → A base (merid a (i₁ ∧ i))) (~ i) (g base))

--     merid-aId : merid-a (ptSn (suc m)) ≡ λ i → transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g base)
--     merid-aId =
--        (λ j i → hcomp (λ k → λ {(i = i0) → g base
--                                 ; (i = i1) → rCancel (helper2 (ptSn (suc m))) j k})
--                        (transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g base)))
--      ∙ λ j i → hfill (λ k → λ { (i = i0) → g base
--                                 ; (i = i1) → transport (λ i₁ → A base (merid (ptSn (suc m)) i₁)) (g base)})
--                        (inS (transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g base))) (~ j)

-- hLevelS2 (suc n) zero {A = A} hlev f g hom x y = {!y!}
-- hLevelS2 (suc n) (suc m) hlev f g hom x north = g x
-- hLevelS2 (suc n) (suc m) {A = A} hlev f g hom x south = transport (λ i → A x (merid (ptSn (suc m)) i)) (g x)
-- hLevelS2 (suc n) (suc m) {A = A} hlev f g hom x (merid a i) = hLevelS2HLP i
--   where
--   hLevelS2HLP : PathP (λ i → A x (merid a i))
--                       (g x)
--                       (transport (λ i → A x (merid (ptSn (suc m)) i)) (g x))
--   hLevelS2HLP = hLevelS2 (suc n) m {A = λ x a → PathP (λ i → A x (merid a i))
--                                                        (g x)
--                                                        (transport (λ i → A x (merid (ptSn (suc m)) i))
--                                                                   (g x))}
--                          (λ _ _ → isOfHLevelPathP' (2 + (n + (suc m))) (hlevHelper _) _ _)
--                          merid-a
--                          (λ x i → transp (λ i₁ → A x (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g x))
--                          (sym (merid-aId)) x a
--     where
--     hlevHelper : (x : _) → isOfHLevel (3 + (n + suc m)) (A x south)
--     hlevHelper x = subst (λ n → isOfHLevel n (A x south))
--                          (cong (λ x → suc (suc x)) (+-suc n (suc m)))
--                          (hlev x south)

--     helper2 : (a : S₊ (suc m)) → transport (λ i₁ → A north (merid a i₁)) (g north) ≡ f south
--     helper2 a = cong (transport (λ i₁ → A north (merid a i₁))) hom
--               ∙ (λ i → transp (λ j → A north (merid a (i ∨ j))) i (f (merid a i)))

--     merid-a : (a : S₊ (suc m)) → PathP (λ i₁ → A north (merid a i₁)) (g north)
--                                         (transport (λ i₁ → A north (merid (ptSn (suc m)) i₁))
--                                         (g north))
--     merid-a a i = hcomp (λ k → λ { (i = i0) → g north
--                                   ; (i = i1) → (helper2 a ∙ sym (helper2 (ptSn (suc m)))) k})
--                         (transp (λ i₁ → A north (merid a (i₁ ∧ i))) (~ i) (g north))

--     merid-aId : merid-a (ptSn (suc m)) ≡ λ i → transp (λ i₁ → A north (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g north)
--     merid-aId =
--        (λ j i → hcomp (λ k → λ {(i = i0) → g north
--                                 ; (i = i1) → rCancel (helper2 (ptSn (suc m))) j k})
--                        (transp (λ i₁ → A north (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g north)))
--      ∙ λ j i → hfill (λ k → λ { (i = i0) → g north
--                                 ; (i = i1) → transport (λ i₁ → A north (merid (ptSn (suc m)) i₁)) (g north)})
--                        (inS (transp (λ i₁ → A north (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i) (g north))) (~ j)


-- -- hLevelS2 : ∀ {ℓ} (n : ℕ) {A : (S₊ (suc n)) → (S₊ (suc n)) → Type ℓ} → ((x y : S₊ (suc n)) → isOfHLevel ((suc n) + (suc n)) (A x y))
-- --           → (f : (x : _) → A (ptSn (suc n)) x)
-- --           → (g : (x : _) → A x (ptSn (suc n)))
-- --           → (g (ptSn (suc n)) ≡ f (ptSn (suc n)))
-- --           → (x y : S₊ (suc n)) → A x y
-- -- hLevelS2 zero hlev f g hom base y = f y
-- -- hLevelS2 zero hlev f g hom (loop i) base = hcomp (λ k → λ {(i = i0) → hom k ; (i = i1) → hom k}) (g (loop i))
-- -- hLevelS2 zero {A = A} hlev f g hom (loop i) (loop j) = helper i j
-- --   where
-- --   helper : SquareP (λ i j → A (loop i) (loop j)) (cong f loop) (cong f loop)
-- --                         (λ i → hcomp (λ k → λ {(i = i0) → hom k
-- --                                                ; (i = i1) → hom k})
-- --                                       (g (loop i)))
-- --                          λ i → hcomp (λ k → λ { (i = i0) → hom k
-- --                                                 ; (i = i1) → hom k})
-- --                                        (g (loop i))
-- --   helper = transport (sym (PathP≡Path _ _ _))
-- --                      (isOfHLevelPathP' 1 (hlev base base) _ _ _ _)
-- -- hLevelS2 (suc n) hlev f g hom north y = f y
-- -- hLevelS2 (suc n) hlev f g hom south north = g south
-- -- hLevelS2 (suc n) {A = A} hlev f g hom south south =
-- --   transport (λ j → A south (merid (ptSn (suc n)) j)) (g south)
-- -- hLevelS2 (suc n) hlev f g hom south (merid a i) =
-- --   {!!}
-- -- hLevelS2 (suc n) hlev f g hom (merid a i) north = {!!}
-- -- hLevelS2 (suc n) hlev f g hom (merid a i) south = {!!}
-- -- hLevelS2 (suc n) hlev f g hom (merid a i) (merid a₁ i₁) = {!!}



-- -- -- ----
-- -- -- open import Cubical.HITs.S2
-- -- -- open import Cubical.Foundations.GroupoidLaws
-- -- -- helper : S² → S² → HubAndSpoke S² 3
-- -- -- helper base y = ∣ y ∣
-- -- -- helper (surf i j) base = ∣ surf i j ∣
-- -- -- helper (surf i j) (surf k l) = {!!}

-- -- -- helperId : (a : S²) → isEquiv {A = HubAndSpoke S² 3} {B = HubAndSpoke S² 3} (rec (isOfHLevelTrunc 4) (helper a))
-- -- -- helperId =
-- -- --   S²ToSetRec (λ _ → isOfHLevelSuc 1 (isPropIsEquiv _))
-- -- --              (subst isEquiv (funExt (elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
-- -- --              (λ _ → refl)))
-- -- --              (idIsEquiv (HubAndSpoke S² 3)))

-- -- -- test : (a : S²) → hLevelTrunc 4 S² ≃ hLevelTrunc 4 S²
-- -- -- test a = rec (isOfHLevelTrunc 4) (helper a) , helperId a

-- -- -- test3 : (Susp S²) → Type₀
-- -- -- test3 north = hLevelTrunc 4 S²
-- -- -- test3 south = hLevelTrunc 4 S²
-- -- -- test3 (merid a i) = ua (test a) i

-- -- -- encoder : (x : Susp S²) → test3 x → Path (hLevelTrunc 5 (Susp S²)) ∣ north ∣ ∣ x ∣
-- -- -- encoder north = rec (isOfHLevelTrunc 5 _ _) λ a → (λ j → ∣ merid base j ∣) ∙ λ j → ∣ merid a (~ j) ∣
-- -- -- encoder south = rec (isOfHLevelTrunc 5 _ _) λ a → (λ j → ∣ merid a j ∣)
-- -- -- encoder (merid a i) = {!!}
-- -- --   where
-- -- --   helper2 : (a s : S²) → transport (λ i → ua (test a) i → Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid a i ∣)
-- -- --                                      (encoder north) ∣ s ∣
-- -- --                          ≡ encoder south ∣ s ∣
-- -- --   helper2 base s = (λ i → transport (λ k → Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid base k ∣)
-- -- --                                      {!!})
-- -- --                 ∙∙ {!!}
-- -- --                 ∙∙ {!!}
-- -- --   helper2 (surf i i₁) base = {!!}
-- -- --   helper2 (surf i i₁) (surf i₂ i₃) = {!!}

-- -- -- -- encoder : (x : Susp S²) → test3 x → Path (hLevelTrunc 5 (Susp S²)) ∣ north ∣ ∣ x ∣
-- -- -- -- encoder north = rec (isOfHLevelTrunc 5 _ _) λ a → ((λ i → ∣ merid a i ∣) ∙ (λ i → ∣ merid base (~ i) ∣)) -- ∣ refl ∣
-- -- -- -- encoder south = rec (isOfHLevelTrunc 5 _ _) λ a j → ∣ merid a j ∣ -- ∣ merid base i ∣ -- ∣ merid base ∣
-- -- -- -- encoder (merid a i) =
-- -- -- --   hcomp (λ k → λ { (i = i0) → encoder north
-- -- -- --                   ; (i = i1) → helper2 a k})
-- -- -- --         (transp (λ j → ua (test a) (i ∧ j) → Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid a (i ∧ j) ∣)
-- -- -- --                 (~ i)
-- -- -- --                 (encoder north))
-- -- -- --   where
-- -- -- --   helper3 : (a s : S²) → transport (λ i → ua (test a) i → Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid a i ∣)
-- -- -- --                                   (encoder north) ∣ s ∣
-- -- -- --                        ≡ encoder south ∣ s ∣
-- -- -- --   helper3 base s =  (λ j → transp
-- -- -- --       (λ i₁ → Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid base (i₁ ∨ j) ∣) j
-- -- -- --       ((λ i₁ → ∣ merid s i₁ ∣) ∙ (λ i₁ → ∣ merid base (~ i₁ ∨ j) ∣))) ∙ {!!} -- sym (rUnit _)
-- -- -- --   helper3 (surf i j) base = {!(λ k → transp
-- -- -- --       (λ i₁ → Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid (surf i j) (i₁ ∨ k) ∣) k
-- -- -- --       ((λ i₁ → ∣ merid (surf i j) i₁ ∣) ∙ (λ i₁ → ∣ merid (surf i j) (~ i₁ ∨ k) ∣))) ∙ ?!}
-- -- -- --     where
-- -- -- --     more! : Path (cong (cong (λ a → transport (λ i → ua (test a) i → Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid a i ∣)
-- -- -- --                                   (encoder north) ∣ base ∣)) surf i0 ≡ cong (cong (λ a → transport (λ i → ua (test a) i → Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid a i ∣)
-- -- -- --                                   (encoder north) ∣ base ∣)) surf i0) (λ i j → transport (λ k → Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid (surf i j) k ∣) ((λ k → ∣ merid (surf i j) k ∣) ∙ (λ k → ∣ merid base (~ k) ∣))) λ i j → transport (λ k → Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid (surf i j) k ∣) ((λ k → ∣ merid base k ∣) ∙ (λ k → ∣ merid (surf i j) (~ k) ∣))
-- -- -- --     more! = (λ z i j → transport (λ k → Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid (surf i j) k ∣) ((λ k → ∣ merid (surf {!!} (j ∨ z)) k ∣) ∙ (λ k → ∣ merid {!!} (~ k) ∣))) ∙ {!!} -- refl -- ((λ k → ∣ merid base k ∣) ∙ (λ k → ∣ merid base (~ k) ∣)
-- -- -- --   helper3 (surf i j) (surf i₁ i₂) = {!transport
-- -- -- --       (λ i₁ →
-- -- -- --          ua (test (surf i₃ j)) i₁ →
-- -- -- --          Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid (surf i₃ j) i₁ ∣)
      
-- -- -- --        (λ a₁ → (λ i₁ → ∣ merid a₁ i₁ ∣) ∙ (λ i₁ → ∣ merid base (~ i₁) ∣))
-- -- -- --       ∣ base ∣!}

-- -- -- --   helper2 : (a : S²) → transport (λ i → ua (test a) i → Path (HubAndSpoke (Susp S²) 4) ∣ north ∣ ∣ merid a i ∣)
-- -- -- --                                   (encoder north)
-- -- -- --                      ≡ encoder south
-- -- -- --   helper2 a = funExt (elim {!!} (helper3 a))


-- -- -- -- -- Test2 : S₊ 3 → Type₀
-- -- -- -- -- Test2 north = hLevelTrunc 4 (S₊ 2)
-- -- -- -- -- Test2 south = hLevelTrunc 4 (S₊ 2)
-- -- -- -- -- Test2 (merid a i) = ua (test a) i
-- -- -- -- --   where
-- -- -- -- --   test : (a : Susp S¹) → hLevelTrunc 4 (S₊ 2) ≃ hLevelTrunc 4 (S₊ 2)
-- -- -- -- --   test a =
-- -- -- -- --     isoToEquiv
-- -- -- -- --       (iso (rec {!!} (helper2 a))
-- -- -- -- --            {!!}
-- -- -- -- --            {!!}
-- -- -- -- --            {!!})
-- -- -- -- --     where
-- -- -- -- --     helper2 : (a b : Susp S¹) → hLevelTrunc 4 (Susp S¹)
-- -- -- -- --     helper2 north b = {!b!}
-- -- -- -- --     helper2 south b = {!!}
-- -- -- -- --     helper2 (merid a i) b = {!!}


-- -- -- -- -- -- Test3 : hLevelTrunc 5 (S₊ 3) → TypeOfHLevel ℓ-zero 4
-- -- -- -- -- -- Test3 = rec (isOfHLevelTypeOfHLevel 4)
-- -- -- -- -- --             λ { north → hLevelTrunc 4 (S₊ 2) , isOfHLevelTrunc 4
-- -- -- -- -- --               ; south → hLevelTrunc 4 (S₊ 2) , isOfHLevelTrunc 4
-- -- -- -- -- --               ; (merid a i) → Σ≡Prop (λ _ → isPropIsOfHLevel 4)
-- -- -- -- -- --                                       {u = hLevelTrunc 4 (S₊ 2) , isOfHLevelTrunc 4}
-- -- -- -- -- --                                       {v = hLevelTrunc 4 (S₊ 2) , isOfHLevelTrunc 4}
-- -- -- -- -- --                                       (ua (helper a)) i}
-- -- -- -- -- --   where
-- -- -- -- -- --   helper5 : (i : I) → (a : S¹) → Iso (hLevelTrunc 4 (S₊ 2)) (hLevelTrunc 4 (S₊ 2))
-- -- -- -- -- --   Iso.fun (helper5 i a) = map λ {north → merid a i
-- -- -- -- -- --                                ; south → merid a (~ i)
-- -- -- -- -- --                                ; (merid x z) → ((λ j → merid a (i ∧ ~ j)) ∙∙ merid x ∙∙ λ j → merid a (~ i ∨ ~ j)) z}
-- -- -- -- -- --   Iso.inv (helper5 i a) = idfun _
-- -- -- -- -- --   Iso.rightInv (helper5 i a) = elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
-- -- -- -- -- --                                          λ {north j → ∣ merid a (i ∧ ~ j) ∣
-- -- -- -- -- --                                           ; south j → ∣ merid a (~ i ∨ j) ∣
-- -- -- -- -- --                                           ; (merid x z) j → ∣ hcomp (λ k → λ { (z = i0) → merid a (i ∧ (~ j ∧ k))
-- -- -- -- -- --                                                                               ; (z = i1) → merid a (~ i ∨ j ∨ ~ k)
-- -- -- -- -- --                                                                               ; (j = i1) → merid x z})
-- -- -- -- -- --                                                                     (merid x z) ∣}
-- -- -- -- -- --   Iso.leftInv (helper5 i a) =
-- -- -- -- -- --     elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
-- -- -- -- -- --          λ { north j → ∣ merid a (i ∧ ~ j) ∣
-- -- -- -- -- --            ; south j → ∣ merid a (~ i ∨ j) ∣
-- -- -- -- -- --            ; (merid x z) j → ∣ hcomp (λ k → λ { (z = i0) → merid a (i ∧ (~ j ∧ k))
-- -- -- -- -- --                                                ; (z = i1) → merid a (~ i ∨ j ∨ ~ k)
-- -- -- -- -- --                                                ; (j = i1) → merid x z})
-- -- -- -- -- --                                      (merid x z) ∣}


-- -- -- -- -- --   helper : (a : S₊ 2) → (hLevelTrunc 4 (S₊ 2)) ≃ (hLevelTrunc 4 (S₊ 2))
-- -- -- -- -- --   helper north = isoToEquiv (helper5 i0 base)
-- -- -- -- -- --   helper south = isoToEquiv (helper5 i1 base)
-- -- -- -- -- --   helper (merid a i) = hcomp (λ k → λ { (i = i0) → i0case k
-- -- -- -- -- --                                        ; (i = i1) → {!!}})
-- -- -- -- -- --                              (isoToEquiv (helper5 i a))
-- -- -- -- -- --     where
-- -- -- -- -- --     i0case : isoToEquiv (helper5 i0 a) ≡ isoToEquiv (helper5 i0 base)
-- -- -- -- -- --     i0case = Σ≡Prop isPropIsEquiv (funExt (elim {!!} λ {north → refl ; south → refl ; (merid x i) → refl }))
-- -- -- -- -- --     i1case : isoToEquiv (helper5 i1 a) ≡ isoToEquiv (helper5 i1 base)
-- -- -- -- -- --     i1case = Σ≡Prop isPropIsEquiv (funExt (elim {!!} λ {north → {!((λ j → merid a (~ j)) ∙∙ merid x ∙∙ (λ j → merid a (~ j)))!} ; south → {!!} ; (merid base i) → {!!} ; (merid (loop j) i) k → {!!}}))
-- -- -- -- -- --     helper2 : (a : S¹) → Iso (hLevelTrunc 4 (S₊ 2)) (hLevelTrunc 4 (S₊ 2))
-- -- -- -- -- --     Iso.fun (helper2 a) = map λ {north → north ; south → north ; (merid x i) → ((merid x) ∙ (sym (merid a))) i}
-- -- -- -- -- --     Iso.inv (helper2 a) = idfun (hLevelTrunc 4 (S₊ 2))
-- -- -- -- -- --     Iso.rightInv (helper2 a) =
-- -- -- -- -- --       elim {!!}
-- -- -- -- -- --            λ {north → refl ; south j → ∣ merid a j ∣
-- -- -- -- -- --            ; (merid x i) j → ∣ hcomp (λ k → λ { (i = i0) → north
-- -- -- -- -- --                                                ; (i = i1) → merid a (~ k ∨ j)
-- -- -- -- -- --                                                ; (j = i1) → merid x i})
-- -- -- -- -- --                                                  (merid x i) ∣}
-- -- -- -- -- --     Iso.leftInv (helper2 a) =
-- -- -- -- -- --       elim {!!} λ { north → refl
-- -- -- -- -- --                   ; south j → ∣ merid a j ∣
-- -- -- -- -- --                   ; (merid x i) j → helper3 x j i}
-- -- -- -- -- --       where
-- -- -- -- -- --       helper3 : (x : S¹) → PathP (λ j → Path (hLevelTrunc 4 (S₊ 2)) ∣ north ∣ ∣ merid a j ∣) (cong (λ x → Iso.inv (helper2 a) (Iso.fun (helper2 a) x)) (λ i → ∣ merid x i ∣)) (λ i → ∣ merid x i ∣)
-- -- -- -- -- --       helper3 x = compPathR→PathP (helper4 ∙ lUnit ((λ j → ∣ merid x j ∣) ∙ (λ j → ∣ merid a (~ j) ∣)))
-- -- -- -- -- --         where
-- -- -- -- -- --         open import Cubical.Foundations.GroupoidLaws
-- -- -- -- -- --         helper4 : cong (λ x → Iso.inv (helper2 a) (Iso.fun (helper2 a) x)) (λ i → ∣ merid x i ∣) ≡ (λ j → ∣ merid x j ∣) ∙ λ j → ∣ merid a (~ j) ∣
-- -- -- -- -- --         helper4 = congFunct (λ x → ∣ x ∣) (merid x) (sym (merid a))

-- -- -- -- -- -- -- Test2 : (n : ℕ) → hLevelTrunc (5 + n) (S₊ (3 + n)) → TypeOfHLevel ℓ-zero (4 + n)
-- -- -- -- -- -- -- helpi : (n : ℕ) → (a : S₊ (3 + n)) → hLevelTrunc (5 + n) (S₊ (3 + n)) ≃ hLevelTrunc (5 + n) (S₊ (3 + n))
-- -- -- -- -- -- -- helpi2 : (n : ℕ) → {!!}
-- -- -- -- -- -- -- helpi2 = {!!}
-- -- -- -- -- -- -- helpi zero a = {!!}
-- -- -- -- -- -- -- helpi (suc n) north = {!!}
-- -- -- -- -- -- -- helpi (suc n) south = {!!}
-- -- -- -- -- -- -- helpi (suc n) (merid a i) = {!isoToEquiv (test a)!}
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --   test : (a : S₊ (3 + n)) → Iso {!!} {!!}
-- -- -- -- -- -- --   test = {!!}
-- -- -- -- -- -- -- Test2 zero = rec (isOfHLevelTypeOfHLevel 4)
-- -- -- -- -- -- --            λ {north → hLevelTrunc 4 (S₊ 2) , isOfHLevelTrunc 4
-- -- -- -- -- -- --             ; south → hLevelTrunc 4 (S₊ 2) , isOfHLevelTrunc 4
-- -- -- -- -- -- --             ; (merid a i) → Σ≡Prop (λ _ → isPropIsOfHLevel 4)
-- -- -- -- -- -- --                                     {u = hLevelTrunc 4 (S₊ 2) , isOfHLevelTrunc 4}
-- -- -- -- -- -- --                                     {v = hLevelTrunc 4 (S₊ 2) , isOfHLevelTrunc 4}
-- -- -- -- -- -- --                                     (ua {!Test2 n!}) i}
-- -- -- -- -- -- -- Test2 (suc n) = rec (isOfHLevelTypeOfHLevel (5 + n))
-- -- -- -- -- -- --            λ {north → hLevelTrunc (5 + n) (S₊ (3 + n)) , isOfHLevelTrunc (5 + n)
-- -- -- -- -- -- --             ; south → hLevelTrunc (5 + n) (S₊ (3 + n)) , isOfHLevelTrunc (5 + n)
-- -- -- -- -- -- --             ; (merid a i) → Σ≡Prop (λ _ → isPropIsOfHLevel (5 + n))
-- -- -- -- -- -- --                                     {u = hLevelTrunc (5 + n) (S₊ (3 + n)) , isOfHLevelTrunc (5 + n)}
-- -- -- -- -- -- --                                     {v = hLevelTrunc (5 + n) (S₊ (3 + n)) , isOfHLevelTrunc (5 + n)}
-- -- -- -- -- -- --                                     (ua (helpi n a)) i}
-- -- -- -- -- -- --   where


-- -- -- -- -- -- -- Test : (n : ℕ) → hLevelTrunc (5 + n) (S₊ (3 + n)) → TypeOfHLevel ℓ-zero (4 + n)
-- -- -- -- -- -- -- Test n = rec (isOfHLevelTypeOfHLevel (4 + n))
-- -- -- -- -- -- --            λ {north → hLevelTrunc (4 + n) (S₊ (2 + n)) , isOfHLevelTrunc (4 + n)
-- -- -- -- -- -- --             ; south → hLevelTrunc (4 + n) (S₊ (2 + n)) , isOfHLevelTrunc (4 + n)
-- -- -- -- -- -- --             ; (merid a i) → Σ≡Prop (λ _ → isPropIsOfHLevel (4 + n))
-- -- -- -- -- -- --                                     {u = hLevelTrunc (4 + n) (S₊ (2 + n)) , isOfHLevelTrunc (4 + n)}
-- -- -- -- -- -- --                                     {v = hLevelTrunc (4 + n) (S₊ (2 + n)) , isOfHLevelTrunc (4 + n)}
-- -- -- -- -- -- --                                     (ua (helper a)) i}
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --   helper2 : Iso (hLevelTrunc (4 + n) (S₊ (2 + n))) (hLevelTrunc (4 + n) (S₊ (2 + n)))
-- -- -- -- -- -- --   Iso.fun helper2 = map λ {north → north ; south → north ; (merid a i) → ((merid a) ∙ sym (merid (ptSn (suc n)))) i}
-- -- -- -- -- -- --   Iso.inv helper2 = map λ {north → north ; south → north ; (merid a i) → ((merid a) ∙ sym (merid (ptSn (suc n)))) i}
-- -- -- -- -- -- --   Iso.rightInv helper2 = {!!}
-- -- -- -- -- -- --   Iso.leftInv helper2 = {!!}

-- -- -- -- -- -- --   helper : (a : S₊ (2 + n) ) → (hLevelTrunc (4 + n) (S₊ (2 + n))) ≃ (hLevelTrunc (4 + n) (S₊ (2 + n)))
-- -- -- -- -- -- --   helper north = idEquiv (hLevelTrunc (4 + n) (S₊ (2 + n)))
-- -- -- -- -- -- --   helper south = idEquiv (hLevelTrunc (4 + n) (S₊ (2 + n)))
-- -- -- -- -- -- --     where

-- -- -- -- -- -- --   helper (merid a i) = Σ≡Prop (isPropIsEquiv) {u = idEquiv (hLevelTrunc (4 + n) (S₊ (2 + n)))}
-- -- -- -- -- -- --                                               {v = {!!} } -- idEquiv (hLevelTrunc (4 + n) (S₊ (2 + n)))
-- -- -- -- -- -- --                               (funExt
-- -- -- -- -- -- --                                 (elim {!!} (λ {north → {!!}
-- -- -- -- -- -- --                                              ; south j → {!!} -- ∣ ? -- (sym (merid (ptSn (suc n))) ∙ (merid a)) j ∣
-- -- -- -- -- -- --                                              ; (merid x i) j → {!!}}))) i
