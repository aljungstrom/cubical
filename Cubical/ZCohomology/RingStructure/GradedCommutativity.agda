{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.RingStructure.GradedCommutativity where
open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.Properties

open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.S1 hiding (_·_)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.Truncation
  renaming (elim to trElim ; map to trMap ; map2 to trMap2; rec to trRec ; elim3 to trElim3)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Data.Int
  renaming (_+_ to _ℤ+_ ; _·_ to _ℤ∙_ ; +-comm to +ℤ-comm ; ·-comm to ∙-comm ; +-assoc to ℤ+-assoc ; -_ to -ℤ_)
    hiding (_+'_ ; +'≡+)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary

open import Cubical.Foundations.Path
pathalg : ∀ {ℓ} {A : Type ℓ} (x y : A) → (p q : x ≡ y) (P : Square p q refl refl)
          → PathP (λ j → PathP (λ i → Path A (p (i ∧ j)) (q (i ∨ ~ j))) (λ k → q (~ j ∧ k)) λ k → p (j ∨ k)) (sym P) (flipSquare P)
pathalg {A = A} x y = J (λ y p → (q : x ≡ y) → (P : Square p q refl refl) →
      PathP
      (λ j →
         PathP (λ i → Path A (p (i ∧ j)) (q (i ∨ ~ j)))
         (λ k₁ → q (~ j ∧ k₁)) (λ k₁ → p (j ∨ k₁)))
      (sym P) (flipSquare P))
        λ q → J (λ q P → PathP
      (λ j →
         PathP (λ i → Path A x (q (i ∨ ~ j)))
         (λ k₁ → q (~ j ∧ k₁)) refl)
      (λ i → P (~ i)) λ i j → P j i)
        refl

inst : ∀ {ℓ} {A : Type ℓ} (x : A) → (P : Square (refl {x = x}) refl refl refl) → sym P ≡ flipSquare P
inst x = pathalg x x refl refl

pathalg2 : ∀ {ℓ} {A : Type ℓ} (x y : A) → (p q : x ≡ y) (P : Square p q refl refl)
          → PathP (λ i → PathP (λ j → p i ≡ q (~ i)) ((λ j → p (i ∨ j)) ∙ (λ j → q (~ i ∨ ~ j))) ((λ j → p (i ∧ ~ j)) ∙ (λ j → q (~ i ∧ j))))
                   (sym (rUnit p) ∙∙ P ∙∙ lUnit _)
                   (sym (lUnit (sym q)) ∙∙ (λ i j → P (~ i) (~ j)) ∙∙ rUnit (sym p))
pathalg2 x y = J (λ y p → (q : x ≡ y) (P : Square p q refl refl)
          → PathP (λ i → PathP (λ j → p i ≡ q (~ i)) ((λ j → p (i ∨ j)) ∙ (λ j → q (~ i ∨ ~ j))) ((λ j → p (i ∧ ~ j)) ∙ (λ j → q (~ i ∧ j))))
                   (sym (rUnit p) ∙∙ P ∙∙ lUnit _)
                   (sym (lUnit (sym q)) ∙∙ (λ i j → P (~ i) (~ j)) ∙∙ rUnit (sym p)))
                 λ q → J (λ q P → PathP
      (λ i →
         (λ j → x) ∙ (λ j → q (~ i ∨ ~ j)) ≡
         (λ j → x) ∙ (λ j → q (~ i ∧ j)))
      ((λ i → rUnit refl (~ i)) ∙∙ P ∙∙ lUnit q)
      ((λ i → lUnit (λ i₁ → q (~ i₁)) (~ i)) ∙∙ (λ i j → P (~ i) (~ j))
       ∙∙ rUnit refl)) refl


inst2 : ∀ {ℓ} {A : Type ℓ} (x : A) → (P : Square (refl {x = x}) refl refl refl) → P ≡ λ i j → P (~ i) (~ j)
inst2 x P =
  transport (λ i → doubleCompPath-filler (sym (rUnit refl)) P (lUnit refl) (~ i) ≡ doubleCompPath-filler (sym (rUnit refl))
            (λ i j → P (~ i) (~ j)) (lUnit refl) (~ i)) (pathalg2 _ _ refl refl P)

inst3 : ∀ {ℓ} {A : Type ℓ} (x : A) → (P : Square (refl {x = x}) refl refl refl) → flipSquare P ≡ λ i j → P i (~ j)
inst3 x P = sym (inst x P) ∙ sym (inst2 x (cong sym P))

inst4 : ∀ {ℓ} {A : Type ℓ} {x : A} → (P : Square (refl {x = x}) refl refl refl) → sym P ≡ cong sym P
inst4 P = inst _ _ ∙ inst3 _ P

is-even : ℕ → Type
is-even zero = Unit
is-even (suc zero) = ⊥
is-even (suc (suc n)) = is-even n

isProp-iseven : (n : ℕ) → isProp (is-even n)
isProp-iseven zero x y = refl
isProp-iseven (suc zero) = isProp⊥
isProp-iseven (suc (suc n)) = isProp-iseven n

is-odd : ℕ → Type
is-odd n = is-even (suc n)

is-even-suc : (n : ℕ) → is-odd n → is-even (suc n)
is-even-suc (suc zero) p = tt
is-even-suc (suc (suc n)) p = is-even-suc n p

is-odd-suc : (n : ℕ) → is-even n → is-odd (suc n)
is-odd-suc zero p = tt
is-odd-suc (suc (suc n)) p = is-odd-suc n p

evenOrOdd : (n : ℕ) → is-even n ⊎ is-odd n
evenOrOdd zero = inl tt
evenOrOdd (suc zero) = inr tt
evenOrOdd (suc (suc n)) = evenOrOdd n

¬evenAndOdd : (n : ℕ) → ¬ is-even n × is-odd n
¬evenAndOdd zero (p , ())
¬evenAndOdd (suc zero) ()
¬evenAndOdd (suc (suc n)) = ¬evenAndOdd n

evenOrOdd-Prop : (n : ℕ) → isProp (is-even n ⊎ is-odd n)
evenOrOdd-Prop n (inl x) (inl x₁) = cong inl (isProp-iseven n x x₁)
evenOrOdd-Prop n (inl x) (inr x₁) = ⊥-rec (¬evenAndOdd _ (x , x₁))
evenOrOdd-Prop n (inr x) (inl x₁) = ⊥-rec (¬evenAndOdd _ (x , x₁))
evenOrOdd-Prop n (inr x) (inr x₁) = cong inr (isProp-iseven _ x x₁)

coHomKTyp : (n : ℕ) → Type
coHomKTyp zero = Int
coHomKTyp (suc n) = S₊ (suc n)

-ₖ-helper : {k : ℕ} → (n m : ℕ) → is-even n ⊎ is-odd n → is-even m ⊎ is-odd m → coHomKTyp k → coHomKTyp k
-ₖ-helper {k = zero} n m (inl x₁) q x = x
-ₖ-helper {k = zero} n m (inr x₁) (inl x₂) x = x
-ₖ-helper {k = zero} n m (inr x₁) (inr x₂) x = 0 - x
-ₖ-helper {k = suc zero} n m p q base = base
-ₖ-helper {k = suc zero} n m (inl x) q (loop i) = loop i
-ₖ-helper {k = suc zero} n m (inr x) (inl x₁) (loop i) = loop i
-ₖ-helper {k = suc zero} n m (inr x) (inr x₁) (loop i) = loop (~ i)
-ₖ-helper {k = suc (suc k)} n m p q north = north
-ₖ-helper {k = suc (suc k)} n m p q south = north
-ₖ-helper {k = suc (suc k)} n m (inl x) q (merid a i) = (merid a ∙ sym (merid (ptSn (suc k)))) i
-ₖ-helper {k = suc (suc k)} n m (inr x) (inl x₁) (merid a i) = (merid a ∙ sym (merid (ptSn (suc k)))) i
-ₖ-helper {k = suc (suc k)} n m (inr x) (inr x₁) (merid a i) = (merid a ∙ sym (merid (ptSn (suc k)))) (~ i)

-ₖ-gen : {k : ℕ} (n m : ℕ) (p : is-even n ⊎ is-odd n) (q : is-even m ⊎ is-odd m) → coHomK k → coHomK k
-ₖ-gen {k = zero} = -ₖ-helper {k = zero}
-ₖ-gen {k = suc k} n m p q = trMap (-ₖ-helper {k = suc k} n m p q)

-ₖ^_·_ : {k : ℕ} (n m : ℕ) → coHomK k → coHomK k
-ₖ^_·_ {k = zero} n m = -ₖ-helper {k = zero} n m (evenOrOdd n) (evenOrOdd m)
-ₖ^_·_ {k = suc k} n m = trMap (-ₖ-helper n m (evenOrOdd n) (evenOrOdd m))

-ₖ-gen-inr : {k : ℕ} → (n m : ℕ) (p : _) (q : _) (x : coHomK k) → -ₖ-gen n m (inr p) (inr q) x ≡ (-ₖ x)
-ₖ-gen-inr {k = zero} n m p q _ = refl
-ₖ-gen-inr {k = suc zero} n m p q =
  trElim ((λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _))
         λ { base → refl
          ; (loop i) → refl}
-ₖ-gen-inr {k = suc (suc k)} n m p q =
  trElim ((λ _ → isOfHLevelPath (4 + k) (isOfHLevelTrunc (4 + k)) _ _))
         λ { north → refl
           ; south → refl
           ; (merid a i) k → ∣ symDistr (merid (ptSn _)) (sym (merid a)) (~ k) (~ i) ∣ₕ}

-ₖ-gen-inl-left : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : coHomK k) → -ₖ-gen n m (inl p) q x ≡ x
-ₖ-gen-inl-left {k = zero} n m p q x = refl
-ₖ-gen-inl-left {k = suc zero} n m p q =
  trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
         λ { base → refl ; (loop i) → refl}
-ₖ-gen-inl-left {k = suc (suc k)} n m p q =
  trElim (λ _ → isOfHLevelPath (4 + k) (isOfHLevelTrunc (4 + k)) _ _)
         λ { north → refl
           ; south → cong ∣_∣ₕ (merid (ptSn _))
           ; (merid a i) k → ∣ compPath-filler (merid a) (sym (merid (ptSn _))) (~ k) i  ∣ₕ}

-ₖ-gen-inl-right : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : coHomK k) → -ₖ-gen n m p (inl q) x ≡ x
-ₖ-gen-inl-right {k = zero} n m (inl x₁) q x = refl
-ₖ-gen-inl-right {k = zero} n m (inr x₁) q x = refl
-ₖ-gen-inl-right {k = suc zero} n m (inl x₁) q =
  trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
         λ { base → refl ; (loop i) → refl}
-ₖ-gen-inl-right {k = suc zero} n m (inr x₁) q =
  trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
         λ { base → refl ; (loop i) → refl}
-ₖ-gen-inl-right {k = suc (suc k)} n m (inl x₁) q =
  trElim (λ _ → isOfHLevelPath (4 + k) (isOfHLevelTrunc (4 + k)) _ _)
         λ { north → refl
           ; south → cong ∣_∣ₕ (merid (ptSn _))
           ; (merid a i) k → ∣ compPath-filler (merid a) (sym (merid (ptSn _))) (~ k) i  ∣ₕ}
-ₖ-gen-inl-right {k = suc (suc k)} n m (inr x₁) q =
  trElim (λ _ → isOfHLevelPath (4 + k) (isOfHLevelTrunc (4 + k)) _ _)
         λ { north → refl
           ; south → cong ∣_∣ₕ (merid (ptSn _))
           ; (merid a i) k → ∣ compPath-filler (merid a) (sym (merid (ptSn _))) (~ k) i  ∣ₕ}

cong-₁ : (n m : ℕ) (p : _) (q : _) (P : Path (coHomK 1) (0ₖ _) (0ₖ _))
     → cong (trMap (-ₖ-helper n m (inr p) (inr q))) P ≡ sym P
cong-₁ n m p q P = code≡sym (0ₖ _) P
  where
  t : PathP (λ i → 0ₖ 1 ≡ ∣ loop i ∣ → ∣ loop i ∣ ≡ 0ₖ 1) (cong (trMap (-ₖ-helper n m (inr p) (inr q)))) (cong (trMap (-ₖ-helper n m (inr p) (inr q))))
  t = toPathP (funExt λ P → cong (transport (λ i → ∣ loop i ∣ ≡ 0ₖ 1) ∘ (cong (trMap (-ₖ-helper n m (inr p) (inr q)))))
                                  (λ j → transp (λ i → 0ₖ 1 ≡ ∣ loop (~ i ∧ ~ j) ∣) j (compPath-filler P (sym (cong ∣_∣ₕ loop)) j))
                          ∙∙ cong (transport (λ i → ∣ loop i ∣ ≡ 0ₖ 1))
                                  (cong-∙ (trMap (-ₖ-helper n m (inr p) (inr q))) P (sym (cong ∣_∣ₕ loop)) ∙ isCommΩK 1 _ _)
                          ∙∙ (λ j → transp (λ i → ∣ loop (i ∨ j) ∣ ≡ 0ₖ 1) j
                                  (((λ i → ∣ loop (i ∨ j) ∣) ∙ cong (trMap (-ₖ-helper n m (inr p) (inr q))) P)))
                           ∙ sym (lUnit _))

  code : (x : coHomK 1) → 0ₖ _ ≡ x → x ≡ 0ₖ _
  code = trElim (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                λ { base → cong (trMap (-ₖ-helper n m (inr p) (inr q))) ; (loop i) → t i}

  code≡sym : (x : coHomK 1) → (p : 0ₖ _ ≡ x) → code x p ≡ sym p
  code≡sym x = J (λ x p → code x p ≡ sym p) refl


cong-₂ : {k : ℕ} (n m : ℕ)  (p : _) (q : _) (P : Path (coHomK (2 + k)) (0ₖ _) (0ₖ _))
     → cong (trMap (-ₖ-helper n m (inr p) (inr q))) P ≡ sym P
cong-₂ {k = k} n m p q P = code≡sym (0ₖ _) P
  where
  code : (x : coHomK (2 + k)) → 0ₖ _ ≡ x → x ≡ 0ₖ _
  code = trElim (λ _ → isOfHLevelΠ (4 + k) λ _ → isOfHLevelPath (4 + k) (isOfHLevelTrunc (4 + k)) _ _)
                λ { north → cong (trMap (-ₖ-helper n m (inr p) (inr q)))
                   ; south P → cong ∣_∣ₕ (sym (merid (ptSn _))) ∙ (cong (trMap (-ₖ-helper n m (inr p) (inr q))) P)
                   ; (merid a i) → t a i}
    where
    t : (a : S₊ (suc k)) → PathP (λ i → 0ₖ (2 + k) ≡ ∣ merid a i ∣ₕ → ∣ merid a i ∣ₕ ≡ 0ₖ (2 + k))
                                  (cong (trMap (-ₖ-helper n m (inr p) (inr q))))
                                  (λ P → cong ∣_∣ₕ (sym (merid (ptSn _))) ∙ (cong (trMap (-ₖ-helper n m (inr p) (inr q))) P))
    t a = toPathP (funExt λ P → cong (transport (λ i → ∣ merid a i ∣ ≡ 0ₖ (suc (suc k))))
                   (cong (cong (trMap (-ₖ-helper n m (inr p) (inr q)))) (λ i → (transp (λ j → 0ₖ (suc (suc k)) ≡ ∣ merid a (~ j ∧ ~ i) ∣) i
                         (compPath-filler P (λ j → ∣ merid a (~ j) ∣ₕ) i))))
        ∙∙ cong (transport (λ i → ∣ merid a i ∣ ≡ 0ₖ (suc (suc k)))) (congFunct (trMap (-ₖ-helper n m (inr p) (inr q))) P (sym (cong ∣_∣ₕ (merid a))))
        ∙∙ (λ j → transp (λ i → ∣ merid a (i ∨ j) ∣ ≡ 0ₖ (suc (suc k))) j
                  (compPath-filler' (cong ∣_∣ₕ (sym (merid a)))
                    (cong (trMap (-ₖ-helper n m (inr p) (inr q))) P
                    ∙ cong (trMap (-ₖ-helper n m (inr p) (inr q))) (sym (cong ∣_∣ₕ (merid a)))) j))
        ∙∙ (λ i → sym (cong ∣_∣ₕ (merid a))
                 ∙ isCommΩK (2 + k) (cong (trMap (-ₖ-helper n m (inr p) (inr q))) P)
                                    (cong (trMap (-ₖ-helper n m (inr p) (inr q))) (sym (cong ∣_∣ₕ (merid a)))) i)
        ∙∙ (λ j → (λ i → ∣ merid a (~ i ∨ j) ∣)
                 ∙ (cong ∣_∣ₕ (compPath-filler' (merid a) (sym (merid (ptSn _))) (~ j)) ∙ (λ i → trMap (-ₖ-helper n m (inr p) (inr q)) (P i))))
        ∙ sym (lUnit _))

  code≡sym : (x : coHomK (2 + k)) → (p : 0ₖ _ ≡ x) → code x p ≡ sym p
  code≡sym x = J (λ x p → code x p ≡ sym p) refl

-ₖ-gen-Kn→ΩKn+1 : {k : ℕ} → (n m : ℕ) (p : _) (q : _) (x : coHomK k) → Kn→ΩKn+1 _ (-ₖ-gen n m (inr p) (inr q) x) ≡ sym (Kn→ΩKn+1 _ x)
-ₖ-gen-Kn→ΩKn+1 n m p q x = cong (Kn→ΩKn+1 _) (-ₖ-gen-inr n m p q x) ∙ Kn→ΩKn+1-ₖ _ x

Kn→ΩKn+1-ₖ' : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : coHomK k) → Kn→ΩKn+1 k (-ₖ-gen n m (inr p) (inr q) x) ≡ sym (Kn→ΩKn+1 k x)
Kn→ΩKn+1-ₖ' = -ₖ-gen-Kn→ΩKn+1

+'-comm : (n m : ℕ) → n +' m ≡ m +' n
+'-comm n m = +'≡+ n m ∙∙ +-comm n m ∙∙ sym (+'≡+ m n)

∪ₗ'-1-cool : (m : ℕ) → S¹ → S₊ (suc m) → S₊ (suc (suc m))
∪ₗ'-1-cool m base y = north
∪ₗ'-1-cool zero (loop i) base = north
∪ₗ'-1-cool zero (loop i) (loop i₁) =
  (sym (rCancel (merid base)) ∙∙ (λ i → merid (loop i) ∙ sym (merid base)) ∙∙ rCancel (merid base)) i i₁
∪ₗ'-1-cool (suc m) (loop i) north = north
∪ₗ'-1-cool (suc m) (loop i) south = north
∪ₗ'-1-cool (suc m) (loop i) (merid a j) = 
  (sym (rCancel (merid north)) ∙∙ (λ i → merid ((∪ₗ'-1-cool m (loop i) a)) ∙ sym (merid north)) ∙∙ rCancel (merid north)) i j

∪ₗ'-cool : (n m : ℕ) → S₊ (suc n) →  S₊ (suc m) → S₊ (suc (suc (n + m)))
∪ₗ'-cool-0 : (n m : ℕ) → (x : S₊ (suc n)) → ∪ₗ'-cool n m x (ptSn _) ≡ north
∪ₗ'-cool-south : (n m : ℕ) → (x : S₊ (suc n)) → ∪ₗ'-cool n (suc m) x south ≡ north
∪ₗ'-cool zero m x y = ∪ₗ'-1-cool m x y
∪ₗ'-cool (suc n) zero north y = north
∪ₗ'-cool (suc n) zero south y = north
∪ₗ'-cool (suc n) zero (merid a i) base = north
∪ₗ'-cool (suc n) zero (merid a i) (loop i₁) =
  ∪ₗ'-1-cool (suc (n + zero))
       (loop i) ((sym (∪ₗ'-cool-0 n zero a)
    ∙∙ (λ i₁ → ∪ₗ'-cool n _ a (loop i₁))
    ∙∙ ∪ₗ'-cool-0 n zero a) i₁)
∪ₗ'-cool (suc n) (suc m) north y = north
∪ₗ'-cool (suc n) (suc m) south y = north
∪ₗ'-cool (suc n) (suc m) (merid a i) north = north
∪ₗ'-cool (suc n) (suc m) (merid a i) south = north
∪ₗ'-cool (suc n) (suc m) (merid a i) (merid b j) =
  ∪ₗ'-1-cool (suc (n + suc m)) (loop i)
    ((sym (∪ₗ'-cool-0 n (suc m) a) ∙∙ (λ i → ∪ₗ'-cool n _ a (merid b i)) ∙∙ ∪ₗ'-cool-south n m a) j)
∪ₗ'-cool-0 zero zero base = refl
∪ₗ'-cool-0 zero zero (loop i) = refl
∪ₗ'-cool-0 (suc n) zero north = refl
∪ₗ'-cool-0 (suc n) zero south = refl
∪ₗ'-cool-0 (suc n) zero (merid a i) = refl
∪ₗ'-cool-0 zero (suc m) base = refl
∪ₗ'-cool-0 zero (suc m) (loop i) = refl
∪ₗ'-cool-0 (suc n) (suc m) north = refl
∪ₗ'-cool-0 (suc n) (suc m) south = refl
∪ₗ'-cool-0 (suc n) (suc m) (merid a i) = refl
∪ₗ'-cool-south zero m base = refl
∪ₗ'-cool-south zero m (loop i) = refl
∪ₗ'-cool-south (suc n) m north = refl
∪ₗ'-cool-south (suc n) m south = refl
∪ₗ'-cool-south (suc n) m (merid a i) = refl

∪-uncool : (n m : ℕ) → S₊ (suc n) → S₊ (suc m) → coHomK (suc n +' suc m)
∪-uncool zero m base y = 0ₖ _
∪-uncool zero m (loop i) y = Kn→ΩKn+1 _ ∣ y ∣ i
∪-uncool (suc n) m north y = 0ₖ _
∪-uncool (suc n) m south y = 0ₖ _
∪-uncool (suc n) m (merid a i) y = Kn→ΩKn+1 _ (∪-uncool n m a y) i

pre-cup : (n m : ℕ) → S₊ (suc n) → S₊ (suc m) → S₊ (suc n +' suc m)
pre-cup-id : (m : ℕ) (b : _) → pre-cup zero m base b ≡ north
pre-cup-id-silly : (n m : ℕ) (a : _) → pre-cup n (suc m) a north ≡ north
pre-cup-id-silly-south : (n m : ℕ) (a : _) → pre-cup n (suc m) a south ≡ north
pre-cup n zero x base = north
pre-cup zero zero base (loop i) = north
pre-cup zero zero (loop i) (loop j) =
  (sym (rCancel (merid base)) ∙∙ cong (λ x → merid x ∙ sym (merid base)) loop ∙∙ rCancel (merid base)) j i
pre-cup (suc n) zero north (loop i) = north
pre-cup (suc n) zero south (loop i) = north
pre-cup (suc n) zero (merid a i) (loop j) =
  (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north)) (cong (pre-cup n zero a) loop) ∙∙ rCancel (merid north)) j i
pre-cup n (suc m) x north = north
pre-cup n (suc m) x south = north
pre-cup zero (suc m) base (merid b j) = north
pre-cup zero (suc m) (loop i) (merid b j) =
     (sym (rCancel (merid north))
  ∙∙ cong (λ x → merid x ∙ sym (merid north))
       (merid b ∙ sym (merid (ptSn _)))
  ∙∙ rCancel (merid north)) j i
pre-cup (suc n) (suc m) north (merid b j) = north
pre-cup (suc n) (suc m) south (merid b j) = north
pre-cup (suc n) (suc m) (merid a i) (merid b j) =
  (sym (rCancel (merid north))
  ∙∙ cong (λ x → merid x ∙ sym (merid north))
          (sym (pre-cup-id-silly n m a)
        ∙∙ cong (pre-cup n (suc m) a) (merid b)
        ∙∙ pre-cup-id-silly-south n m a)
  ∙∙ rCancel (merid north)) j i
pre-cup-id zero base = refl
pre-cup-id zero (loop i) = refl
pre-cup-id (suc m) north = refl
pre-cup-id (suc m) south = refl
pre-cup-id (suc m) (merid a i) = refl
pre-cup-id-silly n m a = refl
pre-cup-id-silly-south n m a = refl

pre-cup-lId : (n m : ℕ) (y : _) → pre-cup n m (ptSn _) y ≡ ptSn _
pre-cup-lId n zero base = refl
pre-cup-lId zero zero (loop i) = refl
pre-cup-lId (suc n) zero (loop i) = refl
pre-cup-lId n (suc m) north = refl
pre-cup-lId n (suc m) south = refl
pre-cup-lId zero (suc m) (merid a i) = refl
pre-cup-lId (suc n) (suc m) (merid a i) = refl

cup∙ : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m)))
cup∙ n m = trRec (isOfHLevel↑∙ (suc n) m)
                 λ x → (λ y → elim-snd n m y .fst x) , elim-snd∙ n m x
  where
  elim-snd : (n m : ℕ) → coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (n + m)))
  elim-snd n m =
    trRec (subst (isOfHLevel (3 + m))
            (λ i → (S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (+-comm m n i)))))
            (isOfHLevel↑∙' (suc m) n))
          λ y → (λ x → ∣ pre-cup n m x y ∣) , cong ∣_∣ₕ (pre-cup-lId n m y)

  elim-snd∙ : (n m : ℕ) (x : _) → elim-snd n m (snd (coHomK-ptd (suc m))) .fst x ≡ 0ₖ _
  elim-snd∙ n zero x = refl
  elim-snd∙ n (suc m) x = refl

cup' : (n m : ℕ) → coHomK (suc n) → coHomK (suc m) → coHomK (suc (suc (n + m)))
cup' n m x = cup∙ n m x .fst

cup∙≡ : (n m : ℕ) (x : coHomK (suc n)) → cup∙ n m x ≡ ⌣ₖ∙ (suc n) (suc m) x
cup∙≡ n m =
  trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevel↑∙ (suc n) m) _ _)
    λ a → →∙Homogeneous≡ (isHomogeneousKn _) (funExt λ x → funExt⁻ (cong fst (⌣ₖ≡cup'' n m x)) a)
  where
  ⌣ₖ' : (n m : ℕ) → coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc n +' suc m)
  fst (⌣ₖ' n m y) x = _⌣ₖ_ {n = suc n} {m = suc m} ∣ x ∣ₕ y
  snd (⌣ₖ' n m y) = 0ₖ-⌣ₖ (suc n) _ y

  cup'' : (n m : ℕ) → coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc n +' suc m)
  cup'' n m = trRec (subst (isOfHLevel (3 + m))
            (λ i → (S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (+-comm m n i)))))
            (isOfHLevel↑∙' (suc m) n))
              λ y → (λ x → ∣ pre-cup n m x y ∣) , cong ∣_∣ₕ (pre-cup-lId n m y)

  ⌣ₖ≡cup'' : (n m : ℕ) (y : _) → cup'' n m y ≡ ⌣ₖ' n m y
  ⌣ₖ≡cup'' n m =
    trElim (λ _ → isOfHLevelPath (3 + m) (subst (isOfHLevel (3 + m))
            (λ i → (S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (+-comm m n i)))))
            (isOfHLevel↑∙' (suc m) n)) _ _)
      λ b → →∙Homogeneous≡ (isHomogeneousKn _)
      (funExt λ a → main n m a b)
    where
    main : (n m : ℕ) (a : _) (b : _) → cup'' n m ∣ b ∣ .fst a ≡ (_⌣ₖ_ {n = suc n} {m = suc m} ∣ a ∣ ∣ b ∣)
    main zero zero base base = refl
    main zero zero (loop i) base k = Kn→ΩKn+10ₖ 1 (~ k) i
    main zero zero base (loop i) k = ∣ north ∣
    main zero zero (loop i) (loop j) k =
      hcomp (λ r → λ {(i = i0) → 0ₖ 2
                     ; (i = i1) → 0ₖ 2
                     ; (j = i0) → ∣ rCancel (merid base) (~ k ∧ r) i ∣
                     ; (j = i1) → ∣ rCancel (merid base) (~ k ∧ r) i ∣
                     ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel (merid base)))
                                    (cong (λ x → merid x ∙ sym (merid base)) loop)
                                    (rCancel (merid base)) r j i ∣
                     ; (k = i1) → _⌣ₖ_ {n = 1} {m = 1} ∣ loop i ∣ ∣ loop j ∣})
            (_⌣ₖ_ {n = 1} {m = 1} ∣ loop i ∣ ∣ loop j ∣)
    main zero (suc m) base north = refl
    main zero (suc m) base south = refl
    main zero (suc m) base (merid a i) = refl
    main zero (suc m) (loop i) north k = Kn→ΩKn+10ₖ _ (~ k) i
    main zero (suc m) (loop i) south k =
      ∣ ((λ i → merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north)) ∙ rCancel (merid north)) (~ k) i ∣ₕ
    main zero (suc m) (loop i) (merid b j) k =
      hcomp (λ r → λ {(i = i0) → ∣ north ∣
                     ; (i = i1) → ∣ north ∣
                     ; (j = i0) → ∣ rCancel (merid north) (~ k ∧ r) i ∣ₕ
                     ; (j = i1) → ∣ compPath-filler ((λ i → merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north))) (rCancel (merid north)) r (~ k) i ∣ₕ
                     ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _)) (cong (λ x → merid x ∙ sym (merid north))
                                      (merid b ∙ sym (merid (ptSn _)))) (rCancel _) r j i ∣ₕ
                     ; (k = i1) → _⌣ₖ_ {n = 1} {m = suc (suc m)} ∣ loop i ∣ ∣ merid b j ∣ₕ})
            (Kn→ΩKn+1 _ (hcomp (λ r → λ { (j = i0) → ∣ merid b j ∣ₕ
                                          ; (j = i1) → ∣ merid (ptSn (suc m)) (~ r ∨ k) ∣
                                          ; (k = i0) → ∣ compPath-filler (merid b) (sym (merid (ptSn (suc m)))) r j ∣
                                          ; (k = i1) → ∣ (merid b) j ∣})
                                ∣ merid b j ∣) i)
    main (suc n) zero north base = refl
    main (suc n) zero north (loop i) = refl
    main (suc n) zero south base = refl
    main (suc n) zero south (loop i) = refl
    main (suc n) zero (merid a i) base k = (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 _) (main n zero a base)) k i
    main (suc n) zero (merid a i) (loop j) k =
      hcomp (λ r → λ {(i = i0) → ∣ north ∣
                     ; (i = i1) → ∣ north ∣
                     ; (j = i0) → compPath-filler' (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 _) (main n zero a base)) r k i
                     ; (j = i1) → compPath-filler' (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 _) (main n zero a base)) r k i
                     ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _)) (cong (λ x → merid x ∙ sym (merid north)) (cong (pre-cup n zero a) loop) ) (rCancel _) r j i ∣ₕ
                     ; (k = i1) → _⌣ₖ_ {n = suc (suc n)} {m = suc zero} ∣ merid a i ∣ ∣ loop j ∣})
            (Kn→ΩKn+1 _ (main n zero a (loop j) k) i)
    main (suc n) (suc m) north north = refl
    main (suc n) (suc m) south north = refl
    main (suc zero) (suc m) (merid a i) north k =
      (cong (Kn→ΩKn+1 (suc (suc (suc m)))) (sym (main zero (suc m) a north)) ∙ Kn→ΩKn+10ₖ _) (~ k) i
    main (suc (suc n)) (suc m) (merid a i) north k =
      (cong (Kn→ΩKn+1 (suc (suc (suc n + suc m)))) (sym (main (suc n) (suc m) a north)) ∙ Kn→ΩKn+10ₖ _) (~ k) i
    main (suc n) (suc m) north south = refl
    main (suc n) (suc m) south south = refl
    main (suc zero) (suc m) (merid a i) south k =
      (cong (Kn→ΩKn+1 (suc (suc (suc m)))) (sym (main zero (suc m) a south)) ∙ Kn→ΩKn+10ₖ _) (~ k) i
    main (suc (suc n)) (suc m) (merid a i) south k =
      (cong (Kn→ΩKn+1 (suc (suc (suc n + suc m)))) (sym (main (suc n) (suc m) a south)) ∙ Kn→ΩKn+10ₖ _) (~ k) i
    main (suc n) (suc m) north (merid b j) = refl
    main (suc n) (suc m) south (merid b j) = refl
    main (suc zero) (suc m) (merid a i) (merid b j) k =
      hcomp (λ r → λ { (i = i0) → ∣ north ∣
                      ; (i = i1) → ∣ north ∣
                      ; (k = i0) →
                        ∣ doubleCompPath-filler (sym (rCancel (merid north))) (
                          cong (λ x → merid x ∙ sym (merid north))
          (rUnit (cong (pre-cup 0 (suc m) a) (merid b)) r))
          (rCancel (merid north)) r j i ∣
                      ; (k = i1) → _⌣ₖ_ {n = 2} {m = 2 + m} ∣ merid a i ∣ ∣ merid b j ∣})
            (Kn→ΩKn+1 _ (main zero (suc m) a (merid b j) k) i)
    main (suc (suc n)) (suc m) (merid a i) (merid b j) k =
      hcomp (λ r → λ { (i = i0) → ∣ north ∣
                      ; (i = i1) → ∣ north ∣
                      ; (k = i0) →
                        ∣ doubleCompPath-filler (sym (rCancel (merid north))) (
                          cong (λ x → merid x ∙ sym (merid north))
          (rUnit (cong (pre-cup (suc n) (suc m) a) (merid b)) r))
          (rCancel (merid north)) r j i ∣
                      ; (k = i1) → _⌣ₖ_ {n = 3 + n} {m = 2 + m} ∣ merid a i ∣ ∣ merid b j ∣})
            (Kn→ΩKn+1 _ (main (suc n) (suc m) a (merid b j) k) i)

natTranspLem : ∀ {A : ℕ → Type} (n m : ℕ) (a : A n) (B : (n : ℕ) → Type)
  (f : (n : ℕ) → (a : A n) → B n) (p : n ≡ m) 
  → f m (subst A p a) ≡ subst B p (f n a)
natTranspLem {A = A} n m a B f = J (λ m p → f m (subst A p a) ≡ subst B p (f n a)) (cong (f n) (substRefl a) ∙ sym (substRefl (f n a)))


cup'-lUnit : (n m : ℕ) (x : coHomK (suc m)) → cup' n m (0ₖ _) x  ≡ 0ₖ _
cup'-lUnit n m x = funExt⁻ (cong fst (cup∙≡ n m (0ₖ (suc n)))) x ∙ 0ₖ-⌣ₖ (suc n) (suc m) x

subst-help : (n m : ℕ) → subst coHomK (+'-comm (suc m) (suc n))
      (0ₖ (suc (suc (m + n))))
      ≡ snd (coHomK-ptd (suc (suc (n + m))))
subst-help zero zero = refl
subst-help zero (suc m) = refl
subst-help (suc n) zero = refl
subst-help (suc n) (suc m) = refl

cup'-anti-comm' :
  (n m : ℕ) (p : _) (q : _) (x : coHomK (suc n))
    → cup∙ n m x ≡ ((λ y → (-ₖ-gen (suc n) (suc m) p q) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n y x)))
                   , cong ((-ₖ-gen (suc n) (suc m) p q) ∘ (subst coHomK (+'-comm (suc m) (suc n)))) (cup'-lUnit m n x)
                          ∙ cong (-ₖ-gen (suc n) (suc m) p q) (subst-help n m))
cup'-anti-comm' = {!!}
  where
  open import Cubical.Foundations.Transport

  lem₂ : {k : ℕ} (n m : ℕ) (x : _) (y : _) → (p : refl {x = 0ₖ (suc (suc k))} ≡ refl {x = 0ₖ (suc (suc k))})
                  → cong (cong (-ₖ-gen n m (inr x) (inr y))) p
                  ≡ sym p
  lem₂ n m x y p = {!!}
  {-
         rUnit _
      ∙∙ (λ k → (λ i → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y refl (i ∧ k))
              ∙∙ cong (λ z → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y z k) p
              ∙∙ λ i → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y refl (~ i ∧ k))
      ∙∙ (λ k → transportRefl (λ _ _ → ∣ north ∣) k
              ∙∙ cong sym p
              ∙∙ sym (transportRefl (λ _ _ → ∣ north ∣) k))
      ∙∙ sym (rUnit _)
      ∙∙ sym (inst4 p) -}


  module _ (n m : ℕ) where
    t₁ = transport (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}
                         ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)})

    t₂ = transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}
                         ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
    
    t₃ = transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}
                         ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})

    t₄ = transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))}
                         ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) })

  t : (n m : ℕ) → _ → _
  t n m = transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}
                          ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
         ∘ (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}
                            ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}))
          ∘ (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))}
                            ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) }))


  final : (n m : ℕ) (p : _) → (t₁ n m ∘ t n m) p
          ≡ p
  final n m p =
       sym (substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) (cong suc ((+'-comm (suc (suc n)) (suc m)))) (+'-comm (suc (suc m)) (suc (suc n)))
            (((transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}))
          ∘ (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))}))) p))
    ∙∙ sym (substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) (cong (suc ∘ suc) (+'-comm (suc m) (suc n)))
                           (((λ i₁ → suc (+'-comm (suc (suc n)) (suc m) i₁)) ∙ +'-comm (suc (suc m)) (suc (suc n))))
                           (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))}) p))
    ∙∙ sym (substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) (cong suc (+'-comm (suc n) (suc (suc m))))
                           (((λ i₁ → suc (suc (+'-comm (suc m) (suc n) i₁)))
                           ∙ (λ i₁ → suc (+'-comm (suc (suc n)) (suc m) i₁))
                           ∙ +'-comm (suc (suc m)) (suc (suc n)))) p)
    ∙∙ cong (λ x → subst (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) x p) (isSetℕ _ _ _ refl)
    ∙∙ transportRefl p



  lem₈ : (n m : ℕ) → (p : refl {x = 0ₖ _} ≡ refl {x = 0ₖ _})
      → cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))) p
       ≡ transport (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}
                         ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}) p
  lem₈ n m p k = transp (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) (i ∨ ~ k))}
                           ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) (i ∨ ~ k))}) (~ k)
                      ((λ i j → transp (λ i → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (i ∧ ~ k))) k (p i j)))

  lUnit₁ : (n m : ℕ) (a : _) → cup' (suc n) m ∣ north ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
  lUnit₁ n zero base = refl
  lUnit₁ n zero (loop i) = refl
  lUnit₁ n (suc m) north = refl
  lUnit₁ n (suc m) south = refl
  lUnit₁ n (suc m) (merid a i) = refl

  lUnit₂ : (n m : ℕ) (a : _) → cup' (suc n) m ∣ south ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
  lUnit₂ n zero base = refl
  lUnit₂ n zero (loop i) = refl
  lUnit₂ n (suc m) north = refl
  lUnit₂ n (suc m) south = refl
  lUnit₂ n (suc m) (merid a i) = refl

  lem₁ : (n m : ℕ) (a : _) (b : _) → (λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)
       ≡ (sym (Kn→ΩKn+10ₖ _)
       ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
       ∙∙ Kn→ΩKn+10ₖ _)
  lem₁ n m a b =
       (λ k i j → ∣ (sym (rCancel _) ∙∙ cong (λ x → merid x ∙ sym (merid north)) (rUnit (λ i → pre-cup m (suc n) b (merid a i)) (~ k)) ∙∙ rCancel _) i j ∣ₕ)
     ∙ (λ k i j → hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) r j ∣
                                 ; (i = i1) → ∣ rCancel (merid north) r j ∣
                                 ; (j = i0) → ∣ north ∣
                                 ; (j = i1) → ∣ north ∣
                                 ; (k = i0) → ∣ doubleCompPath-filler
                                                  (sym (rCancel _))
                                                  (cong (λ x → merid x ∙ sym (merid north))
                                                  ((λ i → pre-cup m (suc n) b (merid a i)))) (rCancel _) r i j ∣ₕ})
                         (Kn→ΩKn+1 _ (cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣) j))

  lem₃ : (n m : ℕ) (a : _) (b : _)
      → (sym (lUnit₁ n m b) ∙∙ ((λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) ∙∙ lUnit₂ n m b)
       ≡ Kn→ΩKn+1 _ (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ)
  lem₃ n zero a base = sym (rUnit refl) ∙ sym (Kn→ΩKn+10ₖ _)
  lem₃ n zero a (loop i) k =
    hcomp (λ r → λ {(i = i0) → compPath-filler' (sym (rUnit refl)) (sym (Kn→ΩKn+10ₖ _)) r k
                   ; (i = i1) → compPath-filler' (sym (rUnit refl)) (sym (Kn→ΩKn+10ₖ _)) r k
                   ; (k = i0) → rUnit (λ i₂ → cup' (suc n) zero ∣ merid a i₂ ∣ₕ ∣ loop i ∣ₕ) r
                   ; (k = i1) → Kn→ΩKn+1 (suc (suc (n + zero)))
                                  (cup' n zero ∣ a ∣ₕ ∣ loop i ∣ₕ) })
          λ j → hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
                      ; (i = i1) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
                      ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
                                      (cong (λ x → merid x ∙ sym (merid north)) ((λ i → pre-cup n zero a (loop i))))
                                      (rCancel _) r i j ∣ₕ
                      ; (k = i1) → Kn→ΩKn+1 (suc (suc (n + zero)))
                                       (cup' n zero ∣ a ∣ₕ ∣ loop i ∣ₕ) j
                      ; (j = i0) → ∣ north ∣
                      ; (j = i1) → ∣ north ∣})
                 (Kn→ΩKn+1 _ (cup' n zero ∣ a ∣ₕ ∣ loop i ∣ₕ) j)
  lem₃ n (suc m) a north = sym (rUnit refl) ∙ sym (Kn→ΩKn+10ₖ _)
  lem₃ n (suc m) a south = sym (rUnit refl) ∙ sym (Kn→ΩKn+10ₖ _)
  lem₃ n (suc m) a (merid b i) k =
    hcomp (λ r → λ {(i = i0) → compPath-filler' (sym (rUnit refl)) (sym (Kn→ΩKn+10ₖ _)) r k
                   ; (i = i1) → compPath-filler' (sym (rUnit refl)) (sym (Kn→ΩKn+10ₖ _)) r k
                   ; (k = i0) → rUnit (λ i₂ → cup' (suc n) (suc m) ∣ merid a i₂ ∣ₕ ∣ merid b i ∣ₕ) r
                   ; (k = i1) → Kn→ΩKn+1 (suc (suc (n + suc m)))
                                  (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ)})
      (λ j → hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
                      ; (i = i1) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
                      ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
                                      (cong (λ x → merid x ∙ sym (merid north)) (rUnit (λ i → pre-cup n (suc m) a (merid b i)) r))
                                      (rCancel _) r i j ∣ₕ
                      ; (k = i1) → Kn→ΩKn+1 (suc (suc (n + suc m)))
                                       (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ) j
                      ; (j = i0) → ∣ north ∣
                      ; (j = i1) → ∣ north ∣})
             (Kn→ΩKn+1 (suc (suc (n + suc m)))
                                       (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ) j))



  main : (n m : ℕ) (p : _) (q : _) (a : _) (b : _)
      → (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡ (-ₖ-gen (suc n) (suc m) p q) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ))
  main zero zero p q base base = refl
  main zero zero p q base (loop i) = refl
  main zero zero p q (loop i) base = refl
  main zero zero p q (loop i) (loop j) = {!refl!}
  main zero (suc m) p q base north = refl
  main zero (suc m) p q base south = refl
  main zero (suc m) p q base (merid a i) = refl
  main zero (suc m) p q (loop i) north = refl
  main zero (suc m) p q (loop i) south = refl
  main zero (suc m) p q (loop i) (merid a j) = {!!}
  main (suc n) zero p q north base = refl
  main (suc n) zero p q north (loop i) = refl
  main (suc n) zero p q south base = refl
  main (suc n) zero p q south (loop i) = refl
  main (suc n) zero p q (merid a i) base = refl
  main (suc n) zero (inl x) q (merid a i) (loop j) = {!!}
  main (suc n) zero (inr x) (inr tt) (merid a i) (loop j) = {!Susp (S₊ (suc (n + 0))) ≡ Susp (S₊ (suc n))!}
    where
    lem1 : (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)} ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)}))
                (λ i j → ∣ (sym (rCancel _) ∙∙ cong (λ x → merid x ∙ sym (merid north)) (merid a ∙ sym (merid (ptSn _))) ∙∙ rCancel _) j i ∣ₕ)
        ≡ flipSquare (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north))
                     (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
                       (merid a ∙ sym (merid (ptSn _))))
                     ∙∙ rCancel (merid north)))
        {- λ i j → ∣ (sym (rCancel _)
                  ∙∙ cong (λ x → merid x ∙ sym (merid north))
                     (transport (λ i → Path (S₊ {!+'-comm 2 (suc n) (~ i)!}) north north) (merid a ∙ sym (merid (ptSn _))))
                  ∙∙ rCancel _ ) j i ∣ₕ -}
    lem1 = {!!}

    help : cong (λ x → cong (λ y → cup' (suc n) zero ∣ x ∣ₕ ∣ y ∣ₕ) loop) (merid a)
         ≡ λ i j → -ₖ-gen (suc (suc n)) 1 (inr x) (inr tt)
      (subst coHomK (+'-comm 1 (suc (suc n)))
       (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ))
    help = (λ k i j → ∣ (sym (rCancel _) ∙∙ cong (λ x → merid x ∙ sym (merid north)) (rUnit (λ i → pre-cup n zero a (loop i)) k) ∙∙ rCancel _) j i ∣ₕ)
        ∙∙ (λ k i j → ∣ (sym (rCancel _) ∙∙ cong (λ x → merid x ∙ sym (merid north)) ({!lem₃!} ∙∙ (λ i → {!!}) ∙∙ {!!}) ∙∙ rCancel _) j i ∣ₕ)
        ∙∙ {!!}
        ∙∙ {!!}
        ∙∙ {!natTranspLem _ _ !}
        ∙∙ cong (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)} ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)}))
                (λ _ i j → ∣ (sym (rCancel _) ∙∙ cong (λ x → merid x ∙ sym (merid north)) (merid a ∙ sym (merid (ptSn _))) ∙∙ rCancel _) j i ∣ₕ)
        ∙∙ (λ k → transp (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) (i ∨ k))} ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) (i ∨ k))}) k
                    λ i j → transp (λ i → coHomK (+'-comm 1 (suc (suc n)) (i ∧ k))) (~ k)
                        (cup' zero (suc n) ∣ loop i ∣ₕ ∣ merid a j ∣ₕ))
        ∙∙ sym (inst _ ((cong (cong (subst coHomK (+'-comm 1 (suc (suc n)))))
                (λ i j → cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ))))
        ∙∙ sym (lem₂ (suc (suc n)) 1 x tt (cong (cong (subst coHomK (+'-comm 1 (suc (suc n)))))
                (λ i j → cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))
  main (suc n) (suc m) p q north north = refl
  main (suc n) (suc m) p q north south = refl
  main (suc n) (suc m) p q north (merid a i) = refl
  main (suc n) (suc m) p q south north = refl
  main (suc n) (suc m) p q south south = refl
  main (suc n) (suc m) p q south (merid a i) = refl
  main (suc n) (suc m) p q (merid a i) north = refl
  main (suc n) (suc m) p q (merid a i) south = refl
  main (suc n) (suc m) (inl x) (inl y) (merid a i) (merid b j) k = {!!} -- help k i j
    where
    {-
    lem₂ : (n m : ℕ) (p : is-even n) (q : is-even m) (a : _) (b : _) →
        ((sym (Kn→ΩKn+10ₖ _)
         ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
         ∙∙ Kn→ΩKn+10ₖ _))
      ≡ transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
          (sym (Kn→ΩKn+10ₖ _)
         ∙∙ cong (Kn→ΩKn+1 _) (sym (lUnit₁ n m b) ∙∙ ((λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) ∙∙ lUnit₂ n m b)
         ∙∙ Kn→ΩKn+10ₖ _)
    lem₂ n m p q a b =
         cong (λ x → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x ∙∙ Kn→ΩKn+10ₖ _)
              ((rUnit (λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ)
            ∙∙ (λ k → (λ i → main m (suc n) (inr q) (inl p) b north (k ∧ i))
                   ∙∙ (λ i → main m (suc n) (inr q) (inl p) b (merid a i) k)
                    ∙∙ λ i → main m (suc n) (inr q) (inl p) b south (k ∧ ~ i))
            ∙∙ cong (main m (suc n) (inr q) (inl p) b north ∙∙_∙∙ sym (main m (suc n) (inr q) (inl p) b south))
                       (rUnit _
                     ∙ (λ k → (λ i → -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
                                          ((subst coHomK (+'-comm (suc (suc n)) (suc m))
                                             (cup' (suc n) m ∣ north ∣ ∣ b ∣))) (i ∧ k))
                            ∙∙ ((λ i → -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
                                          (subst coHomK (+'-comm (suc (suc n)) (suc m))
                                             (cup' (suc n) m ∣ merid a i ∣ ∣ b ∣)) k))
                            ∙∙ λ i → -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
                                          ((subst coHomK (+'-comm (suc (suc n)) (suc m))
                                             (cup' (suc n) m ∣ south ∣ ∣ b ∣))) (~ i ∧ k))))
              ∙ lem n m a b q p)
       ∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n}
          _ _ ((sym (lUnit₁ n m b) ∙∙ ((λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) ∙∙ lUnit₂ n m b)) _ (λ _ p → (sym (Kn→ΩKn+10ₖ _)
         ∙∙ cong (Kn→ΩKn+1 _) p
         ∙∙ Kn→ΩKn+10ₖ _)) (+'-comm (suc (suc n)) (suc m))
      where
      lemType : (n m : ℕ) (a : _) (b : _) (q : _) (p : _) → Type
      lemType n m a b q p =
             (main m (suc n) (inr q) (inl p) b north
          ∙∙ (-ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
                                            ((subst coHomK (+'-comm (suc (suc n)) (suc m))
                                               (cup' (suc n) m ∣ north ∣ ∣ b ∣))))
          ∙∙ cong (subst coHomK (+'-comm (suc (suc n)) (suc m)))
                  (λ i → cup' (suc n) m ∣ merid a i ∣ ∣ b ∣)
          ∙∙ sym (-ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
                                            ((subst coHomK (+'-comm (suc (suc n)) (suc m))
                                               (cup' (suc n) m ∣ south ∣ ∣ b ∣))))
          ∙∙ sym (main m (suc n) (inr q) (inl p) b south))
          ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc m) i) ≡ 0ₖ ((+'-comm (suc (suc n)) (suc m) i)))
                      (sym (lUnit₁ n m b) ∙∙ ((λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) ∙∙ lUnit₂ n m b)

      S¹-case : (i : I) → (n : ℕ) (a : _) (q : _) (p : _) → lemType n zero a (loop i) q p
      S¹-case i n a q p =
           sym (rUnit _)
         ∙ λ k → transp
                 (λ i → 0ₖ ((+'-comm (suc (suc n)) (suc zero) (i ∨ ~ k)))
                    ≡ 0ₖ (+'-comm (suc (suc n)) (suc zero) (i ∨ ~ k)) ) (~ k)
              (((λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc zero) (i ∧ ~ k)))
                k (cup' (suc n) zero ∣ merid a j ∣ ∣ loop i ∣)) ∙ refl))

      Susp-case : (i : I) → (n m : ℕ) (a : _) (b : _) (q : _) (p : _) → lemType n (suc m) a (merid b i) q p
      Susp-case i n m a b q p =
          sym (rUnit _)
        ∙ λ k → transp
                 (λ i → 0ₖ ((+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)))
                    ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)) ) (~ k)
              (((λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc m)) (i ∧ ~ k)))
                k (cup' (suc n) (suc m) ∣ merid a j ∣ ∣ merid b i ∣)) ∙ refl))

      lem : (n m : ℕ) (a : _) (b : _) (q : _) (p : _)
        → lemType n m a b q p
      lem n zero a base q p = S¹-case i0 n a q p
      lem n zero a (loop i) q p = S¹-case i n a q p
      lem n (suc m) a north q p = Susp-case i0 n m a (ptSn (suc m)) q p
      lem n (suc m) a south q p = Susp-case i1 n m a (ptSn (suc m)) q p
      lem n (suc m) a (merid b i) q p = Susp-case i n m a b q p

    lem₄ : Kn→ΩKn+1 _ (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡ sym (Kn→ΩKn+1 _ (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ ∣ a ∣)))
    lem₄ = cong (Kn→ΩKn+1 _) (main n m (inr x) (inr y) a b)
         ∙ -ₖ-gen-Kn→ΩKn+1 (suc n) (suc m) x y (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ ∣ a ∣))

    lem₅ : (n m : ℕ) (a : _) (b : _)
       → Kn→ΩKn+1 _ (cup' m n ∣ b ∣ ∣ a ∣)
      ≡ (sym (lUnit₁ m n a) ∙∙ (λ i → cup' (suc m) n ∣ merid b i ∣ ∣ a ∣) ∙∙ lUnit₂ m n a)
    lem₅ n m a b = sym (lem₃ m n b a)

    lem₆ : (sym (lUnit₁ m n a) ∙∙ (λ i → cup' (suc m) n ∣ merid b i ∣ ∣ a ∣) ∙∙ lUnit₂ m n a)
         ≡ transport (λ i → 0ₖ (+'-comm (suc n) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc n) (suc (suc m)) i))
                     λ i → cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ
    lem₆ = cong (sym (lUnit₁ m n a) ∙∙_∙∙ lUnit₂ m n a)
                (rUnit _ ∙ (λ i → (λ k → main (suc m) n (inl y) (inr x) north a (i ∧ k))
                               ∙∙ (λ k → main (suc m) n (inl y) (inr x) (merid b k) a i)
                               ∙∙ λ k → main (suc m) n (inl y) (inr x) south a (i ∧ ~ k))
                          ∙ cong (main (suc m) n (inl y) (inr x) north a ∙∙_∙∙ sym (main (suc m) n (inl y) (inr x) south a))
                                  (rUnit _
                                    ∙ λ k → (λ i → (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
                                              (subst coHomK (+'-comm (suc n) (suc (suc m)))
                                               (cup' n (suc m) ∣ a ∣ₕ ∣ north ∣ₕ))) (i ∧ k))
                                         ∙∙ (λ i → (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
                                              (subst coHomK (+'-comm (suc n) (suc (suc m)))
                                               (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ))) k)
                                          ∙∙ λ i → (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
                                              (subst coHomK (+'-comm (suc n) (suc (suc m)))
                                               (cup' n (suc m) ∣ a ∣ₕ ∣ south ∣ₕ))) (~ i ∧ k)))
        ∙∙ lem n m a b x y
        ∙∙ refl
      where
      lemType : (n m : ℕ) (a : _) (b : _) (x : _) (y : _) → Type
      lemType n m a b x y =
        ((sym (lUnit₁ m n a)) ∙∙
       main (suc m) n (inl y) (inr x) north a ∙∙
       (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
          (subst coHomK (+'-comm (suc n) (suc (suc m)))
           (cup' n (suc m) ∣ a ∣ₕ ∣ north ∣ₕ)))
       ∙∙
       (λ i₁ →
          (subst coHomK (+'-comm (suc n) (suc (suc m)))
           (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i₁ ∣ₕ)))
       ∙∙
       (sym (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
          (subst coHomK (+'-comm (suc n) (suc (suc m)))
           (cup' n (suc m) ∣ a ∣ₕ ∣ south ∣ₕ))))
       ∙∙ (sym (main (suc m) n (inl y) (inr x) south a))
       ∙∙ lUnit₂ m n a)
       ≡ transport (λ i → 0ₖ (+'-comm (suc n) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc n) (suc (suc m)) i))
                     λ i → cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ

      S¹-case : (i : I) → (m : ℕ) (b : _) (x : _) (y : _) → lemType zero m (loop i) b x y
      S¹-case i m b x y =
           sym (rUnit _)
        ∙∙ sym (rUnit _)
        ∙∙ sym (rUnit _)
         ∙ λ k → transp (λ i → 0ₖ (+'-comm 1 (suc (suc m)) (i ∨ ~ k)) ≡ 0ₖ (+'-comm 1 (suc (suc m)) (i ∨ ~ k)))
                         (~ k)
                         λ j → transp (λ i → coHomK (+'-comm 1 (suc (suc m)) (i ∧ ~ k))) k
                               (cup' zero (suc m) ∣ loop i ∣ₕ ∣ merid b j ∣ₕ)

      Susp-case : (i : I) (n m : ℕ) (a : _) (b : _) (x : _) (y : _) → lemType (suc n) m (merid a i) b x y
      Susp-case i n m a b x y =
           sym (rUnit _)
        ∙∙ sym (rUnit _)
        ∙∙ sym (rUnit _)
         ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)) ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)))
                         (~ k)
                         λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc m)) (i ∧ ~ k))) k
                               (cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)

      lem : (n m : ℕ) (a : _) (b : _) (x : _) (y : _) → lemType n m a b x y
      lem zero m base b x y = S¹-case i0 m b x y
      lem zero m (loop i) b x y = S¹-case i m b x y
      lem (suc n) m north b x y = Susp-case i0 n m (ptSn (suc n)) b x y
      lem (suc n) m south b x y = Susp-case i1 n m (ptSn (suc n)) b x y
      lem (suc n) m (merid a i) b x y = Susp-case i n m a b x y

    MAIN₂ : (sym (Kn→ΩKn+10ₖ _)
         ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
         ∙∙ Kn→ΩKn+10ₖ _)
         ≡ transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
           (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})
            (sym ((sym (Kn→ΩKn+10ₖ _)
         ∙∙ cong (Kn→ΩKn+1 _) ((Kn→ΩKn+1 _ (cup' m n ∣ b ∣ ∣ a ∣)))
         ∙∙ Kn→ΩKn+10ₖ _))))
    MAIN₂ = lem₂ n m x y a b
          ∙ cong (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}
                                   ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}))
                 (cong ((λ x → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x ∙∙ (Kn→ΩKn+10ₖ _)))
                        (lem₃ n m a b ∙ lem₄)
                 ∙∙ natTranspLem {A = coHomK} _ _ (cup' m n ∣ b ∣ ∣ a ∣) _
                 (λ _ p → 
                 (sym (Kn→ΩKn+10ₖ _)
              ∙∙ cong (Kn→ΩKn+1 _) (sym (Kn→ΩKn+1 _ p))
              ∙∙ Kn→ΩKn+10ₖ _)) (+'-comm (suc m) (suc n))
                 ∙∙ refl)

    MAIN₃ : (sym (Kn→ΩKn+10ₖ _)
         ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
         ∙∙ Kn→ΩKn+10ₖ _)
         ≡ transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
           (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})
             (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) })
                        (sym ((sym (Kn→ΩKn+10ₖ _)
                       ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' n (suc m) ∣ a ∣ ∣ merid b i ∣))
                       ∙∙ Kn→ΩKn+10ₖ _)))))
    MAIN₃ = MAIN₂
          ∙ cong (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}
                                  ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}) ∘
                 (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}
                                  ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})))
             (cong (λ x → (sym (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙∙
               cong (Kn→ΩKn+1 (suc (suc (suc (m + n))))) (sym x)
               ∙∙ (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣))) (lem₅ n m a b ∙ lem₆)
               ∙ natTranspLem {λ n → 0ₖ n ≡ 0ₖ n} _ _ ((λ i₂ → cup' n (suc m) ∣ a ∣ ∣ merid b i₂ ∣)) _
                    (λ _ p → sym (Kn→ΩKn+10ₖ _)
                           ∙∙ cong (Kn→ΩKn+1 _) (sym p)
                           ∙∙ Kn→ΩKn+10ₖ _) (+'-comm (suc n) (suc (suc m))))
    lem₇ : (sym ((sym (Kn→ΩKn+10ₖ _)
                       ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' n (suc m) ∣ a ∣ ∣ merid b i ∣))
                       ∙∙ Kn→ΩKn+10ₖ _)))
           ≡ (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)
    lem₇ = cong sym (sym (lem₁ _ _ b a))
        ∙∙ sym (inst _ (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b (~ j) ∣ₕ))
        ∙∙ sym (inst2 _ _)

    MAIN₄ : transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
           (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})
             (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) })
                        (sym ((sym (Kn→ΩKn+10ₖ _)
                       ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' n (suc m) ∣ a ∣ ∣ merid b i ∣))
                       ∙∙ Kn→ΩKn+10ₖ _)))))
         ≡ t n m (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)
    MAIN₄ =
         cong (λ x → transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
           (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})
             (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) }) x)))
               lem₇

    help : (cong (λ x → (cong (λ y → cup' (suc n) (suc m) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
         ≡ λ i j → -ₖ-gen (suc (suc n)) (suc (suc m)) (inl x) (inl y)
      (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
       (cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
    help =
         ((sym (final n m ((cong (λ x → (cong (λ y → cup' (suc n) (suc m) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))))
         ∙ cong (transport (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}
                                 ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}))
                 (sym (MAIN₃ ∙ MAIN₄))
         ∙ sym (lem₈ n m (lem₁ n m a b i1)))
         ∙ cong (cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))))
           (sym (lem₁ n m a b)))
       ∙ (λ k → cong (cong (λ z → -ₖ-gen-inl-left (suc (suc n)) (suc (suc m)) x (inl y) z (~ k)) ∘ cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))
                         (λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ ∣ merid a i ∣)) -}

  main (suc n) (suc (suc m)) (inl x) (inr y) (merid a i) (merid b j) = {!y!}
    where
    {-
    lem1 : (n m : ℕ)  (x : is-even n) (y : is-odd (suc (suc (suc m)))) (a : _) (b : _)
         → cong (cup' (suc m) (suc n) ∣ b ∣ₕ ∘ ∣_∣ₕ) (merid a)
         ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i))
                     ((sym (lUnit₁ n _ b) ∙∙ (λ i → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ n _ b))
    lem1 n m x y a = λ { north → m-case i0 a (ptSn (suc m))
                       ; south → m-case i1 a (ptSn (suc m))
                       ; (merid b i) → m-case i a b }
      where
      m-case : (i : I) → (a : _) (b : _)
             → cong (cup' (suc m) (suc n) ∣ merid b i ∣ₕ ∘ ∣_∣ₕ) (merid a)
         ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i))
                     ((sym (lUnit₁ n _ (merid b i)) ∙∙ (λ j → cup' (suc n) (suc m) ∣ merid a j ∣ₕ ∣ merid b i ∣ₕ) ∙∙ lUnit₂ n _ (merid b i))) 
      m-case i a b =
           (λ k j →  main (suc m) (suc n) (inl y) (inl x) (merid b i) (merid a j) k)
        ∙∙ (λ k j → -ₖ-gen-inl-left (suc (suc m)) (suc (suc n)) y (inl x) (subst coHomK (+'-comm (suc (suc n)) (suc (suc m)))
                       (cup' (suc n) (suc m) ∣ merid a j ∣ ∣ merid b i ∣)) k)
        ∙∙ (rUnit _
          ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)) ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k))) (~ k)
                          ((λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc m)) (i ∧ ~ k))) k
                                          (cup' (suc n) (suc m) ∣ merid a j ∣ ∣ merid b i ∣)) ∙ refl))

    lem2 : (sym (Kn→ΩKn+10ₖ (suc (suc (suc m + suc n)))) ∙∙
                cong (Kn→ΩKn+1 (suc (suc (suc m + suc n))))
                (λ i₁ → cup' (suc m) (suc n) ∣ b ∣ₕ ∣ merid a i₁ ∣ₕ)
                ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc m + suc n))))
        ≡ t₂ n (suc m)
            (t₃ n (suc m)
              ((sym (Kn→ΩKn+10ₖ _) ∙∙
                cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (cup' (suc m) n ∣ b ∣ ∣ a ∣))
                ∙∙ Kn→ΩKn+10ₖ _)))
    lem2 =
         cong (λ x → sym (Kn→ΩKn+10ₖ (suc (suc (suc m + suc n)))) ∙∙
                cong (Kn→ΩKn+1 (suc (suc (suc m + suc n)))) x
                ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc m + suc n))))
              (lem1 n m x y a b
              ∙ cong (transport (λ i₁ →
                      0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i₁) ≡
                      0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i₁)))
                     (lem₃ n (suc m) a b
                      ∙ cong (Kn→ΩKn+1 (suc (suc (n + suc m))))
                             (main n (suc m) (inr x) (inl y) a b
                             ∙ -ₖ-gen-inl-right (suc n) (suc (suc m)) (inr x) y
                                       (subst coHomK (+'-comm (suc (suc m)) (suc n))
                                        (cup' (suc m) n ∣ b ∣ₕ ∣ a ∣ₕ)))))
      ∙∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n} _ _ ((Kn→ΩKn+1 _) (subst coHomK (+'-comm (suc (suc m)) (suc n)) (cup' (suc m) n ∣ b ∣ₕ ∣ a ∣ₕ))) _
           (λ _ x → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x ∙∙ Kn→ΩKn+10ₖ _) (+'-comm (suc (suc n)) (suc (suc m)))
      ∙∙ cong (subst (λ n₁ → refl ≡ refl) (+'-comm (suc (suc n)) (suc (suc m))))
              (natTranspLem {A = coHomK} _ _ (cup' (suc m) n ∣ b ∣ ∣ a ∣) _
                (λ _ x → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ x) ∙∙ Kn→ΩKn+10ₖ _)
                (+'-comm (suc (suc m)) (suc n)))

    lem3 : (n m : ℕ) (x : is-even n) (y : is-odd (suc (suc (suc m)))) (b : _) (a : _) → (sym (lUnit₁ (suc m) n a) ∙∙
                                        (λ i₁ → cup' (suc (suc m)) n ∣ merid b i₁ ∣ₕ ∣ a ∣ₕ) ∙∙
                                        lUnit₂ (suc m) n a)
                                     ≡ transport (λ i → 0ₖ (+'-comm (suc n) (suc (suc (suc m))) i)
                                                       ≡ 0ₖ (+'-comm (suc n) (suc (suc (suc m))) i))
                                         λ i₁ → cup' n (suc (suc m)) ∣ a ∣ₕ ∣ merid b (~ i₁) ∣ₕ
    lem3 = λ { zero m x y b base → S¹-case i0 m x y b
             ; zero m x y b (loop i) → S¹-case i m x y b
             ; (suc n) m x y b north → merid-case i0 n m x y (ptSn (suc n)) b
             ; (suc n) m x y b south → merid-case i1 n m x y (ptSn (suc n)) b
             ; (suc n) m x y b (merid a i) → merid-case i n m x y a b}
      where
      S¹-case : (i : I) → (m : ℕ) (x : is-even zero) (y : is-odd (suc (suc (suc m)))) (b : _) → (sym (lUnit₁ (suc m) zero (loop i)) ∙∙
                                        (λ i₁ → cup' (suc (suc m)) zero ∣ merid b i₁ ∣ₕ ∣ (loop i) ∣ₕ) ∙∙
                                        lUnit₂ (suc m) zero (loop i))
                                     ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc (suc (suc m))) i)
                                                       ≡ 0ₖ (+'-comm (suc zero) (suc (suc (suc m))) i))
                                         λ i₁ → cup' zero (suc (suc m)) ∣ loop i ∣ₕ ∣ merid b (~ i₁) ∣ₕ
      S¹-case i m x y b =
           sym (rUnit _)
        ∙∙ (λ k j → main (suc (suc m)) zero (inr y) (inr x) (merid b j) (loop i) k)
        ∙∙ cong-₂ (suc (suc (suc m))) 1 y x ((λ j₁ → (subst coHomK (+'-comm 1 (suc (suc (suc m))))
                                                       (cup' zero (suc (suc m)) ∣ loop i ∣ ∣ merid b j₁ ∣))))
         ∙ λ k → transp (λ i → 0ₖ (+'-comm 1 (suc (suc (suc m))) (i ∨ ~ k))
                                   ≡ 0ₖ (+'-comm 1 (suc (suc (suc m))) (i ∨ ~ k))) (~ k)
                   (λ j → transp (λ i → coHomK (+'-comm (suc zero) (suc (suc (suc m))) (i ∧ ~ k))) k
                                  (cup' zero (suc (suc m)) ∣ loop i ∣ₕ ∣ merid b (~ j) ∣ₕ))


      merid-case : (i : I) (n m : ℕ) (x : is-even (suc n)) (y : is-odd (suc (suc (suc m)))) (a : _) (b : _)
                 → (sym (lUnit₁ (suc m) (suc n) (merid a i)) ∙∙
                    (λ i₁ → cup' (suc (suc m)) (suc n) ∣ merid b i₁ ∣ₕ ∣ (merid a i) ∣ₕ) ∙∙
                    lUnit₂ (suc m) (suc n) (merid a i))
                 ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i)
                                   ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i))
                     λ i₁ → cup' (suc n) (suc (suc m)) ∣ merid a i ∣ₕ ∣ merid b (~ i₁) ∣ₕ
      merid-case i n m x y a b =
        sym (rUnit _)
        ∙∙ (λ k j → main (suc (suc m)) (suc n) (inr y) (inr x) (merid b j) (merid a i) k)
        ∙∙ cong-₂ (suc (suc (suc m))) (suc (suc n)) y x ((λ j₁ → (subst coHomK (+'-comm (suc (suc n)) (suc (suc (suc m))))
                                                       (cup' (suc n) (suc (suc m)) ∣ merid a i ∣ ∣ merid b j₁ ∣))))
         ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∨ ~ k))
                                   ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∨ ~ k))) (~ k)
                   (λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∧ ~ k))) k
                                  (cup' (suc n) (suc (suc m)) ∣ merid a i ∣ₕ ∣ merid b (~ j) ∣ₕ))

    help : (cong (λ x → (cong (λ y → cup' (suc n) (suc (suc m)) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
         ≡ λ i j → -ₖ-gen (suc (suc n)) (suc (suc (suc m))) (inl x) (inr y)
              (subst coHomK (+'-comm (suc (suc (suc m))) (suc (suc n)))
               (cup' (suc (suc m)) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
    help =
      sym ((λ k i j → -ₖ-gen-inl-left (suc (suc n)) (suc (suc (suc m))) x (inr y)
              (subst coHomK (+'-comm (suc (suc (suc m))) (suc (suc n)))
               (cup' (suc (suc m)) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)) k)
        ∙∙ lem₈ n (suc m) (λ i j → (cup' (suc (suc m)) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
        ∙∙ cong (transport (λ i₁ → refl ≡ refl))
                (lem₁ n (suc m) a b
              ∙∙ lem2
              ∙∙ cong (t₂ n (suc m) ∘ t₃ n (suc m))
                   (cong (λ x → (sym (Kn→ΩKn+10ₖ _) ∙∙
                                 cong (Kn→ΩKn+1 _) x
                                 ∙∙ Kn→ΩKn+10ₖ _))
                         (sym (lem₃ (suc m) n b a)
                       ∙ lem3 n m x y b a
                      )
                  ∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n} _ _ (λ i₂ → cup' n (suc (suc m)) ∣ a ∣ ∣ merid b (~ i₂) ∣) _
                                  (λ _ x → (sym (Kn→ΩKn+10ₖ _) ∙∙
                                 cong (Kn→ΩKn+1 _) x
                                 ∙∙ Kn→ΩKn+10ₖ _))
                                  (+'-comm (suc n) (suc (suc (suc m))))
                  ∙ cong (t₄ n (suc m)) ( sym (cong sym (lem₁ (suc m) n b a)))))
        ∙∙ final n (suc m)
             (λ i₁ j₁ →
            cup' (suc n) (suc (suc m)) ∣ merid a j₁ ∣ ∣ merid b (~ i₁) ∣)
        ∙∙ inst _ (λ i₁ j₁ →
         cup' (suc n) (suc (suc m)) ∣ merid a j₁ ∣ ∣ merid b i₁ ∣))
    -}
  main (suc n) (suc m) (inr x) (inl y) (merid a i) (merid b j) = {!!}
    where
    help : (cong (λ x → (cong (λ y → cup' (suc n) (suc m) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
         ≡ λ i j → -ₖ-gen (suc (suc n)) (suc (suc m)) (inr x) (inl y)
              (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
               (cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
    help = ((sym (transportRefl _)
          ∙ cong (λ x → subst (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) x (λ i₁ j₁ → cup' (suc n) (suc m) ∣ merid a i₁ ∣ ∣ merid b j₁ ∣)) (isSetℕ _ _ refl _))
          ∙ substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n})
                            (+'-comm (suc (suc n)) (suc (suc m)))
                            (+'-comm (suc (suc m)) (suc (suc n)))
                            (λ i₁ j₁ → cup' (suc n) (suc m) ∣ merid a i₁ ∣ ∣ merid b j₁ ∣))
        ∙∙ (λ k → lem₈ n m (lem₈ m n (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ ∣ merid b j ∣) (~ k)) (~ k))
        ∙∙ (cong (cong (cong ((subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))))
                  λ k i j → -ₖ-gen-inl-left (suc (suc m)) (suc (suc n)) y (inr x)
                              (subst coHomK (+'-comm (suc (suc n)) (suc (suc m)))
                              (cup' (suc n) (suc m) ∣ merid a i ∣ ∣ merid b j ∣)) (~ k))
        ∙∙ sym (cong (cong (cong ((subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))))
                (λ k i j → main (suc m) (suc n) (inl y) (inr x) (merid b j) (merid a i) k))
        ∙∙ λ k i j → -ₖ-gen-inl-right (suc (suc n)) (suc (suc m)) (inr x) y
         (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
          (cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)) (~ k)
  main (suc (suc n)) (suc (suc m)) (inr x) (inr y) (merid a i) (merid b j) =
    {!!}
    where
    {-
    lem₂ : {k : ℕ} (p : refl {x = 0ₖ (suc (suc k))} ≡ refl {x = 0ₖ (suc (suc k))})
                  → cong (cong (-ₖ-gen (suc (suc (suc n))) (suc (suc (suc m))) (inr x) (inr y))) p
                  ≡ sym p
    lem₂ p =
         rUnit _
      ∙∙ (λ k → (λ i → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y refl (i ∧ k))
              ∙∙ cong (λ z → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y z k) p
              ∙∙ λ i → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y refl (~ i ∧ k))
      ∙∙ (λ k → transportRefl (λ _ _ → ∣ north ∣) k
              ∙∙ cong sym p
              ∙∙ sym (transportRefl (λ _ _ → ∣ north ∣) k))
      ∙∙ sym (rUnit _)
      ∙∙ sym (inst4 p)

    lem2 : cong (cup' (suc m) (suc (suc n)) ∣ b ∣ₕ ∘ ∣_∣ₕ) (merid a)
      ≡ transport (λ i → 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i))
                  (sym (lUnit₁ (suc n) _ b) ∙∙ (λ i → cup' (suc (suc n)) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ _ _ b)
    lem2 = fin b
      where
      help : (i : I) (b : _) →
                 cong (cup' (suc m) (suc (suc n)) ∣ merid b i ∣ₕ ∘ ∣_∣ₕ) (merid a)
               ≡ transport (λ i → 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i)
                                 ≡ 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i))
                 (sym (lUnit₁ (suc n) _ (merid b i)) ∙∙ (λ j → cup' (suc (suc n)) (suc m) ∣ merid a j ∣ₕ ∣ merid b i ∣ₕ) ∙∙ lUnit₂ (suc n) _ (merid b i))
      help i b =
           (λ k j → main (suc m) (suc (suc n)) (inl y) (inr x) (merid b i) (merid a j) k)
         ∙ (λ k j → -ₖ-gen-inl-left (suc (suc m)) (suc (suc (suc n))) y (inr x)
                 (subst coHomK (+'-comm (suc (suc (suc n))) (suc (suc m)))
                   (cup' (suc (suc n)) (suc m) ∣ merid a j ∣ ∣ merid b i ∣)) k)
         ∙ (λ k → transp (λ i → 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) (i ∨ ~ k))
                                ≡ 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) (i ∨ ~ k))) (~ k)
                          λ j → transp (λ i → coHomK (+'-comm (suc (suc (suc n))) (suc (suc m)) (i ∧ ~ k))) k
                                        (cup' (suc (suc n)) (suc m) ∣ merid a j ∣ ∣ merid b i ∣))
         ∙ cong (transport (λ i → 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i)
                                 ≡ 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i)))
                 (rUnit λ j → cup' (suc (suc n)) (suc m) ∣ merid a j ∣ₕ ∣ merid b i ∣ₕ)

      fin : (b : _) → cong (cup' (suc m) (suc (suc n)) ∣ b ∣ₕ ∘ ∣_∣ₕ) (merid a)
             ≡ transport (λ i → 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i)
                                 ≡ 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i))
              (sym (lUnit₁ (suc n) _ b) ∙∙ (λ i → cup' (suc (suc n)) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ _ _ b)
      fin north = help i0 (ptSn (suc m))
      fin south = help i1 (ptSn (suc m))
      fin (merid a i) = help i a

    lem3 : (sym (Kn→ΩKn+10ₖ (suc (suc (suc m + suc (suc n))))) ∙∙
       cong (Kn→ΩKn+1 (suc (suc (suc m + suc (suc n)))))
       (λ i₁ → cup' (suc m) (suc (suc n)) ∣ b ∣ₕ ∣ merid a i₁ ∣ₕ)
       ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc m + suc (suc n)))))
        ≡ transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc (suc n))) (suc (suc m)) i))}
                          ≡ refl {x = 0ₖ ((suc (+'-comm (suc (suc (suc n))) (suc (suc m)) i)))})
                    (sym (Kn→ΩKn+10ₖ _)
                  ∙∙ cong (Kn→ΩKn+1 _) (sym (lUnit₁ (suc n) _ b) ∙∙ (λ i → cup' (suc (suc n)) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ _ _ b)
                  ∙∙ Kn→ΩKn+10ₖ _)
    lem3 =
        cong (λ x → (sym (Kn→ΩKn+10ₖ (suc (suc (suc m + suc (suc n))))) ∙∙
       cong (Kn→ΩKn+1 (suc (suc (suc m + suc (suc n))))) x
       ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc m + suc (suc n)))))) lem2
      ∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n}
          _ _ ((sym (lUnit₁ (suc n) _ b) ∙∙ (λ i → cup' (suc (suc n)) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ _ _ b)) _
              (λ _ x → (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x ∙∙ Kn→ΩKn+10ₖ _))
         ((+'-comm (suc (suc (suc n))) (suc (suc m))))

    lem4 : (sym (lUnit₁ (suc n) _ b) ∙∙ (λ i → cup' (suc (suc n)) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ _ _ b)
                     ≡ Kn→ΩKn+1 _ ((subst coHomK (+'-comm (suc (suc m)) (suc (suc n))) (cup' (suc m) (suc n) ∣ b ∣ₕ ∣ a ∣ₕ)))
    lem4 = lem₃ (suc n) (suc m) a b
        ∙∙ cong (Kn→ΩKn+1 _) (main (suc n) (suc m) (inl x) (inl y) a b)
        ∙∙ cong (Kn→ΩKn+1 _) (-ₖ-gen-inl-left (suc (suc n)) (suc (suc m)) x (inl y) _)

    lem₅ : ((λ i₁ → Kn→ΩKn+10ₖ _ (~ i₁)) ∙∙
       (λ i₁ →
          Kn→ΩKn+1 _
          (Kn→ΩKn+1 _
           (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
            (cup' (suc m) (suc n) ∣ b ∣ₕ ∣ a ∣ₕ))
           i₁))
       ∙∙ Kn→ΩKn+10ₖ _)
       ≡ transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc (suc m)) (suc (suc n)) i)))}
                         ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc (suc m)) (suc (suc n)) i)))})
                   ((λ i₁ → Kn→ΩKn+10ₖ _ (~ i₁)) ∙∙
       (λ i₁ →
          Kn→ΩKn+1 _
          (Kn→ΩKn+1 _
            (cup' (suc m) (suc n) ∣ b ∣ₕ ∣ a ∣ₕ)
           i₁))
       ∙∙ Kn→ΩKn+10ₖ _)
    lem₅ =
      natTranspLem {A = coHomK} _ _ (cup' (suc m) (suc n) ∣ b ∣ₕ ∣ a ∣ₕ) _
        (λ _ x → sym (Kn→ΩKn+10ₖ _) ∙∙ (cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ x)) ∙∙ Kn→ΩKn+10ₖ _)
        (+'-comm (suc (suc m)) (suc (suc n)))

    lem6 : (Kn→ΩKn+1 (suc (suc (suc (m + suc n))))
             (cup' (suc m) (suc n) ∣ b ∣ ∣ a ∣))
          ≡ (sym (lUnit₁ (suc m) _ a) ∙∙ (λ i → cup' (suc (suc m)) (suc n) ∣ merid b i ∣ ∣ a ∣) ∙∙ lUnit₂ (suc m) _ a)
    lem6 = sym (lem₃ (suc m) (suc n) b a)

    lem7 : (sym (lUnit₁ (suc m) _ a) ∙∙ (λ i → cup' (suc (suc m)) (suc n) ∣ merid b i ∣ ∣ a ∣) ∙∙ lUnit₂ (suc m) _ a)
         ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i) ≡  0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i))
             (λ i → cup' (suc n) (suc (suc m)) ∣ a ∣ ∣ merid b i ∣)
    lem7 = mainLem n m a b x y
      where
      meridCase : (i : I) (n m : ℕ) (a : _) (b : _ ) (x : _) (y : _)
        → (sym (lUnit₁ (suc m) _ (merid a i)) ∙∙ (λ j → cup' (suc (suc m)) (suc n) ∣ merid b j ∣ ∣ merid a i ∣) ∙∙ lUnit₂ (suc m) _ (merid a i))
         ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i) ≡  0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i))
                     λ j → cup' (suc n) (suc (suc m)) ∣ merid a i ∣ ∣ merid b j ∣
      meridCase i n m a b x y =
           sym (rUnit _)
        ∙∙ (λ k j → main (suc (suc m)) (suc n) (inr y) (inl x) (merid b j) (merid a i) k)
        ∙∙ (λ k j → -ₖ-gen-inl-right ((suc (suc (suc m)))) (suc (suc n)) (inr y) x
                       (subst coHomK (+'-comm (suc (suc n)) (suc (suc (suc m))))
                        (cup' (suc n) (suc (suc m)) ∣ merid a i ∣ ∣ merid b j ∣)) k)
         ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∨ ~ k))
                               ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∨ ~ k))) (~ k)
                        λ j → (transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∧ ~ k))) k)
                               (cup' (suc n) (suc (suc m)) ∣ merid a i ∣ ∣ merid b j ∣)

      mainLem : (n m : ℕ) (a : _) (b : _ ) (x : is-even (suc (suc n))) (y : is-odd (suc (suc (suc m))))
          → (sym (lUnit₁ (suc m) _ a) ∙∙ (λ j → cup' (suc (suc m)) (suc n) ∣ merid b j ∣ ∣ a ∣) ∙∙ lUnit₂ (suc m) _ a)
           ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i) ≡  0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i))
                       λ j → cup' (suc n) (suc (suc m)) ∣ a ∣ ∣ merid b j ∣
      mainLem n m north b x y = meridCase i0 n m (ptSn (suc n)) b x y
      mainLem n m south b x y = meridCase i1 n m (ptSn (suc n)) b x y
      mainLem n m (merid a i) b x y = meridCase i n m a b x y

    lem8 : (sym (Kn→ΩKn+10ₖ _) ∙∙
       (cong (Kn→ΩKn+1 _)
          (Kn→ΩKn+1 (suc (suc (suc (m + suc n))))
           (cup' (suc m) (suc n) ∣ b ∣ₕ ∣ a ∣ₕ)))
       ∙∙ Kn→ΩKn+10ₖ _)
      ≡ transport (λ i → refl {x = 0ₖ ((suc (+'-comm (suc (suc n)) (suc (suc (suc m))) i)))}
                        ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc (suc (suc m))) i))})
                  (λ i j → cup' (suc (suc n)) (suc (suc m)) ∣ merid a j ∣ ∣ merid b i ∣)
    lem8 = cong (λ x → (sym (Kn→ΩKn+10ₖ _) ∙∙ (cong (Kn→ΩKn+1 _) x) ∙∙ Kn→ΩKn+10ₖ _))
                (lem6 ∙ lem7)
        ∙∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n} _ _ ((λ i₁ → cup' (suc n) (suc (suc m)) ∣ a ∣ ∣ merid b i₁ ∣))
                        _ ((λ _ x → (sym (Kn→ΩKn+10ₖ _) ∙∙ (cong (Kn→ΩKn+1 _) x) ∙∙ Kn→ΩKn+10ₖ _)))
                        (+'-comm (suc (suc n)) (suc (suc (suc m))))
        ∙∙ cong (transport (λ i → refl {x = 0ₖ ((suc (+'-comm (suc (suc n)) (suc (suc (suc m))) i)))}
                        ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc (suc (suc m))) i))}))
                (sym (lem₁ _ _ b a))

    help : (cong (λ x → (cong (λ y → cup' (suc (suc n)) (suc (suc m)) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
         ≡ λ i j → -ₖ-gen (suc (suc (suc n))) (suc (suc (suc m))) (inr x) (inr y)
      (subst coHomK (+'-comm (suc (suc (suc m))) (suc (suc (suc n))))
       (cup' (suc (suc m)) (suc (suc n)) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
    help =
         ((sym (inst _ (λ i j →
         cup' (suc (suc n)) (suc (suc m)) ∣ merid a j ∣ ∣ merid b i ∣)))
        ∙ sym (final (suc n) (suc m) ((λ i j₁ →
              cup' (suc (suc n)) (suc (suc m)) ∣ merid a j₁ ∣ ∣ merid b (~ i) ∣))))
      ∙∙ cong (transport (λ i₁ → refl ≡ refl))
              ((cong (sym ∘ transport (λ i₂ → refl ≡ refl))
                     ((cong (transport (λ i₁ → refl ≡ refl))
                       (sym lem8)
                     ∙ sym lem₅) ∙
                     (cong (λ x → (sym (Kn→ΩKn+10ₖ (suc (suc (suc (suc (n + suc m)))))) ∙∙
                                    cong (Kn→ΩKn+1 (suc (suc (suc (suc (n + suc m)))))) x
                                    ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc (suc (n + suc m)))))))
                           (sym lem4)))
              ∙ sym (cong sym lem3))
              ∙∙ inst _ _
              ∙∙ sym (cong flipSquare (lem₁ (suc n) (suc m) a b)))
      ∙∙ sym (lem₈ (suc n) (suc m) (λ i j → cup' (suc (suc m)) (suc (suc n)) ∣ merid b i ∣ₕ ∣ merid a j ∣ₕ))
      ∙∙ sym (inst _ _)
      ∙∙ sym (lem₂ (cong (cong (subst coHomK (+'-comm (suc (suc (suc m))) (suc (suc (suc n))))))
             λ i j → cup' (suc (suc m)) (suc (suc n)) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))

  -}

  {-
  main : (n m : ℕ) (p : _) (q : _) (a : _) (b : _)
      → (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡ (-ₖ-gen (suc n) (suc m) p q) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ))
  main zero zero p q base base = refl
  main zero zero p q base (loop i) = refl
  main zero zero p q (loop i) base = refl
  main zero zero p q (loop i) (loop i₁) = {!!}
  main zero (suc m) p q base north = refl
  main zero (suc m) p q base south = refl
  main zero (suc m) p q base (merid a i) = refl
  main zero (suc m) p q (loop i) north = refl
  main zero (suc m) p q (loop i) south = refl
  main zero (suc m) p q (loop i) (merid a i₁) = {!!}
  main (suc n) zero p q north base = refl
  main (suc n) zero p q south base = refl
  main (suc n) zero p q (merid a i) base = refl
  main (suc n) zero p q north (loop i) = refl
  main (suc n) zero p q south (loop i) = refl
  main (suc n) zero p q (merid a i₁) (loop i) = {!!}
  main (suc n) (suc m) p q north north = refl
  main (suc n) (suc m) p q north south = refl
  main (suc n) (suc m) p q north (merid a i) = refl
  main (suc n) (suc m) p q south north = refl
  main (suc n) (suc m) p q south south = refl
  main (suc n) (suc m) p q south (merid a i) = refl
  main (suc n) (suc m) p q (merid a i) north = refl
  main (suc n) (suc m) p q (merid a i) south = refl
  main (suc n) (suc zero) p q (merid a i) (merid b j) = {!!}
  main (suc n) (suc (suc m)) p q (merid a i) (merid b j) = {!!}
    where
    natTranspLem : ∀ {A : ℕ → Type} (n m : ℕ) (a : A n) (B : (n : ℕ) → Type)
      (f : (n : ℕ) → (a : A n) → B n) (p : n ≡ m) 
      → f m (subst A p a) ≡ subst B p (f n a)
    natTranspLem {A = A} n m a B f = J (λ m p → f m (subst A p a) ≡ subst B p (f n a)) (cong (f n) (substRefl a) ∙ sym (substRefl (f n a)))


    lUnit₁ : (n m : ℕ) (a : _) → cup' (suc m) n ∣ north ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
    lUnit₁ zero m base = refl
    lUnit₁ zero m (loop i) = refl
    lUnit₁ (suc n) m north = refl
    lUnit₁ (suc n) m south = refl
    lUnit₁ (suc n) m (merid a i) = refl
    
    lUnit₂ : (n m : ℕ) (a : _) → cup' (suc m) n ∣ south ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
    lUnit₂ zero m base = refl
    lUnit₂ zero m (loop i) = refl
    lUnit₂ (suc n) m north = refl
    lUnit₂ (suc n) m south = refl
    lUnit₂ (suc n) m (merid a i) = refl

    transpi : (n m : ℕ) → _ → _
    transpi n m = transport (λ i → refl {x = 0ₖ (suc (suc (suc (+-comm n (suc (suc m)) (~ i)))))}
                                ≡ refl {x = 0ₖ (suc (suc (suc (+-comm n (suc (suc m)) (~ i)))))})

    symmer : {k : ℕ} (n m : ℕ) → is-even n ⊎ is-odd n → is-even m ⊎ is-odd m
                  → (p : Path (coHomK (suc k)) (0ₖ _) (0ₖ _)) → (Path (coHomK (suc k)) (0ₖ _) (0ₖ _))
    symmer n m (inl x) q P = P
    symmer n m (inr x) (inl x₁) P = P
    symmer n m (inr x) (inr x₁) P = sym P

    symmer≡ : {k : ℕ} (n m : ℕ) → (p : Path (coHomK (suc (suc k))) (0ₖ _) (0ₖ _))
      → symmer {k = (suc k)} n m (evenOrOdd n) (evenOrOdd m) p ≡ cong (-ₖ-gen n m (evenOrOdd n) (evenOrOdd m)) p
    symmer≡ = {!!}

    symmer-refl : {k : ℕ} (n m : ℕ) (P : _) (Q : _) → symmer n m P Q (refl {x = 0ₖ (2 + k)}) ≡ refl
    symmer-refl = {!!}

    Kn→ΩKn+1-symmer' : {k : ℕ} (n m : ℕ) → (x : coHomK (suc (suc k))) (P : _) (Q : _)
                      → (Kn→ΩKn+1 _) (-ₖ-gen n m P Q x) ≡ symmer n m P Q (Kn→ΩKn+1 _ x)
    Kn→ΩKn+1-symmer' = {!!}

    Kn→ΩKn+1-symmer : {k : ℕ} (n m : ℕ) → (p : Path (coHomK (suc (suc k))) (0ₖ _) (0ₖ _)) (P : _) (Q : _)
                    → (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (symmer n m P Q p) ∙∙ Kn→ΩKn+10ₖ _)
                    ≡ (sym (symmer-refl n m P Q) ∙∙ cong (symmer n m P Q) (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) p ∙∙ Kn→ΩKn+10ₖ _) ∙∙ symmer-refl n m P Q)
    Kn→ΩKn+1-symmer = {!!}


    lem₁ : (cong (λ x → (cong (λ y → cup' (suc n) (suc (suc m)) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
         ≡ sym (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (λ i → cup' n (suc (suc m)) ∣ a ∣ₕ ∣ merid b i ∣ₕ) ∙∙ Kn→ΩKn+10ₖ _)
    lem₁ =
        (λ k i j → ∣ (sym (rCancel _) ∙∙ cong (λ x → merid x ∙ sym (merid north)) (rUnit (λ i → pre-cup n (suc (suc m)) a (merid b i)) (~ k)) ∙∙ rCancel _) j i ∣ₕ)
      ∙∙ (λ k i j → hcomp (λ r → λ {(i = i0) → ∣ north ∣
                                  ; (i = i1) → ∣ north ∣
                                  ; (j = i0) → ∣ rCancel (merid north) r i ∣ₕ
                                  ; (j = i1) → ∣ rCancel (merid north) r i ∣ₕ
                                  ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
                                                   (cong (λ x → merid x ∙ sym (merid north)) ((λ i → pre-cup n (suc (suc m)) a (merid b i))))
                                                   (rCancel _) r j i ∣ₕ
                                  ; (k = i1) → doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 _) (λ i → cup' n (suc (suc m)) ∣ a ∣ₕ ∣ merid b i ∣ₕ)) (Kn→ΩKn+10ₖ _) r j i})
                         (Kn→ΩKn+1 _ (cup' n (suc (suc m)) ∣ a ∣ₕ ∣ merid b j ∣ₕ) i))

      ∙∙ sym (inst _ _)

    help-lem₁ : (n m : ℕ) (a : _) (b : _) → cong (cup' n (suc (suc m)) ∣ a ∣ₕ) (cong ∣_∣ₕ (merid b))
         ≡ transport (λ i → 0ₖ (suc (suc (+-comm n (suc (suc m)) (~ i)))) ≡ 0ₖ (suc (suc (+-comm n (suc (suc m)) (~ i)))))
           (cong (-ₖ-gen (suc n) (suc (2 + m)) (evenOrOdd (suc n))
                 (evenOrOdd (suc (suc (suc m)))))
           (((sym (lUnit₁ _ _ a) ∙∙ (λ i → (cup' (suc (suc m)) n ∣ merid b i ∣ₕ ∣ a ∣ₕ)) ∙∙ lUnit₂ _ (suc m) a))))
    help-lem₁ zero m a b = {!!}
      where
      help : (i : I) → cong (cup' zero (suc (suc m)) ∣ (loop i) ∣ₕ) (cong ∣_∣ₕ (merid b))
         ≡ transport (λ i → 0ₖ (suc (suc (+-comm zero (suc (suc m)) (~ i)))) ≡ 0ₖ (suc (suc (+-comm zero (suc (suc m)) (~ i)))))
           (cong (-ₖ-gen (suc zero) (suc (2 + m)) (evenOrOdd (suc zero))
                 (evenOrOdd (suc (suc (suc m)))))
           (((sym (lUnit₁ _ _ (loop i)) ∙∙ (λ i → (cup' (suc (suc m)) zero ∣ merid b i ∣ₕ ∣ (loop i) ∣ₕ)) ∙∙ lUnit₂ _ (suc m) (loop i)))))
      help i = {!!}

      mainLem : {!!}
      mainLem = {!!}
    help-lem₁ (suc n) m a b = {!!}
    {-
         rUnit _
      ∙∙ (λ k → (λ i → main n (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd (suc m)) a north (i ∧ k))
              ∙∙ (λ i → (main n (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd (suc m)) a (merid b i) k))
              ∙∙ λ i → main n (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd (suc m)) a south (~ i ∧ k))
      ∙∙ {!!}
      ∙∙ {!!}
      ∙∙ {!!} -}


    help-lem₂ :  (n m : ℕ) (a : _) (b : _) → (sym (Kn→ΩKn+10ₖ _)
                     ∙∙ cong (Kn→ΩKn+1 _)
                          (transport (λ i → 0ₖ (suc (suc (+-comm n (suc (suc m)) (~ i)))) ≡ 0ₖ (suc (suc (+-comm n (suc (suc m)) (~ i)))))
                           (cong (-ₖ-gen (suc n) (suc (2 + m)) (evenOrOdd (suc n)) (evenOrOdd (suc (suc (suc m)))))
                           (((sym (lUnit₁ _ _ a) ∙∙ (λ i → (cup' (suc (suc m)) n ∣ merid b i ∣ₕ ∣ a ∣ₕ)) ∙∙ lUnit₂ _ (suc m) a)))))
                     ∙∙ Kn→ΩKn+10ₖ _)
              ≡ transpi n m (sym (Kn→ΩKn+10ₖ _)
                     ∙∙ cong (Kn→ΩKn+1 _)
                           (cong (-ₖ-gen (suc n) (suc (2 + m)) (evenOrOdd (suc n)) (evenOrOdd (suc (suc (suc m)))))
                           (((sym (lUnit₁ _ _ a) ∙∙ (λ i → (cup' (suc (suc m)) n ∣ merid b i ∣ₕ ∣ a ∣ₕ)) ∙∙ lUnit₂ _ (suc m) a))))
                     ∙∙ Kn→ΩKn+10ₖ _)
    help-lem₂ n m a b = t
      where
      t = natTranspLem {A = λ n → 0ₖ ((suc (suc (n)))) ≡ 0ₖ ((suc (suc (n))))}
        (suc (suc (m + n))) (n + suc (suc m))
        ((cong (-ₖ-gen (suc n) (suc (2 + m)) (evenOrOdd (suc n)) (evenOrOdd (suc (suc (suc m)))))
                           (((sym (lUnit₁ _ _ a) ∙∙ (λ i → (cup' (suc (suc m)) n ∣ merid b i ∣ₕ ∣ a ∣ₕ)) ∙∙ lUnit₂ _ (suc m) a)))))
        (λ n → refl {x = 0ₖ (suc (suc (suc n)))} ≡ refl {x = 0ₖ (suc (suc (suc n)))})
        (λ n p → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) p ∙∙ Kn→ΩKn+10ₖ _)
        (sym (+-comm n (suc (suc m))))

    lem₂ : (n m : ℕ) (a : _) (b : _) → (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (λ i → cup' n (suc (suc m)) ∣ a ∣ₕ ∣ merid b i ∣ₕ) ∙∙ Kn→ΩKn+10ₖ _)
         ≡ transpi n m  (sym (symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                ∙∙ cong (symmer (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                        (sym (Kn→ΩKn+10ₖ _)
                      ∙∙ cong (Kn→ΩKn+1 _) (sym (lUnit₁ _ _ a)
                                         ∙∙ (λ i → (cup' (suc (suc m)) n ∣ merid b i ∣ₕ ∣ a ∣ₕ))
                                         ∙∙ lUnit₂ _ (suc m) a)
                      ∙∙ Kn→ΩKn+10ₖ _)
                ∙∙ symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
    lem₂ n m a b = (λ i → (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (help-lem₁ n m a b i) ∙∙ Kn→ΩKn+10ₖ _))
        ∙∙ (help-lem₂ n m a b)
        ∙∙ cong (transpi n m) (cong (sym (Kn→ΩKn+10ₖ (suc (suc (suc (suc (m + n)))))) ∙∙_∙∙ (Kn→ΩKn+10ₖ (suc (suc (suc (suc (m + n)))))))
                (cong (cong (Kn→ΩKn+1 (suc (suc (suc (suc (m + n)))))))
                  (sym (symmer≡ (suc n) (3 + m) (sym (lUnit₁ n (suc m) a) ∙∙
          (λ i₁ → cup' (suc (suc m)) n ∣ merid b i₁ ∣ₕ ∣ a ∣ₕ) ∙∙
          lUnit₂ n (suc m) a)))))
         ∙ cong (transpi n m) (Kn→ΩKn+1-symmer (suc n) (3 + m) ((sym (lUnit₁ n (suc m) a) ∙∙
          (λ i₁ → cup' (suc (suc m)) n ∣ merid b i₁ ∣ₕ ∣ a ∣ₕ) ∙∙
          lUnit₂ n (suc m) a)) (evenOrOdd (suc n)) (evenOrOdd (3 + m)) )


    help-lem₃ : (n m : ℕ) (a : _) (b : _) → ((sym (lUnit₁ _ _ a)
              ∙∙ (λ i → (cup' (suc (suc m)) n ∣ merid b i ∣ₕ ∣ a ∣ₕ))
              ∙∙ lUnit₂ _ (suc m) a))
              ≡ (Kn→ΩKn+1 _ (cup' (suc m) n ∣ b ∣ₕ ∣ a ∣ₕ))
    help-lem₃ n m a b = {!!}

    help-lem₄ : (n m : ℕ) (a : _) (b : _) → (sym (Kn→ΩKn+10ₖ _)
                      ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (cup' (suc m) n ∣ b ∣ₕ ∣ a ∣ₕ))
                      ∙∙ Kn→ΩKn+10ₖ _)
              ≡ (sym
       (symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       ∙∙
       cong
       (symmer (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       (sym (Kn→ΩKn+10ₖ (suc (suc (suc (suc (m + n)))))) ∙∙
        cong (Kn→ΩKn+1 (suc (suc (suc (suc (m + n))))))
        (Kn→ΩKn+1 (suc (suc (suc (m + n))))
         (subst coHomK (+'-comm (suc n) (suc (suc m)))
          (cup' n (suc m) ∣ a ∣ₕ ∣ b ∣ₕ)))
        ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc (suc (m + n))))))
       ∙∙
       symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
       (evenOrOdd (suc n)))
    help-lem₄ n m a b =
         (λ i → (sym (Kn→ΩKn+10ₖ _)
                      ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (((main (suc m) n (evenOrOdd m) (evenOrOdd (suc n)) b a)) i))
                      ∙∙ Kn→ΩKn+10ₖ _))
      ∙∙ ((λ i → (sym (Kn→ΩKn+10ₖ _)
                      ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1-symmer' _ _ ((subst coHomK (+'-comm (suc n) (suc (suc m)))
                                                                   (cup' n (suc m) ∣ a ∣ₕ ∣ b ∣ₕ)))
                                           (evenOrOdd (suc (suc m))) (evenOrOdd (suc n)) i)
                      ∙∙ Kn→ΩKn+10ₖ _)))
      ∙∙ Kn→ΩKn+1-symmer _ _ (Kn→ΩKn+1 _ (subst coHomK (+'-comm (suc n) (suc (suc m)))
                                                                   (cup' n (suc m) ∣ a ∣ₕ ∣ b ∣ₕ)))
                              (evenOrOdd (suc (suc m))) (evenOrOdd (suc n))


    lem₃ : (n m : ℕ) (a : _) (b : _)
      → transpi n m  (sym (symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                ∙∙ cong (symmer (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                        (sym (Kn→ΩKn+10ₖ _)
                      ∙∙ cong (Kn→ΩKn+1 _) (sym (lUnit₁ _ _ a)
                                         ∙∙ (λ i → (cup' (suc (suc m)) n ∣ merid b i ∣ₕ ∣ a ∣ₕ))
                                         ∙∙ lUnit₂ _ (suc m) a)
                      ∙∙ Kn→ΩKn+10ₖ _)
                ∙∙ symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
        ≡ transpi n m
           (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc n) (suc (suc m)) i)))}
                            ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc n) (suc (suc m)) i)))})
           (sym (symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                ∙∙ cong (symmer (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                        (sym
       (symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       ∙∙
       cong
       (symmer (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       (sym (Kn→ΩKn+10ₖ _) ∙∙
        cong (Kn→ΩKn+1 _)
        (Kn→ΩKn+1 _
         ((cup' n (suc m) ∣ a ∣ₕ ∣ b ∣ₕ)))
        ∙∙ Kn→ΩKn+10ₖ _)
       ∙∙
       symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
       (evenOrOdd (suc n)))
                ∙∙ symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m))))
    lem₃ n m a b =
         cong (λ x → transpi n m  (sym (symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                ∙∙ cong (symmer (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m))) x
                ∙∙ symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m))))
              (cong (λ x → sym (Kn→ΩKn+10ₖ (suc (suc (suc (suc (m + n)))))) ∙∙
          cong (Kn→ΩKn+1 (suc (suc (suc (suc (m + n)))))) x ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc (suc (m + n))))))
              (help-lem₃ n m a b)
        ∙ help-lem₄ n m a b)
      ∙∙ cong (transpi n m)
          (natTranspLem {A = λ n → coHomK n} _ _ (cup' n (suc m) ∣ a ∣ₕ ∣ b ∣ₕ)
            (λ _ → refl ≡ refl)
            (λ l a → (sym (symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                ∙∙ cong (symmer (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                        (sym
       (symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       ∙∙
       cong
       (symmer (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       (sym (Kn→ΩKn+10ₖ _) ∙∙
        cong (Kn→ΩKn+1 _)
        (Kn→ΩKn+1 _ a)
        ∙∙ Kn→ΩKn+10ₖ _)
       ∙∙
       symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
       (evenOrOdd (suc n)))
                ∙∙ symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m))))
            ((+'-comm (suc n) (suc (suc m)))))
      ∙∙ refl

    transpi2 : (n m : ℕ) → _ → _
    transpi2 n m = transpi n m
           ∘ (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc n) (suc (suc m)) i)))}
                            ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc n) (suc (suc m)) i)))}))

    transpi3 : (n m : ℕ) → _ → _
    transpi3 n m = transpi2 n m ∘
        (transport (λ i → refl {x = (0ₖ (suc (suc (suc (+-comm (suc m) (suc n) i)))))} ≡ refl
                                {x = 0ₖ (suc (suc (suc (+-comm (suc m) (suc n) i))))}))

    help-lem₅ : (n m : ℕ) (a : _) (b : _) →
        (Kn→ΩKn+1 _
         ((cup' n (suc m) ∣ a ∣ₕ ∣ b ∣ₕ))) ≡
         (sym (lUnit₁ _ _ b) ∙∙ (λ i → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ _ _ b)
    help-lem₅ = {!!}

    help-lem₆ : (n m : ℕ) (a : _) (b : _) → (sym (lUnit₁ _ _ b) ∙∙ (λ i → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ _ _ b)
                                           ≡ cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m) ∘ (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))
                                                  λ i → cup' (suc m) (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ
    help-lem₆ = {!!}

    help-lem₇ : (n m : ℕ) (p : 0ₖ _ ≡ 0ₖ _)
              → cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))) p
              ≡ transport (λ i → 0ₖ (suc (suc (+-comm (suc m) (suc n) i))) ≡ 0ₖ (suc (suc (+-comm (suc m) (suc n) i)))) p
    help-lem₇ = {!!}

    lem₄ : transpi2 n m
           (sym (symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                ∙∙ cong (symmer (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                        (sym
       (symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       ∙∙
       cong
       (symmer (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       (sym (Kn→ΩKn+10ₖ _) ∙∙
        cong (Kn→ΩKn+1 _)
        (Kn→ΩKn+1 _
         ((cup' n (suc m) ∣ a ∣ₕ ∣ b ∣ₕ)))
        ∙∙ Kn→ΩKn+10ₖ _)
       ∙∙
       symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
       (evenOrOdd (suc n)))
                ∙∙ symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
     ≡ transpi3 n m (
           (sym (symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                ∙∙ cong (symmer (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                        (sym
       (symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       ∙∙
       cong
       (symmer (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       (sym (Kn→ΩKn+10ₖ _) ∙∙
        cong (Kn→ΩKn+1 _)
        (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))
                                                  λ i → cup' (suc m) (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ)
        ∙∙ Kn→ΩKn+10ₖ _)
       ∙∙
       symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
       (evenOrOdd (suc n)))
                ∙∙ symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m))))
    lem₄ =
        cong (λ x → transpi2 n m
           (sym (symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                ∙∙ cong (symmer (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                        (sym
       (symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       ∙∙
       cong
       (symmer (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       (sym (Kn→ΩKn+10ₖ _) ∙∙
        cong (Kn→ΩKn+1 _)
        x
        ∙∙ Kn→ΩKn+10ₖ _)
       ∙∙
       symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
       (evenOrOdd (suc n)))
                ∙∙ symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m))))
              (help-lem₅ n m a b
              ∙∙ help-lem₆ n m a b
              ∙∙ cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)))
                      (help-lem₇ n m λ i → cup' (suc m) (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
     ∙∙ cong (transpi2 n m)
       (natTranspLem {A = λ n → 0ₖ (suc (suc n)) ≡ 0ₖ (suc (suc n))} _ _
         (cong (cup' (suc m) (suc n) ∣ b ∣ₕ) (cong ∣_∣ₕ (merid a)))
         _
         (λ l p → (sym (symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                ∙∙ cong (symmer (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                        (sym
       (symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       ∙∙
       cong
       (symmer (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       (sym (Kn→ΩKn+10ₖ _) ∙∙
        cong (Kn→ΩKn+1 _)
        (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))
                                                  p)
        ∙∙ Kn→ΩKn+10ₖ _)
       ∙∙
       symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
       (evenOrOdd (suc n)))
                ∙∙ symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m))))
         (+-comm (suc m) (suc n)))
     ∙∙ refl


    help-lem₈ : (n m : ℕ) (a : _) (b : _)
      → ((sym (Kn→ΩKn+10ₖ _) ∙∙
        cong (Kn→ΩKn+1 _)
        (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))
                                                  λ i → cup' (suc m) (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ)
        ∙∙ Kn→ΩKn+10ₖ _))
           ≡ (sym (symmer-refl (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)) ∙∙ cong (symmer (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)) ( 
              sym (Kn→ΩKn+10ₖ _) ∙∙
               cong (Kn→ΩKn+1 _)
              (λ i → cup' (suc m) (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ)
            ∙∙ Kn→ΩKn+10ₖ _)
           ∙∙ symmer-refl (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))
    help-lem₈ = {!!}


    help-lem₉ : ((sym (Kn→ΩKn+10ₖ _) ∙∙
               cong (Kn→ΩKn+1 _)
              (λ i → cup' (suc m) (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ)
            ∙∙ Kn→ΩKn+10ₖ _))
             ≡ λ i j → cup' (suc (suc m)) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ
    help-lem₉ =
      (λ k i j → hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) r j ∣ₕ
                                ; (i = i1) → ∣ rCancel (merid north) r j ∣ₕ
                                ; (j = i0) → ∣ north ∣
                                ; (j = i1) → ∣ north ∣
                                ; (k = i0) → doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _))
                                                (cong (Kn→ΩKn+1 _)
                                                      (λ i → cup' (suc m) (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
                                                (Kn→ΩKn+10ₖ _) r i j
                                ; (k = i1) → ∣ doubleCompPath-filler (sym (rCancel _))
                                                 (cong (λ x → merid x ∙ sym (merid north)) ((λ i → pre-cup _ _ b (merid a i))))
                                                 (rCancel _) r i j ∣ₕ })
                        ((Kn→ΩKn+1 _ (cup' (suc m) (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ)) j))
      ∙ λ k i j → ∣ (sym (rCancel _) ∙∙ (cong (λ x → merid x ∙ sym (merid north)) (rUnit (λ i → pre-cup _ _ b (merid a i)) k)) ∙∙ rCancel _) i j ∣ₕ

    lem₁₀ : transpi3 n m (
           (sym (symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                ∙∙ cong (symmer (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                        (sym
       (symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       ∙∙
       cong
       (symmer (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       (sym (Kn→ΩKn+10ₖ _) ∙∙
        cong (Kn→ΩKn+1 _)
        (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))
                                                  λ i → cup' (suc m) (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ)
        ∙∙ Kn→ΩKn+10ₖ _)
       ∙∙
       symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
       (evenOrOdd (suc n)))
                ∙∙ symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m))))
      ≡ transpi3 n m (
           (sym (symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                ∙∙ cong (symmer (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m))) -- (1 + m)(1 + n)
                        (sym
       (symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m))) 
        (evenOrOdd (suc n)))
       ∙∙
       cong
       (symmer (suc (suc m)) (suc n) (evenOrOdd (suc (suc m))) -- m(1 + n)
        (evenOrOdd (suc n)))
       (sym (symmer-refl (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))
       ∙∙ cong (symmer (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)) -- nm
               (λ i j → cup' (suc (suc m)) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)
       ∙∙ symmer-refl (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))
       ∙∙
       symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
       (evenOrOdd (suc n)))
                ∙∙ symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m))))
    lem₁₀ =
      cong
        (λ x → transpi3 n m (
           (sym (symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                ∙∙ cong (symmer (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))
                        (sym
       (symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n)))
       ∙∙
       cong
       (symmer (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
        (evenOrOdd (suc n))) x 
       ∙∙
       symmer-refl (suc (suc m)) (suc n) (evenOrOdd (suc (suc m)))
       (evenOrOdd (suc n)))
                ∙∙ symmer-refl (suc n) (suc (suc (suc m))) (evenOrOdd (suc n)) (evenOrOdd (3 + m)))))
        (help-lem₈ n m a b
       ∙ cong (λ x → sym (symmer-refl (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))
                   ∙∙ cong (symmer (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)) x
                   ∙∙ symmer-refl (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))
              help-lem₉) -}

{-
    hcomp (λ r → λ {(i = i0) → Kn→ΩKn+10ₖ _ (r ∨ k) j
                   ; (i = i1) → Kn→ΩKn+10ₖ _ (r ∨ k) j
                   ; (j = i0) → 0ₖ _
                   ; (j = i1) → 0ₖ _
                   ; (k = i0) → lem₂ (~ r) i j
                   ; (k = i1) → -ₖ-gen (suc (suc n)) (suc (suc m)) p q
                                         (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
                                          (cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))})
      (hcomp (λ r → λ {(i = i0) → {!!}
                   ; (i = i1) → {!compPath!}
                   ; (j = i0) → {!!}
                   ; (j = i1) → {!!}
                   ; (k = i0) → lem₃ (~ r) i j
                   ; (k = i1) → {!!}})
             {!hcomp (λ r → λ {(i = i0) → {!!}
                   ; (i = i1) → {!!}
                   ; (j = i0) → {!!}
                   ; (j = i1) → {!!}
                   ; (k = i0) → {!!}
                   ; (k = i1) → {!!}})!})
    where
    lUnit₁ : (n m : ℕ) (a : _) → cup' (suc m) n ∣ north ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
    lUnit₁ = {!i = i0 ⊢ main (suc n) (suc m) p q north (merid b j) k
i = i1 ⊢ main (suc n) (suc m) p q south (merid b j) k
j = i0 ⊢ main (suc n) (suc m) p q (merid a i) north k
j = i1 ⊢ main (suc n) (suc m) p q (merid a i) south k
k = i0 ⊢ cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ
k = i1 ⊢ -ₖ-gen (suc (suc n)) (suc (suc m)) p q
         (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
          (cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))!}

    lUnit₂ : (n m : ℕ) (a : _) → cup' (suc m) n ∣ south ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
    lUnit₂ = {!!}

    lem₁ : (cong (λ x → (cong (λ y → cup' (suc n) (suc m) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
         ≡ (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (λ i → cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ) ∙∙ Kn→ΩKn+10ₖ _)
    lem₁ = (λ k i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣)
        ∙∙ {!!}
        ∙∙ {!!}
        ∙∙ {!!}
        ∙∙ {!!}

    help-lem₂ : cong (λ x → cup' (suc m) n ∣ x ∣ₕ ∣ a ∣ₕ) (merid b)
             ≡ (lUnit₁ n m a ∙∙ Kn→ΩKn+1 _ (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ) ∙∙ sym (lUnit₂ n m a))
    help-lem₂ = {!!}

    help-lem₅ : Kn→ΩKn+1 _ (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡  (sym ((lUnit₁ m n b)) ∙∙ cong (λ x → cup' (suc n) m ∣ x ∣ₕ ∣ b ∣ₕ) (merid a) ∙∙ (lUnit₂ m n b))
    help-lem₅ = {!!}

    help-lem₄ : (n m : ℕ) (a : _) (b : _)
      → Kn→ΩKn+1 _ (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ)
       ≡ (sym (lUnit₁ m n b) ∙∙ (λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣) ∙∙ lUnit₂ m n b)
    help-lem₄ = {!!}

    help-lem₃ : (n : ℕ) (m : ℕ) (l : ℕ) (x : _) → Kn→ΩKn+1 (suc n) (-ₖ-gen m l (evenOrOdd m) (evenOrOdd l) x)
                                                   ≡ cong (-ₖ-gen m l (evenOrOdd m) (evenOrOdd l)) (Kn→ΩKn+1 (suc n) x)
    help-lem₃ = {!!}

    help-lem₆ : (n m l : ℕ) → (p : 0ₖ (suc (suc n)) ≡ 0ₖ (suc (suc n)))
              → cong (Kn→ΩKn+1 _) (cong (-ₖ-gen m l (evenOrOdd m) (evenOrOdd l)) p)
              ≡ {!!}
              ∙∙ cong (cong (-ₖ-gen m l (evenOrOdd m) (evenOrOdd l))) (cong (Kn→ΩKn+1 _) p)
              ∙∙ {!!}
    help-lem₆ = {!!}

    help-lem-₇ : (m l : ℕ) (p : 0ₖ (suc (suc l)) ≡ 0ₖ (suc (suc l)))
       → cong (Kn→ΩKn+1 (suc (suc l))) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                            (cong (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))
                                  (cong (-ₖ-gen (suc (suc n)) (suc m) (evenOrOdd n) (evenOrOdd (suc m)))
                                       p)))
         ≡ cong (Kn→ΩKn+1 (suc (suc l))) (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)) (sym p))
    help-lem-₇ = {!!}

    help-lem-₈ : (l : ℕ) (p : 0ₖ (suc (suc l)) ≡ 0ₖ (suc (suc l)))
       → cong (Kn→ΩKn+1 (suc (suc l))) (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)) (sym p))
        ≡ (Kn→ΩKn+10ₖ _
        ∙∙ cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))) (sym (Kn→ΩKn+10ₖ _)
              ∙∙ cong (Kn→ΩKn+1 (suc (suc l))) (sym p) ∙∙ Kn→ΩKn+10ₖ _)
        ∙∙ sym (Kn→ΩKn+10ₖ _))
    help-lem-₈ = {!!}

    

    help-lem-₉ :
        (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (cong (λ x → cup' m (suc n) ∣ b ∣ₕ ∣ x ∣ₕ) (sym (merid a))) ∙∙ Kn→ΩKn+10ₖ _)
      ≡ λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ
    help-lem-₉ = {!suc (suc (m + suc n))!}

    cpP : {!∀ {ℓ} {A : Type ℓ} {x y z w : A} → ? !}
    cpP = {!!}

    lem₁₁ :
      PathP (λ i → cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))
                         (λ j → transp (λ j → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (j ∧ i))) (~ i) (0ₖ _))
                  ≡ cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))
                         (λ j → transp (λ j → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (j ∧ i))) (~ i) (0ₖ _)))
      (cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)))
       (λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
      ((cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)))
       (cong (cong ((subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))) ((λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)))))

    lem₁₁ i i₁ k =
      -ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)
        (transp (λ j → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (j ∧ i))) (~ i)
          (cup' (suc m) (suc n) ∣ merid b k ∣ₕ ∣ merid a i₁ ∣ₕ))

    lem₁₀ :
      PathP (λ i → Kn→ΩKn+10ₖ (suc (suc (m + suc n))) i
                  ≡ Kn→ΩKn+10ₖ (suc (suc (m + suc n))) i)
      (cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                            (cong (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))
                                  (cong (-ₖ-gen (suc (suc n)) (suc m) (evenOrOdd n) (evenOrOdd (suc m)))
                                       λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))))
      (cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)))
       (λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
    lem₁₀ =
        help-lem-₇ _ _ (λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ) -- help-lem-₇ _ (λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ)
      ◁ (help-lem-₈ _ (λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ) -- help-lem-₈ _ (λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ)
      ◁ (symP (doubleCompPath-filler (Kn→ΩKn+10ₖ (suc (suc (m + suc n)))) (cong
              (cong
               (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)))
              (sym (Kn→ΩKn+10ₖ (suc (suc (m + suc n)))) ∙∙
               cong (Kn→ΩKn+1 (suc (suc (m + suc n))))
               (sym (λ i₁ → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i₁ ∣ₕ))
               ∙∙ Kn→ΩKn+10ₖ (suc (suc (m + suc n)))))
               (sym (Kn→ΩKn+10ₖ (suc (suc (m + suc n))))))
      ▷ (cong (cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m))))
              help-lem-₉
       ∙ refl)))

    lem₉ : PathP (λ i → Kn→ΩKn+1 (+'-comm (suc m) (suc (suc n)) (~ i))
                     ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                       (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))
                         (-ₖ-gen (suc (suc n)) (suc m) (evenOrOdd n) (evenOrOdd (suc m))
                           (transp (λ j → coHomK (+'-comm (suc m) (suc (suc n)) (~ i ∧ j))) i (0ₖ _)))))
                 ≡ Kn→ΩKn+1 (+'-comm (suc m) (suc (suc n)) (~ i))
                     ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                       (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))
                         (-ₖ-gen (suc (suc n)) (suc m) (evenOrOdd n) (evenOrOdd (suc m))
                           (transp (λ j → coHomK (+'-comm (suc m) (suc (suc n)) (~ i ∧ j))) i (0ₖ _))))))
       (cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                            (cong (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))
                                  (cong (-ₖ-gen (suc (suc n)) (suc m) (evenOrOdd n) (evenOrOdd (suc m))
                                       ∘ (subst coHomK (+'-comm (suc m) (suc (suc n)))))
                                       λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))))
       (cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                            (cong (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))
                                  (cong (-ₖ-gen (suc (suc n)) (suc m) (evenOrOdd n) (evenOrOdd (suc m)))
                                       λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))))
    lem₉ i k =
      Kn→ΩKn+1 (+'-comm (suc m) (suc (suc n)) (~ i))
        (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m)
          (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))
            (-ₖ-gen (suc (suc n)) (suc m) (evenOrOdd n) (evenOrOdd (suc m))
              (transp (λ j → coHomK (+'-comm (suc m) (suc (suc n)) (~ i ∧ j))) i (cup' m (suc n) ∣ b ∣ₕ ∣ merid a k ∣ₕ)))))

    lem₈ : 
      PathP (λ i → Kn→ΩKn+1 _
                     ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                       (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))
                         (main (suc n) m (evenOrOdd n) (evenOrOdd (suc m)) north b i)))
                 ≡ Kn→ΩKn+1 _
                     ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                       (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))
                         (main (suc n) m (evenOrOdd n) (evenOrOdd (suc m)) south b i))))
        (cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                            (cong (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))
                                  λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣)))
        ((cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                            (cong (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))
                                  (cong (-ₖ-gen (suc (suc n)) (suc m) (evenOrOdd n) (evenOrOdd (suc m))
                                       ∘ (subst coHomK (+'-comm (suc m) (suc (suc n)))))
                                       λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ)))))
    lem₈ i k = Kn→ΩKn+1 _
                     ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                       (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))
                         (main (suc n) m (evenOrOdd n) (evenOrOdd (suc m)) (merid a k) b i)))

    lem₇ :
      PathP (λ i → Kn→ΩKn+1 _
                     (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m)
                       (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))
                         (lUnit₁ m n b (~ i))))
                  ≡ Kn→ΩKn+1 _
                     (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m)
                       (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))
                         (lUnit₂ m n b (~ i)))))
        ((cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
              (Kn→ΩKn+1 _ (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)) (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ))))))
        (cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                            (cong (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))
                                  λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣)))
    lem₇ =
        cong (cong (Kn→ΩKn+1 _) ∘ (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))))
             (help-lem₃ _ _ _ (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ))
      ◁ (cong (cong (Kn→ΩKn+1 _) ∘ (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))))
             (cong (cong (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))))
               help-lem₅) {-  -}
      ◁ λ k i
        → Kn→ΩKn+1 _
                     (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m)
                       (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))
                         (doubleCompPath-filler (sym ((lUnit₁ m n b))) (cong (λ x → cup' (suc n) m ∣ x ∣ₕ ∣ b ∣ₕ) (merid a)) (lUnit₂ m n b) (~ k) i))))

    lem₆ :
      PathP (λ i → Kn→ΩKn+1 (suc (+'-comm (suc n) (suc m) (~ i))) (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m) (0ₖ _))
                  ≡ Kn→ΩKn+1 (suc (+'-comm (suc n) (suc m) (~ i)))  (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m) (0ₖ _)))
        (cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
              (Kn→ΩKn+1 _ (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ))))
        (cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
              (Kn→ΩKn+1 _ (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)) (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ)))))
    lem₆ =
        cong ((cong (Kn→ΩKn+1 _) ∘ (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m)))) ∘ Kn→ΩKn+1 _)
             (main m n (evenOrOdd (suc m)) (evenOrOdd (suc n)) b a)
      ◁ λ i → cong (Kn→ΩKn+1 (suc (+'-comm (suc n) (suc m) (~ i))))
                     ((cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                       (Kn→ΩKn+1 _
                         (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))
                           (transp (λ k → coHomK (+'-comm (suc n) (suc m) (~ i ∧ k))) i (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ))))))

    lem₅ : 
      PathP (λ i →
             (Kn→ΩKn+1 _) ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
               (lUnit₁ n m a i))
           ≡ (Kn→ΩKn+1 _) ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
               (lUnit₂ n m a i)))
        ((cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                            λ i → cup' (suc m) n ∣ merid b i ∣ₕ ∣ a ∣ₕ)))
        (cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
              (Kn→ΩKn+1 _ (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ))))

    lem₅ = cong (cong (Kn→ΩKn+1 (suc (suc (suc (m + n)))))
              ∘ (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))))
                 help-lem₂
         ◁ λ k i → (Kn→ΩKn+1 _)
                    ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                      (doubleCompPath-filler
                        (lUnit₁ n m a) (Kn→ΩKn+1 _ (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ)) (sym (lUnit₂ n m a)) (~ k) i))

    lem₄ :
      PathP (λ i → Kn→ΩKn+1 (+'-comm (suc (suc m)) (suc n) (~ i))
                      ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m) ∘
                                    transp (λ j → coHomK (+'-comm (suc (suc m)) (suc n) (~ i ∧ j))) i)
                                   (cup' (suc m) n ∣ north ∣ₕ ∣ a ∣ₕ))
                  ≡ Kn→ΩKn+1 (+'-comm (suc (suc m)) (suc n) (~ i))
                      ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m) ∘
                                    transp (λ j → coHomK (+'-comm (suc (suc m)) (suc n) (~ i ∧ j))) i)
                                   (cup' (suc m) n ∣ south ∣ₕ ∣ a ∣ₕ)))
        ((cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m) ∘
                                  (subst coHomK (+'-comm (suc (suc m)) (suc n))))
                                   (λ i → cup' (suc m) n ∣ merid b i ∣ₕ ∣ a ∣ₕ))))
        (cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m))
                            λ i → cup' (suc m) n ∣ merid b i ∣ₕ ∣ a ∣ₕ))
    lem₄ i k = Kn→ΩKn+1 (+'-comm (suc (suc m)) (suc n) (~ i))
                      ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m) ∘
                                    transp (λ j → coHomK (+'-comm (suc (suc m)) (suc n) (~ i ∧ j))) i)
                                   (cup' (suc m) n ∣ merid b k ∣ₕ ∣ a ∣ₕ))

    lem₃ :
      PathP (λ i → cong (Kn→ΩKn+1 _) (main n (suc m) (evenOrOdd (suc n)) (evenOrOdd m) a north) i
                  ≡ cong (Kn→ΩKn+1 _) (main n (suc m) (evenOrOdd (suc n)) (evenOrOdd m) a south) i)
        (cong (Kn→ΩKn+1 _) (λ i → cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ))
        (cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m) ∘
                                  (subst coHomK (+'-comm (suc (suc m)) (suc n))))
                                   (λ i → cup' (suc m) n ∣ merid b i ∣ₕ ∣ a ∣ₕ)))
    lem₃ k i = (Kn→ΩKn+1 _) (main n (suc m) (evenOrOdd (suc n)) (evenOrOdd m) a (merid b i) k)

    lem₂ : PathP (λ i → Kn→ΩKn+10ₖ (suc (suc (n + suc m))) (~ i) ≡ Kn→ΩKn+10ₖ _ (~ i))
      (cong (λ x → (cong (λ y → cup' (suc n) (suc m) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
      (cong (Kn→ΩKn+1 _) (λ i → cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ))
    lem₂ = lem₁ ◁ λ k i j → doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _))
                                                (cong (Kn→ΩKn+1 _) (λ i → cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ))
                                                (Kn→ΩKn+10ₖ _) (~ k) i j

    pathP-lem : {!!}
    pathP-lem = {!!}

    sick : (cong (λ x → (cong (λ y → cup' (suc n) (suc m) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a)) ≡ {!!}
    sick =
         PathP→compPathR lem₂
      ∙∙ (λ i → sym (Kn→ΩKn+10ₖ (suc (suc (n + suc m)))) ∙ PathP→compPathR lem₃ i ∙ Kn→ΩKn+10ₖ (suc (suc (n + suc m)))) 
      ∙∙ (λ i → sym (Kn→ΩKn+10ₖ _) ∙ ((cong (Kn→ΩKn+1 _) (main n (suc m) (evenOrOdd (suc n)) (evenOrOdd m) a north))
                                    ∙ {!PathP→compPathR !}
                                    ∙ sym (cong (Kn→ΩKn+1 _) (main n (suc m) (evenOrOdd (suc n)) (evenOrOdd m) a south))) ∙ Kn→ΩKn+10ₖ _)
      ∙∙ {!!}
      ∙∙ {!!}
      ∙∙ {!!}
      ∙∙ {!(λ i → ((λ i → Kn→ΩKn+10ₖ (suc (suc (n + suc m))) (~ i) ≡ Kn→ΩKn+10ₖ (suc (suc (n + suc m))) (~ i))
                   ∙ (λ i → cong (Kn→ΩKn+1 (suc (suc (n + suc m))))
                                  (main n (suc m) (evenOrOdd (suc n)) (evenOrOdd m) a north) i
                             ≡
                             cong (Kn→ΩKn+1 (suc (suc (n + suc m))))
                             (main n (suc m) (evenOrOdd (suc n)) (evenOrOdd m) a south) i)
                   ∙ (λ i → Kn→ΩKn+1 (+'-comm (suc (suc m)) (suc n) (~ i))
                      ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m) ∘
                                    transp (λ j → coHomK (+'-comm (suc (suc m)) (suc n) (~ i ∧ j))) i)
                                   (cup' (suc m) n ∣ north ∣ₕ ∣ a ∣ₕ))
                     ≡ Kn→ΩKn+1 (+'-comm (suc (suc m)) (suc n) (~ i))
                         ((-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m) ∘
                                       transp (λ j → coHomK (+'-comm (suc (suc m)) (suc n) (~ i ∧ j))) i)
                                      (cup' (suc m) n ∣ south ∣ₕ ∣ a ∣ₕ)))
                   ∙ (λ i₁ → Kn→ΩKn+1 (suc (suc (suc (m + n))))
                               (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m)
                                (lUnit₁ n m a i₁))
                               ≡
                               Kn→ΩKn+1 (suc (suc (suc (m + n))))
                               (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m)
                                (lUnit₂ n m a i₁)))
                   ∙ ((λ i₂ →
                         Kn→ΩKn+1 (suc (+'-comm (suc n) (suc m) (~ i₂)))
                         (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m)
                          (0ₖ (suc (+'-comm (suc n) (suc m) (~ i₂)))))
                         ≡
                         Kn→ΩKn+1 (suc (+'-comm (suc n) (suc m) (~ i₂)))
                         (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m)
                          (0ₖ (suc (+'-comm (suc n) (suc m) (~ i₂)))))))
                   ∙ (λ i → Kn→ΩKn+1 _
                             (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m)
                               (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))
                                 (lUnit₁ m n b (~ i))))
                            ≡ Kn→ΩKn+1 _
                               (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) (evenOrOdd m)
                                 (-ₖ-gen (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n))
                                   (lUnit₂ m n b (~ i)))))
                   ∙ {!!}
                   ∙ {!!}
                   ∙ {!!}) i)!}


    totalPathL :
       PathP _
             (cong (λ x → (cong (λ y → cup' (suc n) (suc m) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
       ((cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd n) (evenOrOdd m)))
       (cong (cong ((subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))) ((λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)))))
    totalPathL =
      {!compPathP lem₂
       (compPathP lem₃
        (compPathP lem₄
          (compPathP lem₅
            (compPathP lem₆
              (compPathP lem₇
               (compPathP lem₈
                (compPathP lem₉
                 (compPathP lem₁₀
                  lem₁₁))))))))!} -}


--   main : (n m : ℕ) (p : _) (q : _) (a : _) (b : _)
--       → (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡ (-ₖ-gen (suc n) (suc m) p q) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ))
--   main zero zero p q a b = {!!}
--   main zero (suc m) p q base north = refl
--   main zero (suc m) p q base south = refl
--   main zero (suc m) p q base (merid a i) = refl
--   main zero (suc m) p q (loop i) north = refl
--   main zero (suc m) p q (loop i) south = refl
--   main zero (suc m) p q (loop i) (merid a i₁) = {!!}
--   main (suc n) zero p q a b = {!!}
--   main (suc n) (suc m) p q north north = refl
--   main (suc n) (suc m) p q north south = refl
--   main (suc n) (suc m) p q north (merid a i) = refl
--   main (suc n) (suc m) p q south north = refl
--   main (suc n) (suc m) p q south south = refl
--   main (suc n) (suc m) p q south (merid a i) = refl
--   main (suc n) (suc m) p q (merid a i) north = refl
--   main (suc n) (suc m) p q (merid a i) south = refl
--   main (suc n) (suc zero) (inl x) (inl y) (merid a i) (merid b j) k = {!y!}
--     where
--     b' : I → _
--     b' i = loop i

    

--   main (suc zero) (suc (suc m)) (inl x) (inl y) (merid a i) (merid b j) k = {!!}
--   main (suc (suc n)) (suc (suc m)) (inl x) (inl y) (merid a i) (merid b j) k = {!!}
  
--     where
--     lem₁ : (a : _) (b : _) → cong (cong ∣_∣ₕ) ((cong (λ x → merid x ∙ sym (merid north))
--                                            (cong (pre-cup zero (suc (suc n)) b) (merid a))))
--         ≡ (cong (Kn→ΩKn+1 _) ((cong ∣_∣ₕ) (cong (pre-cup zero (suc (suc n)) b) (merid a))))
--     lem₁ a = {!!}

--     lem₂ : (i : I) (n : ℕ) (a : _)
--       → cong (λ x → cup' (suc (suc n)) zero ∣ x ∣ₕ ∣ loop i ∣ₕ) (merid a)
--       ≡ Kn→ΩKn+1 _ (cup' (suc n) zero ∣ a ∣ₕ ∣ loop i ∣ₕ)
--     lem₂ i n a = {!!}

--     F : (p : Kn→ΩKn+1 (suc (suc (suc (suc n)))) (0ₖ _) ≡ Kn→ΩKn+1 (suc (suc (suc (suc n)))) (0ₖ _)) → refl ≡ refl
--     F p = cong (cong ∣_∣ₕ) (sym (rCancel (merid north))) ∙∙ p ∙∙ cong (cong ∣_∣ₕ) (rCancel (merid north))

--     Kn-transp : (n m : ℕ) (x : _) (p : m ≡ n)
--       → Kn→ΩKn+1 n (subst coHomK p x) ≡ transport (λ i → snd (coHomK-ptd (suc (p i))) ≡ snd (coHomK-ptd (suc (p i)))) (Kn→ΩKn+1 m x)
--     Kn-transp n m x = {!J ? ?!}

--     lem₅ : (m : ℕ) (a : _) (i : I) (j : I) → cong (λ x → cup' 1 (suc m) ∣ x ∣ₕ ∣ merid a j ∣ₕ) (merid (loop i)) ≡ Kn→ΩKn+1 _ (cup' zero (suc m) ∣ loop i ∣ₕ ∣ merid a j ∣ₕ)
--     lem₅ = {!!}

--     lem₆ : (n : ℕ) → (P : 0ₖ _ ≡ 0ₖ _) → (cong (Kn→ΩKn+1 (suc (suc (suc (suc n)))) ∘ subst coHomK (+'-comm (suc (suc (suc n))) 1)))
--                               (sym ((transport (λ i₂ → 0ₖ (suc (+'-comm 1 (suc (suc n)) i₂)) ≡ 0ₖ (suc (+'-comm 1 (suc (suc n)) i₂))))
--                                 P)) ≡ cong (Kn→ΩKn+1 (suc (suc (suc (suc n))))) P
--     lem₆ n m P = {!!}

--     help1 : (i j : I) (a : _) → cong (λ x → cong (λ y → (cup' (suc zero) (suc (suc n)) ∣ y ∣ₕ ∣ x ∣ₕ)) (merid (loop i))) (merid (merid a j))
--           ≡ {!!}
--     help1 i j a = (λ k i j → ∣ (sym (rCancel (merid north))
--                    ∙∙ cong (λ x → merid x ∙ sym (merid north)) (rUnit (cong (pre-cup zero (suc (suc n)) b') (merid a')) (~ k))
--                    ∙∙ rCancel (merid north)) i j ∣ₕ)
--             ∙∙ (λ k i j → cong-∙∙ (cong ∣_∣ₕ) (sym (rCancel (merid north))) (cong (λ x → merid x ∙ sym (merid north))
--                              (cong (pre-cup zero (suc (suc n)) b') (merid a')) ) (rCancel (merid north)) k i j)
--             ∙∙ cong F (lem₁ a' b'
--                     ∙∙ cong (cong (Kn→ΩKn+1 (suc (suc (suc (suc n))))))
--                             ((λ k i → main zero (suc (suc n)) (inr tt) (inl x) b' (merid a' i) k)
--                          ∙∙ (λ k i → -ₖ-gen-inl-right 1 (suc (suc (suc n))) (inr tt) x
--                                        (subst coHomK (+'-comm (suc (suc (suc n))) 1)
--                                         (cup' (suc (suc n)) zero ∣ merid a' i ∣ₕ ∣ b' ∣ₕ)) k) 
--                          ∙∙ cong (cong (subst coHomK (+'-comm (suc (suc (suc n))) 1)))
--                             λ k j → lem₂ i n a' k j)
--                     ∙∙ cong (cong (Kn→ΩKn+1 (suc (suc (suc (suc n)))) ∘ subst coHomK (+'-comm (suc (suc (suc n))) 1)))
--                               (cong (Kn→ΩKn+1 _) (main (suc n) zero (inr (is-odd-suc _ x)) (inr tt) a' b')
--                             ∙∙ Kn→ΩKn+1-ₖ' _ _ (is-odd-suc _ x) tt ((subst coHomK (+'-comm 1 (suc (suc n))) (cup' zero (suc n) ∣ b' ∣ ∣ a' ∣)))
--                             ∙∙ cong sym (Kn-transp _ _ (cup' zero (suc n) ∣ b' ∣ ∣ a' ∣) (+'-comm 1 (suc (suc n)))))
--                     ∙∙ cong (cong (Kn→ΩKn+1 (suc (suc (suc (suc n)))) ∘ subst coHomK (+'-comm (suc (suc (suc n))) 1)))
--                             (cong sym ((cong (transport (λ i₂ → 0ₖ (suc (+'-comm 1 (suc (suc n)) i₂)) ≡ 0ₖ (suc (+'-comm 1 (suc (suc n)) i₂)))))
--                                            (sym (lem₅ _ a i j)))
--                           ∙∙ cong sym (cong (transport (λ i₂ → 0ₖ (suc (+'-comm 1 (suc (suc n)) i₂)) ≡ 0ₖ (suc (+'-comm 1 (suc (suc n)) i₂))))
--                                            λ k i → main 1 (suc n) (inl tt) (inr (is-odd-suc _ x)) (merid b' i) a' k)
--                           ∙∙ cong sym (cong (transport (λ i₂ → 0ₖ (suc (+'-comm 1 (suc (suc n)) i₂)) ≡ 0ₖ (suc (+'-comm 1 (suc (suc n)) i₂))))
--                                            (λ k i → -ₖ-gen-inl-left (suc 1) (suc (suc n)) tt (inr (is-odd-suc (suc n) x))
--                                              (subst coHomK (+'-comm (suc (suc n)) (suc 1))
--                                               (cup' (suc n) 1 ∣ a' ∣ₕ ∣ merid b' i ∣ₕ)) k)))
--                     ∙∙ lem₆ n (λ i → subst coHomK (+'-comm (suc (suc n)) (suc 1))
--                                               (cup' (suc n) 1 ∣ a' ∣ₕ ∣ merid b' i ∣ₕ)))
--               {-
--                    ∙∙ cong ((cong (Kn→ΩKn+1 _ ∘ (subst coHomK (+'-comm (suc (suc (suc n))) 1)))))
--                             (cong sym (cong (transport (λ i → 0ₖ (suc (+'-comm 1 (suc (suc n)) i)) ≡ 0ₖ (suc (+'-comm 1 (suc (suc n)) i))))
--                                       λ k j → main zero (suc (suc n)) (inr tt) (inl x) b' (merid a j) k))
--                    ∙∙ cong ((cong (Kn→ΩKn+1 _ ∘ (subst coHomK (+'-comm (suc (suc (suc n))) 1)))))
--                             (cong sym (cong (transport (λ i → 0ₖ (suc (+'-comm 1 (suc (suc n)) i)) ≡ 0ₖ (suc (+'-comm 1 (suc (suc n)) i))))
--                                       λ k j → -ₖ-gen-inl-right 1 (suc (suc (suc n))) (inr tt) x
--                                                   (subst coHomK (+'-comm (suc (suc (suc n))) 1)
--                                                   (cup' (suc (suc n)) zero ∣ merid a j ∣ₕ ∣ b' ∣ₕ)) k))
--                    ∙∙ {!cong ((cong (Kn→ΩKn+1 _ ∘ (subst coHomK (+'-comm (suc (suc (suc n))) 1)))))
--                             (cong sym (cong (transport (λ i → 0ₖ (suc (+'-comm 1 (suc (suc n)) i)) ≡ 0ₖ (suc (+'-comm 1 (suc (suc n)) i))))
--                                       λ k j → -ₖ-gen-inl-right 1 (suc (suc (suc n))) (inr tt) x
--                                                   (subst coHomK (+'-comm (suc (suc (suc n))) 1)
--                                                   (cup' (suc (suc n)) zero ∣ merid a j ∣ₕ ∣ b' ∣ₕ)) k))!} -}
--                    ∙∙ cong F ({!!}
--                              ∙∙ {!lem₆ n (λ i → subst coHomK (+'-comm (suc (suc n)) (suc 1))
--                                               (cup' (suc n) 1 ∣ a' ∣ₕ ∣ merid b' i ∣ₕ))!}
--                              ∙∙ {!+'-comm (suc (suc n)) (suc 1)!})
--                    ∙∙ {!!}
--              ∙ {!0ₖ (suc (+'-comm 1 (suc (suc n)) i))!}
--     {-
--     (λ k i j → cup' (suc zero) (suc (suc n)) ∣ merid b' j ∣ₕ ∣ merid a i ∣ₕ)
--            ∙∙ (λ k i j → ∣ (sym (rCancel (merid north))
--                    ∙∙ cong (λ x → merid x ∙ sym (merid north)) (rUnit (cong (pre-cup zero (suc (suc n)) b') (merid a)) (~ k))
--                    ∙∙ rCancel (merid north)) i j ∣ₕ)
--            ∙∙ (λ k i j → cong-∙∙ (cong ∣_∣ₕ) (sym (rCancel (merid north))) (cong (λ x → merid x ∙ sym (merid north))
--                              (cong (pre-cup zero (suc (suc n)) b') (merid a)) ) (rCancel (merid north)) k i j)
--            ∙∙ cong F (lem₁ b'
--                    ∙∙ (λ k i → Kn→ΩKn+1 _ (main zero (suc (suc n)) (inr tt) (inl x) b' (merid a i) k))
--                    ∙∙ ?
--                    ∙∙ cong (cong (Kn→ΩKn+1 _ ∘ (subst coHomK (+'-comm (suc (suc n)) 1)))) (lem₂ i n a)
--                    ∙∙ cong (cong (Kn→ΩKn+1 _ ∘ (subst coHomK (+'-comm (suc (suc n)) 1)))) {!cong (Kn→ΩKn+1 _) (!}
--                    ∙∙ {!!}
--                    ∙∙ {!!})
--            ∙∙ {!!} -}
--     {-
--          (λ k i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)
--       ∙∙ (λ k i j → ∣ (sym (rCancel (merid north))
--                    ∙∙ cong (λ x → merid x ∙ sym (merid north)) (rUnit (cong (pre-cup m (suc n) b) (merid a)) (~ k))
--                    ∙∙ rCancel (merid north)) i j ∣ₕ)
--       ∙∙ (λ k i j → cong-∙∙ (cong ∣_∣ₕ) (sym (rCancel (merid north))) (cong (λ x → merid x ∙ sym (merid north))
--                              (cong (pre-cup m (suc n) b) (merid a)) ) (rCancel (merid north)) k i j)
--       ∙∙ (λ k → cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
--               ∙∙ (lem₁ ∙ cong (cong (Kn→ΩKn+1 (suc (suc (m + suc n)))))
--                          (rUnit (λ i → cup' m (suc n) ∣ b ∣ₕ (∣ merid a i ∣ₕ))
--                        ∙ λ k → ((λ i → main m (suc n) (inr (is-odd-suc m y)) (inl x) b north (i ∧ k)))
--                              ∙∙ (λ i → main m (suc n) (inr (is-odd-suc m y)) (inl x) b (merid a i) k)
--                              ∙∙ λ i → main m (suc n) (inr (is-odd-suc m y)) (inl x) b south (~ i ∧ k))) k
--               ∙∙ cong (cong ∣_∣ₕ) (rCancel (merid north)))
--       ∙∙ (λ k → cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
--               ∙∙ cong (Kn→ΩKn+1 _) (pp-help1 m n x y b k
--                                   ∙∙ (λ i → -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr (is-odd-suc m y)) x
--                                               (subst coHomK (+'-comm (suc (suc n)) (suc m))
--                                               (cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) k)
--                                   ∙∙ sym (pp-help2 m n x y b k))
--               ∙∙ cong (cong ∣_∣ₕ) (rCancel (merid north)))
--               -}
--      where
--      b' = loop i
--      a' = merid a j

--     {-
--     lem₁ : cong (cong ∣_∣ₕ) ((cong (λ x → merid x ∙ sym (merid north))
--                                            (cong (pre-cup m (suc n) b) (merid a))))
--         ≡ (cong (Kn→ΩKn+1 _) ((cong ∣_∣ₕ) (cong (pre-cup m (suc n) b) (merid a))))
--     lem₁ = {!!}

--     lUnit' : (n m : ℕ) (b : _) → subst coHomK (+'-comm (suc (suc n)) (suc m)) (cup' (suc n) m ∣ north ∣ₕ ∣ b ∣ₕ) ≡ 0ₖ _
--     lUnit' n zero base = refl
--     lUnit' n zero (loop i) = refl
--     lUnit' n (suc m) north = refl
--     lUnit' n (suc m) south = refl
--     lUnit' n (suc m) (merid a i) = refl

--     lUnit'' : (n m : ℕ) (b : _) → subst coHomK (+'-comm (suc (suc n)) (suc m)) (cup' (suc n) m ∣ south ∣ₕ ∣ b ∣ₕ) ≡ 0ₖ _
--     lUnit'' n zero base = refl
--     lUnit'' n zero (loop i) = refl
--     lUnit'' n (suc m) north = refl
--     lUnit'' n (suc m) south = refl
--     lUnit'' n (suc m) (merid a i) = refl

--     lUnit₂ : (n m : ℕ) (b : _) → (cup' (suc n) m ∣ north ∣ₕ ∣ b ∣ₕ) ≡ 0ₖ _
--     lUnit₂ = {!!}

--     lUnit₃ : (n m : ℕ) (b : _) → (cup' (suc n) m ∣ south ∣ₕ ∣ b ∣ₕ) ≡ 0ₖ _
--     lUnit₃ = {!!}

--     lem₄ : (n m : ℕ) (a : _) (b : _) → cong (λ x → cup' (suc n) m ∣ x ∣ₕ ∣ b ∣ₕ) (merid a) ≡ (lUnit₂ n m b ∙∙ Kn→ΩKn+1 _ (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ∙∙ sym (lUnit₃ n m b))
--     lem₄ = {!!}

--     lem₅ : (n m : ℕ) (a : _) (b : _) → (sym (lUnit₂ n m b) ∙∙ cong (λ x → cup' (suc n) m ∣ x ∣ₕ ∣ b ∣ₕ) (merid a) ∙∙ lUnit₃ n m b) ≡ Kn→ΩKn+1 _ (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ)
--     lem₅ = {!!}

--     pp-help1 : (m n : ℕ) (x : _) (y : _) (b : _)
--       → PathP (λ i → 0ₖ _ ≡ -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr (is-odd-suc m y)) x
--                (subst coHomK (+'-comm (suc (suc n)) (suc m))
--                  (cup' (suc n) m ∣ north ∣ₕ ∣ b ∣ₕ)) i) (main m (suc n) (inr (is-odd-suc m y)) (inl x) b north)
--                (sym (lUnit' n m b))
--     pp-help1 m n x y b = {!m!}

--     pp-help2 : (m n : ℕ) (x : _) (y : _) (b : _)
--       → PathP (λ i → 0ₖ _ ≡ -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr (is-odd-suc m y)) x
--                (subst coHomK (+'-comm (suc (suc n)) (suc m))
--                  (cup' (suc n) m ∣ south ∣ₕ ∣ b ∣ₕ)) i) (main m (suc n) (inr (is-odd-suc m y)) (inl x) b south)
--                (sym (lUnit'' n m b))
--     pp-help2 m n x y b = {!m!}

--     Kn-transp : (n m : ℕ) (x : _) (p : m ≡ n)
--       → Kn→ΩKn+1 n (subst coHomK p x) ≡ transport (λ i → snd (coHomK-ptd (suc (p i))) ≡ snd (coHomK-ptd (suc (p i)))) (Kn→ΩKn+1 m x)
--     Kn-transp n m x p = {!!}


--     help1 : cong (λ x → cong (λ y → (cup' (suc m) (suc n) ∣ y ∣ₕ ∣ x ∣ₕ)) (merid b)) (merid a)
--           ≡ {!!}
--     help1 =
--          (λ k i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)
--       ∙∙ (λ k i j → ∣ (sym (rCancel (merid north))
--                    ∙∙ cong (λ x → merid x ∙ sym (merid north)) (rUnit (cong (pre-cup m (suc n) b) (merid a)) (~ k))
--                    ∙∙ rCancel (merid north)) i j ∣ₕ)
--       ∙∙ (λ k i j → cong-∙∙ (cong ∣_∣ₕ) (sym (rCancel (merid north))) (cong (λ x → merid x ∙ sym (merid north))
--                              (cong (pre-cup m (suc n) b) (merid a)) ) (rCancel (merid north)) k i j)
--       ∙∙ (λ k → cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
--               ∙∙ (lem₁ ∙ cong (cong (Kn→ΩKn+1 (suc (suc (m + suc n)))))
--                          (rUnit (λ i → cup' m (suc n) ∣ b ∣ₕ (∣ merid a i ∣ₕ))
--                        ∙ λ k → ((λ i → main m (suc n) (inr (is-odd-suc m y)) (inl x) b north (i ∧ k)))
--                              ∙∙ (λ i → main m (suc n) (inr (is-odd-suc m y)) (inl x) b (merid a i) k)
--                              ∙∙ λ i → main m (suc n) (inr (is-odd-suc m y)) (inl x) b south (~ i ∧ k))) k
--               ∙∙ cong (cong ∣_∣ₕ) (rCancel (merid north)))
--       ∙∙ (λ k → cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
--               ∙∙ cong (Kn→ΩKn+1 _) (pp-help1 m n x y b k
--                                   ∙∙ (λ i → -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr (is-odd-suc m y)) x
--                                               (subst coHomK (+'-comm (suc (suc n)) (suc m))
--                                               (cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) k)
--                                   ∙∙ sym (pp-help2 m n x y b k))
--               ∙∙ cong (cong ∣_∣ₕ) (rCancel (merid north)))
--       ∙∙ (λ k → cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
--               ∙∙ cong (Kn→ΩKn+1 _) ((sym (lUnit' n m b)) ∙∙
--                    (cong ((subst coHomK (+'-comm (suc (suc n)) (suc m)))))
--                      (lem₄ n m a b k)
--                    ∙∙ (lUnit'' n m b))
--               ∙∙ cong (cong ∣_∣ₕ) (rCancel (merid north)))
--       ∙∙ (λ k → cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
--               ∙∙ cong (Kn→ΩKn+1 _) ((sym (lUnit' n m b)) ∙∙
--                    (cong ((subst coHomK (+'-comm (suc (suc n)) (suc m)))))
--                        (lUnit₂ n m b
--                      ∙∙ Kn→ΩKn+1 (suc (suc (n + m))) (main n m (inr (is-odd-suc _ x)) (inr (is-odd-suc _ y)) a b k)
--                      ∙∙ sym (lUnit₃ n m b))
--                    ∙∙ (lUnit'' n m b))
--               ∙∙ cong (cong ∣_∣ₕ) (rCancel (merid north)))
--       ∙∙ (λ k → cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
--               ∙∙ cong (Kn→ΩKn+1 _) ((sym (lUnit' n m b)) ∙∙
--                    (cong ((subst coHomK (+'-comm (suc (suc n)) (suc m)))))
--                        (lUnit₂ n m b
--                      ∙∙ Kn→ΩKn+1-ₖ' (suc n) (suc m) (is-odd-suc _ x) (is-odd-suc _ y) ((subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ ∣ a ∣))) k
--                      ∙∙ sym (lUnit₃ n m b))
--                    ∙∙ (lUnit'' n m b))
--               ∙∙ cong (cong ∣_∣ₕ) (rCancel (merid north)))
--       ∙∙ (λ k → cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
--               ∙∙ cong (Kn→ΩKn+1 _) ((sym (lUnit' n m b)) ∙∙
--                    (cong ((subst coHomK (+'-comm (suc (suc n)) (suc m)))))
--                        (lUnit₂ n m b
--                      ∙∙ sym (Kn-transp _ _ (cup' m n ∣ b ∣ ∣ a ∣) (+'-comm (suc m) (suc n)) k)
--                      ∙∙ sym (lUnit₃ n m b))
--                    ∙∙ (lUnit'' n m b))
--               ∙∙ cong (cong ∣_∣ₕ) (rCancel (merid north)))
--       ∙∙ (λ k → cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
--               ∙∙ cong (Kn→ΩKn+1 _) ((sym (lUnit' n m b)) ∙∙
--                    (cong ((subst coHomK (+'-comm (suc (suc n)) (suc m)))))
--                        (lUnit₂ n m b
--                      ∙∙ sym (transport (λ i → 0ₖ (suc (+'-comm (suc m) (suc n) i)) ≡ 0ₖ (suc (+'-comm (suc m) (suc n) i)))
--                               (sym (lem₅ m n b a) k))
--                      ∙∙ sym (lUnit₃ n m b))
--                    ∙∙ (lUnit'' n m b))
--               ∙∙ cong (cong ∣_∣ₕ) (rCancel (merid north)))
--       ∙∙ (λ k → cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
--               ∙∙ cong (Kn→ΩKn+1 _) ((sym (lUnit' n m b)) ∙∙
--                    (cong ((subst coHomK (+'-comm (suc (suc n)) (suc m)))))
--                        (lUnit₂ n m b
--                      ∙∙ sym (transport (λ i → 0ₖ (suc (+'-comm (suc m) (suc n) i)) ≡ 0ₖ (suc (+'-comm (suc m) (suc n) i)))
--                               ({!!}
--                             ∙∙ rUnit {!!} k
--                             ∙∙ {!lUnit₃ n m b!}))
--                      ∙∙ sym (lUnit₃ n m b))
--                    ∙∙ (lUnit'' n m b))
--               ∙∙ cong (cong ∣_∣ₕ) (rCancel (merid north)))
--       ∙∙ {!(sym (lUnit₂ m n a) ∙∙
--                                cong (λ x₁ → cup' (suc m) n ∣ x₁ ∣ ∣ a ∣) (merid b) ∙∙
--                                lUnit₃ m n a)!}
--       ∙∙ {!(λ i → main (suc m) n (inl y) (inr (is-odd-suc _ x)) (merid b i) a k)!}

--     help : (λ i j → cup' (suc n) (suc m)  ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)
--       ≡ cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) (inl x) (inl y) ∘
--               (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))))
--                (λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)
--     help =
--          {!!}
--       ∙∙ {!!}
--       ∙∙ (λ k i j → -ₖ-gen-inl-left n m x (inl y)
--                             (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
--                               (cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)) (~ k))

--  -}
--   main (suc n) (suc m) (inl x) (inr y) (merid a i) (merid b j) = {!!}
--   main (suc n) (suc m) (inr x) (inl y) (merid a i) (merid b j) = {!!}
--   main (suc n) (suc m) (inr x) (inr y) (merid a i) (merid b j) = {!!}

-- -- cup'-anti-comm :
-- --   (n m : ℕ) (x : coHomK (suc n)) → cup∙ n m x ≡ ((λ y → (-ₖ^ (suc n) · (suc m)) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n y x)))
-- --                                                         , cong ((-ₖ^ suc n · suc m) ∘ (subst coHomK (+'-comm (suc m) (suc n))))
-- --                                                                (cup'-lUnit m n x)
-- --                                                          ∙ cong (-ₖ^ suc n · suc m) (subst-help n m))
-- -- cup'-anti-comm n m =
-- --   trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevel↑∙ (suc n) m) _ _)
-- --          elim1 -- elim1
-- --   where

-- --   main : (n m : ℕ) (a : S₊ (suc n)) (b : S₊ (suc m))
-- --       → (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡ (-ₖ^ (suc n) · (suc m)) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ))
-- --   main zero zero base base = refl
-- --   main zero zero base (loop i) = refl
-- --   main zero zero (loop i) base = refl
-- --   main zero zero (loop i) (loop j) k = help k i j
-- --     where
-- --     help : (λ i j → cup' zero zero ∣ loop i ∣ₕ ∣ loop j ∣ₕ)
-- --          ≡ cong (cong ((-ₖ^ 1 · 1) ∘ subst coHomK (+'-comm 1 1)))
-- --                 λ i j → cup' zero zero ∣ loop j ∣ₕ ∣ loop i ∣ₕ
-- --     help = inst2 _ _
-- --       ∙∙ rUnit _
-- --       ∙∙ (λ i → transportRefl refl (~ i)
-- --               ∙∙ (λ i j → cup' zero zero ∣ loop (~ i) ∣ₕ ∣ loop (~ j) ∣ₕ)
-- --               ∙∙ transportRefl refl (~ i))
-- --       ∙∙ (λ i → (λ j → funExt (cong-₂ 1 1 tt tt) (~ i ∧ j)
-- --                  (λ j₁ → cup' zero zero ∣ loop (~ i1) ∣ₕ ∣ loop j₁ ∣ₕ))
-- --               ∙∙ cong (funExt (cong-₂ 1 1 tt tt) (~ i)) (λ i j → cup' zero zero ∣ loop (~ i) ∣ₕ ∣ loop j ∣ₕ)
-- --               ∙∙ λ j → funExt (cong-₂ 1 1 tt tt) (~ i ∧ ~ j)
-- --                  (λ j₁ → cup' zero zero ∣ loop (~ i1) ∣ₕ ∣ loop j₁ ∣ₕ))
-- --       ∙∙ sym (rUnit _)
-- --       ∙∙ cong (cong (cong ((-ₖ^ 1 · 1)))) (inst _ ((λ i j → cup' zero zero ∣ loop i ∣ₕ ∣ loop j ∣ₕ)))
-- --       ∙∙ λ k → cong (cong ((-ₖ^ 1 · 1)
-- --          ∘ λ x → transportRefl x (~ k)))
-- --           λ i j → cup' zero zero ∣ loop j ∣ₕ ∣ loop i ∣ₕ
-- --   main zero (suc m) a b = {!!}
-- --   main (suc n) zero a b = {!!}
-- --   main (suc n) (suc m) north north = refl
-- --   main (suc n) (suc m) north south = refl
-- --   main (suc n) (suc m) north (merid a i) = refl
-- --   main (suc n) (suc m) south north = refl
-- --   main (suc n) (suc m) south south = refl
-- --   main (suc n) (suc m) south (merid a i) = refl
-- --   main (suc n) (suc m) (merid a i) north = refl
-- --   main (suc n) (suc m) (merid a i) south = refl
-- --   main (suc n) (suc m) (merid a i) (merid b j) k = h k i j
-- --     where
-- --     lem₁ : cong (cong ∣_∣ₕ) (sym (cong (λ x → merid x ∙ sym (merid north))
-- --                                           (cong (pre-cup n (suc m) a) (merid b))))
-- --        ≡ sym (cong (Kn→ΩKn+1 _) ((cong ∣_∣ₕ) (cong (pre-cup n (suc m) a) (merid b))))
-- --     lem₁ = {!!}

-- --     lem₂ : cong (Kn→ΩKn+1 _) ((cong ∣_∣ₕ) (cong (pre-cup n (suc m) a) (merid b)))
-- --          ≡ cong (Kn→ΩKn+1 _) (cong (cup' n (suc m) ∣ a ∣) (cong ∣_∣ₕ (merid b)))
-- --     lem₂ = refl

-- --     lem₃ : cong (Kn→ΩKn+1 _) (cong ((-ₖ^ suc n · suc (suc m)) ∘
-- --                                                 (subst coHomK (+'-comm (suc (suc m)) (suc n))))
-- --                                                   (cong (λ x → cup' (suc m) n x ∣ a ∣) (cong ∣_∣ₕ (merid b))))
-- --          ≡ ({!!} ∙∙ {!!} ∙∙ {!!})
-- --     lem₃ = {!!}

-- --     h : (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)
-- --       ≡ cong (cong ((-ₖ^ suc (suc n) · suc (suc m)) ∘
-- --       (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))))
-- --         λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ ∣ merid a i ∣
-- --     h = (λ k i j → ∣ (sym (rCancel (merid north))
-- --            ∙∙ cong (λ x → merid x ∙ sym (merid north))
-- --           (rUnit (cong (pre-cup n (suc m) a) (merid b)) (~ k))
-- --          ∙∙ rCancel (merid north)) j i ∣ₕ)
-- --       ∙∙ sym (inst _ (λ i j → ∣ (sym (rCancel (merid north))
-- --            ∙∙ cong (λ x → merid x ∙ sym (merid north))
-- --           (cong (pre-cup n (suc m) a) (merid b))
-- --          ∙∙ rCancel (merid north)) i j ∣ₕ))
-- --       ∙∙ cong sym (λ k i j → cong-∙∙ (cong ∣_∣ₕ) (sym (rCancel (merid north)))
-- --                                           (cong (λ x → merid x ∙ sym (merid north))
-- --                                           (cong (pre-cup n (suc m) a) (merid b))) (rCancel (merid north)) k i j)
-- --       ∙∙ (λ k → (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
-- --               ∙∙ ((lem₁) k)
-- --               ∙∙ (cong (cong ∣_∣ₕ) ((rCancel (merid north))))))
-- --       ∙∙ ((λ k → (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
-- --               ∙∙ sym ((cong (Kn→ΩKn+1 _)) (rUnit (cong (cup' n (suc m) ∣ a ∣) (cong ∣_∣ₕ (merid b))) k))
-- --               ∙∙ (cong (cong ∣_∣ₕ) ((rCancel (merid north)))))))
-- --       ∙∙ (λ k → (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
-- --               ∙∙ sym (cong (Kn→ΩKn+1 _) ((λ i → main n (suc m) a north (i ∧ k))
-- --                                        ∙∙ (λ i → main n (suc m) a (merid b i) k)
-- --                                        ∙∙ (λ i → main n (suc m) a south (~ i ∧ k))))
-- --               ∙∙ (cong (cong ∣_∣ₕ) ((rCancel (merid north))))))
-- --       ∙∙ ((λ k → (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)))
-- --               ∙∙ sym (cong-∙∙ (Kn→ΩKn+1 _) (main n (suc m) a north)
-- --                                           (cong ((-ₖ^ suc n · suc (suc m)) ∘
-- --                                                 (subst coHomK (+'-comm (suc (suc m)) (suc n))))
-- --                                                   (cong (λ x → cup' (suc m) n x ∣ a ∣) (cong ∣_∣ₕ (merid b))))
-- --                                           (sym (main n (suc m) a south)) k)
-- --               ∙∙ (cong (cong ∣_∣ₕ) ((rCancel (merid north)))))))
-- --       ∙∙ {!!}
-- --       ∙∙ {!!}
-- --       ∙∙ {!!}
-- --       ∙∙ sym {!!}

-- --   cup'' : (n m : ℕ) → coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc n +' suc m)
-- --   fst (cup'' n m y) x = cup' n m ∣ x ∣ y
-- --   snd (cup'' n m y) = cup'-lUnit n m y

-- --   anti-commer : (n m : ℕ) → coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc n +' suc m)
-- --   fst (anti-commer n m y) x = (-ₖ^ (suc n) · (suc m)) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n y ∣ x ∣))
-- --   snd (anti-commer n m x) = cong ((-ₖ^ suc n · suc m) ∘ subst coHomK (+'-comm (suc m) (suc n))) (cup∙ m n x .snd)
-- --                                ∙ cong (-ₖ^ suc n · suc m) (subst-help n m)

-- --   elim-snd : (n m : ℕ) → (y : coHomK (suc m)) → cup'' n m y ≡ anti-commer n m y
-- --   elim-snd n m =
-- --     trElim (λ _ → isOfHLevelPath (3 + m)
-- --              (subst (isOfHLevel (3 + m)) (λ i → (S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (+-comm m n i)))))
-- --              (isOfHLevel↑∙' (suc m) n)) _ _)
-- --            λ b → →∙Homogeneous≡ (isHomogeneousKn _)
-- --                  (funExt λ a → main n m a b)


-- --   elim1 : (a : S₊ (suc n)) →
-- --       cup∙ n m ∣ a ∣ ≡ _
-- --   elim1 a = →∙Homogeneous≡ (isHomogeneousKn _)
-- --              (funExt λ b → funExt⁻ (cong fst (elim-snd n m b)) a)


-- -- -- cup∙∙ : (n m : ℕ) → coHomK-ptd (suc n) →∙ (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m))) ∙)
-- -- -- fst (cup∙∙ n m) = cup∙ n m
-- -- -- snd (cup∙∙ zero m) = refl
-- -- -- snd (cup∙∙ (suc n) m) = refl

-- -- -- _⌣₂_ : {n m : ℕ} → coHomK (suc n) → coHomK (suc m) → coHomK (suc n +' suc m)
-- -- -- _⌣₂_ {n = n} {m = m} a b = fst (cup∙ n m a) b

-- -- -- rUnit-⌣₂ : (n m : ℕ) → (x : coHomK (suc n)) → x ⌣₂ (0ₖ (suc m)) ≡ 0ₖ _
-- -- -- rUnit-⌣₂  n m x = snd (cup∙ n m x)

-- -- -- lUnit-⌣₂ : (n m : ℕ) → (x : coHomK (suc m)) → (0ₖ (suc n)) ⌣₂ x ≡ 0ₖ _
-- -- -- lUnit-⌣₂ n m = funExt⁻ (cong fst (snd (cup∙∙ n m)))


-- -- -- ⌣≡⌣₂ : (n m : ℕ) (a : coHomK (suc n)) → ⌣ₖ∙ (suc n) (suc m) a ≡ cup∙ n m a
-- -- -- ⌣≡⌣₂ n m =
-- -- --   trElim {!!} (help n m)
-- -- --   where
-- -- --   ⌣' : (n m : ℕ) → coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc n +' suc m)
-- -- --   ⌣' n m b = (λ a → _⌣ₖ_ {n = suc n} {m = suc m} ∣ a ∣ₕ b) , 0ₖ-⌣ₖ (suc n) (suc m) b

-- -- --   cup' : (n m : ℕ) → coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc n +' suc m)
-- -- --   cup' n m b = (λ a → fst (cup∙ n m ∣ a ∣) b) , lUnit-⌣₂ n m b

-- -- --   mainHelp : (n m : ℕ) (b : coHomK (suc m)) → ⌣' n m b ≡ cup' n m b 
-- -- --   mainHelp n m =
-- -- --     trElim {!!}
-- -- --       λ b → →∙Homogeneous≡ (isHomogeneousKn _) (funExt λ a → help n m a b)
-- -- --     where
-- -- --     help : (n m : ℕ) (a : S₊ (suc n)) (b : S₊ (suc m)) → (⌣' n m ∣ b ∣ .fst a) ≡ cup' n m ∣ b ∣ .fst a
-- -- --     help zero m base b = refl
-- -- --     help zero zero (loop i) base k = ∣ rCancel (merid base) k i ∣
-- -- --     help zero zero (loop i) (loop j) k =
-- -- --       ∣ doubleCompPath-filler (sym (rCancel (merid base)))
-- -- --                              (λ i → merid (loop i) ∙ sym (merid base))
-- -- --                              (rCancel (merid base)) k j i ∣
-- -- --     help zero (suc m) (loop i) north k =
-- -- --       ∣ rCancel (merid north) k i ∣
-- -- --     help zero (suc m) (loop i) south k =
-- -- --       (cong (cong ∣_∣ₕ) (λ i → merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north)) ∙ cong (cong ∣_∣ₕ) (rCancel (merid north))) k i
-- -- --     help zero (suc m) (loop i) (merid a j) k =
-- -- --       hcomp (λ r → λ { (i = i0) → 0ₖ _
-- -- --                       ; (i = i1) → 0ₖ _
-- -- --                       ; (j = i0) → ∣ rCancel (merid north) (r ∧ k) i ∣
-- -- --                       ; (j = i1) → compPath-filler (cong (cong ∣_∣ₕ) (λ i → merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north)))
-- -- --                                                     (cong (cong ∣_∣ₕ) (rCancel (merid north))) r k i
-- -- --                       ; (k = i0) → ⌣' zero (suc m) ∣ merid a j ∣ .fst (loop i)
-- -- --                       ; (k = i1) → doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 _) λ i → help zero m (loop i) a r) (Kn→ΩKn+10ₖ _) r j i})
-- -- --             ∣ (merid (compPath-filler (merid a) (sym (merid (ptSn (suc m)))) k j) ∙ (sym (merid north))) i ∣
-- -- --     help (suc n) zero north b = refl
-- -- --     help (suc n) zero south b = refl
-- -- --     help (suc n) zero (merid a i) base k = {!cup' (suc n) zero ∣ base ∣ .fst (merid a i)!}
-- -- --     help (suc n) zero (merid a i) (loop j) = {!!}
-- -- --     help (suc n) (suc m) north b = refl
-- -- --     help (suc n) (suc m) south b = refl
-- -- --     help (suc n) (suc m) (merid a i) north = {!!}
-- -- --       where
-- -- --       test : cup' (suc n) (suc m) ∣ north ∣ .fst (merid a i) ≡ 0ₖ _
-- -- --       test = {!)!}
-- -- --     help (suc n) (suc m) (merid a i) south = {!!}
-- -- --     help (suc n) (suc m) (merid a i) (merid a₁ i₁) = {!!}

-- -- --   help : (n m : ℕ) (a : S₊ (suc n)) →
-- -- --       ⌣ₖ∙ (suc n) (suc m) ∣ a ∣ₕ ≡ cup∙ n m ∣ a ∣ₕ
-- -- --   help n m a = →∙Homogeneous≡ (isHomogeneousKn _) (funExt λ b → funExt⁻ (cong fst (mainHelp n m b)) a )
    

-- -- -- -- open import Cubical.Foundations.Path

-- -- -- -- gradedComm-helper' : (k n m : ℕ)
-- -- -- --   → n + m ≡ k
-- -- -- --   → (x : S₊ (suc n)) (y : S₊ (suc m))
-- -- -- --   → Path (coHomK ((suc n) +' (suc m)))
-- -- -- --           (∣ x ∣ ⌣ₖ ∣ y ∣)
-- -- -- --           (subst coHomK (+'-comm (suc m) (suc n)) ((-ₖ^ (suc n) · suc m) (∣ y ∣ ⌣ₖ ∣ x ∣)))
-- -- -- -- gradedComm-helper' k zero zero p x y = {!!}
-- -- -- -- gradedComm-helper' k zero (suc m) p x y = {!!}
-- -- -- -- gradedComm-helper' k (suc n) zero p x y = {!!}
-- -- -- -- gradedComm-helper' k (suc n) (suc m) p north north = refl
-- -- -- -- gradedComm-helper' k (suc n) (suc m) p north south = refl
-- -- -- -- gradedComm-helper' k (suc n) (suc m) p north (merid a i) j =
-- -- -- --     (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- --        ((-ₖ^ suc (suc n) · suc (suc m)) (⌣ₖ-0ₖ _ _ ∣ merid a i ∣ (~ j))))
-- -- -- -- gradedComm-helper' k (suc n) (suc m) p south north = refl
-- -- -- -- gradedComm-helper' k (suc n) (suc m) p south south = refl
-- -- -- -- gradedComm-helper' k (suc n) (suc m) p south (merid a i) j =
-- -- -- --   help (~ j) i
-- -- -- --   where
-- -- -- --   help : cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- --         ∘ ((-ₖ^ suc (suc n) · suc (suc m)))) (Kn→ΩKn+1 _ (_⌣ₖ_ {n = (suc m)} {m = suc (suc n)} ∣ a ∣ ∣ south ∣)) ≡ refl
-- -- -- --   help = cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- --         ∘ ((-ₖ^ suc (suc n) · suc (suc m))))) (cong (Kn→ΩKn+1 _) (λ i → _⌣ₖ_ {n = (suc m)} {m = suc (suc n)} ∣ a ∣ ∣ merid (ptSn (suc n)) (~ i) ∣)
-- -- -- --         ∙∙ cong (Kn→ΩKn+1 (suc (suc (m + suc n)))) (⌣ₖ-0ₖ (suc m) (2 + n) ∣ a ∣)
-- -- -- --         ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- -- gradedComm-helper' k (suc n) (suc m) p (merid a i) north = ⌣ₖ-0ₖ (suc (suc n)) (2 + m) ∣ merid a i ∣
-- -- -- -- gradedComm-helper' k (suc n) (suc m) p (merid a i) south j = help j i
-- -- -- --   where
-- -- -- --   help : Kn→ΩKn+1 _ (_⌣ₖ_ {n = (suc n)} {m = 2 + m} ∣ a ∣ ∣ south ∣) ≡ refl
-- -- -- --   help = cong (Kn→ΩKn+1 _) (λ i → _⌣ₖ_ {n = (suc n)} {m = 2 + m} ∣ a ∣ ∣ merid (ptSn (suc m)) (~ i) ∣)
-- -- -- --       ∙∙ cong (Kn→ΩKn+1 _) (⌣ₖ-0ₖ (suc n) (2 + m) ∣ a ∣)
-- -- -- --       ∙∙ Kn→ΩKn+10ₖ _
-- -- -- -- gradedComm-helper' zero (suc n) (suc m) p (merid a i) (merid b j) l = pp i j l
-- -- -- --   where
-- -- -- --   pp : Cube (λ j l → gradedComm-helper' zero (suc n) (suc m) p north (merid b j) l)
-- -- -- --             (λ j l → gradedComm-helper' zero (suc n) (suc m) p south (merid b j) l)
-- -- -- --             (λ i l → gradedComm-helper' zero (suc n) (suc m) p (merid a i) north l)
-- -- -- --             (λ i l → gradedComm-helper' zero (suc n) (suc m) p (merid a i) south l)
-- -- -- --             (λ i j → _⌣ₖ_ {n = 2 + n} {m = 2 + m} ∣ merid a i ∣ ∣ merid b j ∣)
-- -- -- --             (λ i j → subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- --          ((-ₖ^ suc (suc n) · suc (suc m)) (∣ merid b j ∣ ⌣ₖ ∣ merid a i ∣)))
-- -- -- --   pp = ⊥-rec (snotz p)
-- -- -- -- gradedComm-helper' (suc zero) (suc n) (suc m) p (merid a i) (merid b j) l = pp i j l
-- -- -- --   where
-- -- -- --   pp : Cube (λ j l → gradedComm-helper' (suc zero) (suc n) (suc m) p north (merid b j) l)
-- -- -- --             (λ j l → gradedComm-helper' (suc zero) (suc n) (suc m) p south (merid b j) l)
-- -- -- --             (λ i l → gradedComm-helper' (suc zero) (suc n) (suc m) p (merid a i) north l)
-- -- -- --             (λ i l → gradedComm-helper' (suc zero) (suc n) (suc m) p (merid a i) south l)
-- -- -- --             (λ i j → _⌣ₖ_ {n = 2 + n} {m = 2 + m} ∣ merid a i ∣ ∣ merid b j ∣)
-- -- -- --             (λ i j → subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- --          ((-ₖ^ suc (suc n) · suc (suc m)) (∣ merid b j ∣ ⌣ₖ ∣ merid a i ∣)))
-- -- -- --   pp = ⊥-rec (snotz (sym (+-suc n m) ∙ (cong predℕ p)))
-- -- -- -- gradedComm-helper' (suc (suc k)) (suc n) (suc m) p (merid a i) (merid b j) l =
-- -- -- --   hcomp (λ r → λ { (i = i0) → (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- --                                ((-ₖ^ suc (suc n) · suc (suc m)) {!m-s j i1!}))
-- -- -- --                   ; (i = i1) → {!!}
-- -- -- --                   ; (j = i0) → {!!} -- m-n i (l ∨ ~ r)
-- -- -- --                   ; (j = i1) → {!!} -- m-s (l ∨ ~ r) i
-- -- -- --                   ; (l = i0) →
-- -- -- --                     doubleCompPath-filler
-- -- -- --                       {!λ i j → m-n (~ i) j!}
-- -- -- --                            (cong (λ y → cong (λ x →  _⌣ₖ_ {n = (suc (suc n))} {m = (suc (suc m))} ∣ x ∣ ∣ y ∣) (merid a)) (merid b))
-- -- -- --                            {!!} (~ r) j i
-- -- -- --                   ; (l = i1) → {!!}})
-- -- -- --         {!!}
-- -- -- --   where
-- -- -- --   m-s : _
-- -- -- --   m-s = cong (Kn→ΩKn+1 _) (λ i → _⌣ₖ_ {n = (suc n)} {m = 2 + m} ∣ a ∣ ∣ merid (ptSn (suc m)) (~ i) ∣)
-- -- -- --       ∙∙ cong (Kn→ΩKn+1 _) (⌣ₖ-0ₖ (suc n) (2 + m) ∣ a ∣)
-- -- -- --       ∙∙ Kn→ΩKn+10ₖ _

-- -- -- --   m-n : _
-- -- -- --   m-n = cong (λ x → ⌣ₖ-0ₖ (suc (suc n)) (2 + m) ∣ x ∣) (merid a)

-- -- -- -- {-
-- -- -- -- i = i0 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p north
-- -- -- --          (merid b j) l
-- -- -- -- i = i1 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p south
-- -- -- --          (merid b j) l
-- -- -- -- j = i0 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p
-- -- -- --          (merid a i) north l
-- -- -- -- j = i1 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p
-- -- -- --          (merid a i) south l
-- -- -- -- l = i0 ⊢ ∣ merid a i ∣ ⌣ₖ ∣ merid b j ∣
-- -- -- -- l = i1 ⊢ subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- --          ((-ₖ^ suc (suc n) · suc (suc m)) (∣ merid b j ∣ ⌣ₖ ∣ merid a i ∣))
-- -- -- -- -}
  
  
-- -- -- -- --   id₁ : cong (λ y → cong (λ x →  _⌣ₖ_ {n = (suc (suc n))} {m = (suc (suc m))} ∣ x ∣ ∣ y ∣) (merid a)) (merid b)
-- -- -- -- --       ≡ cong (Kn→ΩKn+1 _) (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north
-- -- -- -- --                         ∙∙ cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- -- -- --                        ((-ₖ^ suc n · suc (suc m)))))
-- -- -- -- --                          (Kn→ΩKn+1 _ ((subst coHomK (+'-comm (suc n) (suc m))
-- -- -- -- --                                       ((-ₖ^ suc m · suc n) (∣ a ∣ ⌣ₖ ∣ b ∣)))))
-- -- -- -- --                         ∙∙ sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south))
-- -- -- -- --   id₁ = (λ i → cong (Kn→ΩKn+1 _) (rUnit (cong (λ y → _⌣ₖ_ {n = (suc n)} {m = (suc (suc m))}  ∣ a ∣ ∣ y ∣) (merid b)) i))
-- -- -- -- --      ∙∙ (λ i → (cong (Kn→ΩKn+1 _) ((λ r → gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north (i ∧ r))
-- -- -- -- --                                  ∙∙ (λ j → (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a (merid b j)) i)
-- -- -- -- --                                  ∙∙ λ r → gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south (i ∧ ~ r))))
-- -- -- -- --      ∙∙ (λ i → cong (Kn→ΩKn+1 _)
-- -- -- -- --                (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north
-- -- -- -- --                ∙∙ cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- -- -- --                        ((-ₖ^ suc n · suc (suc m)))))
-- -- -- -- --                        (Kn→ΩKn+1 _ (gradedComm-helper' k m n (+-comm m n
-- -- -- -- --                       ∙ cong predℕ (sym (+-suc n m) ∙ (cong predℕ p))) b a i) )
-- -- -- -- --                ∙∙ sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south)))

-- -- -- -- --   lem₁ : (n m : ℕ)  (x : _)
-- -- -- -- --        → Kn→ΩKn+1 _ ((subst coHomK (+'-comm (suc n) (suc m))
-- -- -- -- --                       ((-ₖ^ suc m · suc n) x)))
-- -- -- -- --        ≡ cong (subst coHomK (cong (3 +_) (+-comm n m)) ∘
-- -- -- -- --           (-ₖ^_·_ {k = suc (suc (suc (n + m)))} (suc m) (suc n)))
-- -- -- -- --            (Kn→ΩKn+1 _ x)
-- -- -- -- --   lem₁ n m = {!!}

-- -- -- -- --   id₂' : cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- -- -- --                        ((-ₖ^ suc n · suc (suc m)))))
-- -- -- -- --                          (Kn→ΩKn+1 _ ((subst coHomK (+'-comm (suc n) (suc m))
-- -- -- -- --                                       ((-ₖ^ suc m · suc n) (∣ a ∣ ⌣ₖ ∣ b ∣)))))
-- -- -- -- --        ≡ (cong (subst coHomK (+'-comm (suc (suc m)) (suc n))
-- -- -- -- --          ∘ (-ₖ^ suc n · suc (suc m))
-- -- -- -- --           ∘ (subst coHomK (cong (_+_ 3) (+-comm n m)) ∘ (-ₖ^ suc m · suc n))))
-- -- -- -- --             (gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) north b
-- -- -- -- --           ∙∙ (cong (subst coHomK (+'-comm (suc m) (suc (suc n))) ∘
-- -- -- -- --              (-ₖ^ suc (suc n) · suc m)) (λ j → ∣ b ∣ ⌣ₖ ∣ merid a j ∣))
-- -- -- -- --           ∙∙ sym (gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) south b))
-- -- -- -- --   id₂' =
-- -- -- -- --        cong (cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- -- -- --                        ((-ₖ^ suc n · suc (suc m))))))
-- -- -- -- --             (lem₁ n m (∣ a ∣ ⌣ₖ ∣ b ∣))
-- -- -- -- --     ∙ cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc n))
-- -- -- -- --          ∘ (-ₖ^ suc n · suc (suc m))
-- -- -- -- --           ∘ (subst coHomK (cong (_+_ 3) (+-comm n m)) ∘ (-ₖ^ suc m · suc n))))
-- -- -- -- --            ((rUnit λ j → _⌣ₖ_ {n = (suc (suc n))} {m = (suc m)}  ∣ merid a j ∣ ∣ b ∣)
-- -- -- -- --           ∙ λ i → (λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) north b (i ∧ j))
-- -- -- -- --                ∙∙ (λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) (merid a j) b i)
-- -- -- -- --                ∙∙ λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) south b (i ∧ ~ j))
-- -- -- -- --     ∙ λ i → (cong (subst coHomK (+'-comm (suc (suc m)) (suc n))
-- -- -- -- --          ∘ (-ₖ^ suc n · suc (suc m))
-- -- -- -- --           ∘ (subst coHomK (cong (_+_ 3) (+-comm n m)) ∘ (-ₖ^ suc m · suc n))))
-- -- -- -- --             (gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) north b
-- -- -- -- --           ∙∙ (λ j → subst coHomK (+'-comm (suc m) (suc (suc n)))
-- -- -- -- --              ((-ₖ^ suc (suc n) · suc m) (∣ b ∣ ⌣ₖ ∣ merid a j ∣)))
-- -- -- -- --           ∙∙ sym (gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) south b))

-- -- -- -- -- --   id'' : cong (λ y → cong (λ x →  _⌣ₖ_ {n = (suc (suc m))} {m = (suc (suc n))} ∣ x ∣ ∣ y ∣) (merid b)) (merid a)
-- -- -- -- -- --        ≡ cong (λ y → cong (λ x →  _⌣ₖ_ {n = (suc (suc m))} {m = (suc (suc n))} ∣ x ∣ ∣ y ∣) (merid b)) (merid a)
-- -- -- -- -- --   id'' k i j = Kn→ΩKn+1 _ (_⌣ₖ_ {n = (suc m)} {m = (suc (suc n))} ∣ b ∣ ∣ merid a i ∣) j

-- -- -- -- -- --   id' : cong (λ y → cong (λ x →  _⌣ₖ_ {n = (suc (suc n))} {m = (suc (suc m))} ∣ x ∣ ∣ y ∣) (merid a)) (merid b)
-- -- -- -- -- --       ≡ {! !}
-- -- -- -- -- --   id' = -- (λ _ i j → _⌣ₖ_ {n = (suc (suc n))} {m = (suc (suc m))} ∣ merid a j ∣ ∣ merid b i ∣)
-- -- -- -- -- --       (λ i → cong (Kn→ΩKn+1 _) (rUnit (cong (λ y → _⌣ₖ_ {n = (suc n)} {m = (suc (suc m))}  ∣ a ∣ ∣ y ∣) (merid b)) i))
-- -- -- -- -- --      ∙∙ (λ i → (cong (Kn→ΩKn+1 _) ((λ r → gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north (i ∧ r))
-- -- -- -- -- --                                  ∙∙ (λ j → (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a (merid b j)) i)
-- -- -- -- -- --                                  ∙∙ λ r → gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south (i ∧ ~ r))))
-- -- -- -- -- --      ∙∙ (λ i → cong (Kn→ΩKn+1 _)
-- -- -- -- -- --                (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north
-- -- -- -- -- --                ∙∙ cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- -- -- -- --                        ((-ₖ^ suc n · suc (suc m)))))
-- -- -- -- -- --                        (Kn→ΩKn+1 _ (gradedComm-helper' k m n (+-comm m n
-- -- -- -- -- --                       ∙ cong predℕ (sym (+-suc n m) ∙ (cong predℕ p))) b a i) )
-- -- -- -- -- --                ∙∙ sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south)))
-- -- -- -- -- --      ∙∙ (λ i → cong (Kn→ΩKn+1 _)
-- -- -- -- -- --                (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north
-- -- -- -- -- --                ∙∙ cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- -- -- -- --                        ((-ₖ^ suc n · suc (suc m)))))
-- -- -- -- -- --                        (Kn→ΩKn+1 _ (
-- -- -- -- -- --        (subst coHomK (+'-comm (suc n) (suc m))
-- -- -- -- -- --         (trMap
-- -- -- -- -- --          (-ₖ-helper (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))
-- -- -- -- -- --           (_⌣ₖ_ {n = (suc n)} {m = (suc m)}  ∣ a ∣ ∣ b ∣)))))
-- -- -- -- -- --                ∙∙ sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south)))
-- -- -- -- -- --      ∙∙ cong-∙∙ (Kn→ΩKn+1 _) (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north)
-- -- -- -- -- --                               (cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- -- -- -- --                        ((-ₖ^ suc n · suc (suc m)))))
-- -- -- -- -- --                        (Kn→ΩKn+1 _ (
-- -- -- -- -- --        (subst coHomK (+'-comm (suc n) (suc m))
-- -- -- -- -- --         (trMap
-- -- -- -- -- --          (-ₖ-helper (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))
-- -- -- -- -- --           (_⌣ₖ_ {n = (suc n)} {m = (suc m)}  ∣ a ∣ ∣ b ∣))))))
-- -- -- -- -- --                               (sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south))
-- -- -- -- -- --      ∙∙ (λ i → cong (Kn→ΩKn+1 _) (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north)
-- -- -- -- -- --              ∙∙ cong (Kn→ΩKn+1 _) ((cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- -- -- -- --                        ((-ₖ^ suc n · suc (suc m))))))
-- -- -- -- -- --                          (lem₁ n m (evenOrOdd (suc m)) (evenOrOdd (suc n))
-- -- -- -- -- --                            (_⌣ₖ_ {n = (suc n)} {m = (suc m)}  ∣ a ∣ ∣ b ∣) i))
-- -- -- -- -- --              ∙∙ cong (Kn→ΩKn+1 _) (sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south)))
-- -- -- -- -- --      ∙∙ (λ i → cong (Kn→ΩKn+1 _) (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north)
-- -- -- -- -- --              ∙∙ cong (Kn→ΩKn+1 _) ((cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- -- -- -- --                        ((-ₖ^ suc n · suc (suc m)))))) -- (1 + n) (2 + m) + (1 + n) (1 + m). Remaining: 1 + n. -- 
-- -- -- -- -- --                          (cong (subst coHomK (cong (3 +_) (+-comm n m)) ∘
-- -- -- -- -- --         (trMap
-- -- -- -- -- --          (-ₖ-helper (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))))
-- -- -- -- -- --            (rUnit (λ j → _⌣ₖ_ {n = (suc (suc n))} {m = (suc m)}  ∣ merid a j ∣ ∣ b ∣) i)))
-- -- -- -- -- --              ∙∙ cong (Kn→ΩKn+1 _) (sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south)))
-- -- -- -- -- --       ∙ (λ i → cong (Kn→ΩKn+1 _) (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north)
-- -- -- -- -- --              ∙∙ cong (Kn→ΩKn+1 _) ((cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- -- -- -- --                        ((-ₖ^ suc n · suc (suc m)))))) -- (1 + n) (2 + m) + (1 + n) (1 + m). Remaining: 1 + n. + (2 + n) (1 + m) =  x(y + 1) + (x + 1)y + x y = xy + x + y
-- -- -- -- -- --                          (cong (subst coHomK (cong (3 +_) (+-comm n m)) ∘
-- -- -- -- -- --         (trMap
-- -- -- -- -- --          (-ₖ-helper (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))))
-- -- -- -- -- --               ((λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) north b (i ∧ j))
-- -- -- -- -- --            ∙∙ ((λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) (merid a j) b i))
-- -- -- -- -- --            ∙∙ λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) south b (i ∧ ~ j))))
-- -- -- -- -- --              ∙∙ cong (Kn→ΩKn+1 _) (sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south)))
-- -- -- -- -- --       ∙ {!λ i → cong (Kn→ΩKn+1 _) (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north)
-- -- -- -- -- --              ∙∙ cong (Kn→ΩKn+1 _) ((cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- -- -- -- --                        ((-ₖ^ suc n · suc (suc m)))))) -- (1 + n) (2 + m) + (1 + n) (1 + m). Remaining: 1 + n. + (2 + n) (1 + m) =  x(y + 1) + (x + 1)y + x y = xy + x + y
-- -- -- -- -- --                          (cong (subst coHomK (cong (3 +_) (+-comm n m)) ∘
-- -- -- -- -- --         (trMap
-- -- -- -- -- --          (-ₖ-helper (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))))
-- -- -- -- -- --               ((λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) north b (i ∧ j))
-- -- -- -- -- --            ∙∙ ((λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) (merid a j) b i))
-- -- -- -- -- --            ∙∙ λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) south b (i ∧ ~ j))))
-- -- -- -- -- --              ∙∙ cong (Kn→ΩKn+1 _) (sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south))!}
-- -- -- -- -- --       ∙ ?
-- -- -- -- -- --       -- (1 + n) m + (1 + n) (1 + m) + n (1 + m) = m + mn + 1 + n + m + mn + n + mn =₂ mn + 1
-- -- -- -- -- -- {-
-- -- -- -- -- -- WTS : ∣ merid a i ∣ ⌣ ∣ merid b j ∣ ≡ -ₖ⁽¹⁺ⁿ⁾⁽¹⁺ᵐ⁾⁺¹ (∣ merid b i ∣ ⌣ ∣ merid a j ∣)
-- -- -- -- -- -- case 1:

-- -- -- -- -- -- case 2:
-- -- -- -- -- -- case 3:
-- -- -- -- -- -- case 4: 

-- -- -- -- -- -- -}

-- -- -- -- -- --       where
-- -- -- -- -- --       lem₁ : (n m : ℕ) (p : _) (q : _) (x : _) → Kn→ΩKn+1 _ (
-- -- -- -- -- --        (subst coHomK (+'-comm (suc n) (suc m))
-- -- -- -- -- --         (trMap
-- -- -- -- -- --           (-ₖ-helper (suc m) (suc n) p q) x))) ≡ cong (subst coHomK (cong (3 +_) (+-comm n m)) ∘
-- -- -- -- -- --         (trMap
-- -- -- -- -- --          (-ₖ-helper (suc m) (suc n) p q))) (Kn→ΩKn+1 _ x)
-- -- -- -- -- --       lem₁ = {!!}

-- -- -- -- -- --       lem₂ : {!!}
-- -- -- -- -- --       lem₂ = {!!}

-- -- -- -- -- -- {-
-- -- -- -- -- -- i = i0 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p north
-- -- -- -- -- --          (merid b j) l
-- -- -- -- -- -- i = i1 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p south
-- -- -- -- -- --          (merid b j) l
-- -- -- -- -- -- j = i0 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p
-- -- -- -- -- --          (merid a i) north l
-- -- -- -- -- -- j = i1 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p
-- -- -- -- -- --          (merid a i) south l
-- -- -- -- -- -- l = i0 ⊢ ∣ merid a i ∣ ⌣ₖ ∣ merid b j ∣
-- -- -- -- -- -- l = i1 ⊢ subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- -- -- --          ((-ₖ^ suc (suc n) · suc (suc m)) (∣ merid b j ∣ ⌣ₖ ∣ merid a i ∣))
-- -- -- -- -- -- -}
