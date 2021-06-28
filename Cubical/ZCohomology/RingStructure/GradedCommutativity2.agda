{-# OPTIONS --safe --experimental-lossy-unification --no-forcing #-}
module Cubical.ZCohomology.RingStructure.GradedCommutativity2 where
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


testP : (n : ℕ) → subst coHomK (+'-comm 1 (suc n)) (0ₖ _) ≡ 0ₖ _
testP zero = refl
testP (suc n) = refl

transpLem' : (n : ℕ) (a : _) (p : _) (q : _) → (cong (cong (-ₖ-gen (suc (suc n)) (suc zero) p q ∘ 
                  (subst coHomK (+'-comm 1 (suc (suc n)))))) (((sym (Kn→ΩKn+10ₖ _) ∙∙ (λ i j →  Kn→ΩKn+1 _ ((Kn→ΩKn+1 (suc n) ∣ a ∣ₕ i)) j) ∙∙ (Kn→ΩKn+10ₖ _)))))
              ≡ (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 (suc (suc (n + zero))))
                    (sym (testP n) ∙∙ cong (subst coHomK (+'-comm (suc zero) (suc n))) (cong (-ₖ-gen (suc (suc n)) (suc zero) p q) (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ)) ∙∙ testP n)
                  ∙∙ Kn→ΩKn+10ₖ _)
transpLem' n a (inl x) (inr tt) = {!!}
{-
    (λ k i j → -ₖ-gen-inl-left (suc (suc n)) 1 x (inr tt)
                {!!} k)
  ∙ {!!} -}
transpLem' n a (inr x) (inr tt) = {!!}

mainₗ : (n : ℕ) (p : _) (q : _) (a : _) (b : S¹) →
      (_⌣ₖ_  {n = suc n} {m = (suc zero)} ∣ a ∣ₕ ∣ b ∣ₕ)
    ≡ (-ₖ-gen (suc n) (suc zero) p q)
       (subst coHomK (+'-comm (suc zero) (suc n))
        (_⌣ₖ_  {n = suc zero} {m = suc n} ∣ b ∣ₕ ∣ a ∣ₕ))
mainₗ zero (inr tt) (inr tt) a b = proof a b ∙ cong (-ₖ-gen 1 1 (inr tt) (inr tt)) (sym (transportRefl ((_⌣ₖ_ {n = suc zero} {m = suc zero} ∣ b ∣ ∣ a ∣))))
  where
  help : flipSquare ((sym (Kn→ΩKn+10ₖ _)) ∙∙ (λ j i → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ loop i ∣ₕ ∣ loop j ∣ₕ) ∙∙ Kn→ΩKn+10ₖ _) ≡
                    cong (cong (-ₖ-gen 1 1 (inr tt) (inr tt))) ((sym (Kn→ΩKn+10ₖ _) ∙∙ (λ i j → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ loop j ∣ₕ ∣ loop i ∣ₕ) ∙∙ Kn→ΩKn+10ₖ _))
  help = sym (inst _ _)
       ∙ inst4 _
       ∙ rUnit _
       ∙ (λ k → transportRefl refl (~ k)
              ∙∙ cong sym (sym (Kn→ΩKn+10ₖ _) ∙∙ (λ i j → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ loop j ∣ₕ ∣ loop i ∣ₕ) ∙∙ Kn→ΩKn+10ₖ _)
              ∙∙ transportRefl refl (~ k))
      ∙∙ (λ k → (λ i j → (cong-₂ 1 1 tt tt refl (~ k ∧ i) j))
              ∙∙ (λ i j → cong-₂ 1 1 tt tt (((sym (Kn→ΩKn+10ₖ _) ∙∙ (λ i j → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ loop j ∣ₕ ∣ loop i ∣ₕ) ∙∙ Kn→ΩKn+10ₖ _)) i) (~ k) j)
               ∙∙ λ i j → (cong-₂ 1 1 tt tt refl (~ k ∧ ~ i) j))
      ∙∙ sym (rUnit _)

  proof : (a b : S¹) → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ a ∣ₕ ∣ b ∣ₕ ≡
      -ₖ-gen 1 1 (inr tt) (inr tt) (_⌣ₖ_ {n = suc zero} {m = suc zero} ∣ b ∣ ∣ a ∣)
  proof base base = refl
  proof base (loop i) k = -ₖ-gen 1 1 (inr tt) (inr tt) (Kn→ΩKn+10ₖ _ (~ k) i)
  proof (loop i) base k = Kn→ΩKn+10ₖ _ k i
  proof (loop i) (loop j) k =
    hcomp (λ r →  λ {(i = i0) → -ₖ-gen 1 1 (inr tt) (inr tt) (Kn→ΩKn+10ₖ _ (~ k ∨ ~ r) j)
                    ; (i = i1) → -ₖ-gen 1 1 (inr tt) (inr tt) (Kn→ΩKn+10ₖ _ (~ k ∨ ~ r) j)
                    ; (j = i0) → Kn→ΩKn+10ₖ _ (k ∨ ~ r) i
                    ; (j = i1) → Kn→ΩKn+10ₖ _ (k ∨ ~ r) i
                    ; (k = i0) → doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _)) (λ j i → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ loop i ∣ₕ ∣ loop j ∣ₕ) (Kn→ΩKn+10ₖ _) (~ r) j i
                    ; (k = i1) → (-ₖ-gen 1 1 (inr tt) (inr tt)
                                   (doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _)) ((λ i j → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ loop j ∣ₕ ∣ loop i ∣ₕ))
                                   (Kn→ΩKn+10ₖ _) (~ r) i j))})
          (help k i j)
mainₗ (suc n) p q north b =
  cong (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
            (subst coHomK (+'-comm 1 (suc (suc n))))) (sym (⌣ₖ-0ₖ _ (suc (suc n)) ∣ b ∣ₕ))
mainₗ (suc n) p q south b =
  cong (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
            (subst coHomK (+'-comm 1 (suc (suc n))))) ((sym (⌣ₖ-0ₖ _ (suc (suc n)) ∣ b ∣ₕ))
                                                     ∙ λ i → ∣ b ∣ ⌣ₖ ∣ merid (ptSn (suc n)) i ∣ₕ)
mainₗ (suc n) p q (merid a i) base k =
  hcomp (λ j → λ {(i = i0) → (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
                                  (subst coHomK (+'-comm 1 (suc (suc n)))))
                                    (0ₖ _)
                 ; (i = i1) → (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
                                  (subst coHomK (+'-comm 1 (suc (suc n)))))
                                    (compPath-filler (sym (⌣ₖ-0ₖ _ (suc (suc n)) ∣ base ∣ₕ)) (λ i → ∣ base ∣ ⌣ₖ ∣ merid a i ∣ₕ) j k)
                 ; (k = i0) → _⌣ₖ_ {n = suc (suc n)} {m = suc zero} ∣ merid a i ∣ₕ ∣ base ∣ₕ
                 ; (k = i1) → -ₖ-gen (suc (suc n)) 1 p q
                                (subst coHomK (+'-comm 1 (suc (suc n)))
                                 (∣ base ∣ₕ ⌣ₖ ∣ merid a i ∣ₕ))})
        (hcomp (λ j → λ {(i = i0) → ∣ north ∣
                        ; (i = i1) → ∣ north ∣
                        ; (k = i0) → (sym (Kn→ΩKn+10ₖ _) ∙ (λ j → Kn→ΩKn+1 _ (sym (mainₗ n (evenOrOdd (suc n)) (inr tt) a base
                                                ∙ cong (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt))) (testP n)) j))) j i
                        ; (k = i1) → ∣ north ∣})
               ∣ north ∣)
mainₗ (suc n) p q (merid a i) (loop j) k =
  hcomp (λ r → λ { (i = i0) → (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
                                  (subst coHomK (+'-comm 1 (suc (suc n)))))
                                    (sym (⌣ₖ-0ₖ _ (suc (suc n)) ∣ (loop j) ∣ₕ) k)
                  ; (i = i1) → (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
                                  (subst coHomK (+'-comm 1 (suc (suc n)))))
                                    (compPath-filler (sym (⌣ₖ-0ₖ _ (suc (suc n)) ∣ (loop j) ∣ₕ))
                                      (λ i → ∣ loop j ∣ ⌣ₖ ∣ merid (ptSn (suc n)) i ∣ₕ) r k)
                  ; (k = i0) → _⌣ₖ_ {n = suc (suc n)} {m = suc zero} ∣ merid a i ∣ₕ ∣ loop j ∣ₕ
                  ; (k = i1) → -ₖ-gen (suc (suc n)) 1 p q
                                 (subst coHomK (+'-comm 1 (suc (suc n)))
                                  (_⌣ₖ_ {n = suc zero} {m = suc (suc n)} ∣ loop j ∣ₕ ∣ compPath-filler (merid a) (sym (merid (ptSn (suc n)))) (~ r) i ∣ₕ))})
        (hcomp (λ r → λ { (i = i0) → (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
                                         (subst coHomK (+'-comm 1 (suc (suc n)))))
                                           ∣ rCancel (merid (ptSn (suc (suc n)))) (~ k ∧ r) j ∣
                         ; (i = i1) → (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
                                         (subst coHomK (+'-comm 1 (suc (suc n)))))
                                           ∣ rCancel (merid (ptSn (suc (suc n)))) (~ k ∧ r) j ∣
                         ; (k = i0) → help r i j
                         ; (k = i1) → -ₖ-gen (suc (suc n)) 1 p q
                                        (subst coHomK (+'-comm 1 (suc (suc n)))
                                         (_⌣ₖ_ {n = suc zero} {m = suc (suc n)} ∣ loop j ∣ₕ (Kn→ΩKn+1 _ ∣ a ∣ₕ i)))})
                (-ₖ-gen (suc (suc n)) 1 p q
                                        (subst coHomK (+'-comm 1 (suc (suc n)))
                                         (_⌣ₖ_ {n = suc zero} {m = suc (suc n)} ∣ loop j ∣ₕ (Kn→ΩKn+1 _ ∣ a ∣ₕ i)))))
    where
    transpLem : (cong (cong (-ₖ-gen (suc (suc n)) 1 p q ∘ 
                  (subst coHomK (+'-comm 1 (suc (suc n)))))) (((sym (Kn→ΩKn+10ₖ _) ∙∙ (λ i j →  Kn→ΩKn+1 _ ((Kn→ΩKn+1 (suc n) ∣ a ∣ₕ i)) j) ∙∙ (Kn→ΩKn+10ₖ _)))))
              ≡ (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 (suc (suc (n + 0))))
                    (sym (testP n) ∙∙ cong (subst coHomK (+'-comm 1 (suc n))) (cong (-ₖ-gen (suc (suc n)) 1 p q) (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ)) ∙∙ testP n)
                  ∙∙ Kn→ΩKn+10ₖ _)
    transpLem = transpLem' n a p q

    P : Path _ (Kn→ΩKn+1 (suc (suc (n + 0))) (0ₖ _)) (Kn→ΩKn+1 (suc (suc (n + 0))) (_⌣ₖ_ {n = (suc n)} {m = suc zero} ∣ a ∣ ∣ base ∣))
    P j₂ = Kn→ΩKn+1 (suc (suc (n + 0)))
            ( (sym
             (mainₗ n (evenOrOdd (suc n)) (inr tt) a base ∙
              cong (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt)))
              (testP n))
             j₂))

    help₁ : (P ∙∙ ((λ i j → _⌣ₖ_ {n = suc (suc n)} {m = suc zero} ∣ merid a j ∣ₕ ∣ loop i ∣ₕ)) ∙∙ sym P)
         ≡ ((λ i → Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt))
                                                     (testP n (~ i))))
        ∙∙ (λ i j → Kn→ΩKn+1 _ (-ₖ-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt)
                                  (subst coHomK (+'-comm 1 (suc n)) (∣ loop i ∣ₕ ⌣ₖ ∣ a ∣ₕ))) j)
        ∙∙ (λ i → Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt))
                                                     (testP n i))))
    help₁ k i j = ((λ i → (Kn→ΩKn+1 (suc (suc (n + 0)))) (compPath-filler' ((mainₗ n (evenOrOdd (suc n)) (inr tt) a base))
                                                     (cong (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt)))
                                                     (testP n)) (~ k) (~ i))) ∙∙ (λ i j → (Kn→ΩKn+1 _ (mainₗ n (evenOrOdd (suc n)) (inr tt) a (loop i) k) j))
                                                     ∙∙ λ i → (Kn→ΩKn+1 (suc (suc (n + 0)))) (compPath-filler' ((mainₗ n (evenOrOdd (suc n)) (inr tt) a base))
                                                     (cong (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt)))
                                                     (testP n)) (~ k) i)) i j

    help₂ : (n : ℕ) (a : _) (p : _) (q : _) → ((λ i → Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) (suc zero) (evenOrOdd (suc n)) (inr tt))
                                                                                         (testP n (~ i))))
                                            ∙∙ (λ i j → Kn→ΩKn+1 _ (-ₖ-gen (suc n) (suc zero) (evenOrOdd (suc n)) (inr tt)
                                                                      (subst coHomK (+'-comm (suc zero) (suc n)) (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ i))) j)
                                            ∙∙ (λ i → Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) (suc zero) (evenOrOdd (suc n)) (inr tt))
                                                                                         (testP n i))))
         ≡ (cong (Kn→ΩKn+1 (suc (suc (n + zero))))
             (sym (testP n)
           ∙∙ sym (cong (subst coHomK (+'-comm (suc zero) (suc n))) (cong (-ₖ-gen (suc (suc n)) (suc zero) p q) (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ)))
           ∙∙ testP n))
    help₂ zero a (inl x) (inr tt) =
        (λ k → rUnit ((cong (Kn→ΩKn+1 _) (cong-₂ (suc zero) (suc zero) tt tt (λ i → (subst coHomK (+'-comm (suc zero) (suc zero)) (Kn→ΩKn+1 (suc zero) ∣ a ∣ₕ i))) k))) (~ k))
      ∙ λ k → ((cong (Kn→ΩKn+1 (suc (suc zero)))
                 (rUnit (λ i → subst coHomK (+'-comm (suc zero) (suc zero))
                   (-ₖ-gen-inl-left (suc (suc zero)) (suc zero) tt (inr tt) (Kn→ΩKn+1 (suc zero) ∣ a ∣ₕ (~ i)) (~ k))) k)))
    help₂ (suc n) a (inl x) (inr tt) =
        ((λ k → rUnit (cong (Kn→ΩKn+1 _) (λ i → -ₖ-gen (suc (suc n)) (suc zero) (evenOrOdd-Prop n (evenOrOdd (suc (suc n))) (inr x) k) (inr tt)
                                                                      (subst coHomK (+'-comm (suc zero) (suc (suc n))) (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ i)))) (~ k)))
      ∙ (((λ k → ((cong (Kn→ΩKn+1 _) (cong-₂ (suc (suc n)) (suc zero) x tt (λ i → (subst coHomK (+'-comm (suc zero) (suc (suc n))) (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ i))) k))))))
      ∙ λ k → ((cong (Kn→ΩKn+1 (suc (suc (suc n + zero))))
                 (rUnit (λ i → subst coHomK (+'-comm (suc zero) (suc (suc n)))
                   (-ₖ-gen-inl-left (suc (suc (suc n))) (suc zero) x (inr tt) (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ (~ i)) (~ k))) k)))
    help₂ (suc n) a (inr x) (inr tt) =
         (λ k → rUnit (λ i j → Kn→ΩKn+1 _ (-ₖ-gen (suc (suc n)) (suc zero) (evenOrOdd-Prop (suc (suc n)) (evenOrOdd (suc (suc n))) (inl x) k) (inr tt)
                                                                      (subst coHomK (+'-comm (suc zero) (suc (suc n))) (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ i))) j) (~ k))
      ∙∙ (λ k i j → Kn→ΩKn+1 _ (-ₖ-gen-inl-left (suc (suc n)) (suc zero) x (inr tt)
                                  (subst coHomK (+'-comm (suc zero) (suc (suc n))) (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ i)) k) j)
      ∙∙ λ k → cong (Kn→ΩKn+1 _)
                (rUnit (sym (cong (subst coHomK (+'-comm (suc zero) (suc (suc n)))) (cong-₂ (suc (suc (suc n))) (suc zero) x tt (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ) (~ k)))) k)

    help : Cube (λ i j → -ₖ-gen (suc (suc n)) 1 p q
                                        (subst coHomK (+'-comm 1 (suc (suc n)))
                                         (_⌣ₖ_ {n = suc zero} {m = suc (suc n)} ∣ loop j ∣ₕ (Kn→ΩKn+1 _ ∣ a ∣ₕ i))))
                ((λ i j → _⌣ₖ_ {n = suc (suc n)} {m = suc zero} ∣ merid a i ∣ₕ ∣ loop j ∣ₕ))
                (λ r j → (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
                                         (subst coHomK (+'-comm 1 (suc (suc n)))))
                                           ∣ rCancel (merid (ptSn (suc (suc n)))) r j ∣)
                ((λ r j → (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
                                         (subst coHomK (+'-comm 1 (suc (suc n)))))
                                           ∣ rCancel (merid (ptSn (suc (suc n)))) r j ∣))
                (λ r i → (sym (Kn→ΩKn+10ₖ _) ∙ P) r i)
                (λ r i → (sym (Kn→ΩKn+10ₖ _) ∙ P) r i)
    help r i j = hcomp (λ k → λ {(i = i0) → (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
                                                 subst coHomK (+'-comm 1 (suc (suc n))))
                                                ∣ rCancel (merid (ptSn (suc (suc n)))) (~ k ∨ r) j ∣
                                ; (i = i1) → (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
                                                 subst coHomK (+'-comm 1 (suc (suc n))))
                                                ∣ rCancel (merid (ptSn (suc (suc n)))) (~ k ∨ r) j ∣
                                ; (j = i0) → compPath-filler (sym (Kn→ΩKn+10ₖ (suc (suc (n + 0)))))
                                                P k r i
                                ; (j = i1) → compPath-filler (sym (Kn→ΩKn+10ₖ (suc (suc (n + 0)))))
                                                P k r i
                                ; (r = i0) → -ₖ-gen (suc (suc n)) 1 p q
                                               (subst coHomK (+'-comm 1 (suc (suc n)))
                                                 (doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _))
                                                   (λ i j → _⌣ₖ_ {n = suc zero} {m = suc (suc n)} ∣ loop j ∣ₕ (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ i)) (Kn→ΩKn+10ₖ _) (~ k) i j))
                                ; (r = i1) → doubleCompPath-filler P
                                                    (λ i j → _⌣ₖ_ {n = suc (suc n)} {m = suc zero} ∣ merid a j ∣ₕ ∣ loop i ∣ₕ)
                                                    (sym P) (~ k) j i})
                       (hcomp (λ k → λ {(i = i0) → ∣ north ∣
                                ; (i = i1) → ∣ north ∣
                                ; (j = i0) → (Kn→ΩKn+10ₖ (suc (suc (n + 0)))) (~ r) i
                                ; (j = i1) → (Kn→ΩKn+10ₖ (suc (suc (n + 0)))) (~ r) i
                                ; (r = i0) → transpLem (~ k) i j
                                ; (r = i1) → help₁ (~ k) j i})
                              ((hcomp (λ k → λ {(i = i0) → ∣ north ∣
                                ; (i = i1) → ∣ north ∣
                                ; (j = i0) → Kn→ΩKn+10ₖ (suc (suc (n + 0))) (~ r) i
                                ; (j = i1) → Kn→ΩKn+10ₖ (suc (suc (n + 0))) (~ r) i
                                ; (r = i0) → inst3 _ (flipSquare ((sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 (suc (suc (n + 0))))
                                                       (sym (testP n) ∙∙ cong (subst coHomK (+'-comm 1 (suc n))) (cong (-ₖ-gen (suc (suc n)) 1 p q) (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ)) ∙∙ testP n)
                                                     ∙∙ Kn→ΩKn+10ₖ _))) (~ k) i j
                                ; (r = i1) → ((λ i → Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt))
                                                                                         (testP n (~ i))))
                                            ∙∙ (λ i j → Kn→ΩKn+1 _ (-ₖ-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt)
                                                                      (subst coHomK (+'-comm 1 (suc n)) (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ i))) j)
                                            ∙∙ (λ i → Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt))
                                                                                         (testP n i)))) j i})
                                (hcomp (λ k → λ {(i = i0) → ∣ north ∣
                                ; (i = i1) → ∣ north ∣
                                ; (j = i0) → Kn→ΩKn+10ₖ (suc (suc (n + 0))) (~ r ∧ k) i
                                ; (j = i1) → Kn→ΩKn+10ₖ (suc (suc (n + 0))) (~ r ∧ k) i
                                ; (r = i0) → doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _))
                                                (cong (Kn→ΩKn+1 (suc (suc (n + 0))))
                                                  (sym (testP n) ∙∙ sym (cong (subst coHomK (+'-comm 1 (suc n))) (cong (-ₖ-gen (suc (suc n)) 1 p q) (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ))) ∙∙ testP n))
                                              (Kn→ΩKn+10ₖ _) k j i
                                ; (r = i1) → help₂ n a p q (~ k) j i})
                                       (help₂ n a p q i1 j i)))))

{-
r = i0 ⊢ -ₖ-gen (suc (suc n)) 1 p q
         (subst coHomK (+'-comm 1 (suc (suc n)))
          (∣ loop j ∣ₕ ⌣ₖ Kn→ΩKn+1 (suc n) ∣ a ∣ₕ i))
r = i1 ⊢ ∣ merid a i ∣ₕ ⌣ₖ ∣ loop j ∣ₕ
i = i0 ⊢ (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
          subst coHomK (+'-comm 1 (suc (suc n))))
         ∣ rCancel (merid (ptSn (suc (suc n)))) r j ∣
i = i1 ⊢ (trMap (-ₖ-helper (suc (suc n)) 1 p q) ∘
          subst coHomK (+'-comm 1 (suc (suc n))))
         ∣ rCancel (merid (ptSn (suc (suc n)))) r j ∣
j = i0 ⊢ (sym (Kn→ΩKn+10ₖ (suc (suc (n + 0)))) ∙
          (λ j₂ →
             Kn→ΩKn+1 (suc (suc (n + 0)))
             (sym
              (mainₗ n (evenOrOdd (suc n)) (inr tt) a base ∙
               cong (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt)))
               (testP n))
              j₂)))
         r i
j = i1 ⊢ (sym (Kn→ΩKn+10ₖ (suc (suc (n + 0)))) ∙
          (λ j₂ →
             Kn→ΩKn+1 (suc (suc (n + 0)))
             (sym
              (mainₗ n (evenOrOdd (suc n)) (inr tt) a base ∙
               cong (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt)))
               (testP n))
              j₂)))
         r i
-}

-- mainₗ zero p q a b = {!!}
-- mainₗ (suc n) p q north base = refl
-- mainₗ (suc n) p q north (loop i) = {!hcomp ? ?!}
-- {-
--      ((λ k → trMap (-ₖ-helper (suc (suc n)) 1 p q)
--             (testP (suc n) (~ k)))
--    ∙ (λ k → trMap (-ₖ-helper (suc (suc n)) 1 p q)
--                    (subst coHomK (+'-comm 1 (suc (suc n)))
--                      (Kn→ΩKn+10ₖ _ (~ k) i))))
--    ∙ refl -}
-- mainₗ (suc n) p q south base =
--   (refl ∙ refl) ∙ refl
-- mainₗ (suc n) p q south (loop i) = {!!}
-- {-
--   ((λ k → trMap (-ₖ-helper (suc (suc n)) 1 p q)
--             (testP (suc n) (~ k)))
--    ∙ λ k → trMap (-ₖ-helper (suc (suc n)) 1 p q)
--                    (subst coHomK (+'-comm 1 (suc (suc n)))
--                      (Kn→ΩKn+10ₖ _ (~ k) i)))
--    ∙ λ k → trMap (-ₖ-helper (suc (suc n)) 1 p q)
--                    (subst coHomK (+'-comm 1 (suc (suc n)))
--                      (Kn→ΩKn+1 _ ∣ merid (ptSn _) k ∣ i)) -}
-- mainₗ (suc n) p q (merid a i) base = {!!}
-- {-
--     ((λ k → Kn→ΩKn+1 _ (mainₗ n (evenOrOdd (suc n)) (inr tt) a base k) i)
--   ∙ (λ k → Kn→ΩKn+1 (suc (suc (n + 0)))
--       (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt))
--        (testP n k))
--       i))
--   ∙ λ k → Kn→ΩKn+10ₖ _ k i -}
-- mainₗ (suc n) p q (merid a i) (loop j) k = {!!}
-- {-
--   hcomp (λ r → λ {(i = i0) → compPath-filler (((λ k → trMap (-ₖ-helper (suc (suc n)) 1 p q)
--                                                        (testP (suc n) (~ k)))
--                                               ∙ (λ k → trMap (-ₖ-helper (suc (suc n)) 1 p q)
--                                                               (subst coHomK (+'-comm 1 (suc (suc n)))
--                                                                 (Kn→ΩKn+10ₖ _ (~ k) j))))) refl r k
--                  ; (i = i1) → compPath-filler ((λ k → trMap (-ₖ-helper (suc (suc n)) 1 p q)
--                                                          (testP (suc n) (~ k)))
--                                                 ∙ λ k → trMap (-ₖ-helper (suc (suc n)) 1 p q)
--                                                                 (subst coHomK (+'-comm 1 (suc (suc n)))
--                                                                   (Kn→ΩKn+10ₖ _ (~ k) j)))
--                                                 (λ k → trMap (-ₖ-helper (suc (suc n)) 1 p q)
--                                                          (subst coHomK (+'-comm 1 (suc (suc n)))
--                                                            (Kn→ΩKn+1 _ ∣ merid (ptSn _) k ∣ j))) r k
--                  ; (j = i0) → compPath-filler (((λ k → Kn→ΩKn+1 _ (mainₗ n (evenOrOdd (suc n)) (inr tt) a base k) i)
--                                                ∙ (λ k → Kn→ΩKn+1 (suc (suc (n + 0)))
--                                                    (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt))
--                                                     (testP n k))
--                                                    i))) (λ k → Kn→ΩKn+10ₖ _ k i) r k
--                  ; (j = i1) → compPath-filler (((λ k → Kn→ΩKn+1 _ (mainₗ n (evenOrOdd (suc n)) (inr tt) a base k) i)
--                                                ∙ (λ k → Kn→ΩKn+1 (suc (suc (n + 0)))
--                                                    (trMap (-ₖ-helper (suc n) 1 (evenOrOdd (suc n)) (inr tt))
--                                                     (testP n k))
--                                                    i))) (λ k → Kn→ΩKn+10ₖ _ k i) r k
--                  ; (k = i0) → {!compPath-filler' ? ? r i!}
--                  ; (k = i1) → {!doubleCompPath-filler!}})
--         {!!} -}
-- {-
-- i = i0 ⊢ mainₗ (suc n) p q north (loop j) k
-- i = i1 ⊢ mainₗ (suc n) p q south (loop j) k
-- j = i0 ⊢ mainₗ (suc n) p q (merid a i) base k
-- j = i1 ⊢ mainₗ (suc n) p q (merid a i) base k
-- k = i0 ⊢ ∣ merid a i ∣ₕ ⌣ₖ ∣ loop j ∣ₕ
-- k = i1 ⊢ -ₖ-gen (suc (suc n)) 1 p q
--          (subst coHomK (+'-comm 1 (suc (suc n)))
--           (∣ loop j ∣ₕ ⌣ₖ ∣ merid a i ∣ₕ))

--   hcomp (λ r → λ {(i = i0) → {!!}
--                  ; (i = i1) → {!!}
--                  ; (j = i0) → {!!}
--                  ; (j = i1) → {!!}
--                  ; (k = i0) → {!!}
--                  ; (k = i1) → {!!}})
--         {!!} -}
-- {-
-- i = i0 ⊢ mainₗ (suc n) p q north (loop j)
-- i = i1 ⊢ mainₗ (suc n) p q south (loop j)
-- j = i0 ⊢ mainₗ (suc n) p q (merid a i) base
-- j = i1 ⊢ mainₗ (suc n) p q (merid a i) base
-- -}

-- -- ∪ₗ'-1-cool : (m : ℕ) → S¹ → S₊ (suc m) → S₊ (suc (suc m))
-- -- ∪ₗ'-1-cool m base y = north
-- -- ∪ₗ'-1-cool zero (loop i) base = north
-- -- ∪ₗ'-1-cool zero (loop i) (loop i₁) =
-- --   (sym (rCancel (merid base)) ∙∙ (λ i → merid (loop i) ∙ sym (merid base)) ∙∙ rCancel (merid base)) i i₁
-- -- ∪ₗ'-1-cool (suc m) (loop i) north = north
-- -- ∪ₗ'-1-cool (suc m) (loop i) south = north
-- -- ∪ₗ'-1-cool (suc m) (loop i) (merid a j) = 
-- --   (sym (rCancel (merid north)) ∙∙ (λ i → merid ((∪ₗ'-1-cool m (loop i) a)) ∙ sym (merid north)) ∙∙ rCancel (merid north)) i j

-- -- ∪ₗ'-cool : (n m : ℕ) → S₊ (suc n) →  S₊ (suc m) → S₊ (suc (suc (n + m)))
-- -- ∪ₗ'-cool-0 : (n m : ℕ) → (x : S₊ (suc n)) → ∪ₗ'-cool n m x (ptSn _) ≡ north
-- -- ∪ₗ'-cool-south : (n m : ℕ) → (x : S₊ (suc n)) → ∪ₗ'-cool n (suc m) x south ≡ north
-- -- ∪ₗ'-cool zero m x y = ∪ₗ'-1-cool m x y
-- -- ∪ₗ'-cool (suc n) zero north y = north
-- -- ∪ₗ'-cool (suc n) zero south y = north
-- -- ∪ₗ'-cool (suc n) zero (merid a i) base = north
-- -- ∪ₗ'-cool (suc n) zero (merid a i) (loop i₁) =
-- --   ∪ₗ'-1-cool (suc (n + zero))
-- --        (loop i) ((sym (∪ₗ'-cool-0 n zero a)
-- --     ∙∙ (λ i₁ → ∪ₗ'-cool n _ a (loop i₁))
-- --     ∙∙ ∪ₗ'-cool-0 n zero a) i₁)
-- -- ∪ₗ'-cool (suc n) (suc m) north y = north
-- -- ∪ₗ'-cool (suc n) (suc m) south y = north
-- -- ∪ₗ'-cool (suc n) (suc m) (merid a i) north = north
-- -- ∪ₗ'-cool (suc n) (suc m) (merid a i) south = north
-- -- ∪ₗ'-cool (suc n) (suc m) (merid a i) (merid b j) =
-- --   ∪ₗ'-1-cool (suc (n + suc m)) (loop i)
-- --     ((sym (∪ₗ'-cool-0 n (suc m) a) ∙∙ (λ i → ∪ₗ'-cool n _ a (merid b i)) ∙∙ ∪ₗ'-cool-south n m a) j)
-- -- ∪ₗ'-cool-0 zero zero base = refl
-- -- ∪ₗ'-cool-0 zero zero (loop i) = refl
-- -- ∪ₗ'-cool-0 (suc n) zero north = refl
-- -- ∪ₗ'-cool-0 (suc n) zero south = refl
-- -- ∪ₗ'-cool-0 (suc n) zero (merid a i) = refl
-- -- ∪ₗ'-cool-0 zero (suc m) base = refl
-- -- ∪ₗ'-cool-0 zero (suc m) (loop i) = refl
-- -- ∪ₗ'-cool-0 (suc n) (suc m) north = refl
-- -- ∪ₗ'-cool-0 (suc n) (suc m) south = refl
-- -- ∪ₗ'-cool-0 (suc n) (suc m) (merid a i) = refl
-- -- ∪ₗ'-cool-south zero m base = refl
-- -- ∪ₗ'-cool-south zero m (loop i) = refl
-- -- ∪ₗ'-cool-south (suc n) m north = refl
-- -- ∪ₗ'-cool-south (suc n) m south = refl
-- -- ∪ₗ'-cool-south (suc n) m (merid a i) = refl

-- -- ∪-uncool : (n m : ℕ) → S₊ (suc n) → S₊ (suc m) → coHomK (suc n +' suc m)
-- -- ∪-uncool zero m base y = 0ₖ _
-- -- ∪-uncool zero m (loop i) y = Kn→ΩKn+1 _ ∣ y ∣ i
-- -- ∪-uncool (suc n) m north y = 0ₖ _
-- -- ∪-uncool (suc n) m south y = 0ₖ _
-- -- ∪-uncool (suc n) m (merid a i) y = Kn→ΩKn+1 _ (∪-uncool n m a y) i

-- -- pre-cup : (n m : ℕ) → S₊ (suc n) → S₊ (suc m) → S₊ (suc n +' suc m)
-- -- pre-cup-id : (m : ℕ) (b : _) → pre-cup zero m base b ≡ north
-- -- pre-cup-id-silly : (n m : ℕ) (a : _) → pre-cup n (suc m) a north ≡ north
-- -- pre-cup-id-silly-south : (n m : ℕ) (a : _) → pre-cup n (suc m) a south ≡ north
-- -- pre-cup n zero x base = north
-- -- pre-cup zero zero base (loop i) = north
-- -- pre-cup zero zero (loop i) (loop j) =
-- --   (sym (rCancel (merid base)) ∙∙ cong (λ x → merid x ∙ sym (merid base)) loop ∙∙ rCancel (merid base)) j i
-- -- pre-cup (suc n) zero north (loop i) = north
-- -- pre-cup (suc n) zero south (loop i) = north
-- -- pre-cup (suc n) zero (merid a i) (loop j) =
-- --   (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north)) (cong (pre-cup n zero a) loop) ∙∙ rCancel (merid north)) j i
-- -- pre-cup n (suc m) x north = north
-- -- pre-cup n (suc m) x south = north
-- -- pre-cup zero (suc m) base (merid b j) = north
-- -- pre-cup zero (suc m) (loop i) (merid b j) =
-- --      (sym (rCancel (merid north))
-- --   ∙∙ cong (λ x → merid x ∙ sym (merid north))
-- --        (merid b ∙ sym (merid (ptSn _)))
-- --   ∙∙ rCancel (merid north)) j i
-- -- pre-cup (suc n) (suc m) north (merid b j) = north
-- -- pre-cup (suc n) (suc m) south (merid b j) = north
-- -- pre-cup (suc n) (suc m) (merid a i) (merid b j) =
-- --   (sym (rCancel (merid north))
-- --   ∙∙ cong (λ x → merid x ∙ sym (merid north))
-- --           (sym (pre-cup-id-silly n m a)
-- --         ∙∙ cong (pre-cup n (suc m) a) (merid b)
-- --         ∙∙ pre-cup-id-silly-south n m a)
-- --   ∙∙ rCancel (merid north)) j i
-- -- pre-cup-id zero base = refl
-- -- pre-cup-id zero (loop i) = refl
-- -- pre-cup-id (suc m) north = refl
-- -- pre-cup-id (suc m) south = refl
-- -- pre-cup-id (suc m) (merid a i) = refl
-- -- pre-cup-id-silly n m a = refl
-- -- pre-cup-id-silly-south n m a = refl

-- -- pre-cup-lId : (n m : ℕ) (y : _) → pre-cup n m (ptSn _) y ≡ ptSn _
-- -- pre-cup-lId n zero base = refl
-- -- pre-cup-lId zero zero (loop i) = refl
-- -- pre-cup-lId (suc n) zero (loop i) = refl
-- -- pre-cup-lId n (suc m) north = refl
-- -- pre-cup-lId n (suc m) south = refl
-- -- pre-cup-lId zero (suc m) (merid a i) = refl
-- -- pre-cup-lId (suc n) (suc m) (merid a i) = refl

-- -- cup∙ : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m)))
-- -- cup∙ n m = trRec (isOfHLevel↑∙ (suc n) m)
-- --                  λ x → (λ y → elim-snd n m y .fst x) , elim-snd∙ n m x
-- --   where
-- --   elim-snd : (n m : ℕ) → coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (n + m)))
-- --   elim-snd n m =
-- --     trRec (subst (isOfHLevel (3 + m))
-- --             (λ i → (S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (+-comm m n i)))))
-- --             (isOfHLevel↑∙' (suc m) n))
-- --           λ y → (λ x → ∣ pre-cup n m x y ∣) , cong ∣_∣ₕ (pre-cup-lId n m y)

-- --   elim-snd∙ : (n m : ℕ) (x : _) → elim-snd n m (snd (coHomK-ptd (suc m))) .fst x ≡ 0ₖ _
-- --   elim-snd∙ n zero x = refl
-- --   elim-snd∙ n (suc m) x = refl

-- -- cup' : (n m : ℕ) → coHomK (suc n) → coHomK (suc m) → coHomK (suc (suc (n + m)))
-- -- cup' n m x = cup∙ n m x .fst

-- -- open import Cubical.Data.Nat.Order

-- -- cupCommTyp : (n m : ℕ) (p : _) (q : _) (a : _) (b : _) → Type
-- -- cupCommTyp n m p q a b =
-- --   (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡ (-ₖ-gen (suc n) (suc m) p q) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ))

-- -- -- (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡ (-ₖ-gen (suc n) (suc m) p q) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ))
-- -- cupInduction : (zero-zero : (a b : S¹) → cupCommTyp zero zero (inr tt) (inr tt) a b)
-- --             → (suc-zero : ((n : ℕ) (p : _) → (indₗ : (m : ℕ) → m < n → (q : _) (a : _) (b : _) → cupCommTyp m zero q (inr tt) a b)
-- --                                             → (indᵣ : (m : ℕ) → m < n → (q : _) (a : _) (b : _) → cupCommTyp zero m (inr tt) q b a)
-- --                                             → ((P : _) (q : _ ) → cong (indₗ zero P q base) loop ≡ refl)
-- --                                             → ((P : _) (q : _ ) → cong (λ x → indₗ zero P q x base) loop ≡ refl)
-- --                                             → ((n : ℕ) (P : _) (q : _ ) → cong (indₗ (suc n) P q north) loop ≡ refl)
-- --                                             → (((n : ℕ) (P : _) (q : _ ) → cong (indₗ (suc n) P q south) loop ≡ refl))
-- --                                             → ((n : ℕ) (P : _) (q : _ ) (a : _) → cong (λ z → indₗ (suc n) P q z base) (merid a)
-- --                                                                                   ≡ cong (λ z → indₗ (suc n) P q z base) (merid (ptSn _)))
-- --                                             → (a : _) (b : _) → cupCommTyp (suc n) zero p (inr tt) a b))
-- --             → (suc-suc : (n m : ℕ) (p : _) (q : _)
-- --               → (indₗ : (a : _) (b : _) (p : _) (q : _) → cupCommTyp n (suc m) p q a b)
-- --               → (indᵣ : (a : _) (b : _) (p : _)(q : _) → cupCommTyp (suc n) m p q a b)
-- --               → (ind-mid : (a : _) (b : _) (p : _)(q : _) → cupCommTyp n m p q a b)
-- --               → (a : _) (b : _) → cupCommTyp (suc n) (suc m) p q a b)
-- --             → (k : ℕ)
-- --             → ((n m : ℕ) (terminate : n + m ≡ k) (p : _) (q : _) (a : _) (b : _) → cupCommTyp n m p q a b)
-- -- cupInduction zero-zero suc-zero suc-suc k zero m term p q a b = {!!}
-- -- cupInduction zero-zero suc-zero suc-suc k (suc n) zero term p q north base = refl
-- -- cupInduction zero-zero suc-zero suc-suc k (suc n) zero term p q south base = refl
-- -- cupInduction zero-zero suc-zero suc-suc k (suc n) zero term p q (merid a i) base = refl
-- -- cupInduction zero-zero suc-zero suc-suc k (suc n) zero term p q north (loop i) = refl
-- -- cupInduction zero-zero suc-zero suc-suc k (suc n) zero term p q south (loop i) = refl
-- -- cupInduction zero-zero suc-zero suc-suc k (suc n) zero term p q (merid a i₁) (loop i) = {!!}
-- -- cupInduction zero-zero suc-zero suc-suc k (suc n) (suc m) term p q north b = {!!}
-- -- cupInduction zero-zero suc-zero suc-suc k (suc n) (suc m) term p q south b = {!!}
-- -- cupInduction zero-zero suc-zero suc-suc k (suc n) (suc m) term p q (merid a i) b = {!!}

-- -- cup∙≡ : (n m : ℕ) (x : coHomK (suc n)) → cup∙ n m x ≡ ⌣ₖ∙ (suc n) (suc m) x
-- -- cup∙≡ n m =
-- --   trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevel↑∙ (suc n) m) _ _)
-- --     λ a → →∙Homogeneous≡ (isHomogeneousKn _) (funExt λ x → funExt⁻ (cong fst (⌣ₖ≡cup'' n m x)) a)
-- --   where
-- --   ⌣ₖ' : (n m : ℕ) → coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc n +' suc m)
-- --   fst (⌣ₖ' n m y) x = _⌣ₖ_ {n = suc n} {m = suc m} ∣ x ∣ₕ y
-- --   snd (⌣ₖ' n m y) = 0ₖ-⌣ₖ (suc n) _ y

-- --   cup'' : (n m : ℕ) → coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc n +' suc m)
-- --   cup'' n m = trRec (subst (isOfHLevel (3 + m))
-- --             (λ i → (S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (+-comm m n i)))))
-- --             (isOfHLevel↑∙' (suc m) n))
-- --               λ y → (λ x → ∣ pre-cup n m x y ∣) , cong ∣_∣ₕ (pre-cup-lId n m y)

-- --   ⌣ₖ≡cup'' : (n m : ℕ) (y : _) → cup'' n m y ≡ ⌣ₖ' n m y
-- --   ⌣ₖ≡cup'' n m =
-- --     trElim (λ _ → isOfHLevelPath (3 + m) (subst (isOfHLevel (3 + m))
-- --             (λ i → (S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (+-comm m n i)))))
-- --             (isOfHLevel↑∙' (suc m) n)) _ _)
-- --       λ b → →∙Homogeneous≡ (isHomogeneousKn _)
-- --       (funExt λ a → main n m a b)
-- --     where
-- --     main : (n m : ℕ) (a : _) (b : _) → cup'' n m ∣ b ∣ .fst a ≡ (_⌣ₖ_ {n = suc n} {m = suc m} ∣ a ∣ ∣ b ∣)
-- --     main zero zero base base = refl
-- --     main zero zero (loop i) base k = Kn→ΩKn+10ₖ 1 (~ k) i
-- --     main zero zero base (loop i) k = ∣ north ∣
-- --     main zero zero (loop i) (loop j) k =
-- --       hcomp (λ r → λ {(i = i0) → 0ₖ 2
-- --                      ; (i = i1) → 0ₖ 2
-- --                      ; (j = i0) → ∣ rCancel (merid base) (~ k ∧ r) i ∣
-- --                      ; (j = i1) → ∣ rCancel (merid base) (~ k ∧ r) i ∣
-- --                      ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel (merid base)))
-- --                                     (cong (λ x → merid x ∙ sym (merid base)) loop)
-- --                                     (rCancel (merid base)) r j i ∣
-- --                      ; (k = i1) → _⌣ₖ_ {n = 1} {m = 1} ∣ loop i ∣ ∣ loop j ∣})
-- --             (_⌣ₖ_ {n = 1} {m = 1} ∣ loop i ∣ ∣ loop j ∣)
-- --     main zero (suc m) base north = refl
-- --     main zero (suc m) base south = refl
-- --     main zero (suc m) base (merid a i) = refl
-- --     main zero (suc m) (loop i) north k = Kn→ΩKn+10ₖ _ (~ k) i
-- --     main zero (suc m) (loop i) south k =
-- --       ∣ ((λ i → merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north)) ∙ rCancel (merid north)) (~ k) i ∣ₕ
-- --     main zero (suc m) (loop i) (merid b j) k =
-- --       hcomp (λ r → λ {(i = i0) → ∣ north ∣
-- --                      ; (i = i1) → ∣ north ∣
-- --                      ; (j = i0) → ∣ rCancel (merid north) (~ k ∧ r) i ∣ₕ
-- --                      ; (j = i1) → ∣ compPath-filler ((λ i → merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north))) (rCancel (merid north)) r (~ k) i ∣ₕ
-- --                      ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _)) (cong (λ x → merid x ∙ sym (merid north))
-- --                                       (merid b ∙ sym (merid (ptSn _)))) (rCancel _) r j i ∣ₕ
-- --                      ; (k = i1) → _⌣ₖ_ {n = 1} {m = suc (suc m)} ∣ loop i ∣ ∣ merid b j ∣ₕ})
-- --             (Kn→ΩKn+1 _ (hcomp (λ r → λ { (j = i0) → ∣ merid b j ∣ₕ
-- --                                           ; (j = i1) → ∣ merid (ptSn (suc m)) (~ r ∨ k) ∣
-- --                                           ; (k = i0) → ∣ compPath-filler (merid b) (sym (merid (ptSn (suc m)))) r j ∣
-- --                                           ; (k = i1) → ∣ (merid b) j ∣})
-- --                                 ∣ merid b j ∣) i)
-- --     main (suc n) zero north base = refl
-- --     main (suc n) zero north (loop i) = refl
-- --     main (suc n) zero south base = refl
-- --     main (suc n) zero south (loop i) = refl
-- --     main (suc n) zero (merid a i) base k = (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 _) (main n zero a base)) k i
-- --     main (suc n) zero (merid a i) (loop j) k =
-- --       hcomp (λ r → λ {(i = i0) → ∣ north ∣
-- --                      ; (i = i1) → ∣ north ∣
-- --                      ; (j = i0) → compPath-filler' (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 _) (main n zero a base)) r k i
-- --                      ; (j = i1) → compPath-filler' (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 _) (main n zero a base)) r k i
-- --                      ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _)) (cong (λ x → merid x ∙ sym (merid north)) (cong (pre-cup n zero a) loop) ) (rCancel _) r j i ∣ₕ
-- --                      ; (k = i1) → _⌣ₖ_ {n = suc (suc n)} {m = suc zero} ∣ merid a i ∣ ∣ loop j ∣})
-- --             (Kn→ΩKn+1 _ (main n zero a (loop j) k) i)
-- --     main (suc n) (suc m) north north = refl
-- --     main (suc n) (suc m) south north = refl
-- --     main (suc zero) (suc m) (merid a i) north k =
-- --       (cong (Kn→ΩKn+1 (suc (suc (suc m)))) (sym (main zero (suc m) a north)) ∙ Kn→ΩKn+10ₖ _) (~ k) i
-- --     main (suc (suc n)) (suc m) (merid a i) north k =
-- --       (cong (Kn→ΩKn+1 (suc (suc (suc n + suc m)))) (sym (main (suc n) (suc m) a north)) ∙ Kn→ΩKn+10ₖ _) (~ k) i
-- --     main (suc n) (suc m) north south = refl
-- --     main (suc n) (suc m) south south = refl
-- --     main (suc zero) (suc m) (merid a i) south k =
-- --       (cong (Kn→ΩKn+1 (suc (suc (suc m)))) (sym (main zero (suc m) a south)) ∙ Kn→ΩKn+10ₖ _) (~ k) i
-- --     main (suc (suc n)) (suc m) (merid a i) south k =
-- --       (cong (Kn→ΩKn+1 (suc (suc (suc n + suc m)))) (sym (main (suc n) (suc m) a south)) ∙ Kn→ΩKn+10ₖ _) (~ k) i
-- --     main (suc n) (suc m) north (merid b j) = refl
-- --     main (suc n) (suc m) south (merid b j) = refl
-- --     main (suc zero) (suc m) (merid a i) (merid b j) k =
-- --       hcomp (λ r → λ { (i = i0) → ∣ north ∣
-- --                       ; (i = i1) → ∣ north ∣
-- --                       ; (k = i0) →
-- --                         ∣ doubleCompPath-filler (sym (rCancel (merid north))) (
-- --                           cong (λ x → merid x ∙ sym (merid north))
-- --           (rUnit (cong (pre-cup 0 (suc m) a) (merid b)) r))
-- --           (rCancel (merid north)) r j i ∣
-- --                       ; (k = i1) → _⌣ₖ_ {n = 2} {m = 2 + m} ∣ merid a i ∣ ∣ merid b j ∣})
-- --             (Kn→ΩKn+1 _ (main zero (suc m) a (merid b j) k) i)
-- --     main (suc (suc n)) (suc m) (merid a i) (merid b j) k =
-- --       hcomp (λ r → λ { (i = i0) → ∣ north ∣
-- --                       ; (i = i1) → ∣ north ∣
-- --                       ; (k = i0) →
-- --                         ∣ doubleCompPath-filler (sym (rCancel (merid north))) (
-- --                           cong (λ x → merid x ∙ sym (merid north))
-- --           (rUnit (cong (pre-cup (suc n) (suc m) a) (merid b)) r))
-- --           (rCancel (merid north)) r j i ∣
-- --                       ; (k = i1) → _⌣ₖ_ {n = 3 + n} {m = 2 + m} ∣ merid a i ∣ ∣ merid b j ∣})
-- --             (Kn→ΩKn+1 _ (main (suc n) (suc m) a (merid b j) k) i)

-- -- natTranspLem : ∀ {A : ℕ → Type} (n m : ℕ) (a : A n) (B : (n : ℕ) → Type)
-- --   (f : (n : ℕ) → (a : A n) → B n) (p : n ≡ m) 
-- --   → f m (subst A p a) ≡ subst B p (f n a)
-- -- natTranspLem {A = A} n m a B f = J (λ m p → f m (subst A p a) ≡ subst B p (f n a)) (cong (f n) (substRefl a) ∙ sym (substRefl (f n a)))


-- -- cup'-lUnit : (n m : ℕ) (x : coHomK (suc m)) → cup' n m (0ₖ _) x  ≡ 0ₖ _
-- -- cup'-lUnit n m x = funExt⁻ (cong fst (cup∙≡ n m (0ₖ (suc n)))) x ∙ 0ₖ-⌣ₖ (suc n) (suc m) x

-- -- subst-help : (n m : ℕ) → subst coHomK (+'-comm (suc m) (suc n))
-- --       (0ₖ (suc (suc (m + n))))
-- --       ≡ snd (coHomK-ptd (suc (suc (n + m))))
-- -- subst-help zero zero = refl
-- -- subst-help zero (suc m) = refl
-- -- subst-help (suc n) zero = refl
-- -- subst-help (suc n) (suc m) = refl

-- -- cup'-anti-comm' :
-- --   (n m : ℕ) (p : _) (q : _) (x : coHomK (suc n))
-- --     → cup∙ n m x ≡ ((λ y → (-ₖ-gen (suc n) (suc m) p q) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n y x)))
-- --                    , cong ((-ₖ-gen (suc n) (suc m) p q) ∘ (subst coHomK (+'-comm (suc m) (suc n)))) (cup'-lUnit m n x)
-- --                           ∙ cong (-ₖ-gen (suc n) (suc m) p q) (subst-help n m))
-- -- cup'-anti-comm' = {!!}
-- --   where
-- --   open import Cubical.Foundations.Transport

-- --   lem₂ : {k : ℕ} (n m : ℕ) (x : _) (y : _)
-- --       → (p : refl {x = 0ₖ (suc (suc k))}
-- --             ≡ refl {x = 0ₖ (suc (suc k))})
-- --                   → cong (cong (-ₖ-gen n m (inr x) (inr y))) p
-- --                   ≡ sym p
-- --   lem₂ n m x y p = {!!}
-- --   {-
-- --          rUnit _
-- --       ∙∙ (λ k → (λ i → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y refl (i ∧ k))
-- --               ∙∙ cong (λ z → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y z k) p
-- --               ∙∙ λ i → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y refl (~ i ∧ k))
-- --       ∙∙ (λ k → transportRefl (λ _ _ → ∣ north ∣) k
-- --               ∙∙ cong sym p
-- --               ∙∙ sym (transportRefl (λ _ _ → ∣ north ∣) k))
-- --       ∙∙ sym (rUnit _)
-- --       ∙∙ sym (inst4 p) -}


-- --   module _ (n m : ℕ) where
-- --     t₁ = transport (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}
-- --                          ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)})

-- --     t₂ = transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}
-- --                          ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
    
-- --     t₃ = transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}
-- --                          ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})

-- --     t₄ = transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))}
-- --                          ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) })

-- --   t : (n m : ℕ) → _ → _
-- --   t n m = transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}
-- --                           ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
-- --          ∘ (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}
-- --                             ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}))
-- --           ∘ (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))}
-- --                             ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) }))


-- --   final : (n m : ℕ) (p : _) → (t₁ n m ∘ t n m) p
-- --           ≡ p
-- --   final n m p =
-- --        sym (substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) (cong suc ((+'-comm (suc (suc n)) (suc m)))) (+'-comm (suc (suc m)) (suc (suc n)))
-- --             (((transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}))
-- --           ∘ (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))}))) p))
-- --     ∙∙ sym (substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) (cong (suc ∘ suc) (+'-comm (suc m) (suc n)))
-- --                            (((λ i₁ → suc (+'-comm (suc (suc n)) (suc m) i₁)) ∙ +'-comm (suc (suc m)) (suc (suc n))))
-- --                            (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))}) p))
-- --     ∙∙ sym (substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) (cong suc (+'-comm (suc n) (suc (suc m))))
-- --                            (((λ i₁ → suc (suc (+'-comm (suc m) (suc n) i₁)))
-- --                            ∙ (λ i₁ → suc (+'-comm (suc (suc n)) (suc m) i₁))
-- --                            ∙ +'-comm (suc (suc m)) (suc (suc n)))) p)
-- --     ∙∙ cong (λ x → subst (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) x p) (isSetℕ _ _ _ refl)
-- --     ∙∙ transportRefl p



-- --   lem₈ : (n m : ℕ) → (p : refl {x = 0ₖ _} ≡ refl {x = 0ₖ _})
-- --       → cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))) p
-- --        ≡ transport (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}
-- --                          ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}) p
-- --   lem₈ n m p k = transp (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) (i ∨ ~ k))}
-- --                            ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) (i ∨ ~ k))}) (~ k)
-- --                       ((λ i j → transp (λ i → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (i ∧ ~ k))) k (p i j)))

-- --   lUnit₁ : (n m : ℕ) (a : _) → cup' (suc n) m ∣ north ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
-- --   lUnit₁ n zero base = refl
-- --   lUnit₁ n zero (loop i) = refl
-- --   lUnit₁ n (suc m) north = refl
-- --   lUnit₁ n (suc m) south = refl
-- --   lUnit₁ n (suc m) (merid a i) = refl

-- --   lUnit₂ : (n m : ℕ) (a : _) → cup' (suc n) m ∣ south ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
-- --   lUnit₂ n zero base = refl
-- --   lUnit₂ n zero (loop i) = refl
-- --   lUnit₂ n (suc m) north = refl
-- --   lUnit₂ n (suc m) south = refl
-- --   lUnit₂ n (suc m) (merid a i) = refl

-- --   lUnit₁' : (n : ℕ) (a : _) → cup' zero n ∣ base ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
-- --   lUnit₁' zero base = refl
-- --   lUnit₁' zero (loop i) = refl
-- --   lUnit₁' (suc n) north = refl
-- --   lUnit₁' (suc n) south = refl
-- --   lUnit₁' (suc n) (merid a i) = refl

-- --   lUnit₂' : (n : ℕ) (a : _) → cup' zero n ∣ base ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
-- --   lUnit₂' zero base = refl
-- --   lUnit₂' zero (loop i) = refl
-- --   lUnit₂' (suc n) north = refl
-- --   lUnit₂' (suc n) south = refl
-- --   lUnit₂' (suc n) (merid a i) = refl

-- --   open import Cubical.Data.Bool
-- --   ptSn' : (n : ℕ) → S₊ n
-- --   ptSn' zero = false
-- --   ptSn' (suc zero) = base
-- --   ptSn' (suc (suc n)) = south

-- --   lUnit!₁ : (n m : ℕ) (a : _) → cup' n m ∣ ptSn _ ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
-- --   lUnit!₁ zero m a = lUnit₁' _ a
-- --   lUnit!₁ (suc n) m a = lUnit₁ _ _ a

-- --   lUnit!₂ : (n m : ℕ) (a : _) → cup' n m ∣ ptSn' _ ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
-- --   lUnit!₂ zero m a = lUnit₁' _ a
-- --   lUnit!₂ (suc n) m a = lUnit₂ _ _ a

-- --   lem₁ : (n m : ℕ) (a : _) (b : _) → (λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)
-- --        ≡ (sym (Kn→ΩKn+10ₖ _)
-- --        ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
-- --        ∙∙ Kn→ΩKn+10ₖ _)
-- --   lem₁ n m a b =
-- --        (λ k i j → ∣ (sym (rCancel _) ∙∙ cong (λ x → merid x ∙ sym (merid north)) (rUnit (λ i → pre-cup m (suc n) b (merid a i)) (~ k)) ∙∙ rCancel _) i j ∣ₕ)
-- --      ∙ (λ k i j → hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) r j ∣
-- --                                  ; (i = i1) → ∣ rCancel (merid north) r j ∣
-- --                                  ; (j = i0) → ∣ north ∣
-- --                                  ; (j = i1) → ∣ north ∣
-- --                                  ; (k = i0) → ∣ doubleCompPath-filler
-- --                                                   (sym (rCancel _))
-- --                                                   (cong (λ x → merid x ∙ sym (merid north))
-- --                                                   ((λ i → pre-cup m (suc n) b (merid a i)))) (rCancel _) r i j ∣ₕ})
-- --                          (Kn→ΩKn+1 _ (cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣) j))

-- --   lem₃ : (n m : ℕ) (a : _) (b : _)
-- --       → (sym (lUnit₁ n m b) ∙∙ ((λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) ∙∙ lUnit₂ n m b)
-- --        ≡ Kn→ΩKn+1 _ (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ)
-- --   lem₃ n zero a base = sym (rUnit refl) ∙ sym (Kn→ΩKn+10ₖ _)
-- --   lem₃ n zero a (loop i) k =
-- --     hcomp (λ r → λ {(i = i0) → compPath-filler' (sym (rUnit refl)) (sym (Kn→ΩKn+10ₖ _)) r k
-- --                    ; (i = i1) → compPath-filler' (sym (rUnit refl)) (sym (Kn→ΩKn+10ₖ _)) r k
-- --                    ; (k = i0) → rUnit (λ i₂ → cup' (suc n) zero ∣ merid a i₂ ∣ₕ ∣ loop i ∣ₕ) r
-- --                    ; (k = i1) → Kn→ΩKn+1 (suc (suc (n + zero)))
-- --                                   (cup' n zero ∣ a ∣ₕ ∣ loop i ∣ₕ) })
-- --           λ j → hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
-- --                       ; (i = i1) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
-- --                       ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
-- --                                       (cong (λ x → merid x ∙ sym (merid north)) ((λ i → pre-cup n zero a (loop i))))
-- --                                       (rCancel _) r i j ∣ₕ
-- --                       ; (k = i1) → Kn→ΩKn+1 (suc (suc (n + zero)))
-- --                                        (cup' n zero ∣ a ∣ₕ ∣ loop i ∣ₕ) j
-- --                       ; (j = i0) → ∣ north ∣
-- --                       ; (j = i1) → ∣ north ∣})
-- --                  (Kn→ΩKn+1 _ (cup' n zero ∣ a ∣ₕ ∣ loop i ∣ₕ) j)
-- --   lem₃ n (suc m) a north = sym (rUnit refl) ∙ sym (Kn→ΩKn+10ₖ _)
-- --   lem₃ n (suc m) a south = sym (rUnit refl) ∙ sym (Kn→ΩKn+10ₖ _)
-- --   lem₃ n (suc m) a (merid b i) k =
-- --     hcomp (λ r → λ {(i = i0) → compPath-filler' (sym (rUnit refl)) (sym (Kn→ΩKn+10ₖ _)) r k
-- --                    ; (i = i1) → compPath-filler' (sym (rUnit refl)) (sym (Kn→ΩKn+10ₖ _)) r k
-- --                    ; (k = i0) → rUnit (λ i₂ → cup' (suc n) (suc m) ∣ merid a i₂ ∣ₕ ∣ merid b i ∣ₕ) r
-- --                    ; (k = i1) → Kn→ΩKn+1 (suc (suc (n + suc m)))
-- --                                   (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ)})
-- --       (λ j → hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
-- --                       ; (i = i1) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
-- --                       ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
-- --                                       (cong (λ x → merid x ∙ sym (merid north)) (rUnit (λ i → pre-cup n (suc m) a (merid b i)) r))
-- --                                       (rCancel _) r i j ∣ₕ
-- --                       ; (k = i1) → Kn→ΩKn+1 (suc (suc (n + suc m)))
-- --                                        (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ) j
-- --                       ; (j = i0) → ∣ north ∣
-- --                       ; (j = i1) → ∣ north ∣})
-- --              (Kn→ΩKn+1 (suc (suc (n + suc m)))
-- --                                        (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ) j))

-- --   lem₃-take2 : (n : ℕ) (a : _) → (sym (lUnit₁' n a)
-- --                                 ∙∙ (λ j → cup' zero n ∣ loop j ∣ ∣ a ∣)
-- --                                 ∙∙ lUnit₁' n a) ≡ Kn→ΩKn+1 _ ∣ a ∣
-- --   lem₃-take2 zero base = sym (rUnit _) ∙ sym (Kn→ΩKn+10ₖ _)
-- --   lem₃-take2 zero (loop i) k j = 
-- --     hcomp (λ r → λ {(i = i0) → compPath-filler' (sym (rUnit _)) (sym (Kn→ΩKn+10ₖ _)) r k j
-- --                    ; (i = i1) → compPath-filler' (sym (rUnit _)) (sym (Kn→ΩKn+10ₖ _)) r k j
-- --                    ; (k = i0) → rUnit (λ j₁ → cup' zero zero ∣ loop j₁ ∣ ∣ loop i ∣) r j
-- --                    ; (k = i1) → Kn→ΩKn+1 1 ∣ loop i ∣ j
-- --                    ; (j = i0) → ∣ north ∣
-- --                    ; (j = i1) → ∣ north ∣})
-- --           (hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid base) (r ∧ ~ k) j ∣ₕ
-- --                    ; (i = i1) → ∣ rCancel (merid base) (r ∧ ~ k) j ∣ₕ
-- --                    ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel (merid base)))
-- --                                                         (λ i → merid (loop i) ∙ sym (merid base))
-- --                                                         (rCancel (merid base)) r i j ∣ₕ
-- --                    ; (k = i1) → Kn→ΩKn+1 1 ∣ loop i ∣ j
-- --                    ; (j = i0) → ∣ north ∣
-- --                    ; (j = i1) → ∣ north ∣})
-- --                  (Kn→ΩKn+1 1 ∣ loop i ∣ j))
-- --   lem₃-take2 (suc n) north = sym (rUnit _) ∙ sym (Kn→ΩKn+10ₖ _)
-- --   lem₃-take2 (suc n) south = sym (rUnit _) ∙ (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc n))) (cong ∣_∣ₕ (merid (ptSn (suc n)))))
-- --   lem₃-take2 (suc n) (merid a i) k j =
-- --     hcomp (λ r → λ {(i = i0) → compPath-filler' (sym (rUnit _)) (sym (Kn→ΩKn+10ₖ _)) r k j
-- --                    ; (i = i1) → compPath-filler' (sym (rUnit _)) (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc n))) (cong ∣_∣ₕ (merid (ptSn (suc n))))) r k j
-- --                    ; (k = i0) → rUnit (λ j₁ → cup' zero (suc n) ∣ loop j₁ ∣ ∣ merid a i ∣) r j
-- --                    ; (k = i1) → Kn→ΩKn+1 (suc (suc n)) ∣ merid a i ∣ j
-- --                    ; (j = i0) → ∣ north ∣
-- --                    ; (j = i1) → ∣ north ∣})
-- --            (hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
-- --                            ; (i = i1) → compPath-filler' (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 (suc (suc n))) (cong ∣_∣ₕ (merid (ptSn (suc n))))) r k j
-- --                            ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel (merid north)))
-- --                                                                 (λ i → merid ((merid a ∙ sym (merid (ptSn _))) i) ∙ sym (merid north))
-- --                                                                 (rCancel (merid north)) r i j ∣ₕ
-- --                            ; (k = i1) → Kn→ΩKn+1 (suc (suc n)) ∣ merid a i ∣ j
-- --                            ; (j = i0) → ∣ north ∣
-- --                            ; (j = i1) → ∣ north ∣})
-- --                   ∣ (merid (compPath-filler (merid a) (sym (merid (ptSn _))) (~ k) i) ∙ sym (merid (ptSn _))) j ∣ₕ)

-- --   pullOut : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : _) → Kn→ΩKn+1 (suc k) (-ₖ-gen n m p q x) ≡ cong (-ₖ-gen n m p q) (Kn→ΩKn+1 (suc k) x)
-- --   pullOut n m p q x = {!!}

-- --   extraP : (n : ℕ) → subst coHomK (+'-comm 1 (suc n)) (0ₖ (suc (suc n))) ≡ 0ₖ _
-- --   extraP zero = refl
-- --   extraP (suc n) = refl

-- --   stupid : (n : ℕ) (a : S₊ (suc n)) → (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)} ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)}))
-- --                 (λ i j → ∣ (sym (rCancel _) ∙∙ cong (λ x → merid x ∙ sym (merid north)) (merid a ∙ sym (merid (ptSn _))) ∙∙ rCancel _) j i ∣ₕ)
-- --         ≡ flipSquare (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north))
-- --                      (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                        (merid a ∙ sym (merid (ptSn _))))
-- --                      ∙∙ rCancel (merid north)))
-- --   stupid  n a = {!!}
-- --   stupid2 : (n : ℕ)(a : S₊ (suc (suc n))) → transport (λ i₁ →
-- --          0ₖ (+'-comm 1 (suc (suc n)) i₁) ≡ 0ₖ (+'-comm 1 (suc (suc n)) i₁))
-- --       (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣)
-- --       ≡
-- --       cong ∣_∣ₕ
-- --       (transport
-- --        (λ i₁ →
-- --           Path (S₊ (suc (suc (+-comm (suc n) 0 (~ i₁))))) north north)
-- --        (merid a ∙ sym (merid (ptSn (suc (suc n))))))
-- --   stupid2 = {!!}
-- -- {-
-- --          (λ k → (transport (λ i → refl {x = 0ₖ (isSetℕ _ _ (+'-comm 1 (suc (suc n))) (cong (suc ∘ suc ∘ suc) (sym (+-comm n 0))) k i)}
-- --                                   ≡ refl {x = 0ₖ (isSetℕ _ _ (+'-comm 1 (suc (suc n))) (cong (suc ∘ suc ∘ suc) (sym (+-comm n 0))) k i)}))
-- --                 (λ i j → ∣ (sym (rCancel _)
-- --                          ∙∙ cong (λ x → merid x ∙ sym (merid north)) (merid a ∙ sym (merid (ptSn _)))
-- --                          ∙∙ rCancel _) j i ∣ₕ))
-- --        ∙ sym (natTranspLem {A = λ n → Path (S₊ (suc (suc n))) north north} _ _
-- --                (merid a ∙ sym (merid (ptSn _))) (λ n → refl {x = 0ₖ (3 + n)} ≡ refl {x = 0ₖ (3 + n)})
-- --                (λ _ x → flipSquare (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north)) x
-- --                      ∙∙ rCancel (merid north)))) (sym (+-comm n 0))) -}

-- --   mainₗ' : (n : ℕ) (p : _) (q : _) (a : _) (b : S¹) →
-- --       (cup' n zero ∣ a ∣ₕ ∣ b ∣ₕ)
-- --     ≡ (-ₖ-gen (suc n) (suc zero) p q)
-- --        (subst coHomK (+'-comm (suc zero) (suc n))
-- --         (cup' zero n ∣ b ∣ₕ ∣ a ∣ₕ))
-- --   mainₗ' n p q a base =
-- --        cong (-ₖ-gen (suc n) 1 p q) (sym (extraP n))
-- --      ∙ cong (-ₖ-gen (suc n) (suc zero) p q ∘
-- --         (subst coHomK (+'-comm 1 (suc n))))
-- --           (sym (lUnit₁' _ a))
-- --   mainₗ' zero p q base (loop i) = refl ∙ refl
-- --   mainₗ' zero p q (loop i₁) (loop i) = {!!}
-- --   mainₗ' (suc n) p q north (loop i) = refl ∙ refl
-- --   mainₗ' (suc n) p q south (loop i) = refl ∙ refl
-- --   mainₗ' (suc n) p q (merid a i) (loop j) k =
-- --     hcomp (λ r → λ {(i = i0) → compPath-filler' refl {!cong (-ₖ-gen (suc (suc n)) (suc zero) p q ∘
-- --                                                               (subst coHomK (+'-comm 1 (suc n))))
-- --                                                                 (sym (lUnit₁' _ a))!} r k j
-- --                    ; (i = i1) → {!!}
-- --                    ; (j = i0) → {!!}
-- --                    ; (j = i1) → {!!}
-- --                    ; (k = i0) → {!!}
-- --                    ; (k = i1) → {!!}})
-- --           {!!}
-- --     {-
-- --     i = i0 ⊢ mainₗ' (suc n) p q north (loop j) k
-- -- i = i1 ⊢ mainₗ' (suc n) p q south (loop j) k
-- -- j = i0 ⊢ mainₗ' (suc n) p q (merid a i) base k
-- -- j = i1 ⊢ mainₗ' (suc n) p q (merid a i) base k
-- -- k = i0 ⊢ cup' (suc n) zero ∣ merid a i ∣ₕ ∣ loop j ∣ₕ
-- -- k = i1 ⊢ -ₖ-gen (suc (suc n)) 1 p q
-- --          (subst coHomK (+'-comm 1 (suc (suc n)))
-- --           (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ))
-- --     -}
  
-- -- {-
-- --   mainₗ : (n : ℕ) (p : _) (q : _) (a : _) (b : S¹) →
-- --       (cup' n zero ∣ a ∣ₕ ∣ b ∣ₕ)
-- --     ≡ (-ₖ-gen (suc n) (suc zero) p q)
-- --        (subst coHomK (+'-comm (suc zero) (suc n))
-- --         (cup' zero n ∣ b ∣ₕ ∣ a ∣ₕ))
-- --   mainₗ zero p q a b = {!refl!}
-- --   mainₗ (suc n) p q north base = refl
-- --   mainₗ (suc n) p q north (loop i) = refl
-- --   mainₗ (suc n) p q south base = refl
-- --   mainₗ (suc n) p q south (loop i) = refl
-- --   mainₗ (suc n) p q (merid a i) base k =
-- --     (sym (Kn→ΩKn+10ₖ _)
-- --     ∙∙ cong (Kn→ΩKn+1 _) ((mainₗ n (evenOrOdd (suc n)) (inr tt) a base
-- --                         ∙ (λ i → -ₖ-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt) (subst coHomK (+'-comm 1 (suc n)) (lUnit₁' _ a i))))
-- --                         ∙ λ i → -ₖ-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt) (extraP n i))
-- --     ∙∙ (Kn→ΩKn+10ₖ _)) k i
-- --   {-
-- --        (sym (Kn→ΩKn+10ₖ _)
-- --     ∙∙ cong (Kn→ΩKn+1 _) ((mainₗ n (evenOrOdd (suc n)) (inr tt) a base
-- --                         ∙ (λ i → -ₖ-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt) (subst coHomK (+'-comm 1 (suc n)) (lUnit₁' _ a i))))
-- --                         ∙ λ i → -ₖ-gen (suc n) 1 (evenOrOdd (suc n)) (inr tt) (extraP n i))
-- --     ∙∙ (Kn→ΩKn+10ₖ _)) k i -}
-- --   mainₗ (suc zero) p q (merid a i) (loop j) k = {!!}
-- --   mainₗ (suc (suc n)) p q (merid a i) (loop j) k =
-- --    hcomp (λ r → λ {(i = i0) → ∣ north ∣
-- --                    ; (i = i1) → ∣ north ∣
-- --                    ; (j = i0) → (sym (Kn→ΩKn+10ₖ _)
-- --                                ∙∙ cong (Kn→ΩKn+1 _) (compPath-filler ((mainₗ (suc n) (evenOrOdd (suc (suc n))) (inr tt) a base
-- --                                 ∙ (λ i → -ₖ-gen (suc (suc n)) 1 (evenOrOdd (suc (suc n))) (inr tt) (subst coHomK (+'-comm 1 (suc (suc n))) (lUnit₁' _ a i))))) refl r)
-- --                                ∙∙ (Kn→ΩKn+10ₖ _)) k i
-- --                    ; (j = i1) → (sym (Kn→ΩKn+10ₖ _)
-- --                                ∙∙ cong (Kn→ΩKn+1 _) (compPath-filler ((mainₗ (suc n) (evenOrOdd (suc (suc n))) (inr tt) a base
-- --                                 ∙ (λ i → -ₖ-gen (suc (suc n)) 1 (evenOrOdd (suc (suc n))) (inr tt) (subst coHomK (+'-comm 1 (suc (suc n))) (lUnit₁' _ a i))))) refl r)
-- --                                ∙∙ (Kn→ΩKn+10ₖ _)) k i
-- --                    ; (k = i0) → inst _ (λ i j → cup' _ _ ∣ merid a j ∣ₕ ∣ loop i ∣ₕ) r i j
-- --                    ; (k = i1) → h (~ r) i j})
-- --           (hcomp (λ r → λ {(i = i0) → {!!}
-- --                    ; (i = i1) → {!!}
-- --                    ; (j = i0) → {!!}
-- --                    ; (j = i1) → {!!}
-- --                    ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel (merid north))) (λ i → merid (pre-cup _ _  a (loop i)) ∙ sym (merid north)) (rCancel (merid north)) r (~ i) j ∣ₕ
-- --                    ; (k = i1) →  doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 _)
-- --                                     (mainₗ _(evenOrOdd n) _ a base ∙∙ cong (-ₖ-gen (suc (suc n)) 1 (evenOrOdd n) q ∘ 
-- --                                                     (subst coHomK (+'-comm 1 (suc (suc n)))))
-- --                                             ((λ i → cup' zero (suc n) ∣ loop (~ i) ∣ ∣ a ∣))
-- --                               ∙∙ sym (mainₗ _(evenOrOdd n) _ a base))) (Kn→ΩKn+10ₖ _) r i j })
-- --                  {!!})
-- --    where
-- --    h : Path (typ ((Ω^ 2) (coHomK-ptd _))) (λ i j → (-ₖ-gen (suc (suc (suc n))) 1 p q
-- --                                   (subst coHomK (+'-comm 1 (suc (suc (suc n))))
-- --                                     (cup' zero (suc (suc n)) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ))))
-- --             ((sym (Kn→ΩKn+10ₖ _)
-- --             ∙∙ cong (Kn→ΩKn+1 _)
-- --                   (mainₗ _(evenOrOdd n) _ a base ∙∙ cong (-ₖ-gen (suc (suc n)) 1 (evenOrOdd n) q ∘ 
-- --                                   (subst coHomK (+'-comm 1 (suc (suc n)))))
-- --                           ((λ i → cup' zero (suc n) ∣ loop (~ i) ∣ ∣ a ∣))
-- --             ∙∙ sym (mainₗ _(evenOrOdd n) _ a base))
-- --             ∙∙ Kn→ΩKn+10ₖ _))
-- --    h = {!!} -}
-- -- {-
-- --     hcomp (λ r → λ {(i = i0) → ∣ north ∣
-- --                    ; (i = i1) → ∣ north ∣
-- --                    ; (j = i0) → (sym (Kn→ΩKn+10ₖ _)
-- --                                ∙∙ cong (Kn→ΩKn+1 _) (compPath-filler ((mainₗ (suc n) (evenOrOdd (suc (suc n))) (inr tt) a base
-- --                                 ∙ (λ i → -ₖ-gen (suc (suc n)) 1 (evenOrOdd (suc (suc n))) (inr tt) (subst coHomK (+'-comm 1 (suc (suc n))) (lUnit₁' _ a i))))) refl r)
-- --                                ∙∙ (Kn→ΩKn+10ₖ _)) k i
-- --                    ; (j = i1) → (sym (Kn→ΩKn+10ₖ _)
-- --                                ∙∙ cong (Kn→ΩKn+1 _) (compPath-filler ((mainₗ (suc n) (evenOrOdd (suc (suc n))) (inr tt) a base
-- --                                 ∙ (λ i → -ₖ-gen (suc (suc n)) 1 (evenOrOdd (suc (suc n))) (inr tt) (subst coHomK (+'-comm 1 (suc (suc n))) (lUnit₁' _ a i))))) refl r)
-- --                                ∙∙ (Kn→ΩKn+10ₖ _)) k i
-- --                    ; (k = i0) → subst coHomK (+'-comm (suc zero) (suc (suc (suc n))))
-- --                                       (-ₖ-gen (suc (suc (suc n))) 1 p q
-- --                                         (cup' zero (suc (suc n)) ∣ loop j ∣ {!∣ merid a i ∣!}))
-- --                    ; (k = i1) → {!!}})
-- --           {!!}
-- --           -}
-- --   {-
-- --     hcomp (λ r → λ {(i = i0) → {!!}
-- --                    ; (i = i1) → {!!}
-- --                    ; (j = i0) → {!!}
-- --                    ; (j = i1) → {!!}
-- --                    ; (k = i0) → subst coHomK (+'-comm (suc zero) (suc (suc n)))
-- --                                       {!lem₃!}
-- --                    ; (k = i1) → {!!}})
-- --           {!!}
-- --     where
-- --     ind : (p : _) (q : _) (a : _) (b : _) → (cup' n zero ∣ a ∣ₕ ∣ b ∣ₕ)
-- --                                            ≡ (-ₖ-gen (suc n) (suc zero) p q)
-- --                                               (subst coHomK (+'-comm (suc zero) (suc n))
-- --                                                (cup' zero n ∣ b ∣ₕ ∣ a ∣ₕ))
-- --     ind = mainₗ n

-- --     help : Path (typ ((Ω^ 2) (coHomK-ptd _)))
-- --                 (λ i j → (cup' (suc n) zero ∣ merid a i ∣ₕ ∣ loop j ∣ₕ))
-- --                 (λ i j → (subst coHomK (+'-comm (suc zero) (suc (suc n)))
-- --                              (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))
-- --     help = {!!}
-- --         ∙∙ {!!}
-- --         ∙∙ {!!}
-- --         ∙∙ {!!}
-- --         ∙∙ {!!}

-- -- -}
-- -- {-
-- --   mainₗ : (n : ℕ) (p : _) (q : _) (a : _) (b : S¹) →
-- --       (cup' n zero ∣ a ∣ₕ ∣ b ∣ₕ)
-- --     ≡ (-ₖ-gen (suc n) (suc zero) p q)
-- --        (subst coHomK (+'-comm (suc zero) (suc n))
-- --         (cup' zero n ∣ b ∣ₕ ∣ a ∣ₕ))
-- --   coolPath : (n : ℕ) (p : is-even n) (a : _) → Path (Path (coHomK (suc (suc (n + zero)))) _ _)
-- --                      (λ i →  ∣ pre-cup n zero a (loop i) ∣ₕ)
-- --                       (sym (extraP n) ∙∙ (λ i → (subst coHomK (+'-comm (suc zero) (suc n)))
-- --                           ((sym (lUnit₁' n a)
-- --                        ∙∙ (λ j → cup' zero n ∣ loop (~ j) ∣ ∣ a ∣)
-- --                        ∙∙ lUnit₁' n a) i)) ∙∙ extraP n)
-- --   coolPath₂ : (n : ℕ) (a : _) →
-- --                     ((sym (extraP n) ∙∙ (λ i → (subst coHomK (+'-comm (suc zero) (suc n)))
-- --                           ((sym (lUnit₁' n a)
-- --                        ∙∙ (λ j → cup' zero n ∣ loop (~ j) ∣ ∣ a ∣)
-- --                        ∙∙ lUnit₁' n a) i)) ∙∙ extraP n))
-- --                   ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc n) i)
-- --                                     ≡ 0ₖ (+'-comm (suc zero) (suc n) i))
-- --                               (sym (lUnit₁' n a)
-- --                             ∙∙ (λ j → cup' zero n ∣ loop (~ j) ∣ ∣ a ∣)
-- --                             ∙∙ lUnit₁' n a)
-- --   coolPath₃ : (n : ℕ) (x : is-even n) (a : _) → (Path (Path (coHomK (suc (suc ((suc n) + zero)))) _ _)
-- --                    (λ i → ∣ (pre-cup (suc n) zero a (loop i)) ∣ₕ)
-- --                     (λ i → (subst coHomK (+'-comm (suc zero) (suc (suc n))))
-- --                       ((sym (lUnit₁' (suc n) a)
-- --                    ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣)
-- --                    ∙∙ lUnit₁' (suc n) a) i)))
-- --                    × ((λ i → (subst coHomK (+'-comm (suc zero) (suc (suc n))))
-- --                       ((sym (lUnit₁' (suc n) a)
-- --                    ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣)
-- --                    ∙∙ lUnit₁' (suc n) a) i))
-- --                 ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc (suc n)) i)
-- --                                   ≡ 0ₖ (+'-comm (suc zero) (suc (suc n)) i))
-- --                             (sym (lUnit₁' (suc n) a)
-- --                           ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣)
-- --                           ∙∙ lUnit₁' (suc n) a))
-- --   mainₗ (suc n) (inl x) (inr tt) north base = refl
-- --   mainₗ (suc n) (inl x) (inr tt) north (loop i) = refl
-- --   mainₗ (suc n) (inl x) (inr tt) south base = refl
-- --   mainₗ (suc n) (inl x) (inr tt) south (loop i) = refl
-- --   mainₗ (suc n) (inl x) (inr tt) (merid a i) base = refl
-- --   mainₗ (suc n) (inl x) (inr tt) (merid a i) (loop j) k = help k i j
-- --     where
-- --     lem1 : (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)}
-- --                             ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)}))
-- --                 (λ i j → ∣ (sym (rCancel _)
-- --                          ∙∙ (λ z →  merid ((merid a ∙ sym (merid (ptSn _))) z) ∙ sym (merid north))
-- --                          ∙∙ rCancel _) i j ∣ₕ)
-- --         ≡ λ i j → ∣  (sym (rCancel (merid north))
-- --                    ∙∙ (λ i → merid (((subst (λ n₁ → Path (S₊ (suc (suc n₁))) north north)
-- --                           (sym (+-comm n 0)) (merid a ∙ sym (merid (ptSn (suc n)))))) i)  ∙ sym (merid north))
-- --                    ∙∙ rCancel (merid north)) i j ∣ₕ
-- --     lem1 = 
-- --          (λ k → (transport (λ i → refl {x = 0ₖ (isSetℕ _ _ (+'-comm 1 (suc (suc n))) (cong (suc ∘ suc ∘ suc) (sym (+-comm n 0))) k i)}
-- --                                   ≡ refl {x = 0ₖ (isSetℕ _ _ (+'-comm 1 (suc (suc n))) (cong (suc ∘ suc ∘ suc) (sym (+-comm n 0))) k i)}))
-- --                 (λ i j → ∣ (sym (rCancel _)
-- --                          ∙∙ (λ z →  merid ((merid a ∙ sym (merid (ptSn _))) z) ∙ sym (merid north))
-- --                          ∙∙ rCancel _) i j ∣ₕ))
-- --        ∙ sym (natTranspLem {A = λ n → Path (S₊ (suc (suc n))) north north} _ _
-- --                (merid a ∙ sym (merid (ptSn _))) (λ n → refl {x = 0ₖ (3 + n)} ≡ refl {x = 0ₖ (3 + n)})
-- --                (λ _ x → (λ i j → ∣ (sym (rCancel (merid north)) ∙∙ (λ i → merid (x i) ∙ sym (merid north))
-- --                      ∙∙ rCancel (merid north)) i j ∣ )) (sym (+-comm n 0)))


-- --     coolLem : Path (Path (coHomK (suc (suc (n + zero)))) _ _)
-- --                    (λ i → ∣ pre-cup n zero a (loop i) ∣ₕ)
-- --                    (λ i → ∣ (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                                                                          (sym (merid a ∙ sym (merid (ptSn _))))) i ∣ₕ)
-- --     coolLem =
-- --          coolPath n x a
-- --       ∙∙ coolPath₂ n a
-- --       ∙∙ (λ k → (transport (λ i₁ → 0ₖ (+'-comm 1 (suc n) i₁) ≡ 0ₖ (+'-comm 1 (suc n) i₁))
-- --                            (sym (lem₃-take2 n a k))))
-- --        ∙ sym lem2
-- --       where
-- --       lem2 : (λ i → ∣ (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                                                                          (sym (merid a ∙ sym (merid (ptSn _))))) i ∣ₕ)
-- --            ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc n) i)
-- --                                   ≡ 0ₖ (+'-comm (suc zero) (suc n) i))
-- --                        (sym (Kn→ΩKn+1 _ ∣ a ∣))
-- --       lem2 = natTranspLem {A = λ n → Path (S₊ (suc (suc n))) north north} _ _
-- --                           (sym (merid a ∙ sym (merid (ptSn _)))) (λ n → 0ₖ (suc (suc n)) ≡ 0ₖ (suc (suc n)))
-- --                           (λ _ p i → ∣ p i ∣ₕ) (sym (+-comm n 0))
-- --            ∙ λ k → transport (λ i → 0ₖ (isSetℕ _ _ (cong (suc ∘ suc) (sym (+-comm n zero))) (+'-comm (suc zero) (suc n)) k i)
-- --                                     ≡ 0ₖ (isSetℕ _ _ (cong (suc ∘ suc) (sym (+-comm n zero))) (+'-comm (suc zero) (suc n)) k i))
-- --                               (sym (Kn→ΩKn+1 _ ∣ a ∣))           

-- --     lem2 : Path (typ ((Ω^ 2) (coHomK-ptd _)))
-- --       (λ i j → cup' (suc n) zero ∣ (merid a i) ∣ₕ ∣ (loop j) ∣ₕ)
-- --       (λ i j → ∣ (sym (rCancel (merid north))
-- --               ∙∙ (λ z → merid (((sym (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                        (merid a ∙ sym (merid (ptSn _)))))) z) ∙ sym (merid north))
-- --                      ∙∙ rCancel (merid north)) j i ∣ₕ)
-- --     lem2 k i j =
-- --       hcomp (λ r → λ { (i = i0) → ∣ north ∣ₕ
-- --                       ; (i = i1) → ∣ north ∣ₕ
-- --                       ; (j = i0) → ∣ rCancel (merid north) r i ∣ₕ
-- --                       ; (j = i1) → ∣ rCancel (merid north) r i ∣ₕ
-- --                       ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
-- --                                                            (λ i → merid (pre-cup n zero a (loop i)) ∙ sym (merid north))
-- --                                                            (rCancel _) r j i ∣ₕ
-- --                       ; (k = i1) → ∣ doubleCompPath-filler (sym (rCancel _))
-- --                                                            ((λ i → merid ((((transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                                                                          (sym (merid a ∙ sym (merid (ptSn _))))))) i) ∙ sym (merid north)))
-- --                                                            (rCancel _) r j i ∣ₕ})
-- --             (Kn→ΩKn+1 _ (coolLem k j) i)

-- --     help : Path (typ ((Ω^ 2) (coHomK-ptd _)))
-- --                 (λ i j → cup' (suc n) zero ∣ (merid a i) ∣ₕ ∣ (loop j) ∣ₕ)
-- --                 (λ i j → -ₖ-gen (suc (suc n)) 1 (inl x) (inr tt)
-- --                   (subst coHomK (+'-comm 1 (suc (suc n)))
-- --                     (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))
-- --     help =
-- --          (lem2
-- --         ∙ sym (inst _ (λ i j → ∣ (sym (rCancel (merid north))
-- --                               ∙∙ (λ z → merid (((transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                                    (merid a ∙ sym (merid (ptSn _))))) z) ∙ sym (merid north))
-- --                      ∙∙ rCancel (merid north)) (~ i) j ∣ₕ))
-- --         ∙ sym lem1)
-- --       ∙∙ (λ k → transp (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) (i ∨ k))}
-- --                               ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) (i ∨ k))}) k
-- --                         (λ i j → transp (λ i → coHomK (+'-comm 1 (suc (suc n)) (i ∧ k))) (~ k)
-- --                           (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))
-- --       ∙∙ λ k i j →
-- --               -ₖ-gen-inl-left (suc (suc n)) 1 x (inr tt)
-- --                  (subst coHomK (+'-comm 1 (suc (suc n)))
-- --                   (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)) (~ k)

-- --   mainₗ zero (inr x) (inr tt) base base = refl
-- --   mainₗ zero (inr x) (inr tt) base (loop i) = refl
-- --   mainₗ zero (inr x) (inr tt) (loop i) base = refl
-- --   mainₗ zero (inr x) (inr tt) (loop i) (loop j) = {!!}
-- --   mainₗ (suc n) (inr x) (inr tt) north base = refl
-- --   mainₗ (suc n) (inr x) (inr tt) south base = refl
-- --   mainₗ (suc n) (inr x) (inr tt) (merid a i) base = refl
-- --   mainₗ (suc n) (inr x) (inr tt) north (loop i) = refl
-- --   mainₗ (suc n) (inr x) (inr tt) south (loop i) = refl
-- --   mainₗ (suc zero) (inr ()) (inr tt) (merid a i) (loop j) k
-- --   mainₗ (suc (suc n)) (inr x) (inr tt) (merid a i) (loop j) k = help k i j
-- --     where
-- --     lem1 : (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) i)} ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) i)}))
-- --                 (λ i j → ∣ (sym (rCancel _) ∙∙ (λ z → merid ((merid a ∙ sym (merid (ptSn _))) z) ∙ sym (merid north)) ∙∙ rCancel _) j i ∣ₕ)
-- --         ≡ flipSquare (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north))
-- --                      (transport (λ i → Path (S₊ ((suc (suc (+-comm (suc n) 0 (~ i)))))) north north)
-- --                        (merid a ∙ sym (merid (ptSn _))))
-- --                      ∙∙ rCancel (merid north)))
-- --     lem1 = {!!}

-- --     coolLem : Path (Path (coHomK (suc (suc ((suc n) + zero)))) _ _)
-- --                    (λ i → ∣ pre-cup (suc n) zero a (loop i) ∣ₕ)
-- --                    (λ i → ∣ (transport (λ i → Path (S₊ ((suc (suc (+-comm (suc n) 0 (~ i)))))) north north)
-- --                                                                          (merid a ∙ sym (merid (ptSn _)))) i ∣ₕ)
-- --     coolLem =
-- --         coolPath₃ n x a .fst
-- --       ∙∙ coolPath₃ n x a .snd
-- --       ∙∙ (cong (transport (λ i₁ → 0ₖ (+'-comm 1 (suc (suc n)) i₁) ≡ 0ₖ (+'-comm 1 (suc (suc n)) i₁)))
-- --               (lem₃-take2 _ a)
-- --         ∙ stupid2 n a)
-- -- {-
-- -- Path (typ ((Ω^ 2) (coHomK-ptd _)))
-- --       (λ i j → cup' (suc n) zero ∣ (merid a i) ∣ₕ ∣ (loop j) ∣ₕ)
-- --       (λ i j → ∣ (sym (rCancel (merid north))
-- --               ∙∙ (λ z → merid (((sym (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                        (merid a ∙ sym (merid (ptSn _)))))) z) ∙ sym (merid north))
-- --                      ∙∙ rCancel (merid north)) j i ∣ₕ) -}

-- --     lem2 :  Path (typ ((Ω^ 2) (coHomK-ptd _)))
-- --       (λ i j → cup' (suc (suc n)) zero ∣ (merid a i) ∣ₕ ∣ (loop j) ∣ₕ)
-- --            (λ i j →  ∣ (sym (rCancel (merid north))
-- --                     ∙∙ (λ z → merid (((transport (λ i → Path (S₊ ((suc (suc (+-comm (suc n) 0 (~ i)))))) north north)
-- --                        (merid a ∙ sym (merid (ptSn _))))) z) ∙ sym (merid north))
-- --                      ∙∙ rCancel (merid north)) j i ∣ₕ)
-- --     lem2 k i j =
-- --       hcomp (λ r → λ { (i = i0) → ∣ north ∣ₕ
-- --                       ; (i = i1) → ∣ north ∣ₕ
-- --                       ; (j = i0) → ∣ rCancel (merid north) r i ∣ₕ
-- --                       ; (j = i1) → ∣ rCancel (merid north) r i ∣ₕ
-- --                       ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
-- --                                                            (λ i → merid (pre-cup (suc n) zero a (loop i)) ∙ sym (merid north))
-- --                                                            (rCancel _) r j i ∣ₕ
-- --                       ; (k = i1) → ∣ doubleCompPath-filler (sym (rCancel _))
-- --                                                            (λ i → merid ((((transport (λ i → Path (S₊ ((suc (suc (+-comm (suc n) 0 (~ i)))))) north north)
-- --                                                                          (merid a ∙ sym (merid (ptSn _)))))) i) ∙ sym (merid north))
-- --                                                            (rCancel _) r j i ∣ₕ})
-- --             (Kn→ΩKn+1 _ (coolLem k j) i)

-- --     help : Path (typ ((Ω^ 2) (coHomK-ptd _)))
-- --              (λ i j → cup' (suc (suc n)) zero ∣ (merid a i) ∣ₕ ∣ (loop j) ∣ₕ)
-- --           (λ i j → -ₖ-gen (suc (suc (suc n))) 1 (inr x) (inr tt)
-- --       (subst coHomK (+'-comm 1 (suc (suc (suc n))))
-- --        (cup' zero (suc (suc n)) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))
-- --     help =
-- --         lem2
-- --       ∙ (sym lem1
-- --       ∙∙ cong (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) i)}
-- --                                ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) i)}))
-- --                 (λ _ i j → ∣ (sym (rCancel _) ∙∙ (λ i → merid (((merid a ∙ sym (merid (ptSn _)))) i) ∙ sym (merid north)) ∙∙ rCancel _) j i ∣ₕ)
-- --       ∙∙ ((λ k → transp (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) (i ∨ k))} ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) (i ∨ k))}) k
-- --                     λ i j → transp (λ i → coHomK (+'-comm 1 (suc (suc (suc n))) (i ∧ k))) (~ k)
-- --                         (cup' zero (suc (suc n)) ∣ loop i ∣ₕ ∣ merid a j ∣ₕ)))
-- --       ∙∙ sym (inst _ (λ i j →  (subst coHomK (+'-comm 1 (suc (suc (suc n))))
-- --                         (cup' zero (suc (suc n)) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ))))
-- --       ∙∙ sym (lem₂ (suc (suc (suc n))) 1 x tt (λ i j →  (subst coHomK (+'-comm 1 (suc (suc (suc n))))
-- --                 (cup' zero (suc (suc n)) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))))

-- --   coolPath zero p = λ { base → pre-cool-S¹ i0 ; (loop i) → pre-cool-S¹ i}
-- --     where
-- --     pre-cool-S¹ : (i : I)
-- --         → Path (Path (coHomK (suc (suc (zero + zero)))) _ _)
-- --                    (λ j → ∣ pre-cup zero zero (loop i) (loop j) ∣ₕ)
-- --                    (sym (extraP zero) ∙∙ (λ z → (subst coHomK (+'-comm (suc zero) (suc zero)))
-- --                       ((sym (lUnit₁' zero (loop i))
-- --                    ∙∙ (λ j → cup' zero zero ∣ loop (~ j) ∣ ∣ (loop i) ∣)
-- --                    ∙∙ lUnit₁' zero (loop i)) z)) ∙∙ extraP zero)
-- --     pre-cool-S¹ i =
-- --          rUnit _
-- --       ∙∙ (λ k → refl
-- --               ∙∙ (λ j → mainₗ zero (inr tt) (inr tt) (loop i) (loop j) k)
-- --               ∙∙ refl)
-- --       ∙∙ (λ k → refl
-- --               ∙∙ (cong-₂ (suc zero) 1 tt tt
-- --                            (cong (subst coHomK (+'-comm 1 (suc zero)))
-- --                             (λ j → cup' zero zero ∣ loop j ∣ₕ ∣ loop i ∣ₕ)) k)
-- --               ∙∙ refl)
-- --       ∙∙ rUnit _
-- --       ∙∙ refl
-- --   coolPath (suc n) p = {!!}
-- --     where
-- --     pre-cool-merid : (i : I) (a : _)
-- --         → Path (Path (coHomK (suc (suc ((suc n) + zero)))) _ _)
-- --                    (λ j → ∣ (pre-cup (suc n) zero (merid a i)) (loop j) ∣ₕ)
-- --                    (sym (extraP (suc n)) ∙∙ (λ z →  (subst coHomK (+'-comm (suc zero) (suc (suc n))))
-- --                       ((sym (lUnit₁' (suc n) (merid a i))
-- --                    ∙∙ (λ j → cup' zero (suc n) ∣ loop (~ j) ∣ ∣ (merid a i) ∣)
-- --                    ∙∙ lUnit₁' (suc n) (merid a i)) z)) ∙∙ extraP (suc n))
-- --     pre-cool-merid i a =
-- --          rUnit _
-- --       ∙∙ (λ k → refl
-- --               ∙∙ (λ j → mainₗ (suc n) (inr p) (inr tt) (merid a i) (loop j) k)
-- --               ∙∙ refl)
-- --       ∙∙ (λ k → refl
-- --               ∙∙ (cong-₂ (suc (suc n)) 1 p tt
-- --                            (cong (subst coHomK (+'-comm 1 (suc (suc n))))
-- --                             (λ j → cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)) k)
-- --               ∙∙ refl)
-- --       ∙∙ rUnit _
-- --       ∙∙ refl

-- --   coolPath₂ zero a =
-- --            sym (rUnit _)
-- --         ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc zero) (suc zero) (i ∨ ~ k))
-- --                                  ≡ 0ₖ (+'-comm (suc zero) (suc zero) (i ∨ ~ k))) (~ k)
-- --                            λ j → transp (λ i → coHomK (+'-comm (suc zero) (suc zero) (i ∧ ~ k))) k
-- --                                          ((sym (lUnit₁' zero a)
-- --                           ∙∙ (λ j → cup' zero zero ∣ loop (~ j) ∣ ∣ a ∣)
-- --                           ∙∙ lUnit₁' zero a) j)
-- --   coolPath₂ (suc n) a =
-- --     sym (rUnit _) ∙
-- --      λ k → transp (λ i → 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ ~ k))
-- --                                  ≡ 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ ~ k))) (~ k)
-- --                            λ j → transp (λ i → coHomK (+'-comm (suc zero) (suc (suc n)) (i ∧ ~ k))) k
-- --                                          ((sym (lUnit₁' (suc n) a)
-- --                           ∙∙ (λ j → cup' zero (suc n) ∣ loop (~ j) ∣ ∣ a ∣)
-- --                           ∙∙ lUnit₁' (suc n) a) j)
-- --   fst (coolPath₃ n x a) = pre-cool a
-- --     where
-- --     pre-cool-merid : (i : I) (a : _)
-- --       → (λ j → ∣ (pre-cup (suc n) zero (merid a i)) (loop j) ∣ₕ) ≡
-- --       (λ z → (subst coHomK (+'-comm 1 (suc (suc n))))
-- --       ((sym (lUnit₁' (suc n) (merid a i)) ∙∙
-- --        (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ merid a i ∣) ∙∙ lUnit₁' (suc n) (merid a i)) z))
-- --     pre-cool-merid i a =
-- --          (λ k j → mainₗ (suc n) (inl x) (inr tt) (merid a i) (loop j) k)
-- --       ∙∙ (λ k j → -ₖ-gen-inl-left (suc (suc (suc (suc n)))) 1 x (inr tt)
-- --                     ((subst coHomK (+'-comm 1 (suc (suc n)))
-- --                       ((cup' zero (suc n) ∣ loop j ∣ ∣ merid a i ∣)))) k)
-- --       ∙∙ (λ k j → (subst coHomK (+'-comm 1 (suc (suc n)))
-- --                     (rUnit (λ j₁ → cup' zero (suc n) ∣ loop j₁ ∣ ∣ merid a i ∣) k j)))


-- --     pre-cool : (a : _) → Path (Path _ _ _)
-- --       (λ i → ∣ pre-cup (suc n) zero a (loop i) ∣ₕ)
-- --       (λ i →  (subst coHomK (+'-comm 1 (suc (suc n))))
-- --       ((sym (lUnit₁' (suc n) a) ∙∙
-- --        (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣) ∙∙ lUnit₁' (suc n) a) i))
-- --     pre-cool north = pre-cool-merid i0 (ptSn (suc n))
-- --     pre-cool south = pre-cool-merid i1 (ptSn (suc n))
-- --     pre-cool (merid a i) = pre-cool-merid i a
-- --   snd (coolPath₃ n x a) = λ k → transp (λ i → 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ ~ k))
-- --                                  ≡ 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ ~ k))) (~ k)
-- --                            λ j → transp (λ i → coHomK (+'-comm (suc zero) (suc (suc n)) (i ∧ ~ k))) k
-- --                                          ((sym (lUnit₁' (suc n) a)
-- --                           ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣)
-- --                           ∙∙ lUnit₁' (suc n) a) j)

-- -- -}

-- -- {-
-- --   mainₗ : (n : ℕ) (p : _) (q : _) (a : _) (b : S¹) →
-- --       (cup' n zero ∣ a ∣ₕ ∣ b ∣ₕ)
-- --     ≡ (-ₖ-gen (suc n) (suc zero) p q)
-- --        (subst coHomK (+'-comm (suc zero) (suc n))
-- --         (cup' zero n ∣ b ∣ₕ ∣ a ∣ₕ))
-- --   mainₗ zero p q = {!!}
-- --     where
-- --     proof : (a : S₊ 1) (b : S¹) →
-- --       cup' zero zero ∣ a ∣ₕ ∣ b ∣ₕ ≡
-- --       -ₖ-gen 1 1 p q
-- --       (subst coHomK (+'-comm 1 1) (cup' zero zero ∣ b ∣ₕ ∣ a ∣ₕ))
-- --     proof = {!!}
-- --   mainₗ (suc n) p q = {!!}
-- --     where
-- --     proof : (a : S₊ (suc (suc n))) (b : S¹) →
-- --       cup' (suc n) zero ∣ a ∣ₕ ∣ b ∣ₕ ≡
-- --       -ₖ-gen (suc (suc n)) 1 p q
-- --       (subst coHomK (+'-comm 1 (suc (suc n)))
-- --        (cup' zero (suc n) ∣ b ∣ₕ ∣ a ∣ₕ))
-- --     proof a b = {!!} -}
-- -- {-

-- --   mainₗ : (n : ℕ) (p : _) (q : _) (a : _) (b : S¹) →
-- --       (cup' n zero ∣ a ∣ₕ ∣ b ∣ₕ)
-- --     ≡ (-ₖ-gen (suc n) (suc zero) p q)
-- --        (subst coHomK (+'-comm (suc zero) (suc n))
-- --         (cup' zero n ∣ b ∣ₕ ∣ a ∣ₕ))
-- --   mainᵣ : (n : ℕ) (p : _) (q : _) (a : _) (b : _) →
-- --     (cup' zero n ∣ a ∣ₕ ∣ b ∣ₕ) ≡ (-ₖ-gen (suc zero) (suc n) q p) (subst coHomK (+'-comm (suc n) (suc zero)) (cup' n zero ∣ b ∣ₕ ∣ a ∣ₕ))
-- --   coolPath : (n : ℕ) (p : is-even n) (a : _) → Path (Path (coHomK (suc (suc (n + zero)))) _ _)
-- --                      (λ i →  ∣ pre-cup n zero a (loop i) ∣ₕ)
-- --                       (sym (extraP n) ∙∙ (λ i → (subst coHomK (+'-comm (suc zero) (suc n)))
-- --                           ((sym (lUnit₁' n a)
-- --                        ∙∙ (λ j → cup' zero n ∣ loop (~ j) ∣ ∣ a ∣)
-- --                        ∙∙ lUnit₁' n a) i)) ∙∙ extraP n)
-- --   coolPath₂ : (n : ℕ) (a : _) →
-- --                     ((sym (extraP n) ∙∙ (λ i → (subst coHomK (+'-comm (suc zero) (suc n)))
-- --                           ((sym (lUnit₁' n a)
-- --                        ∙∙ (λ j → cup' zero n ∣ loop (~ j) ∣ ∣ a ∣)
-- --                        ∙∙ lUnit₁' n a) i)) ∙∙ extraP n))
-- --                   ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc n) i)
-- --                                     ≡ 0ₖ (+'-comm (suc zero) (suc n) i))
-- --                               (sym (lUnit₁' n a)
-- --                             ∙∙ (λ j → cup' zero n ∣ loop (~ j) ∣ ∣ a ∣)
-- --                             ∙∙ lUnit₁' n a)
-- --   coolPath₃ : (n : ℕ) (x : is-even n) (a : _) → (Path (Path (coHomK (suc (suc ((suc n) + zero)))) _ _)
-- --                    (λ i → ∣ (pre-cup (suc n) zero a (loop i)) ∣ₕ)
-- --                     (λ i → (subst coHomK (+'-comm (suc zero) (suc (suc n))))
-- --                       ((sym (lUnit₁' (suc n) a)
-- --                    ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣)
-- --                    ∙∙ lUnit₁' (suc n) a) i)))
-- --                    × ((λ i → (subst coHomK (+'-comm (suc zero) (suc (suc n))))
-- --                       ((sym (lUnit₁' (suc n) a)
-- --                    ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣)
-- --                    ∙∙ lUnit₁' (suc n) a) i))
-- --                 ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc (suc n)) i)
-- --                                   ≡ 0ₖ (+'-comm (suc zero) (suc (suc n)) i))
-- --                             (sym (lUnit₁' (suc n) a)
-- --                           ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣)
-- --                           ∙∙ lUnit₁' (suc n) a))
-- --   mainₗ zero p q base base = refl
-- --   mainₗ zero p q base (loop i) = refl
-- --   mainₗ zero p q (loop i) base = refl
-- --   mainₗ zero p q (loop i) (loop i₁) = {!!}
-- --   mainₗ (suc n) p q north base = refl
-- --   mainₗ (suc n) p q north (loop i) = refl
-- --   mainₗ (suc n) p q south base = refl
-- --   mainₗ (suc n) p q south (loop i) = refl
-- --   mainₗ (suc n) p q (merid a i) base = refl
-- --   mainₗ (suc n) (inl x) (inr y) (merid a i) (loop j) k = help k i j
-- --     where
-- --     lem1 : (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)}
-- --                             ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)}))
-- --                 (λ i j → ∣ (sym (rCancel _)
-- --                          ∙∙ (λ z →  merid ((merid a ∙ sym (merid (ptSn _))) z) ∙ sym (merid north))
-- --                          ∙∙ rCancel _) i j ∣ₕ)
-- --         ≡ λ i j → ∣  (sym (rCancel (merid north))
-- --                    ∙∙ (λ i → merid (((subst (λ n₁ → Path (S₊ (suc (suc n₁))) north north)
-- --                           (sym (+-comm n 0)) (merid a ∙ sym (merid (ptSn (suc n)))))) i)  ∙ sym (merid north))
-- --                    ∙∙ rCancel (merid north)) i j ∣ₕ
-- --     lem1 = 
-- --          (λ k → (transport (λ i → refl {x = 0ₖ (isSetℕ _ _ (+'-comm 1 (suc (suc n))) (cong (suc ∘ suc ∘ suc) (sym (+-comm n 0))) k i)}
-- --                                   ≡ refl {x = 0ₖ (isSetℕ _ _ (+'-comm 1 (suc (suc n))) (cong (suc ∘ suc ∘ suc) (sym (+-comm n 0))) k i)}))
-- --                 (λ i j → ∣ (sym (rCancel _)
-- --                          ∙∙ (λ z →  merid ((merid a ∙ sym (merid (ptSn _))) z) ∙ sym (merid north))
-- --                          ∙∙ rCancel _) i j ∣ₕ))
-- --        ∙ sym (natTranspLem {A = λ n → Path (S₊ (suc (suc n))) north north} _ _
-- --                (merid a ∙ sym (merid (ptSn _))) (λ n → refl {x = 0ₖ (3 + n)} ≡ refl {x = 0ₖ (3 + n)})
-- --                (λ _ x → (λ i j → ∣ (sym (rCancel (merid north)) ∙∙ (λ i → merid (x i) ∙ sym (merid north))
-- --                      ∙∙ rCancel (merid north)) i j ∣ )) (sym (+-comm n 0)))


-- --     coolLem : Path (Path (coHomK (suc (suc (n + zero)))) _ _)
-- --                    (λ i → ∣ pre-cup n zero a (loop i) ∣ₕ)
-- --                    (λ i → ∣ (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                                                                          (sym (merid a ∙ sym (merid (ptSn _))))) i ∣ₕ)
-- --     coolLem =
-- --          coolPath n x a
-- --       ∙∙ coolPath₂ n a
-- --       ∙∙ (λ k → (transport (λ i₁ → 0ₖ (+'-comm 1 (suc n) i₁) ≡ 0ₖ (+'-comm 1 (suc n) i₁))
-- --                            (sym (lem₃-take2 n a k))))
-- --        ∙ sym lem2
-- --       where
-- --       lem2 : (λ i → ∣ (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                                                                          (sym (merid a ∙ sym (merid (ptSn _))))) i ∣ₕ)
-- --            ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc n) i)
-- --                                   ≡ 0ₖ (+'-comm (suc zero) (suc n) i))
-- --                        (sym (Kn→ΩKn+1 _ ∣ a ∣))
-- --       lem2 = natTranspLem {A = λ n → Path (S₊ (suc (suc n))) north north} _ _
-- --                           (sym (merid a ∙ sym (merid (ptSn _)))) (λ n → 0ₖ (suc (suc n)) ≡ 0ₖ (suc (suc n)))
-- --                           (λ _ p i → ∣ p i ∣ₕ) (sym (+-comm n 0))
-- --            ∙ λ k → transport (λ i → 0ₖ (isSetℕ _ _ (cong (suc ∘ suc) (sym (+-comm n zero))) (+'-comm (suc zero) (suc n)) k i)
-- --                                     ≡ 0ₖ (isSetℕ _ _ (cong (suc ∘ suc) (sym (+-comm n zero))) (+'-comm (suc zero) (suc n)) k i))
-- --                               (sym (Kn→ΩKn+1 _ ∣ a ∣))           

-- --     lem2 : Path (typ ((Ω^ 2) (coHomK-ptd _)))
-- --       (λ i j → cup' (suc n) zero ∣ (merid a i) ∣ₕ ∣ (loop j) ∣ₕ)
-- --       (λ i j → ∣ (sym (rCancel (merid north))
-- --               ∙∙ (λ z → merid (((sym (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                        (merid a ∙ sym (merid (ptSn _)))))) z) ∙ sym (merid north))
-- --                      ∙∙ rCancel (merid north)) j i ∣ₕ)
-- --     lem2 k i j =
-- --       hcomp (λ r → λ { (i = i0) → ∣ north ∣ₕ
-- --                       ; (i = i1) → ∣ north ∣ₕ
-- --                       ; (j = i0) → ∣ rCancel (merid north) r i ∣ₕ
-- --                       ; (j = i1) → ∣ rCancel (merid north) r i ∣ₕ
-- --                       ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
-- --                                                            (λ i → merid (pre-cup n zero a (loop i)) ∙ sym (merid north))
-- --                                                            (rCancel _) r j i ∣ₕ
-- --                       ; (k = i1) → ∣ doubleCompPath-filler (sym (rCancel _))
-- --                                                            ((λ i → merid ((((transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                                                                          (sym (merid a ∙ sym (merid (ptSn _))))))) i) ∙ sym (merid north)))
-- --                                                            (rCancel _) r j i ∣ₕ})
-- --             (Kn→ΩKn+1 _ (coolLem k j) i)

-- --     help : Path (typ ((Ω^ 2) (coHomK-ptd _)))
-- --                 (λ i j → cup' (suc n) zero ∣ (merid a i) ∣ₕ ∣ (loop j) ∣ₕ)
-- --                 (λ i j → -ₖ-gen (suc (suc n)) 1 (inl x) (inr tt)
-- --                   (subst coHomK (+'-comm 1 (suc (suc n)))
-- --                     (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))
-- --     help =
-- --          (lem2
-- --         ∙ sym (inst _ (λ i j → ∣ (sym (rCancel (merid north))
-- --                               ∙∙ (λ z → merid (((transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                                    (merid a ∙ sym (merid (ptSn _))))) z) ∙ sym (merid north))
-- --                      ∙∙ rCancel (merid north)) (~ i) j ∣ₕ))
-- --         ∙ sym lem1)
-- --       ∙∙ (λ k → transp (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) (i ∨ k))}
-- --                               ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) (i ∨ k))}) k
-- --                         (λ i j → transp (λ i → coHomK (+'-comm 1 (suc (suc n)) (i ∧ k))) (~ k)
-- --                           (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))
-- --       ∙∙ λ k i j →
-- --               -ₖ-gen-inl-left (suc (suc n)) 1 x (inr tt)
-- --                  (subst coHomK (+'-comm 1 (suc (suc n)))
-- --                   (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)) (~ k)
-- --   mainₗ (suc zero) (inr x) (inr y) (merid a i) (loop j) k = {!!}
-- --   mainₗ (suc (suc n)) (inr x) (inr y) (merid a i) (loop j) k = 
-- --         ((λ k i j → (hcomp (λ r → λ { (i = i0) → ∣ north ∣ₕ
-- --                       ; (i = i1) → ∣ north ∣ₕ
-- --                       ; (j = i0) → ∣ rCancel (merid north) r i ∣ₕ
-- --                       ; (j = i1) → ∣ rCancel (merid north) r i ∣ₕ
-- --                       ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
-- --                                                            (λ i → merid (pre-cup (suc n) zero a (loop i)) ∙ sym (merid north))
-- --                                                            (rCancel _) r j i ∣ₕ
-- --                       ; (k = i1) → ∣ doubleCompPath-filler (sym (rCancel _))
-- --                                                            (λ i → merid ((((transport (λ i → Path (S₊ ((suc (suc (+-comm (suc n) 0 (~ i)))))) north north)
-- --                                                                          (merid a ∙ sym (merid (ptSn _)))))) i) ∙ sym (merid north))
-- --                                                            (rCancel _) r j i ∣ₕ})
-- --             (Kn→ΩKn+1 _ ((coolPath₃ n x a .fst
-- --       ∙∙ coolPath₃ n x a .snd
-- --       ∙∙ (cong (transport (λ i₁ → 0ₖ (+'-comm 1 (suc (suc n)) i₁) ≡ 0ₖ (+'-comm 1 (suc (suc n)) i₁)))
-- --               (lem₃-take2 _ a)
-- --         ∙ stupid2 n a)) k j) i)))
-- --       ∙ (sym lem1
-- --       ∙∙ cong (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) i)}
-- --                                ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) i)}))
-- --                 (λ _ i j → ∣ (sym (rCancel _) ∙∙ (λ i → merid (((merid a ∙ sym (merid (ptSn _)))) i) ∙ sym (merid north)) ∙∙ rCancel _) j i ∣ₕ)
-- --       ∙∙ ((λ k → transp (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) (i ∨ k))} ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) (i ∨ k))}) k
-- --                     λ i j → transp (λ i → coHomK (+'-comm 1 (suc (suc (suc n))) (i ∧ k))) (~ k)
-- --                         (cup' zero (suc (suc n)) ∣ loop i ∣ₕ ∣ merid a j ∣ₕ)))
-- --       ∙∙ sym (inst _ (λ i j →  (subst coHomK (+'-comm 1 (suc (suc (suc n))))
-- --                         (cup' zero (suc (suc n)) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ))))
-- --       ∙∙ sym (lem₂ (suc (suc (suc n))) 1 x tt (λ i j →  (subst coHomK (+'-comm 1 (suc (suc (suc n))))
-- --                 (cup' zero (suc (suc n)) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))))) k i j
-- --     where
-- --     lem1 : (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) i)} ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) i)}))
-- --                 (λ i j → ∣ (sym (rCancel _) ∙∙ (λ z → merid ((merid a ∙ sym (merid (ptSn _))) z) ∙ sym (merid north)) ∙∙ rCancel _) j i ∣ₕ)
-- --         ≡ flipSquare (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north))
-- --                      (transport (λ i → Path (S₊ ((suc (suc (+-comm (suc n) 0 (~ i)))))) north north)
-- --                        (merid a ∙ sym (merid (ptSn _))))
-- --                      ∙∙ rCancel (merid north)))
-- --     lem1 = {!!}

-- --     coolLem : Path (Path (coHomK (suc (suc ((suc n) + zero)))) _ _)
-- --                    (λ i → ∣ pre-cup (suc n) zero a (loop i) ∣ₕ)
-- --                    (λ i → ∣ (transport (λ i → Path (S₊ ((suc (suc (+-comm (suc n) 0 (~ i)))))) north north)
-- --                                                                          (merid a ∙ sym (merid (ptSn _)))) i ∣ₕ)
-- --     coolLem =
-- --         coolPath₃ n x a .fst
-- --       ∙∙ coolPath₃ n x a .snd
-- --       ∙∙ (cong (transport (λ i₁ → 0ₖ (+'-comm 1 (suc (suc n)) i₁) ≡ 0ₖ (+'-comm 1 (suc (suc n)) i₁)))
-- --               (lem₃-take2 _ a)
-- --         ∙ stupid2 n a)
-- -- {-
-- -- Path (typ ((Ω^ 2) (coHomK-ptd _)))
-- --       (λ i j → cup' (suc n) zero ∣ (merid a i) ∣ₕ ∣ (loop j) ∣ₕ)
-- --       (λ i j → ∣ (sym (rCancel (merid north))
-- --               ∙∙ (λ z → merid (((sym (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- --                        (merid a ∙ sym (merid (ptSn _)))))) z) ∙ sym (merid north))
-- --                      ∙∙ rCancel (merid north)) j i ∣ₕ) -}

-- --     lem2 :  Path (typ ((Ω^ 2) (coHomK-ptd _)))
-- --       (λ i j → cup' (suc (suc n)) zero ∣ (merid a i) ∣ₕ ∣ (loop j) ∣ₕ)
-- --            (λ i j →  ∣ (sym (rCancel (merid north))
-- --                     ∙∙ (λ z → merid (((transport (λ i → Path (S₊ ((suc (suc (+-comm (suc n) 0 (~ i)))))) north north)
-- --                        (merid a ∙ sym (merid (ptSn _))))) z) ∙ sym (merid north))
-- --                      ∙∙ rCancel (merid north)) j i ∣ₕ)
-- --     lem2 k i j =
-- --       hcomp (λ r → λ { (i = i0) → ∣ north ∣ₕ
-- --                       ; (i = i1) → ∣ north ∣ₕ
-- --                       ; (j = i0) → ∣ rCancel (merid north) r i ∣ₕ
-- --                       ; (j = i1) → ∣ rCancel (merid north) r i ∣ₕ
-- --                       ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
-- --                                                            (λ i → merid (pre-cup (suc n) zero a (loop i)) ∙ sym (merid north))
-- --                                                            (rCancel _) r j i ∣ₕ
-- --                       ; (k = i1) → ∣ doubleCompPath-filler (sym (rCancel _))
-- --                                                            (λ i → merid ((((transport (λ i → Path (S₊ ((suc (suc (+-comm (suc n) 0 (~ i)))))) north north)
-- --                                                                          (merid a ∙ sym (merid (ptSn _)))))) i) ∙ sym (merid north))
-- --                                                            (rCancel _) r j i ∣ₕ})
-- --             (Kn→ΩKn+1 _ (coolLem k j) i)

-- --     help : Path (typ ((Ω^ 2) (coHomK-ptd _)))
-- --              (λ i j → cup' (suc (suc n)) zero ∣ (merid a i) ∣ₕ ∣ (loop j) ∣ₕ)
-- --           (λ i j → -ₖ-gen (suc (suc (suc n))) 1 (inr x) (inr tt)
-- --       (subst coHomK (+'-comm 1 (suc (suc (suc n))))
-- --        (cup' zero (suc (suc n)) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))
-- --     help =
-- --         lem2
-- --       ∙ (sym lem1
-- --       ∙∙ cong (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) i)}
-- --                                ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) i)}))
-- --                 (λ _ i j → ∣ (sym (rCancel _) ∙∙ (λ i → merid (((merid a ∙ sym (merid (ptSn _)))) i) ∙ sym (merid north)) ∙∙ rCancel _) j i ∣ₕ)
-- --       ∙∙ ((λ k → transp (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) (i ∨ k))} ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) (i ∨ k))}) k
-- --                     λ i j → transp (λ i → coHomK (+'-comm 1 (suc (suc (suc n))) (i ∧ k))) (~ k)
-- --                         (cup' zero (suc (suc n)) ∣ loop i ∣ₕ ∣ merid a j ∣ₕ)))
-- --       ∙∙ sym (inst _ (λ i j →  (subst coHomK (+'-comm 1 (suc (suc (suc n))))
-- --                         (cup' zero (suc (suc n)) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ))))
-- --       ∙∙ sym (lem₂ (suc (suc (suc n))) 1 x tt (λ i j →  (subst coHomK (+'-comm 1 (suc (suc (suc n))))
-- --                 (cup' zero (suc (suc n)) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))))

-- --   mainᵣ zero p q b a = {!!}
-- --   mainᵣ (suc n) p q base north = refl
-- --   mainᵣ (suc n) p q base south = refl
-- --   mainᵣ (suc n) p q base (merid a i) = refl
-- --   mainᵣ (suc n) p q (loop i) north = refl
-- --   mainᵣ (suc n) p q (loop i) south = refl
-- --   mainᵣ (suc n) p q (loop i) (merid b j) = {!!}
-- --   coolPath zero p = λ { base → pre-cool-S¹ i0 ; (loop i) → pre-cool-S¹ i}
-- --     where
-- --     pre-cool-S¹ : (i : I)
-- --         → Path (Path (coHomK (suc (suc (zero + zero)))) _ _)
-- --                    (λ j → ∣ pre-cup zero zero (loop i) (loop j) ∣ₕ)
-- --                    (sym (extraP zero) ∙∙ (λ z → (subst coHomK (+'-comm (suc zero) (suc zero)))
-- --                       ((sym (lUnit₁' zero (loop i))
-- --                    ∙∙ (λ j → cup' zero zero ∣ loop (~ j) ∣ ∣ (loop i) ∣)
-- --                    ∙∙ lUnit₁' zero (loop i)) z)) ∙∙ extraP zero)
-- --     pre-cool-S¹ i =
-- --          rUnit _
-- --       ∙∙ (λ k → refl
-- --               ∙∙ (λ j → mainₗ zero (inr tt) (inr tt) (loop i) (loop j) k)
-- --               ∙∙ refl)
-- --       ∙∙ (λ k → refl
-- --               ∙∙ (cong-₂ (suc zero) 1 tt tt
-- --                            (cong (subst coHomK (+'-comm 1 (suc zero)))
-- --                             (λ j → cup' zero zero ∣ loop j ∣ₕ ∣ loop i ∣ₕ)) k)
-- --               ∙∙ refl)
-- --       ∙∙ rUnit _
-- --       ∙∙ refl
-- --   coolPath (suc n) p = {!!}
-- --     where
-- --     pre-cool-merid : (i : I) (a : _)
-- --         → Path (Path (coHomK (suc (suc ((suc n) + zero)))) _ _)
-- --                    (λ j → ∣ (pre-cup (suc n) zero (merid a i)) (loop j) ∣ₕ)
-- --                    (sym (extraP (suc n)) ∙∙ (λ z →  (subst coHomK (+'-comm (suc zero) (suc (suc n))))
-- --                       ((sym (lUnit₁' (suc n) (merid a i))
-- --                    ∙∙ (λ j → cup' zero (suc n) ∣ loop (~ j) ∣ ∣ (merid a i) ∣)
-- --                    ∙∙ lUnit₁' (suc n) (merid a i)) z)) ∙∙ extraP (suc n))
-- --     pre-cool-merid i a =
-- --          rUnit _
-- --       ∙∙ (λ k → refl
-- --               ∙∙ (λ j → mainₗ (suc n) (inr p) (inr tt) (merid a i) (loop j) k)
-- --               ∙∙ refl)
-- --       ∙∙ (λ k → refl
-- --               ∙∙ (cong-₂ (suc (suc n)) 1 p tt
-- --                            (cong (subst coHomK (+'-comm 1 (suc (suc n))))
-- --                             (λ j → cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)) k)
-- --               ∙∙ refl)
-- --       ∙∙ rUnit _
-- --       ∙∙ refl

-- --   coolPath₂ zero a =
-- --            sym (rUnit _)
-- --         ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc zero) (suc zero) (i ∨ ~ k))
-- --                                  ≡ 0ₖ (+'-comm (suc zero) (suc zero) (i ∨ ~ k))) (~ k)
-- --                            λ j → transp (λ i → coHomK (+'-comm (suc zero) (suc zero) (i ∧ ~ k))) k
-- --                                          ((sym (lUnit₁' zero a)
-- --                           ∙∙ (λ j → cup' zero zero ∣ loop (~ j) ∣ ∣ a ∣)
-- --                           ∙∙ lUnit₁' zero a) j)
-- --   coolPath₂ (suc n) a =
-- --     sym (rUnit _) ∙
-- --      λ k → transp (λ i → 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ ~ k))
-- --                                  ≡ 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ ~ k))) (~ k)
-- --                            λ j → transp (λ i → coHomK (+'-comm (suc zero) (suc (suc n)) (i ∧ ~ k))) k
-- --                                          ((sym (lUnit₁' (suc n) a)
-- --                           ∙∙ (λ j → cup' zero (suc n) ∣ loop (~ j) ∣ ∣ a ∣)
-- --                           ∙∙ lUnit₁' (suc n) a) j)
-- --   fst (coolPath₃ n x a) = pre-cool a
-- --     where
-- --     pre-cool-merid : (i : I) (a : _)
-- --       → (λ j → ∣ (pre-cup (suc n) zero (merid a i)) (loop j) ∣ₕ) ≡
-- --       (λ z → (subst coHomK (+'-comm 1 (suc (suc n))))
-- --       ((sym (lUnit₁' (suc n) (merid a i)) ∙∙
-- --        (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ merid a i ∣) ∙∙ lUnit₁' (suc n) (merid a i)) z))
-- --     pre-cool-merid i a =
-- --          (λ k j → mainₗ (suc n) (inl x) (inr tt) (merid a i) (loop j) k)
-- --       ∙∙ (λ k j → -ₖ-gen-inl-left (suc (suc (suc (suc n)))) 1 x (inr tt)
-- --                     ((subst coHomK (+'-comm 1 (suc (suc n)))
-- --                       ((cup' zero (suc n) ∣ loop j ∣ ∣ merid a i ∣)))) k)
-- --       ∙∙ (λ k j → (subst coHomK (+'-comm 1 (suc (suc n)))
-- --                     (rUnit (λ j₁ → cup' zero (suc n) ∣ loop j₁ ∣ ∣ merid a i ∣) k j)))


-- --     pre-cool : (a : _) → Path (Path _ _ _)
-- --       (λ i → ∣ pre-cup (suc n) zero a (loop i) ∣ₕ)
-- --       (λ i →  (subst coHomK (+'-comm 1 (suc (suc n))))
-- --       ((sym (lUnit₁' (suc n) a) ∙∙
-- --        (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣) ∙∙ lUnit₁' (suc n) a) i))
-- --     pre-cool north = pre-cool-merid i0 (ptSn (suc n))
-- --     pre-cool south = pre-cool-merid i1 (ptSn (suc n))
-- --     pre-cool (merid a i) = pre-cool-merid i a
-- --   snd (coolPath₃ n x a) = λ k → transp (λ i → 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ ~ k))
-- --                                  ≡ 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ ~ k))) (~ k)
-- --                            λ j → transp (λ i → coHomK (+'-comm (suc zero) (suc (suc n)) (i ∧ ~ k))) k
-- --                                          ((sym (lUnit₁' (suc n) a)
-- --                           ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣)
-- --                           ∙∙ lUnit₁' (suc n) a) j)
-- --                          -}

-- -- --   main : (k : ℕ) (n m : ℕ) (term : n + m ≡ k) (p : _) (q : _) (a : _) (b : _)
-- -- --       → (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡ (-ₖ-gen (suc n) (suc m) p q) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ))
-- -- --   mainHelp1 : (k n m : ℕ) (term : _) (a : _) (b : _) → (p : _) (q : _)
-- -- --     → ((main (suc k) m (suc n) term p q b north
-- -- --        ∙∙ cong (-ₖ-gen (suc m) (suc (suc n)) p q ∘ (subst coHomK (+'-comm (suc (suc n)) (suc m))))
-- -- --                (λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)
-- -- --        ∙∙ sym (main (suc k) m (suc n) term p q b south)))
-- -- --        ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc m) i) ≡ 0ₖ (+'-comm (suc (suc n)) (suc m) i))
-- -- --              (cong (-ₖ-gen (suc m) (suc (suc n)) p q) (Kn→ΩKn+1 _ (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ)))
-- -- --   mainHelp2 : (k n m : ℕ) (term : _) (a : _) (b : _) → (p : _) (q : _)
-- -- --     → ((sym (lUnit₁ m n a)
-- -- --      ∙∙ (main (suc k) (suc m) n term p q north a
-- -- --      ∙∙ (λ i → -ₖ-gen (suc (suc m)) (suc n) p q
-- -- --                   (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- --                    (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ)))
-- -- --      ∙∙ (sym (main (suc k) (suc m) n term p q south a)))
-- -- --      ∙∙ lUnit₂ m n a)
-- -- --      ≡ transport (λ i → 0ₖ (+'-comm (suc n) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc n) (suc (suc m)) i))
-- -- --                  (cong (-ₖ-gen (suc (suc m)) (suc n) p q)
-- -- --                        λ i → cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ))
-- -- --   mainHelp2 k n m term a b p q = {!!}
-- -- --   main k zero zero term p q a b = {!!}
-- -- --   main k zero (suc m) term p q a b = {!!}
-- -- --   main k (suc n) zero term p q a b = {!!}
-- -- --   main k (suc n) (suc m) term p q north north = refl
-- -- --   main k (suc n) (suc m) term p q north south = refl
-- -- --   main k (suc n) (suc m) term p q north (merid a i) = refl
-- -- --   main k (suc n) (suc m) term p q south north = refl
-- -- --   main k (suc n) (suc m) term p q south south = refl
-- -- --   main k (suc n) (suc m) termr p q south (merid a i) = refl
-- -- --   main k (suc n) (suc m) retm p q (merid a i) north = refl
-- -- --   main k (suc n) (suc m) term p q (merid a i) south = refl
-- -- --   main zero (suc n) (suc m) term p q (merid a i) (merid b j) = {!!}
-- -- --   main (suc zero) (suc n) (suc m) term p q (merid a i) (merid b j) = {!!}
-- -- --   main (suc (suc k)) (suc n) (suc m) term p q (merid a i) (merid b j) = {!!}
-- -- --     where
-- -- --     term₁ : m + suc n ≡ suc k
-- -- --     term₁ = +-suc m n ∙∙ +-comm (suc m) n ∙∙ cong predℕ term

-- -- --     term₂ : n + m ≡ k
-- -- --     term₂ = +-comm n m ∙∙ cong predℕ (+-comm (suc m) n) ∙∙ cong (predℕ ∘ predℕ) term

-- -- --     term₃ : suc (m + n) ≡ suc k
-- -- --     term₃ = sym (+-suc m n) ∙ term₁

-- -- --     lem1 : {k : ℕ} (n m : ℕ) (p : _) (q : _)
-- -- --          → (x : Path (coHomK (suc (suc k))) (0ₖ _) (0ₖ _)) →  cong ((-ₖ-gen {k = suc (suc k)} m (suc n) (evenOrOdd m) (evenOrOdd (suc n)))
-- -- --            ∘ (-ₖ-gen n m (evenOrOdd n) (evenOrOdd m))
-- -- --            ∘ (-ₖ-gen (suc m) n (evenOrOdd (suc m)) (evenOrOdd n))) x
-- -- --          ≡ sym (cong (-ₖ-gen {k = suc (suc k)} (suc n) (suc m) p q) x)
-- -- --     lem1 = {!!}

-- -- --     lem2 : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : Path (coHomK (suc (suc k))) (0ₖ _) (0ₖ _))
-- -- --       → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 (suc (suc k))) (cong (-ₖ-gen n m p q) x) ∙∙ Kn→ΩKn+10ₖ _
-- -- --       ≡ cong (cong (-ₖ-gen n m p q)) (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 (suc (suc k))) x ∙∙ Kn→ΩKn+10ₖ _)
-- -- --     lem2 = {!!}

-- -- --     transpFix : (A : ℕ → Type) {n m l o : ℕ} (p : n ≡ m) (q : m ≡ l) (r : l ≡ o) (s : o ≡ n)
-- -- --              → (x : A n) → (subst A r (subst A q (subst A p x))) ≡ subst A (sym s) x
-- -- --     transpFix = {!!}

-- -- --     -ₖ-cong²-idemp : {k : ℕ} (n m : ℕ) (p : _) (q : _) (P : typ ((Ω^ 2) (coHomK-ptd (suc (suc k))))) → cong (cong (-ₖ-gen n m p q ∘ -ₖ-gen n m p q)) P ≡ P
-- -- --     -ₖ-cong²-idemp = {!!}

-- -- --     help : (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ) ≡
-- -- --       cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) p q ∘
-- -- --       (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))))
-- -- --        (λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)
-- -- --     help = (sym (inst _ (λ i₁ j₁ → cup' (suc n) (suc m) ∣ merid a j₁ ∣ ∣ merid b i₁ ∣))
-- -- --           ∙ sym (-ₖ-cong²-idemp (suc (suc n)) (suc (suc m)) p q
-- -- --                 (λ i j → cup' (suc n) (suc m) ∣ merid a j ∣ ∣ merid b (~ i) ∣)))
-- -- --         ∙∙ cong (cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) p q)))
-- -- --                 (sym (transportTransport⁻ (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)} ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)})
-- -- --                                      _)
-- -- --                 ∙ sym (lem₈ n m (subst (λ x → refl {x = 0ₖ x} ≡ refl {x = 0ₖ x})
-- -- --                         (sym (+'-comm (suc (suc m)) (suc (suc n))))
-- -- --                         (λ i₃ i₄ →
-- -- --                            trMap (-ₖ-helper (suc (suc n)) (suc (suc m)) p q)
-- -- --                            (cup' (suc n) (suc m) ∣ merid a i₄ ∣ ∣ merid b (~ i₃) ∣)))))
-- -- --         ∙∙ cong (cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) p q ∘
-- -- --                 (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))))
-- -- --                   ((sym (transpFix (λ x → refl {x = 0ₖ x} ≡ refl {x = 0ₖ x})
-- -- --                         (cong (suc ∘ suc ∘ suc) (+-comm n (suc m)))
-- -- --                         (cong (suc ∘ suc ∘ suc ∘ suc) (+-comm m n)) (cong suc (+'-comm (suc (suc n)) (suc m))) ((+'-comm (suc (suc m)) (suc (suc n))))
-- -- --                           (cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) p q)) λ i j → cup' (suc n) (suc m) ∣ merid a j ∣ₕ ∣ merid b (~ i) ∣ₕ))
-- -- --                  ∙∙ cong (t₂ n m)
-- -- --                      (refl 
-- -- --                    ∙∙ cong (subst (λ n₁ → refl ≡ refl) (+-comm m n))
-- -- --                            ((cong (subst (λ n₁ → refl ≡ refl) (+-comm n (suc m)))
-- -- --                              (cong (cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) p q)))
-- -- --                                    ((cong sym (lem₁ _ _ b a)))
-- -- --                             ∙ sym (cong sym (lem2 (suc (suc n)) (suc (suc m)) p q (λ i₂ → cup' n (suc m) ∣ a ∣ ∣ merid b i₂ ∣)))
-- -- --                             ∙ cong (λ x → (sym (Kn→ΩKn+10ₖ _) ∙∙
-- -- --                                    cong (Kn→ΩKn+1 _) x
-- -- --                                    ∙∙ Kn→ΩKn+10ₖ _))
-- -- --                                    (sym (lem1 (suc n) (suc m) p q (λ i₁ → cup' n (suc m) ∣ a ∣ ∣ merid b i₁ ∣))))
-- -- --                            ∙ sym (natTranspLem {A = λ n → 0ₖ (suc (suc n)) ≡ 0ₖ (suc (suc n))} _ _
-- -- --                                 ((λ i₂ → -ₖ-gen (suc (suc m)) (suc n) (evenOrOdd m) (evenOrOdd (suc n))
-- -- --                                     (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i₂ ∣ₕ))) _
-- -- --                                       (λ _ x → (sym (Kn→ΩKn+10ₖ _) ∙∙
-- -- --                                    cong (Kn→ΩKn+1 _) (((cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) (evenOrOdd n)))
-- -- --                                 ∘ (cong (-ₖ-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m))))) x)
-- -- --                                    ∙∙ Kn→ΩKn+10ₖ _))
-- -- --                                       ((+-comm n (suc m)))))
-- -- --                            ∙ cong (λ x → (sym (Kn→ΩKn+10ₖ _) ∙∙
-- -- --                                    cong (Kn→ΩKn+1 _) x
-- -- --                                    ∙∙ Kn→ΩKn+10ₖ _))
-- -- --                            (cong ((cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) (evenOrOdd n)))
-- -- --                                 ∘ (cong (-ₖ-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m)))))
-- -- --                                    ((λ i → transport (λ i₁ → 0ₖ (isSetℕ _ _ (cong (suc ∘ suc) (+-comm n (suc m))) (+'-comm (suc n) (suc (suc m))) i i₁)
-- -- --                                                              ≡ 0ₖ (isSetℕ _ _ (cong (suc ∘ suc) (+-comm n (suc m))) (+'-comm (suc n) (suc (suc m))) i i₁))
-- -- --                                            (cong (-ₖ-gen (suc (suc m)) (suc n) (evenOrOdd m) (evenOrOdd (suc n)))
-- -- --                                             (λ i₁ → cup' n (suc m) ∣ a ∣ₕ ∣ merid b i₁ ∣ₕ)))
-- -- --                                   ∙ (sym (mainHelp2 k n m term₃ a b (evenOrOdd m) (evenOrOdd (suc n)))
-- -- --                                   ∙ (λ r → (sym (lUnit₁ m n a)
-- -- --                                     ∙∙ (λ i → main (suc k) (suc m) n term₃ (evenOrOdd m) (evenOrOdd (suc n)) north a (~ r ∧ i))
-- -- --                                     ∙∙ (λ i → main (suc k) (suc m) n term₃ (evenOrOdd m) (evenOrOdd (suc n)) (merid b i) a (~ r))
-- -- --                                     ∙∙ (λ i → main (suc k) (suc m) n term₃ (evenOrOdd m) (evenOrOdd (suc n)) south a (~ r ∧ ~ i))
-- -- --                                     ∙∙ lUnit₂ m n a)))
-- -- --                                  ∙∙ (λ k → (sym (lUnit₁ m n a)
-- -- --                                  ∙∙ rUnit (λ i₁ → cup' (suc m) n ∣ merid b i₁ ∣ₕ ∣ a ∣ₕ) (~ k)
-- -- --                                  ∙∙ lUnit₂ m n a)) ∙∙ lem₃ m n b a)
-- -- --                           ∙ cong (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) (evenOrOdd n)))
-- -- --                                  (sym (pullOut (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m)) (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ)))))
-- -- --                    ∙∙ sym (natTranspLem {A = λ n → coHomK (suc (suc n))} _ _ (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ) _
-- -- --                           (λ _ x → (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _)
-- -- --                                          (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) (evenOrOdd n))
-- -- --                                            (Kn→ΩKn+1 _ (-ₖ-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m)) x)))
-- -- --                                    ∙∙ Kn→ΩKn+10ₖ _)) ((+-comm m n))))
-- -- --                  ∙∙ (λ i → (natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n} _ _
-- -- --                    ((λ i₂ →  -ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) (evenOrOdd n)
-- -- --                              (Kn→ΩKn+1 (suc (suc (n + m)))
-- -- --                               (-ₖ-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m))
-- -- --                                (subst coHomK (isSetℕ _ _ (cong (suc ∘ suc) (+-comm m n)) (+'-comm (suc m) (suc n)) i) (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ)))
-- -- --                               i₂)))
-- -- --                    _ (λ _ x → (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x
-- -- --                                    ∙∙ Kn→ΩKn+10ₖ _))
-- -- --                     (+'-comm (suc (suc n)) (suc m))) (~ i)))
-- -- --             ∙∙ cong (λ x → (sym (Kn→ΩKn+10ₖ (suc (suc (m + suc n)))) ∙∙
-- -- --                                    cong (Kn→ΩKn+1 (suc (suc (m + suc n)))) x
-- -- --                                    ∙∙ Kn→ΩKn+10ₖ (suc (suc (m + suc n)))))
-- -- --                      (cong (transport
-- -- --                             (λ i₁ →
-- -- --                                0ₖ (+'-comm (suc (suc n)) (suc m) i₁) ≡
-- -- --                                0ₖ (+'-comm (suc (suc n)) (suc m) i₁)))
-- -- --                            (cong (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) (evenOrOdd n)) ∘ (Kn→ΩKn+1 (suc (suc (n + m)))))
-- -- --                                  (sym (main k n m term₂ (evenOrOdd (suc n)) (evenOrOdd (suc m)) a b)))
-- -- --                      ∙∙ sym (mainHelp1 k n m term₁ a b (evenOrOdd (suc m)) (evenOrOdd n))
-- -- --                      ∙∙ (λ r → (λ i₁ → main (suc k) m (suc n) term₁ (evenOrOdd (suc m)) (evenOrOdd n) b north (i₁ ∧ ~ r))
-- -- --                            ∙∙ (λ i₁ → main (suc k) m (suc n) term₁ (evenOrOdd (suc m)) (evenOrOdd n) b (merid a i₁) (~ r))
-- -- --                            ∙∙ λ i₁ → main (suc k) m (suc n) term₁ (evenOrOdd (suc m)) (evenOrOdd n) b south (~ i₁ ∧ ~ r))
-- -- --                     ∙ sym (rUnit (λ i₁ → cup' m (suc n) ∣ b ∣ ∣ merid a i₁ ∣)))
-- -- --             ∙∙ sym (lem₁ n m a b))
-- -- --   mainHelp1 = {!!}

-- -- -- --   main : (k : ℕ) (n m : ℕ) (term : n + m ≡ k) (p : _) (q : _) (a : _) (b : _)
-- -- -- --       → (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡ (-ₖ-gen (suc n) (suc m) p q) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ))
-- -- -- --   main k zero zero term p q a b = {!!}
-- -- -- --   main k zero (suc m) term p q base north = refl
-- -- -- --   main k zero (suc m) term p q base south = refl
-- -- -- --   main k zero (suc m) term p q base (merid a i) = refl
-- -- -- --   main k zero (suc m) term p q (loop i) north = refl
-- -- -- --   main k zero (suc m) term p q (loop i) south = refl
-- -- -- --   main k (suc n) zero term p q north base = refl
-- -- -- --   main k (suc n) zero term p q north (loop i) = refl
-- -- -- --   main k (suc n) zero term p q south base = refl
-- -- -- --   main k (suc n) zero term p q south (loop i) = refl
-- -- -- --   main k (suc n) zero term p q (merid a i) base = refl
-- -- -- --   main k (suc n) (suc m) term p q north north = refl
-- -- -- --   main k (suc n) (suc m) term p q north south = refl
-- -- -- --   main k (suc n) (suc m) term p q north (merid a i) = refl
-- -- -- --   main k (suc n) (suc m) term p q south north = refl
-- -- -- --   main k (suc n) (suc m) term p q south south = refl
-- -- -- --   main k (suc n) (suc m) term p q south (merid a i) = refl
-- -- -- --   main k (suc n) (suc m) term p q (merid a i) north = refl
-- -- -- --   main k (suc n) (suc m) term p q (merid a i) south = refl
-- -- -- --   main zero zero (suc m) term p q (loop i) (merid b j) = λ k → help k i j -- λ k → help k i j
-- -- -- --     where
-- -- -- --     help : (λ i j → cup' zero (suc m) ∣ loop i ∣ₕ ∣ merid b j ∣ₕ )
-- -- -- --          ≡ cong (cong (-ₖ-gen (suc zero) (suc (suc m)) p q ∘ (subst coHomK (+'-comm (suc (suc m)) (suc zero)))))
-- -- -- --                 λ i j → (cup' (suc m) zero ∣ merid b j ∣ₕ ∣ loop i ∣ₕ)
-- -- -- --     help = ⊥-rec (snotz term)
-- -- -- --   main (suc k) zero (suc m) term (inr tt) q (loop i) (merid b j) = {!!}
-- -- -- --   main zero (suc n) zero term p q (merid a i) (loop j) = λ k → help k i j
-- -- -- --     where
-- -- -- --     help : (λ i j → cup' (suc n) zero ∣ merid a i ∣ₕ ∣ loop j ∣ₕ )
-- -- -- --          ≡ cong (cong (-ₖ-gen (suc (suc n)) (suc zero) p q ∘ (subst coHomK (+'-comm (suc zero) (suc (suc n))))))
-- -- -- --                 λ i j → (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)
-- -- -- --     help = ⊥-rec (snotz term)
-- -- -- --   main (suc k) (suc n) zero term p q (merid a i) (loop j) = {!!}
-- -- -- --   main zero (suc n) (suc m) term p q (merid a i) (merid b j) = λ k → help k i j
-- -- -- --     where
-- -- -- --     help : (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)
-- -- -- --       ≡ cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) p q ∘ subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))
-- -- -- --           (λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)
-- -- -- --     help = ⊥-rec (snotz term)
-- -- -- --   main (suc zero) (suc n) (suc m) term p q (merid a i) (merid b j) = λ k → help k i j
-- -- -- --     where
-- -- -- --     help : (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)
-- -- -- --       ≡ cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) p q ∘ subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))
-- -- -- --           (λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)
-- -- -- --     help = ⊥-rec (snotz (sym (+-comm n (suc m)) ∙ cong predℕ term))
-- -- -- --   main (suc (suc z)) (suc n) (suc m) term (inl x) (inl y) (merid a i) (merid b j) = λ k → help k i j
-- -- -- --     where
-- -- -- --     lem57 : (k : ℕ) (n m : ℕ) (term : m + suc n ≡ k) (p : is-even n) (q : is-even m) (a : _) (b : _) →
-- -- -- --         ((sym (Kn→ΩKn+10ₖ _)
-- -- -- --          ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- --          ∙∙ Kn→ΩKn+10ₖ _))
-- -- -- --       ≡ transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
-- -- -- --           (sym (Kn→ΩKn+10ₖ _)
-- -- -- --          ∙∙ cong (Kn→ΩKn+1 _) (sym (lUnit₁ n m b) ∙∙ ((λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) ∙∙ lUnit₂ n m b)
-- -- -- --          ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- --     lem57 z n m term p q a b =
-- -- -- --          cong (λ x → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- --               ((rUnit (λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ)
-- -- -- --             ∙∙ (λ k → (λ i → main z m (suc n) term (inr q) (inl p) b north (k ∧ i))
-- -- -- --                    ∙∙ (λ i → main z m (suc n) term (inr q) (inl p) b (merid a i) k)
-- -- -- --                     ∙∙ λ i → main z m (suc n) term (inr q) (inl p) b south (k ∧ ~ i))
-- -- -- --             ∙∙ cong (main z m (suc n) term (inr q) (inl p) b north ∙∙_∙∙ sym (main z m (suc n) term (inr q) (inl p) b south))
-- -- -- --                        (rUnit _
-- -- -- --                      ∙ (λ k → (λ i → -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
-- -- -- --                                           ((subst coHomK (+'-comm (suc (suc n)) (suc m))
-- -- -- --                                              (cup' (suc n) m ∣ north ∣ ∣ b ∣))) (i ∧ k))
-- -- -- --                             ∙∙ ((λ i → -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
-- -- -- --                                           (subst coHomK (+'-comm (suc (suc n)) (suc m))
-- -- -- --                                              (cup' (suc n) m ∣ merid a i ∣ ∣ b ∣)) k))
-- -- -- --                             ∙∙ λ i → -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
-- -- -- --                                           ((subst coHomK (+'-comm (suc (suc n)) (suc m))
-- -- -- --                                              (cup' (suc n) m ∣ south ∣ ∣ b ∣))) (~ i ∧ k))))
-- -- -- --               ∙ lem z n m term a b q p)
-- -- -- --        ∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n}
-- -- -- --           _ _ ((sym (lUnit₁ n m b) ∙∙ ((λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) ∙∙ lUnit₂ n m b)) _ (λ _ p → (sym (Kn→ΩKn+10ₖ _)
-- -- -- --          ∙∙ cong (Kn→ΩKn+1 _) p
-- -- -- --          ∙∙ Kn→ΩKn+10ₖ _)) (+'-comm (suc (suc n)) (suc m))
-- -- -- --       where
-- -- -- --       lemType : (k n m : ℕ) (term : m + suc n ≡ k) (a : _) (b : _) (q : _) (p : _) → Type
-- -- -- --       lemType k n m term a b q p =
-- -- -- --              (main k m (suc n) term (inr q) (inl p) b north
-- -- -- --           ∙∙ (-ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
-- -- -- --                                             ((subst coHomK (+'-comm (suc (suc n)) (suc m))
-- -- -- --                                                (cup' (suc n) m ∣ north ∣ ∣ b ∣))))
-- -- -- --           ∙∙ cong (subst coHomK (+'-comm (suc (suc n)) (suc m)))
-- -- -- --                   (λ i → cup' (suc n) m ∣ merid a i ∣ ∣ b ∣)
-- -- -- --           ∙∙ sym (-ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
-- -- -- --                                             ((subst coHomK (+'-comm (suc (suc n)) (suc m))
-- -- -- --                                                (cup' (suc n) m ∣ south ∣ ∣ b ∣))))
-- -- -- --           ∙∙ sym (main k m (suc n) term (inr q) (inl p) b south))
-- -- -- --           ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc m) i) ≡ 0ₖ ((+'-comm (suc (suc n)) (suc m) i)))
-- -- -- --                       (sym (lUnit₁ n m b) ∙∙ ((λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) ∙∙ lUnit₂ n m b)

-- -- -- --       S¹-case : (i : I) → (k : ℕ) (n : ℕ) (term : _) (a : _) (q : _) (p : _) → lemType k n zero term a (loop i) q p
-- -- -- --       S¹-case i k n term a q p =
-- -- -- --            sym (rUnit _)
-- -- -- --          ∙ λ k → transp
-- -- -- --                  (λ i → 0ₖ ((+'-comm (suc (suc n)) (suc zero) (i ∨ ~ k)))
-- -- -- --                     ≡ 0ₖ (+'-comm (suc (suc n)) (suc zero) (i ∨ ~ k)) ) (~ k)
-- -- -- --               (((λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc zero) (i ∧ ~ k)))
-- -- -- --                 k (cup' (suc n) zero ∣ merid a j ∣ ∣ loop i ∣)) ∙ refl))

-- -- -- --       Susp-case : (i : I) → (k n m : ℕ) (term : _) (a : _) (b : _) (q : _) (p : _) → lemType k n (suc m) term a (merid b i) q p
-- -- -- --       Susp-case i z n m term a b q p =
-- -- -- --           sym (rUnit _)
-- -- -- --         ∙ λ k → transp
-- -- -- --                  (λ i → 0ₖ ((+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)))
-- -- -- --                     ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)) ) (~ k)
-- -- -- --               (((λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc m)) (i ∧ ~ k)))
-- -- -- --                 k (cup' (suc n) (suc m) ∣ merid a j ∣ ∣ merid b i ∣)) ∙ refl))

-- -- -- --       lem : (k n m : ℕ) (term : _) (a : _) (b : _) (q : _) (p : _)
-- -- -- --         → lemType k n m term a b q p
-- -- -- --       lem k n zero term a base q p = S¹-case i0 k n term a q p
-- -- -- --       lem k n zero term a (loop i) q p = S¹-case i k n term a q p
-- -- -- --       lem k n (suc m) term a north q p = Susp-case i0 k n m term a (ptSn (suc m)) q p
-- -- -- --       lem k n (suc m) term a south q p = Susp-case i1 k n m term a (ptSn (suc m)) q p
-- -- -- --       lem k n (suc m) term a (merid b i) q p = Susp-case i k n m term a b q p

-- -- -- --     lem₄ : Kn→ΩKn+1 _ (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡ sym (Kn→ΩKn+1 _ (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ ∣ a ∣)))
-- -- -- --     lem₄ = cong (Kn→ΩKn+1 _) (main z n m ((+-comm n m ∙ cong predℕ (+-comm (suc m) n)) ∙ cong (predℕ ∘ predℕ) term) (inr x) (inr y) a b)
-- -- -- --          ∙ -ₖ-gen-Kn→ΩKn+1 (suc n) (suc m) x y (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ ∣ a ∣))

-- -- -- --     lem₅ : (n m : ℕ) (a : _) (b : _)
-- -- -- --        → Kn→ΩKn+1 _ (cup' m n ∣ b ∣ ∣ a ∣)
-- -- -- --       ≡ (sym (lUnit₁ m n a) ∙∙ (λ i → cup' (suc m) n ∣ merid b i ∣ ∣ a ∣) ∙∙ lUnit₂ m n a)
-- -- -- --     lem₅ n m a b = sym (lem₃ m n b a)

-- -- -- --     lem₆ : (sym (lUnit₁ m n a) ∙∙ (λ i → cup' (suc m) n ∣ merid b i ∣ ∣ a ∣) ∙∙ lUnit₂ m n a)
-- -- -- --          ≡ transport (λ i → 0ₖ (+'-comm (suc n) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc n) (suc (suc m)) i))
-- -- -- --                      λ i → cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ
-- -- -- --     lem₆ = cong (sym (lUnit₁ m n a) ∙∙_∙∙ lUnit₂ m n a)
-- -- -- --                 (rUnit _ ∙ (λ i → (λ k → main (suc z) (suc m) n (+-comm (suc m) n ∙ cong predℕ term) (inl y) (inr x) north a (i ∧ k))
-- -- -- --                                ∙∙ (λ k → main (suc z) (suc m) n (+-comm (suc m) n ∙ cong predℕ term) (inl y) (inr x) (merid b k) a i)
-- -- -- --                                ∙∙ λ k → main (suc z) (suc m) n (+-comm (suc m) n ∙ cong predℕ term) (inl y) (inr x) south a (i ∧ ~ k))
-- -- -- --                           ∙ cong (main (suc z) (suc m) n (+-comm (suc m) n ∙ cong predℕ term) (inl y) (inr x) north a
-- -- -- --                               ∙∙_∙∙ sym (main (suc z) (suc m) n (+-comm (suc m) n ∙ cong predℕ term) (inl y) (inr x) south a))
-- -- -- --                                   (rUnit _
-- -- -- --                                     ∙ λ k → (λ i → (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
-- -- -- --                                               (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- -- --                                                (cup' n (suc m) ∣ a ∣ₕ ∣ north ∣ₕ))) (i ∧ k))
-- -- -- --                                          ∙∙ (λ i → (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
-- -- -- --                                               (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- -- --                                                (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ))) k)
-- -- -- --                                           ∙∙ λ i → (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
-- -- -- --                                               (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- -- --                                                (cup' n (suc m) ∣ a ∣ₕ ∣ south ∣ₕ))) (~ i ∧ k)))
-- -- -- --         ∙∙ lem (suc z) n m (+-comm (suc m) n ∙ cong predℕ term) a b x y
-- -- -- --         ∙∙ refl
-- -- -- --       where
-- -- -- --       lemType : (k n m : ℕ) (term : _) (a : _) (b : _) (x : _) (y : _) → Type
-- -- -- --       lemType k n m term a b x y =
-- -- -- --         ((sym (lUnit₁ m n a)) ∙∙
-- -- -- --        main k (suc m) n term (inl y) (inr x) north a ∙∙
-- -- -- --        (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
-- -- -- --           (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- -- --            (cup' n (suc m) ∣ a ∣ₕ ∣ north ∣ₕ)))
-- -- -- --        ∙∙
-- -- -- --        (λ i₁ →
-- -- -- --           (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- -- --            (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i₁ ∣ₕ)))
-- -- -- --        ∙∙
-- -- -- --        (sym (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
-- -- -- --           (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- -- --            (cup' n (suc m) ∣ a ∣ₕ ∣ south ∣ₕ))))
-- -- -- --        ∙∙ (sym (main k (suc m) n term (inl y) (inr x) south a))
-- -- -- --        ∙∙ lUnit₂ m n a)
-- -- -- --        ≡ transport (λ i → 0ₖ (+'-comm (suc n) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc n) (suc (suc m)) i))
-- -- -- --                      λ i → cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ

-- -- -- --       S¹-case : (i : I) → (k m : ℕ) (term : _) (b : _) (x : _) (y : _) → lemType k zero m term (loop i) b x y
-- -- -- --       S¹-case i k m term b x y =
-- -- -- --            sym (rUnit _)
-- -- -- --         ∙∙ sym (rUnit _)
-- -- -- --         ∙∙ sym (rUnit _)
-- -- -- --          ∙ λ k → transp (λ i → 0ₖ (+'-comm 1 (suc (suc m)) (i ∨ ~ k)) ≡ 0ₖ (+'-comm 1 (suc (suc m)) (i ∨ ~ k)))
-- -- -- --                          (~ k)
-- -- -- --                          λ j → transp (λ i → coHomK (+'-comm 1 (suc (suc m)) (i ∧ ~ k))) k
-- -- -- --                                (cup' zero (suc m) ∣ loop i ∣ₕ ∣ merid b j ∣ₕ)

-- -- -- --       Susp-case : (i : I) (k n m : ℕ) (term : _) (a : _) (b : _) (x : _) (y : _) → lemType k (suc n) m term (merid a i) b x y
-- -- -- --       Susp-case i k n m term a b x y =
-- -- -- --            sym (rUnit _)
-- -- -- --         ∙∙ sym (rUnit _)
-- -- -- --         ∙∙ sym (rUnit _)
-- -- -- --          ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)) ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)))
-- -- -- --                          (~ k)
-- -- -- --                          λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc m)) (i ∧ ~ k))) k
-- -- -- --                                (cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)

-- -- -- --       lem : (k n m : ℕ) (term : _) (a : _) (b : _) (x : _) (y : _) → lemType k n m term a b x y
-- -- -- --       lem k zero m term base b x y = S¹-case i0 k m term b x y
-- -- -- --       lem k zero m term (loop i) b x y = S¹-case i k m term b x y
-- -- -- --       lem k (suc n) m term north b x y = Susp-case i0 k n m term (ptSn (suc n)) b x y
-- -- -- --       lem k (suc n) m term south b x y = Susp-case i1 k n m term (ptSn (suc n)) b x y
-- -- -- --       lem k (suc n) m term (merid a i) b x y = Susp-case i k n m term a b x y

-- -- -- --     MAIN₂ : (sym (Kn→ΩKn+10ₖ _)
-- -- -- --          ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- --          ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- --          ≡ transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
-- -- -- --            (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})
-- -- -- --             (sym ((sym (Kn→ΩKn+10ₖ _)
-- -- -- --          ∙∙ cong (Kn→ΩKn+1 _) ((Kn→ΩKn+1 _ (cup' m n ∣ b ∣ ∣ a ∣)))
-- -- -- --          ∙∙ Kn→ΩKn+10ₖ _))))
-- -- -- --     MAIN₂ = lem57 (suc z) n m ((+-suc m n ∙ +-comm (suc m) n) ∙ cong predℕ term) x y a b
-- -- -- --           ∙ cong (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}
-- -- -- --                                    ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}))
-- -- -- --                  (cong ((λ x → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x ∙∙ (Kn→ΩKn+10ₖ _)))
-- -- -- --                         (lem₃ n m a b ∙ lem₄)
-- -- -- --                  ∙∙ natTranspLem {A = coHomK} _ _ (cup' m n ∣ b ∣ ∣ a ∣) _
-- -- -- --                  (λ _ p → 
-- -- -- --                  (sym (Kn→ΩKn+10ₖ _)
-- -- -- --               ∙∙ cong (Kn→ΩKn+1 _) (sym (Kn→ΩKn+1 _ p))
-- -- -- --               ∙∙ Kn→ΩKn+10ₖ _)) (+'-comm (suc m) (suc n))
-- -- -- --                  ∙∙ refl)

-- -- -- --     MAIN₃ : (sym (Kn→ΩKn+10ₖ _)
-- -- -- --          ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- --          ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- --          ≡ transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
-- -- -- --            (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})
-- -- -- --              (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) })
-- -- -- --                         (sym ((sym (Kn→ΩKn+10ₖ _)
-- -- -- --                        ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' n (suc m) ∣ a ∣ ∣ merid b i ∣))
-- -- -- --                        ∙∙ Kn→ΩKn+10ₖ _)))))
-- -- -- --     MAIN₃ = MAIN₂
-- -- -- --           ∙ cong (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}
-- -- -- --                                   ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}) ∘
-- -- -- --                  (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}
-- -- -- --                                   ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})))
-- -- -- --              (cong (λ x → (sym (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙∙
-- -- -- --                cong (Kn→ΩKn+1 (suc (suc (suc (m + n))))) (sym x)
-- -- -- --                ∙∙ (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣))) (lem₅ n m a b ∙ lem₆)
-- -- -- --                ∙ natTranspLem {λ n → 0ₖ n ≡ 0ₖ n} _ _ ((λ i₂ → cup' n (suc m) ∣ a ∣ ∣ merid b i₂ ∣)) _
-- -- -- --                     (λ _ p → sym (Kn→ΩKn+10ₖ _)
-- -- -- --                            ∙∙ cong (Kn→ΩKn+1 _) (sym p)
-- -- -- --                            ∙∙ Kn→ΩKn+10ₖ _) (+'-comm (suc n) (suc (suc m))))
-- -- -- --     lem₇ : (sym ((sym (Kn→ΩKn+10ₖ _)
-- -- -- --                        ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' n (suc m) ∣ a ∣ ∣ merid b i ∣))
-- -- -- --                        ∙∙ Kn→ΩKn+10ₖ _)))
-- -- -- --            ≡ (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)
-- -- -- --     lem₇ = cong sym (sym (lem₁ _ _ b a))
-- -- -- --         ∙∙ sym (inst _ (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b (~ j) ∣ₕ))
-- -- -- --         ∙∙ sym (inst2 _ _)

-- -- -- --     MAIN₄ : transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
-- -- -- --            (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})
-- -- -- --              (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) })
-- -- -- --                         (sym ((sym (Kn→ΩKn+10ₖ _)
-- -- -- --                        ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' n (suc m) ∣ a ∣ ∣ merid b i ∣))
-- -- -- --                        ∙∙ Kn→ΩKn+10ₖ _)))))
-- -- -- --          ≡ t n m (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)
-- -- -- --     MAIN₄ =
-- -- -- --          cong (λ x → transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
-- -- -- --            (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})
-- -- -- --              (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) }) x)))
-- -- -- --                lem₇

-- -- -- --     help : (cong (λ x → (cong (λ y → cup' (suc n) (suc m) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
-- -- -- --          ≡ λ i j → -ₖ-gen (suc (suc n)) (suc (suc m)) (inl x) (inl y)
-- -- -- --       (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- --        (cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- --     help =
-- -- -- --          ((sym (final n m ((cong (λ x → (cong (λ y → cup' (suc n) (suc m) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))))
-- -- -- --          ∙ cong (transport (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}
-- -- -- --                                  ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}))
-- -- -- --                  (sym (MAIN₃ ∙ MAIN₄))
-- -- -- --          ∙ sym (lem₈ n m (lem₁ n m a b i1)))
-- -- -- --          ∙ cong (cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))))
-- -- -- --            (sym (lem₁ n m a b)))
-- -- -- --        ∙ (λ k → cong (cong (λ z → -ₖ-gen-inl-left (suc (suc n)) (suc (suc m)) x (inl y) z (~ k)) ∘ cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))
-- -- -- --                          (λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ ∣ merid a i ∣))
-- -- -- --   main (suc (suc (suc k))) (suc n) (suc (suc m)) term (inl x) (inr y) (merid a i) (merid b j) = {!!}
-- -- -- --     where
-- -- -- --     lem1 : (k n m : ℕ) (term : _)  (x : is-even n) (y : is-odd (suc (suc (suc m)))) (a : _) (b : _)
-- -- -- --          → cong (cup' (suc m) (suc n) ∣ b ∣ₕ ∘ ∣_∣ₕ) (merid a)
-- -- -- --          ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i))
-- -- -- --                      ((sym (lUnit₁ n _ b) ∙∙ (λ i → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ n _ b))
-- -- -- --     lem1 z n m term x y a = λ { north → m-case i0 a (ptSn (suc m))
-- -- -- --                        ; south → m-case i1 a (ptSn (suc m))
-- -- -- --                        ; (merid b i) → m-case i a b }
-- -- -- --       where
-- -- -- --       m-case : (i : I) → (a : _) (b : _)
-- -- -- --              → cong (cup' (suc m) (suc n) ∣ merid b i ∣ₕ ∘ ∣_∣ₕ) (merid a)
-- -- -- --          ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i))
-- -- -- --                      ((sym (lUnit₁ n _ (merid b i)) ∙∙ (λ j → cup' (suc n) (suc m) ∣ merid a j ∣ₕ ∣ merid b i ∣ₕ) ∙∙ lUnit₂ n _ (merid b i))) 
-- -- -- --       m-case i a b =
-- -- -- --            (λ k j →  main z (suc m) (suc n) term (inl y) (inl x) (merid b i) (merid a j) k)
-- -- -- --         ∙∙ (λ k j → -ₖ-gen-inl-left (suc (suc m)) (suc (suc n)) y (inl x) (subst coHomK (+'-comm (suc (suc n)) (suc (suc m)))
-- -- -- --                        (cup' (suc n) (suc m) ∣ merid a j ∣ ∣ merid b i ∣)) k)
-- -- -- --         ∙∙ (rUnit _
-- -- -- --           ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)) ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k))) (~ k)
-- -- -- --                           ((λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc m)) (i ∧ ~ k))) k
-- -- -- --                                           (cup' (suc n) (suc m) ∣ merid a j ∣ ∣ merid b i ∣)) ∙ refl))

-- -- -- --     lem2 : (sym (Kn→ΩKn+10ₖ (suc (suc (suc m + suc n)))) ∙∙
-- -- -- --                 cong (Kn→ΩKn+1 (suc (suc (suc m + suc n))))
-- -- -- --                 (λ i₁ → cup' (suc m) (suc n) ∣ b ∣ₕ ∣ merid a i₁ ∣ₕ)
-- -- -- --                 ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc m + suc n))))
-- -- -- --         ≡ t₂ n (suc m)
-- -- -- --             (t₃ n (suc m)
-- -- -- --               ((sym (Kn→ΩKn+10ₖ _) ∙∙
-- -- -- --                 cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (cup' (suc m) n ∣ b ∣ ∣ a ∣))
-- -- -- --                 ∙∙ Kn→ΩKn+10ₖ _)))
-- -- -- --     lem2 =
-- -- -- --          cong (λ x → sym (Kn→ΩKn+10ₖ (suc (suc (suc m + suc n)))) ∙∙
-- -- -- --                 cong (Kn→ΩKn+1 (suc (suc (suc m + suc n)))) x
-- -- -- --                 ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc m + suc n))))
-- -- -- --               (lem1 (suc (suc k)) n m ((cong suc (+-suc m n) ∙∙ +-comm (suc (suc m)) n ∙∙ cong predℕ term)) x y a b
-- -- -- --               ∙ cong (transport (λ i₁ →
-- -- -- --                       0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i₁) ≡
-- -- -- --                       0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i₁)))
-- -- -- --                      (lem₃ n (suc m) a b
-- -- -- --                       ∙ cong (Kn→ΩKn+1 (suc (suc (n + suc m))))
-- -- -- --                              (main (suc k) n (suc m) (+-comm n (suc m) ∙∙ cong predℕ (+-comm (suc (suc m)) n) ∙∙ cong predℕ (cong predℕ term))
-- -- -- --                                                      (inr x) (inl y) a b
-- -- -- --                              ∙ -ₖ-gen-inl-right (suc n) (suc (suc m)) (inr x) y
-- -- -- --                                        (subst coHomK (+'-comm (suc (suc m)) (suc n))
-- -- -- --                                         (cup' (suc m) n ∣ b ∣ₕ ∣ a ∣ₕ)))))
-- -- -- --       ∙∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n} _ _ ((Kn→ΩKn+1 _) (subst coHomK (+'-comm (suc (suc m)) (suc n)) (cup' (suc m) n ∣ b ∣ₕ ∣ a ∣ₕ))) _
-- -- -- --            (λ _ x → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x ∙∙ Kn→ΩKn+10ₖ _) (+'-comm (suc (suc n)) (suc (suc m)))
-- -- -- --       ∙∙ cong (subst (λ n₁ → refl ≡ refl) (+'-comm (suc (suc n)) (suc (suc m))))
-- -- -- --               (natTranspLem {A = coHomK} _ _ (cup' (suc m) n ∣ b ∣ ∣ a ∣) _
-- -- -- --                 (λ _ x → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ x) ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- --                 (+'-comm (suc (suc m)) (suc n)))

-- -- -- -- --     lem3 : (n m : ℕ) (x : is-even n) (y : is-odd (suc (suc (suc m)))) (b : _) (a : _) → (sym (lUnit₁ (suc m) n a) ∙∙
-- -- -- -- --                                         (λ i₁ → cup' (suc (suc m)) n ∣ merid b i₁ ∣ₕ ∣ a ∣ₕ) ∙∙
-- -- -- -- --                                         lUnit₂ (suc m) n a)
-- -- -- -- --                                      ≡ transport (λ i → 0ₖ (+'-comm (suc n) (suc (suc (suc m))) i)
-- -- -- -- --                                                        ≡ 0ₖ (+'-comm (suc n) (suc (suc (suc m))) i))
-- -- -- -- --                                          λ i₁ → cup' n (suc (suc m)) ∣ a ∣ₕ ∣ merid b (~ i₁) ∣ₕ
-- -- -- -- --     lem3 = λ { zero m x y b base → S¹-case i0 m x y b
-- -- -- -- --              ; zero m x y b (loop i) → S¹-case i m x y b
-- -- -- -- --              ; (suc n) m x y b north → merid-case i0 n m x y (ptSn (suc n)) b
-- -- -- -- --              ; (suc n) m x y b south → merid-case i1 n m x y (ptSn (suc n)) b
-- -- -- -- --              ; (suc n) m x y b (merid a i) → merid-case i n m x y a b}
-- -- -- -- --       where
-- -- -- -- --       S¹-case : (i : I) → (m : ℕ) (x : is-even zero) (y : is-odd (suc (suc (suc m)))) (b : _) → (sym (lUnit₁ (suc m) zero (loop i)) ∙∙
-- -- -- -- --                                         (λ i₁ → cup' (suc (suc m)) zero ∣ merid b i₁ ∣ₕ ∣ (loop i) ∣ₕ) ∙∙
-- -- -- -- --                                         lUnit₂ (suc m) zero (loop i))
-- -- -- -- --                                      ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc (suc (suc m))) i)
-- -- -- -- --                                                        ≡ 0ₖ (+'-comm (suc zero) (suc (suc (suc m))) i))
-- -- -- -- --                                          λ i₁ → cup' zero (suc (suc m)) ∣ loop i ∣ₕ ∣ merid b (~ i₁) ∣ₕ
-- -- -- -- --       S¹-case i m x y b =
-- -- -- -- --            sym (rUnit _)
-- -- -- -- --         ∙∙ (λ k j → main (suc (suc m)) zero (inr y) (inr x) (merid b j) (loop i) k)
-- -- -- -- --         ∙∙ cong-₂ (suc (suc (suc m))) 1 y x ((λ j₁ → (subst coHomK (+'-comm 1 (suc (suc (suc m))))
-- -- -- -- --                                                        (cup' zero (suc (suc m)) ∣ loop i ∣ ∣ merid b j₁ ∣))))
-- -- -- -- --          ∙ λ k → transp (λ i → 0ₖ (+'-comm 1 (suc (suc (suc m))) (i ∨ ~ k))
-- -- -- -- --                                    ≡ 0ₖ (+'-comm 1 (suc (suc (suc m))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                    (λ j → transp (λ i → coHomK (+'-comm (suc zero) (suc (suc (suc m))) (i ∧ ~ k))) k
-- -- -- -- --                                   (cup' zero (suc (suc m)) ∣ loop i ∣ₕ ∣ merid b (~ j) ∣ₕ))


-- -- -- -- --       merid-case : (i : I) (n m : ℕ) (x : is-even (suc n)) (y : is-odd (suc (suc (suc m)))) (a : _) (b : _)
-- -- -- -- --                  → (sym (lUnit₁ (suc m) (suc n) (merid a i)) ∙∙
-- -- -- -- --                     (λ i₁ → cup' (suc (suc m)) (suc n) ∣ merid b i₁ ∣ₕ ∣ (merid a i) ∣ₕ) ∙∙
-- -- -- -- --                     lUnit₂ (suc m) (suc n) (merid a i))
-- -- -- -- --                  ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i)
-- -- -- -- --                                    ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i))
-- -- -- -- --                      λ i₁ → cup' (suc n) (suc (suc m)) ∣ merid a i ∣ₕ ∣ merid b (~ i₁) ∣ₕ
-- -- -- -- --       merid-case i n m x y a b =
-- -- -- -- --         sym (rUnit _)
-- -- -- -- --         ∙∙ (λ k j → main (suc (suc m)) (suc n) (inr y) (inr x) (merid b j) (merid a i) k)
-- -- -- -- --         ∙∙ cong-₂ (suc (suc (suc m))) (suc (suc n)) y x ((λ j₁ → (subst coHomK (+'-comm (suc (suc n)) (suc (suc (suc m))))
-- -- -- -- --                                                        (cup' (suc n) (suc (suc m)) ∣ merid a i ∣ ∣ merid b j₁ ∣))))
-- -- -- -- --          ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∨ ~ k))
-- -- -- -- --                                    ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                    (λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∧ ~ k))) k
-- -- -- -- --                                   (cup' (suc n) (suc (suc m)) ∣ merid a i ∣ₕ ∣ merid b (~ j) ∣ₕ))

-- -- -- -- --     help : (cong (λ x → (cong (λ y → cup' (suc n) (suc (suc m)) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
-- -- -- -- --          ≡ λ i j → -ₖ-gen (suc (suc n)) (suc (suc (suc m))) (inl x) (inr y)
-- -- -- -- --               (subst coHomK (+'-comm (suc (suc (suc m))) (suc (suc n)))
-- -- -- -- --                (cup' (suc (suc m)) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --     help =
-- -- -- -- --       sym ((λ k i j → -ₖ-gen-inl-left (suc (suc n)) (suc (suc (suc m))) x (inr y)
-- -- -- -- --               (subst coHomK (+'-comm (suc (suc (suc m))) (suc (suc n)))
-- -- -- -- --                (cup' (suc (suc m)) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)) k)
-- -- -- -- --         ∙∙ lem₈ n (suc m) (λ i j → (cup' (suc (suc m)) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --         ∙∙ cong (transport (λ i₁ → refl ≡ refl))
-- -- -- -- --                 (lem₁ n (suc m) a b
-- -- -- -- --               ∙∙ lem2
-- -- -- -- --               ∙∙ cong (t₂ n (suc m) ∘ t₃ n (suc m))
-- -- -- -- --                    (cong (λ x → (sym (Kn→ΩKn+10ₖ _) ∙∙
-- -- -- -- --                                  cong (Kn→ΩKn+1 _) x
-- -- -- -- --                                  ∙∙ Kn→ΩKn+10ₖ _))
-- -- -- -- --                          (sym (lem₃ (suc m) n b a)
-- -- -- -- --                        ∙ lem3 n m x y b a
-- -- -- -- --                       )
-- -- -- -- --                   ∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n} _ _ (λ i₂ → cup' n (suc (suc m)) ∣ a ∣ ∣ merid b (~ i₂) ∣) _
-- -- -- -- --                                   (λ _ x → (sym (Kn→ΩKn+10ₖ _) ∙∙
-- -- -- -- --                                  cong (Kn→ΩKn+1 _) x
-- -- -- -- --                                  ∙∙ Kn→ΩKn+10ₖ _))
-- -- -- -- --                                   (+'-comm (suc n) (suc (suc (suc m))))
-- -- -- -- --                   ∙ cong (t₄ n (suc m)) ( sym (cong sym (lem₁ (suc m) n b a)))))
-- -- -- -- --         ∙∙ final n (suc m)
-- -- -- -- --              (λ i₁ j₁ →
-- -- -- -- --             cup' (suc n) (suc (suc m)) ∣ merid a j₁ ∣ ∣ merid b (~ i₁) ∣)
-- -- -- -- --         ∙∙ inst _ (λ i₁ j₁ →
-- -- -- -- --          cup' (suc n) (suc (suc m)) ∣ merid a j₁ ∣ ∣ merid b i₁ ∣))

-- -- -- -- --   main (suc (suc k)) (suc n) (suc m) term (inr x) (inl y) (merid a i) (merid b j) = {!!}
-- -- -- -- --   main (suc (suc k)) (suc n) (suc m) term (inr x) (inr y) (merid a i) (merid b j) = {!!}

-- -- -- -- -- {-
-- -- -- -- -- cup'-anti-comm' :
-- -- -- -- --   (n m : ℕ) (p : _) (q : _) (x : coHomK (suc n))
-- -- -- -- --     → cup∙ n m x ≡ ((λ y → (-ₖ-gen (suc n) (suc m) p q) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n y x)))
-- -- -- -- --                    , cong ((-ₖ-gen (suc n) (suc m) p q) ∘ (subst coHomK (+'-comm (suc m) (suc n)))) (cup'-lUnit m n x)
-- -- -- -- --                           ∙ cong (-ₖ-gen (suc n) (suc m) p q) (subst-help n m))
-- -- -- -- -- cup'-anti-comm' = {!!}
-- -- -- -- --   where
-- -- -- -- --   open import Cubical.Foundations.Transport

-- -- -- -- --   lem₂ : {k : ℕ} (n m : ℕ) (x : _) (y : _) → (p : refl {x = 0ₖ (suc (suc k))} ≡ refl {x = 0ₖ (suc (suc k))})
-- -- -- -- --                   → cong (cong (-ₖ-gen n m (inr x) (inr y))) p
-- -- -- -- --                   ≡ sym p
-- -- -- -- --   lem₂ n m x y p = {!!}
-- -- -- -- --   {-
-- -- -- -- --          rUnit _
-- -- -- -- --       ∙∙ (λ k → (λ i → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y refl (i ∧ k))
-- -- -- -- --               ∙∙ cong (λ z → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y z k) p
-- -- -- -- --               ∙∙ λ i → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y refl (~ i ∧ k))
-- -- -- -- --       ∙∙ (λ k → transportRefl (λ _ _ → ∣ north ∣) k
-- -- -- -- --               ∙∙ cong sym p
-- -- -- -- --               ∙∙ sym (transportRefl (λ _ _ → ∣ north ∣) k))
-- -- -- -- --       ∙∙ sym (rUnit _)
-- -- -- -- --       ∙∙ sym (inst4 p) -}


-- -- -- -- --   module _ (n m : ℕ) where
-- -- -- -- --     t₁ = transport (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}
-- -- -- -- --                          ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)})

-- -- -- -- --     t₂ = transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}
-- -- -- -- --                          ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
    
-- -- -- -- --     t₃ = transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}
-- -- -- -- --                          ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})

-- -- -- -- --     t₄ = transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))}
-- -- -- -- --                          ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) })

-- -- -- -- --   t : (n m : ℕ) → _ → _
-- -- -- -- --   t n m = transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}
-- -- -- -- --                           ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
-- -- -- -- --          ∘ (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}
-- -- -- -- --                             ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}))
-- -- -- -- --           ∘ (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))}
-- -- -- -- --                             ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) }))


-- -- -- -- --   final : (n m : ℕ) (p : _) → (t₁ n m ∘ t n m) p
-- -- -- -- --           ≡ p
-- -- -- -- --   final n m p =
-- -- -- -- --        sym (substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) (cong suc ((+'-comm (suc (suc n)) (suc m)))) (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- -- --             (((transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}))
-- -- -- -- --           ∘ (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))}))) p))
-- -- -- -- --     ∙∙ sym (substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) (cong (suc ∘ suc) (+'-comm (suc m) (suc n)))
-- -- -- -- --                            (((λ i₁ → suc (+'-comm (suc (suc n)) (suc m) i₁)) ∙ +'-comm (suc (suc m)) (suc (suc n))))
-- -- -- -- --                            (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))}) p))
-- -- -- -- --     ∙∙ sym (substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) (cong suc (+'-comm (suc n) (suc (suc m))))
-- -- -- -- --                            (((λ i₁ → suc (suc (+'-comm (suc m) (suc n) i₁)))
-- -- -- -- --                            ∙ (λ i₁ → suc (+'-comm (suc (suc n)) (suc m) i₁))
-- -- -- -- --                            ∙ +'-comm (suc (suc m)) (suc (suc n)))) p)
-- -- -- -- --     ∙∙ cong (λ x → subst (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) x p) (isSetℕ _ _ _ refl)
-- -- -- -- --     ∙∙ transportRefl p



-- -- -- -- --   lem₈ : (n m : ℕ) → (p : refl {x = 0ₖ _} ≡ refl {x = 0ₖ _})
-- -- -- -- --       → cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))) p
-- -- -- -- --        ≡ transport (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}
-- -- -- -- --                          ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}) p
-- -- -- -- --   lem₈ n m p k = transp (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) (i ∨ ~ k))}
-- -- -- -- --                            ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) (i ∨ ~ k))}) (~ k)
-- -- -- -- --                       ((λ i j → transp (λ i → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (i ∧ ~ k))) k (p i j)))

-- -- -- -- --   lUnit₁ : (n m : ℕ) (a : _) → cup' (suc n) m ∣ north ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
-- -- -- -- --   lUnit₁ n zero base = refl
-- -- -- -- --   lUnit₁ n zero (loop i) = refl
-- -- -- -- --   lUnit₁ n (suc m) north = refl
-- -- -- -- --   lUnit₁ n (suc m) south = refl
-- -- -- -- --   lUnit₁ n (suc m) (merid a i) = refl

-- -- -- -- --   lUnit₂ : (n m : ℕ) (a : _) → cup' (suc n) m ∣ south ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
-- -- -- -- --   lUnit₂ n zero base = refl
-- -- -- -- --   lUnit₂ n zero (loop i) = refl
-- -- -- -- --   lUnit₂ n (suc m) north = refl
-- -- -- -- --   lUnit₂ n (suc m) south = refl
-- -- -- -- --   lUnit₂ n (suc m) (merid a i) = refl

-- -- -- -- --   lUnit₁' : (n : ℕ) (a : _) → cup' zero n ∣ base ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
-- -- -- -- --   lUnit₁' zero base = refl
-- -- -- -- --   lUnit₁' zero (loop i) = refl
-- -- -- -- --   lUnit₁' (suc n) north = refl
-- -- -- -- --   lUnit₁' (suc n) south = refl
-- -- -- -- --   lUnit₁' (suc n) (merid a i) = refl

-- -- -- -- --   lUnit₂' : (n : ℕ) (a : _) → cup' zero n ∣ base ∣ₕ ∣ a ∣ₕ ≡ 0ₖ _
-- -- -- -- --   lUnit₂' zero base = refl
-- -- -- -- --   lUnit₂' zero (loop i) = refl
-- -- -- -- --   lUnit₂' (suc n) north = refl
-- -- -- -- --   lUnit₂' (suc n) south = refl
-- -- -- -- --   lUnit₂' (suc n) (merid a i) = refl

-- -- -- -- --   lem₁ : (n m : ℕ) (a : _) (b : _) → (λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)
-- -- -- -- --        ≡ (sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --        ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --        ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- -- --   lem₁ n m a b =
-- -- -- -- --        (λ k i j → ∣ (sym (rCancel _) ∙∙ cong (λ x → merid x ∙ sym (merid north)) (rUnit (λ i → pre-cup m (suc n) b (merid a i)) (~ k)) ∙∙ rCancel _) i j ∣ₕ)
-- -- -- -- --      ∙ (λ k i j → hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) r j ∣
-- -- -- -- --                                  ; (i = i1) → ∣ rCancel (merid north) r j ∣
-- -- -- -- --                                  ; (j = i0) → ∣ north ∣
-- -- -- -- --                                  ; (j = i1) → ∣ north ∣
-- -- -- -- --                                  ; (k = i0) → ∣ doubleCompPath-filler
-- -- -- -- --                                                   (sym (rCancel _))
-- -- -- -- --                                                   (cong (λ x → merid x ∙ sym (merid north))
-- -- -- -- --                                                   ((λ i → pre-cup m (suc n) b (merid a i)))) (rCancel _) r i j ∣ₕ})
-- -- -- -- --                          (Kn→ΩKn+1 _ (cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣) j))

-- -- -- -- --   lem₃ : (n m : ℕ) (a : _) (b : _)
-- -- -- -- --       → (sym (lUnit₁ n m b) ∙∙ ((λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) ∙∙ lUnit₂ n m b)
-- -- -- -- --        ≡ Kn→ΩKn+1 _ (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ)
-- -- -- -- --   lem₃ n zero a base = sym (rUnit refl) ∙ sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --   lem₃ n zero a (loop i) k =
-- -- -- -- --     hcomp (λ r → λ {(i = i0) → compPath-filler' (sym (rUnit refl)) (sym (Kn→ΩKn+10ₖ _)) r k
-- -- -- -- --                    ; (i = i1) → compPath-filler' (sym (rUnit refl)) (sym (Kn→ΩKn+10ₖ _)) r k
-- -- -- -- --                    ; (k = i0) → rUnit (λ i₂ → cup' (suc n) zero ∣ merid a i₂ ∣ₕ ∣ loop i ∣ₕ) r
-- -- -- -- --                    ; (k = i1) → Kn→ΩKn+1 (suc (suc (n + zero)))
-- -- -- -- --                                   (cup' n zero ∣ a ∣ₕ ∣ loop i ∣ₕ) })
-- -- -- -- --           λ j → hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
-- -- -- -- --                       ; (i = i1) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
-- -- -- -- --                       ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
-- -- -- -- --                                       (cong (λ x → merid x ∙ sym (merid north)) ((λ i → pre-cup n zero a (loop i))))
-- -- -- -- --                                       (rCancel _) r i j ∣ₕ
-- -- -- -- --                       ; (k = i1) → Kn→ΩKn+1 (suc (suc (n + zero)))
-- -- -- -- --                                        (cup' n zero ∣ a ∣ₕ ∣ loop i ∣ₕ) j
-- -- -- -- --                       ; (j = i0) → ∣ north ∣
-- -- -- -- --                       ; (j = i1) → ∣ north ∣})
-- -- -- -- --                  (Kn→ΩKn+1 _ (cup' n zero ∣ a ∣ₕ ∣ loop i ∣ₕ) j)
-- -- -- -- --   lem₃ n (suc m) a north = sym (rUnit refl) ∙ sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --   lem₃ n (suc m) a south = sym (rUnit refl) ∙ sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --   lem₃ n (suc m) a (merid b i) k =
-- -- -- -- --     hcomp (λ r → λ {(i = i0) → compPath-filler' (sym (rUnit refl)) (sym (Kn→ΩKn+10ₖ _)) r k
-- -- -- -- --                    ; (i = i1) → compPath-filler' (sym (rUnit refl)) (sym (Kn→ΩKn+10ₖ _)) r k
-- -- -- -- --                    ; (k = i0) → rUnit (λ i₂ → cup' (suc n) (suc m) ∣ merid a i₂ ∣ₕ ∣ merid b i ∣ₕ) r
-- -- -- -- --                    ; (k = i1) → Kn→ΩKn+1 (suc (suc (n + suc m)))
-- -- -- -- --                                   (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ)})
-- -- -- -- --       (λ j → hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
-- -- -- -- --                       ; (i = i1) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
-- -- -- -- --                       ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
-- -- -- -- --                                       (cong (λ x → merid x ∙ sym (merid north)) (rUnit (λ i → pre-cup n (suc m) a (merid b i)) r))
-- -- -- -- --                                       (rCancel _) r i j ∣ₕ
-- -- -- -- --                       ; (k = i1) → Kn→ΩKn+1 (suc (suc (n + suc m)))
-- -- -- -- --                                        (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ) j
-- -- -- -- --                       ; (j = i0) → ∣ north ∣
-- -- -- -- --                       ; (j = i1) → ∣ north ∣})
-- -- -- -- --              (Kn→ΩKn+1 (suc (suc (n + suc m)))
-- -- -- -- --                                        (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ) j))

-- -- -- -- --   lem₃-take2 : (n : ℕ) (a : _) → (sym (lUnit₁' n a)
-- -- -- -- --                                 ∙∙ (λ j → cup' zero n ∣ loop j ∣ ∣ a ∣)
-- -- -- -- --                                 ∙∙ lUnit₁' n a) ≡ Kn→ΩKn+1 _ ∣ a ∣
-- -- -- -- --   lem₃-take2 zero base = sym (rUnit _) ∙ sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --   lem₃-take2 zero (loop i) k j = 
-- -- -- -- --     hcomp (λ r → λ {(i = i0) → compPath-filler' (sym (rUnit _)) (sym (Kn→ΩKn+10ₖ _)) r k j
-- -- -- -- --                    ; (i = i1) → compPath-filler' (sym (rUnit _)) (sym (Kn→ΩKn+10ₖ _)) r k j
-- -- -- -- --                    ; (k = i0) → rUnit (λ j₁ → cup' zero zero ∣ loop j₁ ∣ ∣ loop i ∣) r j
-- -- -- -- --                    ; (k = i1) → Kn→ΩKn+1 1 ∣ loop i ∣ j
-- -- -- -- --                    ; (j = i0) → ∣ north ∣
-- -- -- -- --                    ; (j = i1) → ∣ north ∣})
-- -- -- -- --           (hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid base) (r ∧ ~ k) j ∣ₕ
-- -- -- -- --                    ; (i = i1) → ∣ rCancel (merid base) (r ∧ ~ k) j ∣ₕ
-- -- -- -- --                    ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel (merid base)))
-- -- -- -- --                                                         (λ i → merid (loop i) ∙ sym (merid base))
-- -- -- -- --                                                         (rCancel (merid base)) r i j ∣ₕ
-- -- -- -- --                    ; (k = i1) → Kn→ΩKn+1 1 ∣ loop i ∣ j
-- -- -- -- --                    ; (j = i0) → ∣ north ∣
-- -- -- -- --                    ; (j = i1) → ∣ north ∣})
-- -- -- -- --                  (Kn→ΩKn+1 1 ∣ loop i ∣ j))
-- -- -- -- --   lem₃-take2 (suc n) north = sym (rUnit _) ∙ sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --   lem₃-take2 (suc n) south = sym (rUnit _) ∙ (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc n))) (cong ∣_∣ₕ (merid (ptSn (suc n)))))
-- -- -- -- --   lem₃-take2 (suc n) (merid a i) k j =
-- -- -- -- --     hcomp (λ r → λ {(i = i0) → compPath-filler' (sym (rUnit _)) (sym (Kn→ΩKn+10ₖ _)) r k j
-- -- -- -- --                    ; (i = i1) → compPath-filler' (sym (rUnit _)) (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 (suc (suc n))) (cong ∣_∣ₕ (merid (ptSn (suc n))))) r k j
-- -- -- -- --                    ; (k = i0) → rUnit (λ j₁ → cup' zero (suc n) ∣ loop j₁ ∣ ∣ merid a i ∣) r j
-- -- -- -- --                    ; (k = i1) → Kn→ΩKn+1 (suc (suc n)) ∣ merid a i ∣ j
-- -- -- -- --                    ; (j = i0) → ∣ north ∣
-- -- -- -- --                    ; (j = i1) → ∣ north ∣})
-- -- -- -- --            (hcomp (λ r → λ {(i = i0) → ∣ rCancel (merid north) (r ∧ ~ k) j ∣ₕ
-- -- -- -- --                            ; (i = i1) → compPath-filler' (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 (suc (suc n))) (cong ∣_∣ₕ (merid (ptSn (suc n))))) r k j
-- -- -- -- --                            ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel (merid north)))
-- -- -- -- --                                                                 (λ i → merid ((merid a ∙ sym (merid (ptSn _))) i) ∙ sym (merid north))
-- -- -- -- --                                                                 (rCancel (merid north)) r i j ∣ₕ
-- -- -- -- --                            ; (k = i1) → Kn→ΩKn+1 (suc (suc n)) ∣ merid a i ∣ j
-- -- -- -- --                            ; (j = i0) → ∣ north ∣
-- -- -- -- --                            ; (j = i1) → ∣ north ∣})
-- -- -- -- --                   ∣ (merid (compPath-filler (merid a) (sym (merid (ptSn _))) (~ k) i) ∙ sym (merid (ptSn _))) j ∣ₕ)

-- -- -- -- --   main : (n m : ℕ) (p : _) (q : _) (a : _) (b : _)
-- -- -- -- --       → (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡ (-ₖ-gen (suc n) (suc m) p q) (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ₕ ∣ a ∣ₕ))
-- -- -- -- --   main zero zero p q base base = refl
-- -- -- -- --   main zero zero p q base (loop i) = refl
-- -- -- -- --   main zero zero p q (loop i) base = refl
-- -- -- -- --   main zero zero p q (loop i) (loop j) = {!!}
-- -- -- -- --   main zero (suc m) p q base north = refl
-- -- -- -- --   main zero (suc m) p q base south = refl
-- -- -- -- --   main zero (suc m) p q base (merid a i) = refl
-- -- -- -- --   main zero (suc m) p q (loop i) north = refl
-- -- -- -- --   main zero (suc m) p q (loop i) south = refl
-- -- -- -- --   main (suc n) zero p q north base = refl
-- -- -- -- --   main (suc n) zero p q north (loop i) = refl
-- -- -- -- --   main (suc n) zero p q south base = refl
-- -- -- -- --   main (suc n) zero p q south (loop i) = refl
-- -- -- -- --   main (suc n) zero p q (merid a i) base = refl
-- -- -- -- --   main (suc n) (suc m) p q north north = refl
-- -- -- -- --   main (suc n) (suc m) p q north south = refl
-- -- -- -- --   main (suc n) (suc m) p q north (merid a i) = refl
-- -- -- -- --   main (suc n) (suc m) p q south north = refl
-- -- -- -- --   main (suc n) (suc m) p q south south = refl
-- -- -- -- --   main (suc n) (suc m) p q south (merid a i) = refl
-- -- -- -- --   main (suc n) (suc m) p q (merid a i) north = refl
-- -- -- -- --   main (suc n) (suc m) p q (merid a i) south = refl
-- -- -- -- --   main (suc n) zero (inl x) q (merid a i) (loop j) =
-- -- -- -- --     {!!} -- λ k → help k i j
-- -- -- -- --     where
-- -- -- -- --     lem1 : (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)}
-- -- -- -- --                             ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)}))
-- -- -- -- --                 (λ i j → ∣ (sym (rCancel _)
-- -- -- -- --                          ∙∙ cong (λ x → merid x ∙ sym (merid north)) (merid a ∙ sym (merid (ptSn _)))
-- -- -- -- --                          ∙∙ rCancel _) i j ∣ₕ)
-- -- -- -- --         ≡ (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north))
-- -- -- -- --                      (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- -- -- -- --                        (merid a ∙ sym (merid (ptSn _))))
-- -- -- -- --                      ∙∙ rCancel (merid north)))
-- -- -- -- --     lem1 = 
-- -- -- -- --          (λ k → (transport (λ i → refl {x = 0ₖ (isSetℕ _ _ (+'-comm 1 (suc (suc n))) (cong (suc ∘ suc ∘ suc) (sym (+-comm n 0))) k i)}
-- -- -- -- --                                   ≡ refl {x = 0ₖ (isSetℕ _ _ (+'-comm 1 (suc (suc n))) (cong (suc ∘ suc ∘ suc) (sym (+-comm n 0))) k i)}))
-- -- -- -- --                 (λ i j → ∣ (sym (rCancel _)
-- -- -- -- --                          ∙∙ cong (λ x → merid x ∙ sym (merid north)) (merid a ∙ sym (merid (ptSn _)))
-- -- -- -- --                          ∙∙ rCancel _) i j ∣ₕ))
-- -- -- -- --        ∙ sym (natTranspLem {A = λ n → Path (S₊ (suc (suc n))) north north} _ _
-- -- -- -- --                (merid a ∙ sym (merid (ptSn _))) (λ n → refl {x = 0ₖ (3 + n)} ≡ refl {x = 0ₖ (3 + n)})
-- -- -- -- --                (λ _ x → (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north)) x
-- -- -- -- --                      ∙∙ rCancel (merid north)))) (sym (+-comm n 0)))


-- -- -- -- --     coolLem : (n : ℕ)  (x : is-odd (suc n)) (a : _) → Path (Path (coHomK (suc (suc (n + zero)))) _ _)
-- -- -- -- --                    (cong ∣_∣ₕ (cong (pre-cup n zero a) loop))
-- -- -- -- --                    (cong ∣_∣ₕ (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- -- -- -- --                                                                          (sym (merid a ∙ sym (merid (ptSn _))))))
-- -- -- -- --     coolLem n x a =
-- -- -- -- --          pre-cool n x a
-- -- -- -- --       ∙∙ pre-cool2 n a
-- -- -- -- --       ∙∙ (λ k → (transport (λ i₁ → 0ₖ (+'-comm 1 (suc n) i₁) ≡ 0ₖ (+'-comm 1 (suc n) i₁))
-- -- -- -- --                            (sym (lem₃-take2 n a k))))
-- -- -- -- --        ∙ sym lem2
-- -- -- -- --       where
-- -- -- -- --       lem2 : (cong ∣_∣ₕ (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- -- -- -- --                                                                          (sym (merid a ∙ sym (merid (ptSn _))))))
-- -- -- -- --            ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc n) i)
-- -- -- -- --                                   ≡ 0ₖ (+'-comm (suc zero) (suc n) i))
-- -- -- -- --                        (sym (Kn→ΩKn+1 _ ∣ a ∣))
-- -- -- -- --       lem2 = natTranspLem {A = λ n → Path (S₊ (suc (suc n))) north north} _ _
-- -- -- -- --                           (sym (merid a ∙ sym (merid (ptSn _)))) (λ n → 0ₖ (suc (suc n)) ≡ 0ₖ (suc (suc n)))
-- -- -- -- --                           (λ _ → cong ∣_∣ₕ) (sym (+-comm n 0))
-- -- -- -- --            ∙ λ k → transport (λ i → 0ₖ (isSetℕ _ _ (cong (suc ∘ suc) (sym (+-comm n zero))) (+'-comm (suc zero) (suc n)) k i)
-- -- -- -- --                                     ≡ 0ₖ (isSetℕ _ _ (cong (suc ∘ suc) (sym (+-comm n zero))) (+'-comm (suc zero) (suc n)) k i))
-- -- -- -- --                               (sym (Kn→ΩKn+1 _ ∣ a ∣))

-- -- -- -- --       extraP : (n : ℕ) → subst coHomK (+'-comm 1 (suc n)) (0ₖ (suc (suc n))) ≡ 0ₖ _
-- -- -- -- --       extraP zero = refl
-- -- -- -- --       extraP (suc n) = refl

-- -- -- -- --       pre-cool-S¹ : (i : I)
-- -- -- -- --           → Path (Path (coHomK (suc (suc (zero + zero)))) _ _)
-- -- -- -- --                      (cong ∣_∣ₕ (cong (pre-cup zero zero (loop i)) loop))
-- -- -- -- --                      (sym (extraP zero) ∙∙ (cong (subst coHomK (+'-comm (suc zero) (suc zero)))
-- -- -- -- --                         (sym (lUnit₁' zero (loop i))
-- -- -- -- --                      ∙∙ (λ j → cup' zero zero ∣ loop (~ j) ∣ ∣ (loop i) ∣)
-- -- -- -- --                      ∙∙ lUnit₁' zero (loop i))) ∙∙ extraP zero)
-- -- -- -- --       pre-cool-S¹ i =
-- -- -- -- --            rUnit _
-- -- -- -- --         ∙∙ (λ k → refl
-- -- -- -- --                 ∙∙ (λ j → main zero zero (inr tt) (inr tt) (loop i) (loop j) k)
-- -- -- -- --                 ∙∙ refl)
-- -- -- -- --         ∙∙ (λ k → refl
-- -- -- -- --                 ∙∙ (cong-₂ (suc zero) 1 tt tt
-- -- -- -- --                              (cong (subst coHomK (+'-comm 1 (suc zero)))
-- -- -- -- --                               (λ j → cup' zero zero ∣ loop j ∣ₕ ∣ loop i ∣ₕ)) k)
-- -- -- -- --                 ∙∙ refl)
-- -- -- -- --         ∙∙ rUnit _
-- -- -- -- --         ∙∙ refl


-- -- -- -- --       pre-cool-merid : (n : ℕ) (p : is-even (suc n)) (i : I) (a : _)
-- -- -- -- --           → Path (Path (coHomK (suc (suc ((suc n) + zero)))) _ _)
-- -- -- -- --                      (cong ∣_∣ₕ (cong (pre-cup (suc n) zero (merid a i)) loop))
-- -- -- -- --                      (sym (extraP (suc n)) ∙∙ (cong (subst coHomK (+'-comm (suc zero) (suc (suc n))))
-- -- -- -- --                         (sym (lUnit₁' (suc n) (merid a i))
-- -- -- -- --                      ∙∙ (λ j → cup' zero (suc n) ∣ loop (~ j) ∣ ∣ (merid a i) ∣)
-- -- -- -- --                      ∙∙ lUnit₁' (suc n) (merid a i))) ∙∙ extraP (suc n))
-- -- -- -- --       pre-cool-merid n p i a =
-- -- -- -- --            rUnit _
-- -- -- -- --         ∙∙ (λ k → refl
-- -- -- -- --                 ∙∙ (λ j → main (suc n) zero (inr p) (inr tt) (merid a i) (loop j) k)
-- -- -- -- --                 ∙∙ refl)
-- -- -- -- --         ∙∙ (λ k → refl
-- -- -- -- --                 ∙∙ (cong-₂ (suc (suc n)) 1 p tt
-- -- -- -- --                              (cong (subst coHomK (+'-comm 1 (suc (suc n))))
-- -- -- -- --                               (λ j → cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)) k)
-- -- -- -- --                 ∙∙ refl)
-- -- -- -- --         ∙∙ rUnit _
-- -- -- -- --         ∙∙ refl


-- -- -- -- --       pre-cool : (n : ℕ) (p : is-even n) (a : _) → Path (Path (coHomK (suc (suc (n + zero)))) _ _)
-- -- -- -- --                    (cong ∣_∣ₕ (cong (pre-cup n zero a) loop))
-- -- -- -- --                     (sym (extraP n) ∙∙ (cong (subst coHomK (+'-comm (suc zero) (suc n)))
-- -- -- -- --                         (sym (lUnit₁' n a)
-- -- -- -- --                      ∙∙ (λ j → cup' zero n ∣ loop (~ j) ∣ ∣ a ∣)
-- -- -- -- --                      ∙∙ lUnit₁' n a)) ∙∙ extraP n)
-- -- -- -- --       pre-cool zero p base = pre-cool-S¹ i0
-- -- -- -- --       pre-cool zero p (loop i) = pre-cool-S¹ i
-- -- -- -- --       pre-cool (suc n) p north = pre-cool-merid n p i0 (ptSn _)
-- -- -- -- --       pre-cool (suc n) p south = pre-cool-merid n p i1 (ptSn _)
-- -- -- -- --       pre-cool (suc n) p (merid a i) = pre-cool-merid n p i a

-- -- -- -- --       pre-cool2 : (n : ℕ) (a : _) →
-- -- -- -- --                   ((sym (extraP n) ∙∙ (cong (subst coHomK (+'-comm (suc zero) (suc n)))
-- -- -- -- --                         (sym (lUnit₁' n a)
-- -- -- -- --                      ∙∙ (λ j → cup' zero n ∣ loop (~ j) ∣ ∣ a ∣)
-- -- -- -- --                      ∙∙ lUnit₁' n a)) ∙∙ extraP n))
-- -- -- -- --                 ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc n) i)
-- -- -- -- --                                   ≡ 0ₖ (+'-comm (suc zero) (suc n) i))
-- -- -- -- --                             (sym (lUnit₁' n a)
-- -- -- -- --                           ∙∙ (λ j → cup' zero n ∣ loop (~ j) ∣ ∣ a ∣)
-- -- -- -- --                           ∙∙ lUnit₁' n a)
-- -- -- -- --       pre-cool2 zero a =
-- -- -- -- --           sym (rUnit _)
-- -- -- -- --         ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc zero) (suc zero) (i ∨ ~ k))
-- -- -- -- --                                  ≡ 0ₖ (+'-comm (suc zero) (suc zero) (i ∨ ~ k))) (~ k)
-- -- -- -- --                            λ j → transp (λ i → coHomK (+'-comm (suc zero) (suc zero) (i ∧ ~ k))) k
-- -- -- -- --                                          ((sym (lUnit₁' zero a)
-- -- -- -- --                           ∙∙ (λ j → cup' zero zero ∣ loop (~ j) ∣ ∣ a ∣)
-- -- -- -- --                           ∙∙ lUnit₁' zero a) j)
-- -- -- -- --       pre-cool2 (suc n) a =
-- -- -- -- --          sym (rUnit _)
-- -- -- -- --        ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ ~ k))
-- -- -- -- --                                  ≡ 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ ~ k))) (~ k)
-- -- -- -- --                            λ j → transp (λ i → coHomK (+'-comm (suc zero) (suc (suc n)) (i ∧ ~ k))) k
-- -- -- -- --                                          ((sym (lUnit₁' (suc n) a)
-- -- -- -- --                           ∙∙ (λ j → cup' zero (suc n) ∣ loop (~ j) ∣ ∣ a ∣)
-- -- -- -- --                           ∙∙ lUnit₁' (suc n) a) j)

-- -- -- -- --     lem2 : cong
-- -- -- -- --       (λ x₁ → cong (λ y → cup' (suc n) zero ∣ x₁ ∣ₕ ∣ y ∣ₕ) loop)
-- -- -- -- --       (merid a)
-- -- -- -- --          ≡ (flipSquare ((cong (cong ∣_∣ₕ) (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north))
-- -- -- -- --                      (sym (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- -- -- -- --                        (merid a ∙ sym (merid (ptSn _)))))
-- -- -- -- --                      ∙∙ rCancel (merid north)))))
-- -- -- -- --     lem2 k i j =
-- -- -- -- --       hcomp (λ r → λ { (i = i0) → ∣ north ∣ₕ
-- -- -- -- --                       ; (i = i1) → ∣ north ∣ₕ
-- -- -- -- --                       ; (j = i0) → ∣ rCancel (merid north) r i ∣ₕ
-- -- -- -- --                       ; (j = i1) → ∣ rCancel (merid north) r i ∣ₕ
-- -- -- -- --                       ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
-- -- -- -- --                                                            (cong (λ x → merid x ∙ sym (merid north)) (λ i → pre-cup n zero a (loop i)))
-- -- -- -- --                                                            (rCancel _) r j i ∣ₕ
-- -- -- -- --                       ; (k = i1) → ∣ doubleCompPath-filler (sym (rCancel _))
-- -- -- -- --                                                            (cong (λ x → merid x ∙ sym (merid north))
-- -- -- -- --                                                              ((transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- -- -- -- --                                                                          (sym (merid a ∙ sym (merid (ptSn _)))))))
-- -- -- -- --                                                            (rCancel _) r j i ∣ₕ})
-- -- -- -- --             (Kn→ΩKn+1 _ (coolLem n x a k j) i)

-- -- -- -- --     help : cong (λ x → cong (λ y → cup' (suc n) zero ∣ x ∣ₕ ∣ y ∣ₕ) loop) (merid a)
-- -- -- -- --          ≡ λ i j → -ₖ-gen (suc (suc n)) 1 (inl x) (inr tt)
-- -- -- -- --       (subst coHomK (+'-comm 1 (suc (suc n)))
-- -- -- -- --        (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --     help =
-- -- -- -- --          (lem2
-- -- -- -- --         ∙ sym (inst _ (sym ((cong (cong ∣_∣ₕ) (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north))
-- -- -- -- --                      (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- -- -- -- --                        (merid a ∙ sym (merid (ptSn _))))
-- -- -- -- --                      ∙∙ rCancel (merid north))))))
-- -- -- -- --         ∙ sym lem1)
-- -- -- -- --       ∙∙ (λ k → transp (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) (i ∨ k))}
-- -- -- -- --                               ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) (i ∨ k))}) k
-- -- -- -- --                         (λ i j → transp (λ i → coHomK (+'-comm 1 (suc (suc n)) (i ∧ k))) (~ k)
-- -- -- -- --                           (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))
-- -- -- -- --       ∙∙ λ k i j →
-- -- -- -- --               -ₖ-gen-inl-left (suc (suc n)) 1 x (inr tt)
-- -- -- -- --                  (subst coHomK (+'-comm 1 (suc (suc n)))
-- -- -- -- --                   (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)) (~ k)
-- -- -- -- --   main zero (suc m) (inr tt) q (loop i) (merid a j) =
-- -- -- -- --     {!!} -- λ k → help k i j
-- -- -- -- --     where
-- -- -- -- --     fin : (q : _) →
-- -- -- -- --       (λ i₁ j₁ → cup' zero (suc m) ∣ loop i₁ ∣ₕ ∣ merid a j₁ ∣ₕ) ≡
-- -- -- -- --       (λ i₁ j₁ →
-- -- -- -- --          -ₖ-gen 1 (suc (suc m)) (inr tt) q
-- -- -- -- --          (-ₖ-gen (suc (suc m)) 1 q (inr tt)
-- -- -- -- --           (cup' zero (suc m) ∣ loop i₁ ∣ₕ ∣ merid a j₁ ∣ₕ)))
-- -- -- -- --     fin (inl x) k i j =
-- -- -- -- --       -ₖ-gen-inl-right 1 (suc (suc m)) (inr tt) x
-- -- -- -- --         (-ₖ-gen-inl-left (suc (suc m)) 1 x (inr tt)
-- -- -- -- --           (cup' zero (suc m) ∣ loop i ∣ₕ ∣ merid a j ∣ₕ)
-- -- -- -- --          (~ k)) (~ k)
-- -- -- -- --     fin (inr x) =
-- -- -- -- --         rUnit _
-- -- -- -- --       ∙∙ (λ k → (λ i → cong-₂ 1 (suc (suc m)) tt x
-- -- -- -- --                            (cong-₂ (suc (suc m)) 1 x tt
-- -- -- -- --                            (λ i₁ → cup' zero (suc m) ∣ base ∣ₕ ∣ merid a i₁ ∣ₕ) (~ k ∨ ~ i))
-- -- -- -- --                            (~ k ∨ ~ i))
-- -- -- -- --               ∙∙ (cong (λ z → cong-₂ (suc zero) (suc (suc m)) tt x z (~ k))
-- -- -- -- --                    (cong (λ z → cong-₂ (suc (suc m)) (suc zero) x tt z (~ k))
-- -- -- -- --                      (cong (λ x → cong (λ y → cup' zero (suc m) ∣ x ∣ₕ ∣ y ∣ₕ) (merid a)) loop)))
-- -- -- -- --               ∙∙ λ i → cong-₂ 1 (suc (suc m)) tt x
-- -- -- -- --                            (cong-₂ (suc (suc m)) 1 x tt
-- -- -- -- --                            (λ i₁ → cup' zero (suc m) ∣ base ∣ₕ ∣ merid a i₁ ∣ₕ) (~ k ∨ i))
-- -- -- -- --                            (~ k ∨ i))
-- -- -- -- --       ∙∙ ((λ k → (λ i → cong-₂ 1 (suc (suc m)) tt x
-- -- -- -- --                            (transportRefl (refl {x = refl {x = 0ₖ (suc (suc (suc m)))}}) k (~ i))
-- -- -- -- --                            (~ i))
-- -- -- -- --              ∙∙ cong (cong (trMap (-ₖ-helper 1 (suc (suc m)) (inr tt) (inr x))) ∘
-- -- -- -- --                  (cong (trMap (-ₖ-helper (suc (suc m)) 1 (inr x) (inr tt)))))
-- -- -- -- --                   (λ i j → cup' zero (suc m) ∣ loop i ∣ ∣ merid a j ∣)
-- -- -- -- --                ∙∙ λ i → cong-₂ 1 (suc (suc m)) tt x
-- -- -- -- --                            (transportRefl (refl {x = refl {x = 0ₖ (suc (suc (suc m)))}}) k i) i)
-- -- -- -- --       ∙∙ (λ k → (λ i → transportRefl (refl {x = refl {x = 0ₖ (suc (suc (suc m)))}}) k (~ i))
-- -- -- -- --               ∙∙ cong (cong (trMap (-ₖ-helper 1 (suc (suc m)) (inr tt) (inr x))) ∘
-- -- -- -- --                  (cong (trMap (-ₖ-helper (suc (suc m)) 1 (inr x) (inr tt)))))
-- -- -- -- --                   (λ i j → cup' zero (suc m) ∣ loop i ∣ ∣ merid a j ∣)
-- -- -- -- --               ∙∙ λ i → transportRefl (refl {x = refl {x = 0ₖ (suc (suc (suc m)))}}) k i)
-- -- -- -- --       ∙∙ sym (rUnit _))

-- -- -- -- --     help : (λ i j → cup' zero (suc m) ∣ loop i ∣ₕ ∣ merid a j ∣ₕ)
-- -- -- -- --       ≡ cong (cong (-ₖ-gen 1 (suc (suc m)) (inr tt) q ∘
-- -- -- -- --       (subst coHomK (+'-comm (suc (suc m)) 1))))
-- -- -- -- --        (λ i j → cup' (suc m) zero ∣ merid a j ∣ₕ ∣ loop i ∣ₕ)
-- -- -- -- --     help = ((fin q
-- -- -- -- --            ∙ sym (transportRefl _))
-- -- -- -- --          ∙ (λ k → subst (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) (isSetℕ _ _ refl (+'-comm 1 (suc (suc m)) ∙ +'-comm (suc (suc m)) 1) k)
-- -- -- -- --                    (λ i j → -ₖ-gen 1 (suc (suc m)) (inr tt) q
-- -- -- -- --                                          (-ₖ-gen (suc (suc m)) 1 q (inr tt)
-- -- -- -- --                                              (cup' zero (suc m) ∣ loop i ∣ₕ ∣ merid a j ∣ₕ)))))
-- -- -- -- --         ∙∙ substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n})
-- -- -- -- --                            (+'-comm (suc zero) (suc (suc m))) (+'-comm (suc (suc m)) (suc zero))
-- -- -- -- --                            (λ i j → -ₖ-gen 1 (suc (suc m)) (inr tt) q
-- -- -- -- --                                          (-ₖ-gen (suc (suc m)) 1 q (inr tt)
-- -- -- -- --                                              (cup' zero (suc m) ∣ loop i ∣ₕ ∣ merid a j ∣ₕ)))
-- -- -- -- --         ∙∙ cong (transport (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc zero) i)}
-- -- -- -- --                                 ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc zero) i)}))
-- -- -- -- --                 (λ k → transp (λ i → refl {x = 0ₖ (+'-comm (suc zero) (suc (suc m)) (i ∨ k))}
-- -- -- -- --                                 ≡ refl {x = 0ₖ (+'-comm (suc zero) (suc (suc m)) (i ∨ k))}) k
-- -- -- -- --                                λ i j → -ₖ-gen 1 (suc (suc m)) (inr tt) q
-- -- -- -- --                                          (-ₖ-gen (suc (suc m)) 1 q (inr tt)
-- -- -- -- --                                            (transp (λ i → coHomK (+'-comm 1 (suc (suc m)) (i ∧ k))) (~ k)
-- -- -- -- --                                              (cup' zero (suc m) ∣ loop i ∣ₕ ∣ merid a j ∣ₕ))))
-- -- -- -- --         ∙∙ (λ k → transp (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc zero) (i ∨ k))}
-- -- -- -- --                                 ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc zero) (i ∨ k))}) k
-- -- -- -- --                   λ i j → -ₖ-gen 1 (suc (suc m)) (inr tt) q
-- -- -- -- --                             (transp (λ i → coHomK (+'-comm (suc (suc m)) (suc zero) (i ∧ k))) (~ k)
-- -- -- -- --                               (-ₖ-gen (suc (suc m)) 1 q (inr tt)
-- -- -- -- --                                 (subst coHomK (+'-comm 1 (suc (suc m)))
-- -- -- -- --                                  (cup' zero (suc m) ∣ loop i ∣ₕ ∣ merid a j ∣ₕ)))))
-- -- -- -- --         ∙∙ λ k i j →
-- -- -- -- --              -ₖ-gen 1 (suc (suc m)) (inr tt) q (subst coHomK (+'-comm (suc (suc m)) 1)
-- -- -- -- --                (main (suc m) zero q (inr tt) (merid a j) (loop i) (~ k)))
-- -- -- -- --   main (suc n) zero (inr x) (inr tt) (merid a i) (loop j) = λ k → help k i j
-- -- -- -- --     where
-- -- -- -- --     lem1 : (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)} ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)}))
-- -- -- -- --                 (λ i j → ∣ (sym (rCancel _) ∙∙ cong (λ x → merid x ∙ sym (merid north)) (merid a ∙ sym (merid (ptSn _))) ∙∙ rCancel _) j i ∣ₕ)
-- -- -- -- --         ≡ flipSquare (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north))
-- -- -- -- --                      (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- -- -- -- --                        (merid a ∙ sym (merid (ptSn _))))
-- -- -- -- --                      ∙∙ rCancel (merid north)))
-- -- -- -- --     lem1 =
-- -- -- -- --          (λ k → (transport (λ i → refl {x = 0ₖ (isSetℕ _ _ (+'-comm 1 (suc (suc n))) (cong (suc ∘ suc ∘ suc) (sym (+-comm n 0))) k i)}
-- -- -- -- --                                   ≡ refl {x = 0ₖ (isSetℕ _ _ (+'-comm 1 (suc (suc n))) (cong (suc ∘ suc ∘ suc) (sym (+-comm n 0))) k i)}))
-- -- -- -- --                 (λ i j → ∣ (sym (rCancel _)
-- -- -- -- --                          ∙∙ cong (λ x → merid x ∙ sym (merid north)) (merid a ∙ sym (merid (ptSn _)))
-- -- -- -- --                          ∙∙ rCancel _) j i ∣ₕ))
-- -- -- -- --        ∙ sym (natTranspLem {A = λ n → Path (S₊ (suc (suc n))) north north} _ _
-- -- -- -- --                (merid a ∙ sym (merid (ptSn _))) (λ n → refl {x = 0ₖ (3 + n)} ≡ refl {x = 0ₖ (3 + n)})
-- -- -- -- --                (λ _ x → flipSquare (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north)) x
-- -- -- -- --                      ∙∙ rCancel (merid north)))) (sym (+-comm n 0)))

-- -- -- -- --     coolLem : (n : ℕ)  (x : is-even (suc n)) (a : _) → Path (Path (coHomK (suc (suc (n + zero)))) _ _)
-- -- -- -- --                    (cong ∣_∣ₕ (cong (pre-cup n zero a) loop))
-- -- -- -- --                    (cong ∣_∣ₕ (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- -- -- -- --                                                                          (merid a ∙ sym (merid (ptSn _)))))
-- -- -- -- --     coolLem (suc n) x a =
-- -- -- -- --          pre-cool a
-- -- -- -- --       ∙∙ (pre-cool2
-- -- -- -- --        ∙ cong (transport (λ i₁ → 0ₖ (+'-comm 1 (suc (suc n)) i₁) ≡ 0ₖ (+'-comm 1 (suc (suc n)) i₁)))
-- -- -- -- --               (lem₃-take2 _ a))
-- -- -- -- --       ∙∙ sym lem2
-- -- -- -- --       where
-- -- -- -- --       pre-cool-merid : (i : I) → (a : _)
-- -- -- -- --         → Path (Path (coHomK (suc (suc ((suc n) + zero)))) _ _)
-- -- -- -- --                    (cong ∣_∣ₕ (cong (pre-cup (suc n) zero (merid a i)) loop))
-- -- -- -- --                    ((cong (subst coHomK (+'-comm (suc zero) (suc (suc n))))
-- -- -- -- --                      (sym (lUnit₁' (suc n) (merid a i))
-- -- -- -- --                   ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ merid a i ∣)
-- -- -- -- --                   ∙∙ lUnit₁' (suc n) (merid a i))))
-- -- -- -- --       pre-cool-merid i a =
-- -- -- -- --            (λ k j → main (suc n) zero (inl x) (inr tt) (merid a i) (loop j) k)
-- -- -- -- --         ∙∙ (λ k j → -ₖ-gen-inl-left (suc (suc n)) 1 x (inr tt)
-- -- -- -- --                     (subst coHomK (+'-comm 1 (suc (suc n)))
-- -- -- -- --                       (cup' zero (suc n) ∣ loop j ∣ ∣ merid a i ∣)) k)
-- -- -- -- --         ∙∙ cong (cong (subst coHomK (+'-comm 1 (suc (suc n))))) (rUnit λ j₁ → cup' zero (suc n) ∣ loop j₁ ∣ ∣ merid a i ∣)

-- -- -- -- --       pre-cool : (a : _) → Path (Path (coHomK (suc (suc ((suc n) + zero)))) _ _)
-- -- -- -- --                    (cong ∣_∣ₕ (cong (pre-cup (suc n) zero a) loop))
-- -- -- -- --                     (cong (subst coHomK (+'-comm (suc zero) (suc (suc n))))
-- -- -- -- --                       (sym (lUnit₁' (suc n) a)
-- -- -- -- --                    ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣)
-- -- -- -- --                    ∙∙ lUnit₁' (suc n) a))
-- -- -- -- --       pre-cool north = pre-cool-merid i0 (ptSn (suc n))
-- -- -- -- --       pre-cool south = pre-cool-merid i1 (ptSn (suc n))
-- -- -- -- --       pre-cool (merid a i) = pre-cool-merid i a

-- -- -- -- --       pre-cool2 : (cong (subst coHomK (+'-comm (suc zero) (suc (suc n))))
-- -- -- -- --                       (sym (lUnit₁' (suc n) a)
-- -- -- -- --                    ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣)
-- -- -- -- --                    ∙∙ lUnit₁' (suc n) a))
-- -- -- -- --                 ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc (suc n)) i)
-- -- -- -- --                                   ≡ 0ₖ (+'-comm (suc zero) (suc (suc n)) i))
-- -- -- -- --                             (sym (lUnit₁' (suc n) a)
-- -- -- -- --                           ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣)
-- -- -- -- --                           ∙∙ lUnit₁' (suc n) a)
-- -- -- -- --       pre-cool2 k = transp (λ i → 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ ~ k))
-- -- -- -- --                                  ≡ 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ ~ k))) (~ k)
-- -- -- -- --                            λ j → transp (λ i → coHomK (+'-comm (suc zero) (suc (suc n)) (i ∧ ~ k))) k
-- -- -- -- --                                          ((sym (lUnit₁' (suc n) a)
-- -- -- -- --                           ∙∙ (λ j → cup' zero (suc n) ∣ loop j ∣ ∣ a ∣)
-- -- -- -- --                           ∙∙ lUnit₁' (suc n) a) j)

-- -- -- -- --       lem2 : (cong ∣_∣ₕ (transport (λ i → Path (S₊ ((suc (suc (+-comm (suc n) 0 (~ i)))))) north north)
-- -- -- -- --                                                                          (merid a ∙ sym (merid (ptSn _)))))
-- -- -- -- --            ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc (suc n)) i)
-- -- -- -- --                                   ≡ 0ₖ (+'-comm (suc zero) (suc (suc n)) i))
-- -- -- -- --                        (Kn→ΩKn+1 _ ∣ a ∣)
-- -- -- -- --       lem2 = natTranspLem {A = λ n → Path (S₊ (suc (suc n))) north north} _ _
-- -- -- -- --                           (merid a ∙ sym (merid (ptSn _))) (λ n → 0ₖ (suc (suc n)) ≡ 0ₖ (suc (suc n)))
-- -- -- -- --                           (λ _ → cong ∣_∣ₕ) (sym (+-comm (suc n) 0))
-- -- -- -- --            ∙ λ k → transport (λ i → 0ₖ (isSetℕ _ _ (cong (suc ∘ suc) (sym (+-comm (suc n) zero))) (+'-comm (suc zero) (suc (suc n))) k i)
-- -- -- -- --                                     ≡ 0ₖ (isSetℕ _ _ (cong (suc ∘ suc) (sym (+-comm (suc n) zero))) (+'-comm (suc zero) (suc (suc n))) k i))
-- -- -- -- --                               (Kn→ΩKn+1 _ ∣ a ∣)

-- -- -- -- --     lem2 :  cong (λ x → cong (λ y → cup' (suc n) zero ∣ x ∣ₕ ∣ y ∣ₕ) loop) (merid a)
-- -- -- -- --           ≡ (flipSquare (cong (cong ∣_∣ₕ) (sym (rCancel (merid north)) ∙∙ cong (λ x → merid x ∙ sym (merid north))
-- -- -- -- --                      (transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- -- -- -- --                        (merid a ∙ sym (merid (ptSn _))))
-- -- -- -- --                      ∙∙ rCancel (merid north))))
-- -- -- -- --     lem2 k i j =
-- -- -- -- --       hcomp (λ r → λ { (i = i0) → ∣ north ∣ₕ
-- -- -- -- --                       ; (i = i1) → ∣ north ∣ₕ
-- -- -- -- --                       ; (j = i0) → ∣ rCancel (merid north) r i ∣ₕ
-- -- -- -- --                       ; (j = i1) → ∣ rCancel (merid north) r i ∣ₕ
-- -- -- -- --                       ; (k = i0) → ∣ doubleCompPath-filler (sym (rCancel _))
-- -- -- -- --                                                            (cong (λ x → merid x ∙ sym (merid north)) (λ i → pre-cup n zero a (loop i)))
-- -- -- -- --                                                            (rCancel _) r j i ∣ₕ
-- -- -- -- --                       ; (k = i1) → ∣ doubleCompPath-filler (sym (rCancel _))
-- -- -- -- --                                                            (cong (λ x → merid x ∙ sym (merid north))
-- -- -- -- --                                                              ((transport (λ i → Path (S₊ ((suc (suc (+-comm n 0 (~ i)))))) north north)
-- -- -- -- --                                                                          (merid a ∙ sym (merid (ptSn _))))))
-- -- -- -- --                                                            (rCancel _) r j i ∣ₕ})
-- -- -- -- --             (Kn→ΩKn+1 _ (coolLem n x a k j) i)



-- -- -- -- --     help : cong (λ x → cong (λ y → cup' (suc n) zero ∣ x ∣ₕ ∣ y ∣ₕ) loop) (merid a)
-- -- -- -- --          ≡ λ i j → -ₖ-gen (suc (suc n)) 1 (inr x) (inr tt)
-- -- -- -- --       (subst coHomK (+'-comm 1 (suc (suc n)))
-- -- -- -- --        (cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --     help = lem2
-- -- -- -- --          ∙ sym lem1
-- -- -- -- --         ∙∙ cong (transport (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)} ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) i)}))
-- -- -- -- --                 (λ _ i j → ∣ (sym (rCancel _) ∙∙ cong (λ x → merid x ∙ sym (merid north)) (merid a ∙ sym (merid (ptSn _))) ∙∙ rCancel _) j i ∣ₕ)
-- -- -- -- --         ∙∙ (λ k → transp (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc n)) (i ∨ k))} ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc n)) (i ∨ k))}) k
-- -- -- -- --                     λ i j → transp (λ i → coHomK (+'-comm 1 (suc (suc n)) (i ∧ k))) (~ k)
-- -- -- -- --                         (cup' zero (suc n) ∣ loop i ∣ₕ ∣ merid a j ∣ₕ))
-- -- -- -- --         ∙∙ sym (inst _ ((cong (cong (subst coHomK (+'-comm 1 (suc (suc n)))))
-- -- -- -- --                 (λ i j → cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ))))
-- -- -- -- --         ∙∙ sym (lem₂ (suc (suc n)) 1 x tt (cong (cong (subst coHomK (+'-comm 1 (suc (suc n)))))
-- -- -- -- --                 (λ i j → cup' zero (suc n) ∣ loop j ∣ₕ ∣ merid a i ∣ₕ)))
-- -- -- -- --   main (suc n) (suc m) (inl x) (inl y) (merid a i) (merid b j) k = {!!} -- help k i j
-- -- -- -- --     where
-- -- -- -- --     lem57 : (n m : ℕ) (p : is-even n) (q : is-even m) (a : _) (b : _) →
-- -- -- -- --         ((sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --          ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --          ∙∙ Kn→ΩKn+10ₖ _))
-- -- -- -- --       ≡ transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
-- -- -- -- --           (sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --          ∙∙ cong (Kn→ΩKn+1 _) (sym (lUnit₁ n m b) ∙∙ ((λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) ∙∙ lUnit₂ n m b)
-- -- -- -- --          ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- -- --     lem57 n m p q a b =
-- -- -- -- --          cong (λ x → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- -- --               ((rUnit (λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ)
-- -- -- -- --             ∙∙ (λ k → (λ i → main m (suc n) (inr q) (inl p) b north (k ∧ i))
-- -- -- -- --                    ∙∙ (λ i → main m (suc n) (inr q) (inl p) b (merid a i) k)
-- -- -- -- --                     ∙∙ λ i → main m (suc n) (inr q) (inl p) b south (k ∧ ~ i))
-- -- -- -- --             ∙∙ cong (main m (suc n) (inr q) (inl p) b north ∙∙_∙∙ sym (main m (suc n) (inr q) (inl p) b south))
-- -- -- -- --                        (rUnit _
-- -- -- -- --                      ∙ (λ k → (λ i → -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
-- -- -- -- --                                           ((subst coHomK (+'-comm (suc (suc n)) (suc m))
-- -- -- -- --                                              (cup' (suc n) m ∣ north ∣ ∣ b ∣))) (i ∧ k))
-- -- -- -- --                             ∙∙ ((λ i → -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
-- -- -- -- --                                           (subst coHomK (+'-comm (suc (suc n)) (suc m))
-- -- -- -- --                                              (cup' (suc n) m ∣ merid a i ∣ ∣ b ∣)) k))
-- -- -- -- --                             ∙∙ λ i → -ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
-- -- -- -- --                                           ((subst coHomK (+'-comm (suc (suc n)) (suc m))
-- -- -- -- --                                              (cup' (suc n) m ∣ south ∣ ∣ b ∣))) (~ i ∧ k))))
-- -- -- -- --               ∙ lem n m a b q p)
-- -- -- -- --        ∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n}
-- -- -- -- --           _ _ ((sym (lUnit₁ n m b) ∙∙ ((λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) ∙∙ lUnit₂ n m b)) _ (λ _ p → (sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --          ∙∙ cong (Kn→ΩKn+1 _) p
-- -- -- -- --          ∙∙ Kn→ΩKn+10ₖ _)) (+'-comm (suc (suc n)) (suc m))
-- -- -- -- --       where
-- -- -- -- --       lemType : (n m : ℕ) (a : _) (b : _) (q : _) (p : _) → Type
-- -- -- -- --       lemType n m a b q p =
-- -- -- -- --              (main m (suc n) (inr q) (inl p) b north
-- -- -- -- --           ∙∙ (-ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
-- -- -- -- --                                             ((subst coHomK (+'-comm (suc (suc n)) (suc m))
-- -- -- -- --                                                (cup' (suc n) m ∣ north ∣ ∣ b ∣))))
-- -- -- -- --           ∙∙ cong (subst coHomK (+'-comm (suc (suc n)) (suc m)))
-- -- -- -- --                   (λ i → cup' (suc n) m ∣ merid a i ∣ ∣ b ∣)
-- -- -- -- --           ∙∙ sym (-ₖ-gen-inl-right (suc m) (suc (suc n)) (inr q) p
-- -- -- -- --                                             ((subst coHomK (+'-comm (suc (suc n)) (suc m))
-- -- -- -- --                                                (cup' (suc n) m ∣ south ∣ ∣ b ∣))))
-- -- -- -- --           ∙∙ sym (main m (suc n) (inr q) (inl p) b south))
-- -- -- -- --           ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc m) i) ≡ 0ₖ ((+'-comm (suc (suc n)) (suc m) i)))
-- -- -- -- --                       (sym (lUnit₁ n m b) ∙∙ ((λ i → cup' (suc n) m ∣ merid a i ∣ₕ ∣ b ∣ₕ)) ∙∙ lUnit₂ n m b)

-- -- -- -- --       S¹-case : (i : I) → (n : ℕ) (a : _) (q : _) (p : _) → lemType n zero a (loop i) q p
-- -- -- -- --       S¹-case i n a q p =
-- -- -- -- --            sym (rUnit _)
-- -- -- -- --          ∙ λ k → transp
-- -- -- -- --                  (λ i → 0ₖ ((+'-comm (suc (suc n)) (suc zero) (i ∨ ~ k)))
-- -- -- -- --                     ≡ 0ₖ (+'-comm (suc (suc n)) (suc zero) (i ∨ ~ k)) ) (~ k)
-- -- -- -- --               (((λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc zero) (i ∧ ~ k)))
-- -- -- -- --                 k (cup' (suc n) zero ∣ merid a j ∣ ∣ loop i ∣)) ∙ refl))

-- -- -- -- --       Susp-case : (i : I) → (n m : ℕ) (a : _) (b : _) (q : _) (p : _) → lemType n (suc m) a (merid b i) q p
-- -- -- -- --       Susp-case i n m a b q p =
-- -- -- -- --           sym (rUnit _)
-- -- -- -- --         ∙ λ k → transp
-- -- -- -- --                  (λ i → 0ₖ ((+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)))
-- -- -- -- --                     ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)) ) (~ k)
-- -- -- -- --               (((λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc m)) (i ∧ ~ k)))
-- -- -- -- --                 k (cup' (suc n) (suc m) ∣ merid a j ∣ ∣ merid b i ∣)) ∙ refl))

-- -- -- -- --       lem : (n m : ℕ) (a : _) (b : _) (q : _) (p : _)
-- -- -- -- --         → lemType n m a b q p
-- -- -- -- --       lem n zero a base q p = S¹-case i0 n a q p
-- -- -- -- --       lem n zero a (loop i) q p = S¹-case i n a q p
-- -- -- -- --       lem n (suc m) a north q p = Susp-case i0 n m a (ptSn (suc m)) q p
-- -- -- -- --       lem n (suc m) a south q p = Susp-case i1 n m a (ptSn (suc m)) q p
-- -- -- -- --       lem n (suc m) a (merid b i) q p = Susp-case i n m a b q p

-- -- -- -- --     lem₄ : Kn→ΩKn+1 _ (cup' n m ∣ a ∣ₕ ∣ b ∣ₕ) ≡ sym (Kn→ΩKn+1 _ (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ ∣ a ∣)))
-- -- -- -- --     lem₄ = cong (Kn→ΩKn+1 _) (main n m (inr x) (inr y) a b)
-- -- -- -- --          ∙ -ₖ-gen-Kn→ΩKn+1 (suc n) (suc m) x y (subst coHomK (+'-comm (suc m) (suc n)) (cup' m n ∣ b ∣ ∣ a ∣))

-- -- -- -- --     lem₅ : (n m : ℕ) (a : _) (b : _)
-- -- -- -- --        → Kn→ΩKn+1 _ (cup' m n ∣ b ∣ ∣ a ∣)
-- -- -- -- --       ≡ (sym (lUnit₁ m n a) ∙∙ (λ i → cup' (suc m) n ∣ merid b i ∣ ∣ a ∣) ∙∙ lUnit₂ m n a)
-- -- -- -- --     lem₅ n m a b = sym (lem₃ m n b a)

-- -- -- -- --     lem₆ : (sym (lUnit₁ m n a) ∙∙ (λ i → cup' (suc m) n ∣ merid b i ∣ ∣ a ∣) ∙∙ lUnit₂ m n a)
-- -- -- -- --          ≡ transport (λ i → 0ₖ (+'-comm (suc n) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc n) (suc (suc m)) i))
-- -- -- -- --                      λ i → cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ
-- -- -- -- --     lem₆ = cong (sym (lUnit₁ m n a) ∙∙_∙∙ lUnit₂ m n a)
-- -- -- -- --                 (rUnit _ ∙ (λ i → (λ k → main (suc m) n (inl y) (inr x) north a (i ∧ k))
-- -- -- -- --                                ∙∙ (λ k → main (suc m) n (inl y) (inr x) (merid b k) a i)
-- -- -- -- --                                ∙∙ λ k → main (suc m) n (inl y) (inr x) south a (i ∧ ~ k))
-- -- -- -- --                           ∙ cong (main (suc m) n (inl y) (inr x) north a ∙∙_∙∙ sym (main (suc m) n (inl y) (inr x) south a))
-- -- -- -- --                                   (rUnit _
-- -- -- -- --                                     ∙ λ k → (λ i → (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
-- -- -- -- --                                               (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- -- -- --                                                (cup' n (suc m) ∣ a ∣ₕ ∣ north ∣ₕ))) (i ∧ k))
-- -- -- -- --                                          ∙∙ (λ i → (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
-- -- -- -- --                                               (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- -- -- --                                                (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ))) k)
-- -- -- -- --                                           ∙∙ λ i → (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
-- -- -- -- --                                               (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- -- -- --                                                (cup' n (suc m) ∣ a ∣ₕ ∣ south ∣ₕ))) (~ i ∧ k)))
-- -- -- -- --         ∙∙ lem n m a b x y
-- -- -- -- --         ∙∙ refl
-- -- -- -- --       where
-- -- -- -- --       lemType : (n m : ℕ) (a : _) (b : _) (x : _) (y : _) → Type
-- -- -- -- --       lemType n m a b x y =
-- -- -- -- --         ((sym (lUnit₁ m n a)) ∙∙
-- -- -- -- --        main (suc m) n (inl y) (inr x) north a ∙∙
-- -- -- -- --        (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
-- -- -- -- --           (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- -- -- --            (cup' n (suc m) ∣ a ∣ₕ ∣ north ∣ₕ)))
-- -- -- -- --        ∙∙
-- -- -- -- --        (λ i₁ →
-- -- -- -- --           (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- -- -- --            (cup' n (suc m) ∣ a ∣ₕ ∣ merid b i₁ ∣ₕ)))
-- -- -- -- --        ∙∙
-- -- -- -- --        (sym (-ₖ-gen-inl-left (suc (suc m)) (suc n) y (inr x)
-- -- -- -- --           (subst coHomK (+'-comm (suc n) (suc (suc m)))
-- -- -- -- --            (cup' n (suc m) ∣ a ∣ₕ ∣ south ∣ₕ))))
-- -- -- -- --        ∙∙ (sym (main (suc m) n (inl y) (inr x) south a))
-- -- -- -- --        ∙∙ lUnit₂ m n a)
-- -- -- -- --        ≡ transport (λ i → 0ₖ (+'-comm (suc n) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc n) (suc (suc m)) i))
-- -- -- -- --                      λ i → cup' n (suc m) ∣ a ∣ₕ ∣ merid b i ∣ₕ

-- -- -- -- --       S¹-case : (i : I) → (m : ℕ) (b : _) (x : _) (y : _) → lemType zero m (loop i) b x y
-- -- -- -- --       S¹-case i m b x y =
-- -- -- -- --            sym (rUnit _)
-- -- -- -- --         ∙∙ sym (rUnit _)
-- -- -- -- --         ∙∙ sym (rUnit _)
-- -- -- -- --          ∙ λ k → transp (λ i → 0ₖ (+'-comm 1 (suc (suc m)) (i ∨ ~ k)) ≡ 0ₖ (+'-comm 1 (suc (suc m)) (i ∨ ~ k)))
-- -- -- -- --                          (~ k)
-- -- -- -- --                          λ j → transp (λ i → coHomK (+'-comm 1 (suc (suc m)) (i ∧ ~ k))) k
-- -- -- -- --                                (cup' zero (suc m) ∣ loop i ∣ₕ ∣ merid b j ∣ₕ)

-- -- -- -- --       Susp-case : (i : I) (n m : ℕ) (a : _) (b : _) (x : _) (y : _) → lemType (suc n) m (merid a i) b x y
-- -- -- -- --       Susp-case i n m a b x y =
-- -- -- -- --            sym (rUnit _)
-- -- -- -- --         ∙∙ sym (rUnit _)
-- -- -- -- --         ∙∙ sym (rUnit _)
-- -- -- -- --          ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)) ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)))
-- -- -- -- --                          (~ k)
-- -- -- -- --                          λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc m)) (i ∧ ~ k))) k
-- -- -- -- --                                (cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)

-- -- -- -- --       lem : (n m : ℕ) (a : _) (b : _) (x : _) (y : _) → lemType n m a b x y
-- -- -- -- --       lem zero m base b x y = S¹-case i0 m b x y
-- -- -- -- --       lem zero m (loop i) b x y = S¹-case i m b x y
-- -- -- -- --       lem (suc n) m north b x y = Susp-case i0 n m (ptSn (suc n)) b x y
-- -- -- -- --       lem (suc n) m south b x y = Susp-case i1 n m (ptSn (suc n)) b x y
-- -- -- -- --       lem (suc n) m (merid a i) b x y = Susp-case i n m a b x y

-- -- -- -- --     MAIN₂ : (sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --          ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --          ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- -- --          ≡ transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
-- -- -- -- --            (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})
-- -- -- -- --             (sym ((sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --          ∙∙ cong (Kn→ΩKn+1 _) ((Kn→ΩKn+1 _ (cup' m n ∣ b ∣ ∣ a ∣)))
-- -- -- -- --          ∙∙ Kn→ΩKn+10ₖ _))))
-- -- -- -- --     MAIN₂ = lem57 n m x y a b
-- -- -- -- --           ∙ cong (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}
-- -- -- -- --                                    ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}))
-- -- -- -- --                  (cong ((λ x → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x ∙∙ (Kn→ΩKn+10ₖ _)))
-- -- -- -- --                         (lem₃ n m a b ∙ lem₄)
-- -- -- -- --                  ∙∙ natTranspLem {A = coHomK} _ _ (cup' m n ∣ b ∣ ∣ a ∣) _
-- -- -- -- --                  (λ _ p → 
-- -- -- -- --                  (sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --               ∙∙ cong (Kn→ΩKn+1 _) (sym (Kn→ΩKn+1 _ p))
-- -- -- -- --               ∙∙ Kn→ΩKn+10ₖ _)) (+'-comm (suc m) (suc n))
-- -- -- -- --                  ∙∙ refl)

-- -- -- -- --     MAIN₃ : (sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --          ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' m (suc n) ∣ b ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --          ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- -- --          ≡ transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
-- -- -- -- --            (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})
-- -- -- -- --              (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) })
-- -- -- -- --                         (sym ((sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --                        ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' n (suc m) ∣ a ∣ ∣ merid b i ∣))
-- -- -- -- --                        ∙∙ Kn→ΩKn+10ₖ _)))))
-- -- -- -- --     MAIN₃ = MAIN₂
-- -- -- -- --           ∙ cong (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}
-- -- -- -- --                                   ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))}) ∘
-- -- -- -- --                  (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))}
-- -- -- -- --                                   ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})))
-- -- -- -- --              (cong (λ x → (sym (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣) ∙∙
-- -- -- -- --                cong (Kn→ΩKn+1 (suc (suc (suc (m + n))))) (sym x)
-- -- -- -- --                ∙∙ (λ i₁ j₁ → ∣ rCancel (merid north) i₁ j₁ ∣))) (lem₅ n m a b ∙ lem₆)
-- -- -- -- --                ∙ natTranspLem {λ n → 0ₖ n ≡ 0ₖ n} _ _ ((λ i₂ → cup' n (suc m) ∣ a ∣ ∣ merid b i₂ ∣)) _
-- -- -- -- --                     (λ _ p → sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --                            ∙∙ cong (Kn→ΩKn+1 _) (sym p)
-- -- -- -- --                            ∙∙ Kn→ΩKn+10ₖ _) (+'-comm (suc n) (suc (suc m))))
-- -- -- -- --     lem₇ : (sym ((sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --                        ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' n (suc m) ∣ a ∣ ∣ merid b i ∣))
-- -- -- -- --                        ∙∙ Kn→ΩKn+10ₖ _)))
-- -- -- -- --            ≡ (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)
-- -- -- -- --     lem₇ = cong sym (sym (lem₁ _ _ b a))
-- -- -- -- --         ∙∙ sym (inst _ (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b (~ j) ∣ₕ))
-- -- -- -- --         ∙∙ sym (inst2 _ _)

-- -- -- -- --     MAIN₄ : transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
-- -- -- -- --            (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})
-- -- -- -- --              (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) })
-- -- -- -- --                         (sym ((sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --                        ∙∙ cong (Kn→ΩKn+1 _) ((λ i → cup' n (suc m) ∣ a ∣ ∣ merid b i ∣))
-- -- -- -- --                        ∙∙ Kn→ΩKn+10ₖ _)))))
-- -- -- -- --          ≡ t n m (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ merid b j ∣ₕ)
-- -- -- -- --     MAIN₄ =
-- -- -- -- --          cong (λ x → transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc m) i))})
-- -- -- -- --            (transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))} ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc m) (suc n) i)))})
-- -- -- -- --              (transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i))} ≡ refl {x = 0ₖ (suc (+'-comm (suc n) (suc (suc m)) i)) }) x)))
-- -- -- -- --                lem₇

-- -- -- -- --     help : (cong (λ x → (cong (λ y → cup' (suc n) (suc m) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
-- -- -- -- --          ≡ λ i j → -ₖ-gen (suc (suc n)) (suc (suc m)) (inl x) (inl y)
-- -- -- -- --       (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- -- --        (cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --     help =
-- -- -- -- --          ((sym (final n m ((cong (λ x → (cong (λ y → cup' (suc n) (suc m) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))))
-- -- -- -- --          ∙ cong (transport (λ i → refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}
-- -- -- -- --                                  ≡ refl {x = 0ₖ (+'-comm (suc (suc m)) (suc (suc n)) i)}))
-- -- -- -- --                  (sym (MAIN₃ ∙ MAIN₄))
-- -- -- -- --          ∙ sym (lem₈ n m (lem₁ n m a b i1)))
-- -- -- -- --          ∙ cong (cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))))
-- -- -- -- --            (sym (lem₁ n m a b)))
-- -- -- -- --        ∙ (λ k → cong (cong (λ z → -ₖ-gen-inl-left (suc (suc n)) (suc (suc m)) x (inl y) z (~ k)) ∘ cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))
-- -- -- -- --                          (λ i j → cup' (suc m) (suc n) ∣ merid b j ∣ ∣ merid a i ∣))
-- -- -- -- --   main (suc n) (suc (suc m)) (inl x) (inr y) (merid a i) (merid b j) = {!y!}
-- -- -- -- --     where
-- -- -- -- --     lem1 : (n m : ℕ)  (x : is-even n) (y : is-odd (suc (suc (suc m)))) (a : _) (b : _)
-- -- -- -- --          → cong (cup' (suc m) (suc n) ∣ b ∣ₕ ∘ ∣_∣ₕ) (merid a)
-- -- -- -- --          ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i))
-- -- -- -- --                      ((sym (lUnit₁ n _ b) ∙∙ (λ i → cup' (suc n) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ n _ b))
-- -- -- -- --     lem1 n m x y a = λ { north → m-case i0 a (ptSn (suc m))
-- -- -- -- --                        ; south → m-case i1 a (ptSn (suc m))
-- -- -- -- --                        ; (merid b i) → m-case i a b }
-- -- -- -- --       where
-- -- -- -- --       m-case : (i : I) → (a : _) (b : _)
-- -- -- -- --              → cong (cup' (suc m) (suc n) ∣ merid b i ∣ₕ ∘ ∣_∣ₕ) (merid a)
-- -- -- -- --          ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i))
-- -- -- -- --                      ((sym (lUnit₁ n _ (merid b i)) ∙∙ (λ j → cup' (suc n) (suc m) ∣ merid a j ∣ₕ ∣ merid b i ∣ₕ) ∙∙ lUnit₂ n _ (merid b i))) 
-- -- -- -- --       m-case i a b =
-- -- -- -- --            (λ k j →  main (suc m) (suc n) (inl y) (inl x) (merid b i) (merid a j) k)
-- -- -- -- --         ∙∙ (λ k j → -ₖ-gen-inl-left (suc (suc m)) (suc (suc n)) y (inl x) (subst coHomK (+'-comm (suc (suc n)) (suc (suc m)))
-- -- -- -- --                        (cup' (suc n) (suc m) ∣ merid a j ∣ ∣ merid b i ∣)) k)
-- -- -- -- --         ∙∙ (rUnit _
-- -- -- -- --           ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k)) ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc m)) (i ∨ ~ k))) (~ k)
-- -- -- -- --                           ((λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc m)) (i ∧ ~ k))) k
-- -- -- -- --                                           (cup' (suc n) (suc m) ∣ merid a j ∣ ∣ merid b i ∣)) ∙ refl))

-- -- -- -- --     lem2 : (sym (Kn→ΩKn+10ₖ (suc (suc (suc m + suc n)))) ∙∙
-- -- -- -- --                 cong (Kn→ΩKn+1 (suc (suc (suc m + suc n))))
-- -- -- -- --                 (λ i₁ → cup' (suc m) (suc n) ∣ b ∣ₕ ∣ merid a i₁ ∣ₕ)
-- -- -- -- --                 ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc m + suc n))))
-- -- -- -- --         ≡ t₂ n (suc m)
-- -- -- -- --             (t₃ n (suc m)
-- -- -- -- --               ((sym (Kn→ΩKn+10ₖ _) ∙∙
-- -- -- -- --                 cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (cup' (suc m) n ∣ b ∣ ∣ a ∣))
-- -- -- -- --                 ∙∙ Kn→ΩKn+10ₖ _)))
-- -- -- -- --     lem2 =
-- -- -- -- --          cong (λ x → sym (Kn→ΩKn+10ₖ (suc (suc (suc m + suc n)))) ∙∙
-- -- -- -- --                 cong (Kn→ΩKn+1 (suc (suc (suc m + suc n)))) x
-- -- -- -- --                 ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc m + suc n))))
-- -- -- -- --               (lem1 n m x y a b
-- -- -- -- --               ∙ cong (transport (λ i₁ →
-- -- -- -- --                       0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i₁) ≡
-- -- -- -- --                       0ₖ (+'-comm (suc (suc n)) (suc (suc m)) i₁)))
-- -- -- -- --                      (lem₃ n (suc m) a b
-- -- -- -- --                       ∙ cong (Kn→ΩKn+1 (suc (suc (n + suc m))))
-- -- -- -- --                              (main n (suc m) (inr x) (inl y) a b
-- -- -- -- --                              ∙ -ₖ-gen-inl-right (suc n) (suc (suc m)) (inr x) y
-- -- -- -- --                                        (subst coHomK (+'-comm (suc (suc m)) (suc n))
-- -- -- -- --                                         (cup' (suc m) n ∣ b ∣ₕ ∣ a ∣ₕ)))))
-- -- -- -- --       ∙∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n} _ _ ((Kn→ΩKn+1 _) (subst coHomK (+'-comm (suc (suc m)) (suc n)) (cup' (suc m) n ∣ b ∣ₕ ∣ a ∣ₕ))) _
-- -- -- -- --            (λ _ x → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x ∙∙ Kn→ΩKn+10ₖ _) (+'-comm (suc (suc n)) (suc (suc m)))
-- -- -- -- --       ∙∙ cong (subst (λ n₁ → refl ≡ refl) (+'-comm (suc (suc n)) (suc (suc m))))
-- -- -- -- --               (natTranspLem {A = coHomK} _ _ (cup' (suc m) n ∣ b ∣ ∣ a ∣) _
-- -- -- -- --                 (λ _ x → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ x) ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- -- --                 (+'-comm (suc (suc m)) (suc n)))

-- -- -- -- --     lem3 : (n m : ℕ) (x : is-even n) (y : is-odd (suc (suc (suc m)))) (b : _) (a : _) → (sym (lUnit₁ (suc m) n a) ∙∙
-- -- -- -- --                                         (λ i₁ → cup' (suc (suc m)) n ∣ merid b i₁ ∣ₕ ∣ a ∣ₕ) ∙∙
-- -- -- -- --                                         lUnit₂ (suc m) n a)
-- -- -- -- --                                      ≡ transport (λ i → 0ₖ (+'-comm (suc n) (suc (suc (suc m))) i)
-- -- -- -- --                                                        ≡ 0ₖ (+'-comm (suc n) (suc (suc (suc m))) i))
-- -- -- -- --                                          λ i₁ → cup' n (suc (suc m)) ∣ a ∣ₕ ∣ merid b (~ i₁) ∣ₕ
-- -- -- -- --     lem3 = λ { zero m x y b base → S¹-case i0 m x y b
-- -- -- -- --              ; zero m x y b (loop i) → S¹-case i m x y b
-- -- -- -- --              ; (suc n) m x y b north → merid-case i0 n m x y (ptSn (suc n)) b
-- -- -- -- --              ; (suc n) m x y b south → merid-case i1 n m x y (ptSn (suc n)) b
-- -- -- -- --              ; (suc n) m x y b (merid a i) → merid-case i n m x y a b}
-- -- -- -- --       where
-- -- -- -- --       S¹-case : (i : I) → (m : ℕ) (x : is-even zero) (y : is-odd (suc (suc (suc m)))) (b : _) → (sym (lUnit₁ (suc m) zero (loop i)) ∙∙
-- -- -- -- --                                         (λ i₁ → cup' (suc (suc m)) zero ∣ merid b i₁ ∣ₕ ∣ (loop i) ∣ₕ) ∙∙
-- -- -- -- --                                         lUnit₂ (suc m) zero (loop i))
-- -- -- -- --                                      ≡ transport (λ i → 0ₖ (+'-comm (suc zero) (suc (suc (suc m))) i)
-- -- -- -- --                                                        ≡ 0ₖ (+'-comm (suc zero) (suc (suc (suc m))) i))
-- -- -- -- --                                          λ i₁ → cup' zero (suc (suc m)) ∣ loop i ∣ₕ ∣ merid b (~ i₁) ∣ₕ
-- -- -- -- --       S¹-case i m x y b =
-- -- -- -- --            sym (rUnit _)
-- -- -- -- --         ∙∙ (λ k j → main (suc (suc m)) zero (inr y) (inr x) (merid b j) (loop i) k)
-- -- -- -- --         ∙∙ cong-₂ (suc (suc (suc m))) 1 y x ((λ j₁ → (subst coHomK (+'-comm 1 (suc (suc (suc m))))
-- -- -- -- --                                                        (cup' zero (suc (suc m)) ∣ loop i ∣ ∣ merid b j₁ ∣))))
-- -- -- -- --          ∙ λ k → transp (λ i → 0ₖ (+'-comm 1 (suc (suc (suc m))) (i ∨ ~ k))
-- -- -- -- --                                    ≡ 0ₖ (+'-comm 1 (suc (suc (suc m))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                    (λ j → transp (λ i → coHomK (+'-comm (suc zero) (suc (suc (suc m))) (i ∧ ~ k))) k
-- -- -- -- --                                   (cup' zero (suc (suc m)) ∣ loop i ∣ₕ ∣ merid b (~ j) ∣ₕ))


-- -- -- -- --       merid-case : (i : I) (n m : ℕ) (x : is-even (suc n)) (y : is-odd (suc (suc (suc m)))) (a : _) (b : _)
-- -- -- -- --                  → (sym (lUnit₁ (suc m) (suc n) (merid a i)) ∙∙
-- -- -- -- --                     (λ i₁ → cup' (suc (suc m)) (suc n) ∣ merid b i₁ ∣ₕ ∣ (merid a i) ∣ₕ) ∙∙
-- -- -- -- --                     lUnit₂ (suc m) (suc n) (merid a i))
-- -- -- -- --                  ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i)
-- -- -- -- --                                    ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i))
-- -- -- -- --                      λ i₁ → cup' (suc n) (suc (suc m)) ∣ merid a i ∣ₕ ∣ merid b (~ i₁) ∣ₕ
-- -- -- -- --       merid-case i n m x y a b =
-- -- -- -- --         sym (rUnit _)
-- -- -- -- --         ∙∙ (λ k j → main (suc (suc m)) (suc n) (inr y) (inr x) (merid b j) (merid a i) k)
-- -- -- -- --         ∙∙ cong-₂ (suc (suc (suc m))) (suc (suc n)) y x ((λ j₁ → (subst coHomK (+'-comm (suc (suc n)) (suc (suc (suc m))))
-- -- -- -- --                                                        (cup' (suc n) (suc (suc m)) ∣ merid a i ∣ ∣ merid b j₁ ∣))))
-- -- -- -- --          ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∨ ~ k))
-- -- -- -- --                                    ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                    (λ j → transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∧ ~ k))) k
-- -- -- -- --                                   (cup' (suc n) (suc (suc m)) ∣ merid a i ∣ₕ ∣ merid b (~ j) ∣ₕ))

-- -- -- -- --     help : (cong (λ x → (cong (λ y → cup' (suc n) (suc (suc m)) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
-- -- -- -- --          ≡ λ i j → -ₖ-gen (suc (suc n)) (suc (suc (suc m))) (inl x) (inr y)
-- -- -- -- --               (subst coHomK (+'-comm (suc (suc (suc m))) (suc (suc n)))
-- -- -- -- --                (cup' (suc (suc m)) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --     help =
-- -- -- -- --       sym ((λ k i j → -ₖ-gen-inl-left (suc (suc n)) (suc (suc (suc m))) x (inr y)
-- -- -- -- --               (subst coHomK (+'-comm (suc (suc (suc m))) (suc (suc n)))
-- -- -- -- --                (cup' (suc (suc m)) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)) k)
-- -- -- -- --         ∙∙ lem₈ n (suc m) (λ i j → (cup' (suc (suc m)) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --         ∙∙ cong (transport (λ i₁ → refl ≡ refl))
-- -- -- -- --                 (lem₁ n (suc m) a b
-- -- -- -- --               ∙∙ lem2
-- -- -- -- --               ∙∙ cong (t₂ n (suc m) ∘ t₃ n (suc m))
-- -- -- -- --                    (cong (λ x → (sym (Kn→ΩKn+10ₖ _) ∙∙
-- -- -- -- --                                  cong (Kn→ΩKn+1 _) x
-- -- -- -- --                                  ∙∙ Kn→ΩKn+10ₖ _))
-- -- -- -- --                          (sym (lem₃ (suc m) n b a)
-- -- -- -- --                        ∙ lem3 n m x y b a
-- -- -- -- --                       )
-- -- -- -- --                   ∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n} _ _ (λ i₂ → cup' n (suc (suc m)) ∣ a ∣ ∣ merid b (~ i₂) ∣) _
-- -- -- -- --                                   (λ _ x → (sym (Kn→ΩKn+10ₖ _) ∙∙
-- -- -- -- --                                  cong (Kn→ΩKn+1 _) x
-- -- -- -- --                                  ∙∙ Kn→ΩKn+10ₖ _))
-- -- -- -- --                                   (+'-comm (suc n) (suc (suc (suc m))))
-- -- -- -- --                   ∙ cong (t₄ n (suc m)) ( sym (cong sym (lem₁ (suc m) n b a)))))
-- -- -- -- --         ∙∙ final n (suc m)
-- -- -- -- --              (λ i₁ j₁ →
-- -- -- -- --             cup' (suc n) (suc (suc m)) ∣ merid a j₁ ∣ ∣ merid b (~ i₁) ∣)
-- -- -- -- --         ∙∙ inst _ (λ i₁ j₁ →
-- -- -- -- --          cup' (suc n) (suc (suc m)) ∣ merid a j₁ ∣ ∣ merid b i₁ ∣))
-- -- -- -- --   main (suc n) (suc m) (inr x) (inl y) (merid a i) (merid b j) = {!!}
-- -- -- -- --     where
-- -- -- -- --     help : (cong (λ x → (cong (λ y → cup' (suc n) (suc m) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
-- -- -- -- --          ≡ λ i j → -ₖ-gen (suc (suc n)) (suc (suc m)) (inr x) (inl y)
-- -- -- -- --               (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- -- --                (cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --     help = ((sym (transportRefl _)
-- -- -- -- --           ∙ cong (λ x → subst (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) x (λ i₁ j₁ → cup' (suc n) (suc m) ∣ merid a i₁ ∣ ∣ merid b j₁ ∣)) (isSetℕ _ _ refl _))
-- -- -- -- --           ∙ substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n})
-- -- -- -- --                             (+'-comm (suc (suc n)) (suc (suc m)))
-- -- -- -- --                             (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- -- --                             (λ i₁ j₁ → cup' (suc n) (suc m) ∣ merid a i₁ ∣ ∣ merid b j₁ ∣))
-- -- -- -- --         ∙∙ (λ k → lem₈ n m (lem₈ m n (λ i j → cup' (suc n) (suc m) ∣ merid a i ∣ ∣ merid b j ∣) (~ k)) (~ k))
-- -- -- -- --         ∙∙ (cong (cong (cong ((subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))))
-- -- -- -- --                   λ k i j → -ₖ-gen-inl-left (suc (suc m)) (suc (suc n)) y (inr x)
-- -- -- -- --                               (subst coHomK (+'-comm (suc (suc n)) (suc (suc m)))
-- -- -- -- --                               (cup' (suc n) (suc m) ∣ merid a i ∣ ∣ merid b j ∣)) (~ k))
-- -- -- -- --         ∙∙ sym (cong (cong (cong ((subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))))
-- -- -- -- --                 (λ k i j → main (suc m) (suc n) (inl y) (inr x) (merid b j) (merid a i) k))
-- -- -- -- --         ∙∙ λ k i j → -ₖ-gen-inl-right (suc (suc n)) (suc (suc m)) (inr x) y
-- -- -- -- --          (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- -- --           (cup' (suc m) (suc n) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ)) (~ k)
-- -- -- -- --   main (suc (suc n)) (suc (suc m)) (inr x) (inr y) (merid a i) (merid b j) =
-- -- -- -- --     {!!}
-- -- -- -- --     where
-- -- -- -- --     lem57 : {k : ℕ} (p : refl {x = 0ₖ (suc (suc k))} ≡ refl {x = 0ₖ (suc (suc k))})
-- -- -- -- --                   → cong (cong (-ₖ-gen (suc (suc (suc n))) (suc (suc (suc m))) (inr x) (inr y))) p
-- -- -- -- --                   ≡ sym p
-- -- -- -- --     lem57 p =
-- -- -- -- --          rUnit _
-- -- -- -- --       ∙∙ (λ k → (λ i → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y refl (i ∧ k))
-- -- -- -- --               ∙∙ cong (λ z → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y z k) p
-- -- -- -- --               ∙∙ λ i → cong-₂ (suc (suc (suc n))) (suc (suc (suc m))) x y refl (~ i ∧ k))
-- -- -- -- --       ∙∙ (λ k → transportRefl (λ _ _ → ∣ north ∣) k
-- -- -- -- --               ∙∙ cong sym p
-- -- -- -- --               ∙∙ sym (transportRefl (λ _ _ → ∣ north ∣) k))
-- -- -- -- --       ∙∙ sym (rUnit _)
-- -- -- -- --       ∙∙ sym (inst4 p)

-- -- -- -- --     lem2 : cong (cup' (suc m) (suc (suc n)) ∣ b ∣ₕ ∘ ∣_∣ₕ) (merid a)
-- -- -- -- --       ≡ transport (λ i → 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i) ≡ 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i))
-- -- -- -- --                   (sym (lUnit₁ (suc n) _ b) ∙∙ (λ i → cup' (suc (suc n)) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ _ _ b)
-- -- -- -- --     lem2 = fin b
-- -- -- -- --       where
-- -- -- -- --       help : (i : I) (b : _) →
-- -- -- -- --                  cong (cup' (suc m) (suc (suc n)) ∣ merid b i ∣ₕ ∘ ∣_∣ₕ) (merid a)
-- -- -- -- --                ≡ transport (λ i → 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i)
-- -- -- -- --                                  ≡ 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i))
-- -- -- -- --                  (sym (lUnit₁ (suc n) _ (merid b i)) ∙∙ (λ j → cup' (suc (suc n)) (suc m) ∣ merid a j ∣ₕ ∣ merid b i ∣ₕ) ∙∙ lUnit₂ (suc n) _ (merid b i))
-- -- -- -- --       help i b =
-- -- -- -- --            (λ k j → main (suc m) (suc (suc n)) (inl y) (inr x) (merid b i) (merid a j) k)
-- -- -- -- --          ∙ (λ k j → -ₖ-gen-inl-left (suc (suc m)) (suc (suc (suc n))) y (inr x)
-- -- -- -- --                  (subst coHomK (+'-comm (suc (suc (suc n))) (suc (suc m)))
-- -- -- -- --                    (cup' (suc (suc n)) (suc m) ∣ merid a j ∣ ∣ merid b i ∣)) k)
-- -- -- -- --          ∙ (λ k → transp (λ i → 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) (i ∨ ~ k))
-- -- -- -- --                                 ≡ 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) (i ∨ ~ k))) (~ k)
-- -- -- -- --                           λ j → transp (λ i → coHomK (+'-comm (suc (suc (suc n))) (suc (suc m)) (i ∧ ~ k))) k
-- -- -- -- --                                         (cup' (suc (suc n)) (suc m) ∣ merid a j ∣ ∣ merid b i ∣))
-- -- -- -- --          ∙ cong (transport (λ i → 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i)
-- -- -- -- --                                  ≡ 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i)))
-- -- -- -- --                  (rUnit λ j → cup' (suc (suc n)) (suc m) ∣ merid a j ∣ₕ ∣ merid b i ∣ₕ)

-- -- -- -- --       fin : (b : _) → cong (cup' (suc m) (suc (suc n)) ∣ b ∣ₕ ∘ ∣_∣ₕ) (merid a)
-- -- -- -- --              ≡ transport (λ i → 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i)
-- -- -- -- --                                  ≡ 0ₖ (+'-comm (suc (suc (suc n))) (suc (suc m)) i))
-- -- -- -- --               (sym (lUnit₁ (suc n) _ b) ∙∙ (λ i → cup' (suc (suc n)) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ _ _ b)
-- -- -- -- --       fin north = help i0 (ptSn (suc m))
-- -- -- -- --       fin south = help i1 (ptSn (suc m))
-- -- -- -- --       fin (merid a i) = help i a

-- -- -- -- --     lem3 : (sym (Kn→ΩKn+10ₖ (suc (suc (suc m + suc (suc n))))) ∙∙
-- -- -- -- --        cong (Kn→ΩKn+1 (suc (suc (suc m + suc (suc n)))))
-- -- -- -- --        (λ i₁ → cup' (suc m) (suc (suc n)) ∣ b ∣ₕ ∣ merid a i₁ ∣ₕ)
-- -- -- -- --        ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc m + suc (suc n)))))
-- -- -- -- --         ≡ transport (λ i → refl {x = 0ₖ (suc (+'-comm (suc (suc (suc n))) (suc (suc m)) i))}
-- -- -- -- --                           ≡ refl {x = 0ₖ ((suc (+'-comm (suc (suc (suc n))) (suc (suc m)) i)))})
-- -- -- -- --                     (sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --                   ∙∙ cong (Kn→ΩKn+1 _) (sym (lUnit₁ (suc n) _ b) ∙∙ (λ i → cup' (suc (suc n)) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ _ _ b)
-- -- -- -- --                   ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- -- --     lem3 =
-- -- -- -- --         cong (λ x → (sym (Kn→ΩKn+10ₖ (suc (suc (suc m + suc (suc n))))) ∙∙
-- -- -- -- --        cong (Kn→ΩKn+1 (suc (suc (suc m + suc (suc n))))) x
-- -- -- -- --        ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc m + suc (suc n)))))) lem2
-- -- -- -- --       ∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n}
-- -- -- -- --           _ _ ((sym (lUnit₁ (suc n) _ b) ∙∙ (λ i → cup' (suc (suc n)) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ _ _ b)) _
-- -- -- -- --               (λ _ x → (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) x ∙∙ Kn→ΩKn+10ₖ _))
-- -- -- -- --          ((+'-comm (suc (suc (suc n))) (suc (suc m))))

-- -- -- -- --     lem4 : (sym (lUnit₁ (suc n) _ b) ∙∙ (λ i → cup' (suc (suc n)) (suc m) ∣ merid a i ∣ₕ ∣ b ∣ₕ) ∙∙ lUnit₂ _ _ b)
-- -- -- -- --                      ≡ Kn→ΩKn+1 _ ((subst coHomK (+'-comm (suc (suc m)) (suc (suc n))) (cup' (suc m) (suc n) ∣ b ∣ₕ ∣ a ∣ₕ)))
-- -- -- -- --     lem4 = lem₃ (suc n) (suc m) a b
-- -- -- -- --         ∙∙ cong (Kn→ΩKn+1 _) (main (suc n) (suc m) (inl x) (inl y) a b)
-- -- -- -- --         ∙∙ cong (Kn→ΩKn+1 _) (-ₖ-gen-inl-left (suc (suc n)) (suc (suc m)) x (inl y) _)

-- -- -- -- --     lem₅ : ((λ i₁ → Kn→ΩKn+10ₖ _ (~ i₁)) ∙∙
-- -- -- -- --        (λ i₁ →
-- -- -- -- --           Kn→ΩKn+1 _
-- -- -- -- --           (Kn→ΩKn+1 _
-- -- -- -- --            (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- -- -- --             (cup' (suc m) (suc n) ∣ b ∣ₕ ∣ a ∣ₕ))
-- -- -- -- --            i₁))
-- -- -- -- --        ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- -- --        ≡ transport (λ i → refl {x = 0ₖ (suc (suc (+'-comm (suc (suc m)) (suc (suc n)) i)))}
-- -- -- -- --                          ≡ refl {x = 0ₖ (suc (suc (+'-comm (suc (suc m)) (suc (suc n)) i)))})
-- -- -- -- --                    ((λ i₁ → Kn→ΩKn+10ₖ _ (~ i₁)) ∙∙
-- -- -- -- --        (λ i₁ →
-- -- -- -- --           Kn→ΩKn+1 _
-- -- -- -- --           (Kn→ΩKn+1 _
-- -- -- -- --             (cup' (suc m) (suc n) ∣ b ∣ₕ ∣ a ∣ₕ)
-- -- -- -- --            i₁))
-- -- -- -- --        ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- -- --     lem₅ =
-- -- -- -- --       natTranspLem {A = coHomK} _ _ (cup' (suc m) (suc n) ∣ b ∣ₕ ∣ a ∣ₕ) _
-- -- -- -- --         (λ _ x → sym (Kn→ΩKn+10ₖ _) ∙∙ (cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ x)) ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- -- --         (+'-comm (suc (suc m)) (suc (suc n)))

-- -- -- -- --     lem6 : (Kn→ΩKn+1 (suc (suc (suc (m + suc n))))
-- -- -- -- --              (cup' (suc m) (suc n) ∣ b ∣ ∣ a ∣))
-- -- -- -- --           ≡ (sym (lUnit₁ (suc m) _ a) ∙∙ (λ i → cup' (suc (suc m)) (suc n) ∣ merid b i ∣ ∣ a ∣) ∙∙ lUnit₂ (suc m) _ a)
-- -- -- -- --     lem6 = sym (lem₃ (suc m) (suc n) b a)

-- -- -- -- --     lem7 : (sym (lUnit₁ (suc m) _ a) ∙∙ (λ i → cup' (suc (suc m)) (suc n) ∣ merid b i ∣ ∣ a ∣) ∙∙ lUnit₂ (suc m) _ a)
-- -- -- -- --          ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i) ≡  0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i))
-- -- -- -- --              (λ i → cup' (suc n) (suc (suc m)) ∣ a ∣ ∣ merid b i ∣)
-- -- -- -- --     lem7 = mainLem n m a b x y
-- -- -- -- --       where
-- -- -- -- --       meridCase : (i : I) (n m : ℕ) (a : _) (b : _ ) (x : _) (y : _)
-- -- -- -- --         → (sym (lUnit₁ (suc m) _ (merid a i)) ∙∙ (λ j → cup' (suc (suc m)) (suc n) ∣ merid b j ∣ ∣ merid a i ∣) ∙∙ lUnit₂ (suc m) _ (merid a i))
-- -- -- -- --          ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i) ≡  0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i))
-- -- -- -- --                      λ j → cup' (suc n) (suc (suc m)) ∣ merid a i ∣ ∣ merid b j ∣
-- -- -- -- --       meridCase i n m a b x y =
-- -- -- -- --            sym (rUnit _)
-- -- -- -- --         ∙∙ (λ k j → main (suc (suc m)) (suc n) (inr y) (inl x) (merid b j) (merid a i) k)
-- -- -- -- --         ∙∙ (λ k j → -ₖ-gen-inl-right ((suc (suc (suc m)))) (suc (suc n)) (inr y) x
-- -- -- -- --                        (subst coHomK (+'-comm (suc (suc n)) (suc (suc (suc m))))
-- -- -- -- --                         (cup' (suc n) (suc (suc m)) ∣ merid a i ∣ ∣ merid b j ∣)) k)
-- -- -- -- --          ∙ λ k → transp (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∨ ~ k))
-- -- -- -- --                                ≡ 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                         λ j → (transp (λ i → coHomK (+'-comm (suc (suc n)) (suc (suc (suc m))) (i ∧ ~ k))) k)
-- -- -- -- --                                (cup' (suc n) (suc (suc m)) ∣ merid a i ∣ ∣ merid b j ∣)

-- -- -- -- --       mainLem : (n m : ℕ) (a : _) (b : _ ) (x : is-even (suc (suc n))) (y : is-odd (suc (suc (suc m))))
-- -- -- -- --           → (sym (lUnit₁ (suc m) _ a) ∙∙ (λ j → cup' (suc (suc m)) (suc n) ∣ merid b j ∣ ∣ a ∣) ∙∙ lUnit₂ (suc m) _ a)
-- -- -- -- --            ≡ transport (λ i → 0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i) ≡  0ₖ (+'-comm (suc (suc n)) (suc (suc (suc m))) i))
-- -- -- -- --                        λ j → cup' (suc n) (suc (suc m)) ∣ a ∣ ∣ merid b j ∣
-- -- -- -- --       mainLem n m north b x y = meridCase i0 n m (ptSn (suc n)) b x y
-- -- -- -- --       mainLem n m south b x y = meridCase i1 n m (ptSn (suc n)) b x y
-- -- -- -- --       mainLem n m (merid a i) b x y = meridCase i n m a b x y

-- -- -- -- --     lem8 : (sym (Kn→ΩKn+10ₖ _) ∙∙
-- -- -- -- --        (cong (Kn→ΩKn+1 _)
-- -- -- -- --           (Kn→ΩKn+1 (suc (suc (suc (m + suc n))))
-- -- -- -- --            (cup' (suc m) (suc n) ∣ b ∣ₕ ∣ a ∣ₕ)))
-- -- -- -- --        ∙∙ Kn→ΩKn+10ₖ _)
-- -- -- -- --       ≡ transport (λ i → refl {x = 0ₖ ((suc (+'-comm (suc (suc n)) (suc (suc (suc m))) i)))}
-- -- -- -- --                         ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc (suc (suc m))) i))})
-- -- -- -- --                   (λ i j → cup' (suc (suc n)) (suc (suc m)) ∣ merid a j ∣ ∣ merid b i ∣)
-- -- -- -- --     lem8 = cong (λ x → (sym (Kn→ΩKn+10ₖ _) ∙∙ (cong (Kn→ΩKn+1 _) x) ∙∙ Kn→ΩKn+10ₖ _))
-- -- -- -- --                 (lem6 ∙ lem7)
-- -- -- -- --         ∙∙ natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n} _ _ ((λ i₁ → cup' (suc n) (suc (suc m)) ∣ a ∣ ∣ merid b i₁ ∣))
-- -- -- -- --                         _ ((λ _ x → (sym (Kn→ΩKn+10ₖ _) ∙∙ (cong (Kn→ΩKn+1 _) x) ∙∙ Kn→ΩKn+10ₖ _)))
-- -- -- -- --                         (+'-comm (suc (suc n)) (suc (suc (suc m))))
-- -- -- -- --         ∙∙ cong (transport (λ i → refl {x = 0ₖ ((suc (+'-comm (suc (suc n)) (suc (suc (suc m))) i)))}
-- -- -- -- --                         ≡ refl {x = 0ₖ (suc (+'-comm (suc (suc n)) (suc (suc (suc m))) i))}))
-- -- -- -- --                 (sym (lem₁ _ _ b a))

-- -- -- -- --     help : (cong (λ x → (cong (λ y → cup' (suc (suc n)) (suc (suc m)) ∣ x ∣ₕ ∣ y ∣)) (merid b)) (merid a))
-- -- -- -- --          ≡ λ i j → -ₖ-gen (suc (suc (suc n))) (suc (suc (suc m))) (inr x) (inr y)
-- -- -- -- --       (subst coHomK (+'-comm (suc (suc (suc m))) (suc (suc (suc n))))
-- -- -- -- --        (cup' (suc (suc m)) (suc (suc n)) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- --     help =
-- -- -- -- --          ((sym (inst _ (λ i j →
-- -- -- -- --          cup' (suc (suc n)) (suc (suc m)) ∣ merid a j ∣ ∣ merid b i ∣)))
-- -- -- -- --         ∙ sym (final (suc n) (suc m) ((λ i j₁ →
-- -- -- -- --               cup' (suc (suc n)) (suc (suc m)) ∣ merid a j₁ ∣ ∣ merid b (~ i) ∣))))
-- -- -- -- --       ∙∙ cong (transport (λ i₁ → refl ≡ refl))
-- -- -- -- --               ((cong (sym ∘ transport (λ i₂ → refl ≡ refl))
-- -- -- -- --                      ((cong (transport (λ i₁ → refl ≡ refl))
-- -- -- -- --                        (sym lem8)
-- -- -- -- --                      ∙ sym lem₅) ∙
-- -- -- -- --                      (cong (λ x → (sym (Kn→ΩKn+10ₖ (suc (suc (suc (suc (n + suc m)))))) ∙∙
-- -- -- -- --                                     cong (Kn→ΩKn+1 (suc (suc (suc (suc (n + suc m)))))) x
-- -- -- -- --                                     ∙∙ Kn→ΩKn+10ₖ (suc (suc (suc (suc (n + suc m)))))))
-- -- -- -- --                            (sym lem4)))
-- -- -- -- --               ∙ sym (cong sym lem3))
-- -- -- -- --               ∙∙ inst _ _
-- -- -- -- --               ∙∙ sym (cong flipSquare (lem₁ (suc n) (suc m) a b)))
-- -- -- -- --       ∙∙ sym (lem₈ (suc n) (suc m) (λ i j → cup' (suc (suc m)) (suc (suc n)) ∣ merid b i ∣ₕ ∣ merid a j ∣ₕ))
-- -- -- -- --       ∙∙ sym (inst _ _)
-- -- -- -- --       ∙∙ sym (lem57 (cong (cong (subst coHomK (+'-comm (suc (suc (suc m))) (suc (suc (suc n))))))
-- -- -- -- --              λ i j → cup' (suc (suc m)) (suc (suc n)) ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
-- -- -- -- -- -}
