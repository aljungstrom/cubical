{-# OPTIONS --safe --no-exact-split --experimental-lossy-unification --no-forcing #-}
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
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Data.Int
  renaming (_+_ to _ℤ+_ ; _·_ to _ℤ∙_ ; +-comm to +ℤ-comm ; ·-comm to ∙-comm ; +-assoc to ℤ+-assoc ; -_ to -ℤ_)
    hiding (_+'_ ; +'≡+)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.EvenOdd
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary

open import Cubical.Foundations.Path
pathalg : ∀ {ℓ} {A : Type ℓ} (x y : A) → (p q : x ≡ y) (P : Square p q refl refl)
  → PathP (λ j → PathP (λ i → Path A (p (i ∧ j)) (q (i ∨ ~ j)))
                    (λ k → q (~ j ∧ k))
                     λ k → p (j ∨ k))
      (sym P)
      (flipSquare P)
pathalg {A = A} x y =
  J (λ y p → (q : x ≡ y) → (P : Square p q refl refl) →
      PathP (λ j → PathP (λ i → Path A (p (i ∧ j)) (q (i ∨ ~ j)))
                     (λ k → q (~ j ∧ k))
                     (λ k → p (j ∨ k)))
       (sym P)
       (flipSquare P))
     λ q →
    J (λ q P → PathP (λ j → PathP (λ i → Path A x (q (i ∨ ~ j)))
                 (λ k → q (~ j ∧ k)) refl)
                 (λ i → P (~ i)) λ i j → P j i)
       refl

inst : ∀ {ℓ} {A : Type ℓ} (x : A) → (P : Square (refl {x = x}) refl refl refl)
  → sym P ≡ flipSquare P
inst x = pathalg x x refl refl

pathalg2 : ∀ {ℓ} {A : Type ℓ} (x y : A) → (p q : x ≡ y) (P : Square p q refl refl)
  → PathP (λ i → PathP (λ j → p i ≡ q (~ i))
                    ((λ j → p (i ∨ j)) ∙ (λ j → q (~ i ∨ ~ j)))
                    ((λ j → p (i ∧ ~ j)) ∙ (λ j → q (~ i ∧ j))))
       (sym (rUnit p) ∙∙ P ∙∙ lUnit _)
       (sym (lUnit (sym q)) ∙∙ (λ i j → P (~ i) (~ j)) ∙∙ rUnit (sym p))
pathalg2 x y =
  J (λ y p → (q : x ≡ y) (P : Square p q refl refl)
      → PathP (λ i → PathP (λ j → p i ≡ q (~ i)) ((λ j → p (i ∨ j)) ∙ (λ j → q (~ i ∨ ~ j)))
                                                    ((λ j → p (i ∧ ~ j)) ∙ (λ j → q (~ i ∧ j))))
               (sym (rUnit p) ∙∙ P ∙∙ lUnit _)
               (sym (lUnit (sym q)) ∙∙ (λ i j → P (~ i) (~ j)) ∙∙ rUnit (sym p)))
      λ q →
      J (λ q P → PathP (λ i → (λ j → x) ∙ (λ j → q (~ i ∨ ~ j)) ≡
                                (λ j → x) ∙ (λ j → q (~ i ∧ j)))
                  ((λ i → rUnit refl (~ i)) ∙∙ P ∙∙ lUnit q)
                  ((λ i → lUnit (λ i₁ → q (~ i₁)) (~ i)) ∙∙ (λ i j → P (~ i) (~ j)) ∙∙ rUnit refl))
        refl

inst2 : ∀ {ℓ} {A : Type ℓ} (x : A) → (P : Square (refl {x = x}) refl refl refl) → P ≡ λ i j → P (~ i) (~ j)
inst2 x P =
  transport (λ i → doubleCompPath-filler (sym (rUnit refl)) P (lUnit refl) (~ i)
                  ≡ doubleCompPath-filler (sym (rUnit refl))
            (λ i j → P (~ i) (~ j)) (lUnit refl) (~ i)) (pathalg2 _ _ refl refl P)

inst3 : ∀ {ℓ} {A : Type ℓ} (x : A) → (P : Square (refl {x = x}) refl refl refl) → flipSquare P ≡ λ i j → P i (~ j)
inst3 x P = sym (inst x P) ∙ sym (inst2 x (cong sym P))

inst4 : ∀ {ℓ} {A : Type ℓ} {x : A} → (P : Square (refl {x = x}) refl refl refl) → sym P ≡ cong sym P
inst4 P = inst _ _ ∙ inst3 _ P

coHomKType : (n : ℕ) → Type
coHomKType zero = Int
coHomKType (suc n) = S₊ (suc n)

-ₖ-helper : {k : ℕ} → (n m : ℕ) → is-even n ⊎ is-odd n → is-even m ⊎ is-odd m → coHomKType k → coHomKType k
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

-ₖ-gen : {k : ℕ} (n m : ℕ)
         (p : is-even n ⊎ is-odd n)
         (q : is-even m ⊎ is-odd m)
         → coHomK k → coHomK k
-ₖ-gen {k = zero} = -ₖ-helper {k = zero}
-ₖ-gen {k = suc k} n m p q = trMap (-ₖ-helper {k = suc k} n m p q)

-ₖ^_·_ : {k : ℕ} (n m : ℕ) → coHomK k → coHomK k
-ₖ^_·_ {k = zero} n m = -ₖ-helper {k = zero} n m (evenOrOdd n) (evenOrOdd m)
-ₖ^_·_ {k = suc k} n m = trMap (-ₖ-helper n m (evenOrOdd n) (evenOrOdd m))

ΩKn+1→Ω²Kn+2 : {k : ℕ} → typ (Ω (coHomK-ptd k)) → typ ((Ω^ 2) (coHomK-ptd (suc k)))
ΩKn+1→Ω²Kn+2 x =
     sym (Kn→ΩKn+10ₖ _)
  ∙∙ cong (Kn→ΩKn+1 _) x
  ∙∙ Kn→ΩKn+10ₖ _

ΩKn+1→Ω²Kn+2' : {k : ℕ} → Kn→ΩKn+1 k (0ₖ k) ≡ Kn→ΩKn+1 k (0ₖ k) → typ ((Ω^ 2) (coHomK-ptd (suc k)))
ΩKn+1→Ω²Kn+2' x =
  sym (Kn→ΩKn+10ₖ _)
  ∙∙ x
  ∙∙ Kn→ΩKn+10ₖ _

Kn→Ω²Kn+2 : {k : ℕ} → coHomK k → typ ((Ω^ 2) (coHomK-ptd (2 + k)))
Kn→Ω²Kn+2 x = ΩKn+1→Ω²Kn+2 (Kn→ΩKn+1 _ x)

-ₖ-gen-inr≡-ₖ : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : coHomK k)
  → -ₖ-gen n m (inr p) (inr q) x ≡ (-ₖ x)
-ₖ-gen-inr≡-ₖ {k = zero} n m p q _ = refl
-ₖ-gen-inr≡-ₖ {k = suc zero} n m p q =
  trElim ((λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _))
         λ { base → refl
          ; (loop i) → refl}
-ₖ-gen-inr≡-ₖ {k = suc (suc k)} n m p q =
  trElim ((λ _ → isOfHLevelPath (4 + k) (isOfHLevelTrunc (4 + k)) _ _))
         λ { north → refl
           ; south → refl
           ; (merid a i) k → ∣ symDistr (merid (ptSn _)) (sym (merid a)) (~ k) (~ i) ∣ₕ}

-ₖ-gen-inl-left : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : coHomK k)
  → -ₖ-gen n m (inl p) q x ≡ x
-ₖ-gen-inl-left {k = zero} n m p q x = refl
-ₖ-gen-inl-left {k = suc zero} n m p q =
  trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
         λ { base → refl ; (loop i) → refl}
-ₖ-gen-inl-left {k = suc (suc k)} n m p q =
  trElim (λ _ → isOfHLevelPath (4 + k) (isOfHLevelTrunc (4 + k)) _ _)
         λ { north → refl
           ; south → cong ∣_∣ₕ (merid (ptSn _))
           ; (merid a i) k → ∣ compPath-filler (merid a) (sym (merid (ptSn _))) (~ k) i  ∣ₕ}

-ₖ-gen-inl-right : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : coHomK k)
  → -ₖ-gen n m p (inl q) x ≡ x
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

cong-ₖ-gen-inr : {k : ℕ} (n m : ℕ)  (p : _) (q : _) (P : Path (coHomK (2 + k)) (0ₖ _) (0ₖ _))
     → cong (-ₖ-gen n m (inr p) (inr q)) P ≡ sym P
cong-ₖ-gen-inr {k = k} n m p q P = code≡sym (0ₖ _) P
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

cong-cong-ₖ-gen-inr : {k : ℕ} (n m : ℕ) (p : _) (q : _) (P : Square (refl {x = 0ₖ (suc (suc k))}) refl refl refl)
           → cong (cong (-ₖ-gen n m (inr p) (inr q))) P ≡ sym P
cong-cong-ₖ-gen-inr n m p q P =
     rUnit _
  ∙∙ (λ k → (λ i → cong-ₖ-gen-inr n m p q refl (i ∧ k))
          ∙∙ (λ i → cong-ₖ-gen-inr n m p q (P i) k)
          ∙∙ λ i → cong-ₖ-gen-inr n m p q refl (~ i ∧ k))
  ∙∙ (λ k → transportRefl refl k
          ∙∙ cong sym P
          ∙∙ transportRefl refl k)
  ∙∙ sym (rUnit (cong sym P))
  ∙∙ sym (inst4 P)

natTranspLem : ∀ {A : ℕ → Type} (n m : ℕ) (a : A n) (B : (n : ℕ) → Type)
  (f : (n : ℕ) → (a : A n) → B n) (p : n ≡ m)
  → f m (subst A p a) ≡ subst B p (f n a)
natTranspLem {A = A} n m a B f = J (λ m p → f m (subst A p a) ≡ subst B p (f n a)) (cong (f n) (substRefl a) ∙ sym (substRefl (f n a)))


-ₖ-gen-Kn→ΩKn+1 : {k : ℕ} → (n m : ℕ) (p : _) (q : _) (x : coHomK k) → Kn→ΩKn+1 _ (-ₖ-gen n m (inr p) (inr q) x) ≡ sym (Kn→ΩKn+1 _ x)
-ₖ-gen-Kn→ΩKn+1 n m p q x = cong (Kn→ΩKn+1 _) (-ₖ-gen-inr≡-ₖ n m p q x) ∙ Kn→ΩKn+1-ₖ _ x

Kn→ΩKn+1-ₖ' : {k : ℕ} (n m : ℕ) (p : _) (q : _) (x : coHomK k) → Kn→ΩKn+1 k (-ₖ-gen n m (inr p) (inr q) x) ≡ sym (Kn→ΩKn+1 k x)
Kn→ΩKn+1-ₖ' = -ₖ-gen-Kn→ΩKn+1

+'-comm : (n m : ℕ) → n +' m ≡ m +' n
+'-comm n m = +'≡+ n m ∙∙ +-comm n m ∙∙ sym (+'≡+ m n)

testP : (n : ℕ) → subst coHomK (+'-comm 1 (suc n)) (0ₖ _) ≡ 0ₖ _
testP zero = refl
testP (suc n) = refl

transpΩ² : {n m : ℕ} (p q : n ≡ m) → (P : _)
        → transport (λ i → refl {x = 0ₖ (p i)} ≡ refl {x = 0ₖ (p i)}) P
        ≡ transport (λ i → refl {x = 0ₖ (q i)} ≡ refl {x = 0ₖ (q i)}) P
transpΩ² p q P k = subst (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n}) (isSetℕ _ _ p q k) P


lem₁ : (n : ℕ) (a : _) → (cong (cong (subst coHomK (+'-comm (suc zero) (suc (suc n))))) (Kn→Ω²Kn+2 ∣ a ∣ₕ))
   ≡ ΩKn+1→Ω²Kn+2
     (sym (testP n)
   ∙∙ cong (subst coHomK (+'-comm (suc zero) (suc n))) (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ)
   ∙∙ testP n)
lem₁ zero a =
     (λ k i j → transportRefl (Kn→Ω²Kn+2 ∣ a ∣ₕ i j) k)
   ∙ cong ΩKn+1→Ω²Kn+2 λ k → rUnit (λ i → transportRefl (Kn→ΩKn+1 1 ∣ a ∣ i) (~ k)) k
lem₁ (suc n) a =
     (λ k → transp (λ i → refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) (i ∨ ~ k))}
                          ≡ refl {x = 0ₖ (+'-comm 1 (suc (suc (suc n))) (i ∨ ~ k))}) (~ k)
              (λ i j → transp (λ i → coHomK (+'-comm 1 (suc (suc (suc n))) (i ∧ ~ k))) k
              (Kn→Ω²Kn+2 ∣ a ∣ₕ i j)))
  ∙∙ transpΩ² (+'-comm 1 (suc (suc (suc n)))) (cong suc (+'-comm (suc zero) (suc (suc n)))) (Kn→Ω²Kn+2 ∣ a ∣ₕ)
  ∙∙ sym (natTranspLem {A = λ n → 0ₖ n ≡ 0ₖ n} _ _
           (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣) _
            (λ _ → ΩKn+1→Ω²Kn+2)
            (+'-comm 1 (suc (suc n))))
  ∙∙ cong ΩKn+1→Ω²Kn+2
       (λ k → transp (λ i → 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ k))
                            ≡ 0ₖ (+'-comm (suc zero) (suc (suc n)) (i ∨ k))) k
        (λ i → transp (λ i → coHomK (+'-comm (suc zero) (suc (suc n)) (i ∧ k))) (~ k)
         (Kn→ΩKn+1 _ ∣ a ∣ₕ i)))
  ∙∙ cong ΩKn+1→Ω²Kn+2 (rUnit (cong (subst coHomK (+'-comm (suc zero) (suc (suc n)))) (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ)))

transpLem' : (n : ℕ) (a : _) (p : _) (q : _)
  → (cong (cong (-ₖ-gen (suc (suc n)) (suc zero) p q ∘ (subst coHomK (+'-comm 1 (suc (suc n))))))
           (Kn→Ω²Kn+2 (∣ a ∣ₕ)))
   ≡ ΩKn+1→Ω²Kn+2
       (sym (testP n)
     ∙∙ cong (subst coHomK (+'-comm (suc zero) (suc n))) (cong (-ₖ-gen (suc (suc n)) (suc zero) p q)
             (Kn→ΩKn+1 (suc n) ∣ a ∣ₕ))
     ∙∙ testP n)
transpLem' n a (inl x) (inr y) =
     (λ k i j → (-ₖ-gen-inl-left (suc (suc n)) 1 x (inr y) (
                  subst coHomK (+'-comm 1 (suc (suc n)))
                (Kn→Ω²Kn+2 ∣ a ∣ₕ i j))) k)
  ∙∙ lem₁ n a
  ∙∙ cong ΩKn+1→Ω²Kn+2 (cong (sym (testP n) ∙∙_∙∙ testP n) 
    λ k i → subst coHomK (+'-comm 1 (suc n))
            (-ₖ-gen-inl-left (suc (suc n)) 1 x (inr y) (Kn→ΩKn+1 (suc n) ∣ a ∣ i) (~ k)))
transpLem' n a (inr x) (inr y) =
     cong-cong-ₖ-gen-inr (suc (suc n)) 1 x y
       (cong
      (cong
       (subst coHomK (+'-comm 1 (suc (suc n)))))
      (Kn→Ω²Kn+2 ∣ a ∣ₕ))
  ∙∙ cong sym (lem₁ n a)
  ∙∙ λ k → ΩKn+1→Ω²Kn+2
              (sym (testP n) ∙∙
               cong (subst coHomK (+'-comm 1 (suc n)))
               (cong-ₖ-gen-inr (suc (suc n)) 1 x y
                (Kn→ΩKn+1 (suc n) ∣ a ∣) (~ k))
               ∙∙ testP n)

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
      ∙∙ (λ k → (λ i j → (cong-ₖ-gen-inr 1 1 tt tt refl (~ k ∧ i) j))
              ∙∙ (λ i j → cong-ₖ-gen-inr 1 1 tt tt (((sym (Kn→ΩKn+10ₖ _) ∙∙ (λ i j → _⌣ₖ_ {n = suc zero} {m = suc zero} ∣ loop j ∣ₕ ∣ loop i ∣ₕ) ∙∙ Kn→ΩKn+10ₖ _)) i) (~ k) j)
               ∙∙ λ i j → (cong-ₖ-gen-inr 1 1 tt tt refl (~ k ∧ ~ i) j))
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
        (λ k → rUnit ((cong (Kn→ΩKn+1 _) (cong-ₖ-gen-inr (suc zero) (suc zero) tt tt (λ i → (subst coHomK (+'-comm (suc zero) (suc zero)) (Kn→ΩKn+1 (suc zero) ∣ a ∣ₕ i))) k))) (~ k))
      ∙ λ k → ((cong (Kn→ΩKn+1 (suc (suc zero)))
                 (rUnit (λ i → subst coHomK (+'-comm (suc zero) (suc zero))
                   (-ₖ-gen-inl-left (suc (suc zero)) (suc zero) tt (inr tt) (Kn→ΩKn+1 (suc zero) ∣ a ∣ₕ (~ i)) (~ k))) k)))
    help₂ (suc n) a (inl x) (inr tt) =
        ((λ k → rUnit (cong (Kn→ΩKn+1 _) (λ i → -ₖ-gen (suc (suc n)) (suc zero) (evenOrOdd-Prop n (evenOrOdd (suc (suc n))) (inr x) k) (inr tt)
                                                                      (subst coHomK (+'-comm (suc zero) (suc (suc n))) (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ i)))) (~ k)))
      ∙ (((λ k → ((cong (Kn→ΩKn+1 _) (cong-ₖ-gen-inr (suc (suc n)) (suc zero) x tt (λ i → (subst coHomK (+'-comm (suc zero) (suc (suc n))) (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ i))) k))))))
      ∙ λ k → ((cong (Kn→ΩKn+1 (suc (suc (suc n + zero))))
                 (rUnit (λ i → subst coHomK (+'-comm (suc zero) (suc (suc n)))
                   (-ₖ-gen-inl-left (suc (suc (suc n))) (suc zero) x (inr tt) (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ (~ i)) (~ k))) k)))
    help₂ (suc n) a (inr x) (inr tt) =
         (λ k → rUnit (λ i j → Kn→ΩKn+1 _ (-ₖ-gen (suc (suc n)) (suc zero) (evenOrOdd-Prop (suc (suc n)) (evenOrOdd (suc (suc n))) (inl x) k) (inr tt)
                                                                      (subst coHomK (+'-comm (suc zero) (suc (suc n))) (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ i))) j) (~ k))
      ∙∙ (λ k i j → Kn→ΩKn+1 _ (-ₖ-gen-inl-left (suc (suc n)) (suc zero) x (inr tt)
                                  (subst coHomK (+'-comm (suc zero) (suc (suc n))) (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ i)) k) j)
      ∙∙ λ k → cong (Kn→ΩKn+1 _)
                (rUnit (sym (cong (subst coHomK (+'-comm (suc zero) (suc (suc n)))) (cong-ₖ-gen-inr (suc (suc (suc n))) (suc zero) x tt (Kn→ΩKn+1 (suc (suc n)) ∣ a ∣ₕ) (~ k)))) k)

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

testP2 : (n m : ℕ) → subst coHomK (+'-comm (suc (suc n)) (suc m)) (0ₖ _) ≡ 0ₖ _
testP2 n zero = refl
testP2 n (suc m) = refl

cuteLem₁-help : (n m : ℕ) (q : _) (p : is-even (suc (suc n)) ⊎ is-odd (suc (suc n))) (x : _)
  → (((sym (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (testP2 m n))
                               ∙∙ (λ j → -ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q
                              (subst coHomK (+'-comm (suc (suc m)) (suc n)) (Kn→ΩKn+1 _ x j)))
                  ∙∙ cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (testP2 m n))))
   ≡ (Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)
                                             (subst coHomK (cong suc (+-comm (suc m) n))
                                             x)))
cuteLem₁-help n m q p x =
  sym (cong-∙∙ (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (sym (testP2 m n))
      (λ j → subst coHomK (+'-comm (suc (suc m)) (suc n)) (Kn→ΩKn+1 _ x j))
      (testP2 m n))
        ∙ h n m p q x
  where
  help : (n m : ℕ) (x : _)
    → ((sym (testP2 m n))
       ∙∙ (λ j → subst coHomK (+'-comm (suc (suc m)) (suc n))
                   (Kn→ΩKn+1 (suc (suc (m + n))) x j))
       ∙∙ testP2 m n)
       ≡ {!!}
  help = {!!}

  h : (n m : ℕ) (p : is-even (suc (suc n)) ⊎ is-odd (suc (suc n))) (q : _) (x : _) →
           cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)
      ((λ i → testP2 m n (~ i)) ∙∙
       (λ j →
          subst coHomK (+'-comm (suc (suc m)) (suc n))
          (Kn→ΩKn+1 (suc (suc (m + n))) x j))
       ∙∙ testP2 m n)
      ≡
      Kn→ΩKn+1 (suc (n + suc m))
      (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)
       (subst coHomK (cong suc (+-comm (suc m) n)) x))
  h n m (inl p) (inl q) x =
       (λ k → cong
      (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd-Prop (suc n) (evenOrOdd (suc n)) (inr p) k) (inl q))
      ((λ i → testP2 m n (~ i)) ∙∙
       (λ j →
          subst coHomK (+'-comm (suc (suc m)) (suc n))
          (Kn→ΩKn+1 (suc (suc (m + n))) x j))
       ∙∙ testP2 m n))
    ∙∙ (λ k i → -ₖ-gen-inl-right (suc n) (suc (suc m)) (inr p) q
                  ((((sym (testP2 m n)) ∙∙
                      (λ j →
                         subst coHomK (+'-comm (suc (suc m)) (suc n))
                         (Kn→ΩKn+1 (suc (suc (m + n))) x j))
                      ∙∙ testP2 m n) i)) k)
    ∙∙ {!!}
     ∙ λ i → Kn→ΩKn+1 (suc (n + suc m))
               (-ₖ-gen-inl-right (suc n) (suc (suc m)) (evenOrOdd-Prop (suc n) (inr p) (evenOrOdd (suc n)) i) q
                (subst coHomK (cong suc (+-comm (suc m) n)) x) (~ i))
  h n m (inl p) (inr q) x = {!!}
  h n m (inr p) (inl q) x = {!!}
  h n m (inr p) (inr q) x = {!!}

cuteLem₁' : (n m : ℕ) (q : _) (p : is-even (suc (suc n)) ⊎ is-odd (suc (suc n))) (a : _) (b : _)
        → cong (Kn→ΩKn+1 _) (((sym (cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (testP2 m n))
                               ∙∙ (λ j → -ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q
                              (subst coHomK (+'-comm (suc (suc m)) (suc n)) (_⌣ₖ_ {n = suc (suc m)} {m = (suc n)} ∣ merid b j ∣ₕ ∣ a ∣)))
                  ∙∙ cong (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) (testP2 m n))))
         ≡ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) -- (suc n) * m
                                             (subst coHomK (cong suc (+-comm (suc m) n))
                                             (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ₕ ∣ a ∣))))
cuteLem₁' n m q p a b = cong (cong (Kn→ΩKn+1 _)) (cuteLem₁-help n m q p (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ₕ ∣ a ∣))

cuteLem₁ : (n m : ℕ) (q : _) (p : is-even (suc (suc n)) ⊎ is-odd (suc (suc n))) (a : _) (b : _)
        → cong (Kn→ΩKn+1 _) (((sym (cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)) (testP2 m n))
                               ∙∙ (λ j → trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)
                              (subst coHomK (+'-comm (suc (suc m)) (suc n)) (_⌣ₖ_ {n = suc (suc m)} {m = (suc n)} ∣ merid b j ∣ₕ ∣ a ∣)))
                  ∙∙ cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)) (testP2 m n))))
         ≡ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) -- (suc n) * m
                                             (subst coHomK (cong suc (+-comm (suc m) n))
                                             (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ₕ ∣ a ∣))))
cuteLem₁ zero m (inl x) (inl y) a b =
    ((λ k → cong (Kn→ΩKn+1 _)
        (rUnit
          ((λ j → -ₖ-gen (suc zero) (suc (suc m)) (inr tt) (inl x)
                              (transp (λ i → coHomK (+'-comm (suc (suc m)) (suc zero) (i ∨ k))) k
                                (Kn→ΩKn+1 _ (transp (λ i → coHomK (predℕ (+'-comm (suc (suc m)) (suc zero) (i ∧ k)))) (~ k)
                                  (_⌣ₖ_ {n = suc m} {m = (suc zero)} ∣ b ∣ₕ ∣ a ∣)) j))))
          (~ k))))
  ∙∙ (λ k j → Kn→ΩKn+1 _ ((-ₖ-gen-inl-right (suc zero) (suc (suc m)) (inr y) x
                             (Kn→ΩKn+1 _ (subst coHomK (cong predℕ (+'-comm (suc (suc m)) (suc zero)))
                               (_⌣ₖ_ {n = suc m} {m = (suc zero)} ∣ b ∣ₕ ∣ a ∣)) j) k)))
  ∙∙ λ k → cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (-ₖ-gen-inl-right (suc zero) (suc (suc m)) (inr tt) x
                                             (subst coHomK
                                               (isSetℕ _ _ (cong predℕ (+'-comm (suc (suc m)) (suc zero)))
                                                 (cong suc (+-comm (suc m) zero)) k)
                                             (_⌣ₖ_ {n = suc m} {m = (suc zero)} ∣ b ∣ₕ ∣ a ∣)) (~ k)))
cuteLem₁ (suc n) m (inl x) (inl y) a b =
  ((λ k → cong (Kn→ΩKn+1 _)
        (rUnit
          ((λ j → -ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd-Prop n (evenOrOdd n) (inr y) k) (inl x)
                              (transp (λ i → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (i ∨ k))) k
                                (Kn→ΩKn+1 _ (transp (λ i → coHomK (predℕ (+'-comm (suc (suc m)) (suc (suc n)) (i ∧ k)))) (~ k)
                                  (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣)) j))))
          (~ k))))
  ∙∙ (λ k j → Kn→ΩKn+1 _ ((-ₖ-gen-inl-right (suc (suc n)) (suc (suc m)) (inr y) x
                             (Kn→ΩKn+1 _ (subst coHomK (cong predℕ (+'-comm (suc (suc m)) (suc (suc n))))
                               (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣)) j) k)))
  ∙∙ λ k → cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (-ₖ-gen-inl-right (suc (suc n)) (suc (suc m)) (evenOrOdd n) x -- (suc n) * m
                                             (subst coHomK
                                               (isSetℕ _ _ (cong predℕ (+'-comm (suc (suc m)) (suc (suc n))))
                                                 (cong suc (+-comm (suc m) (suc n))) k)
                                             (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣)) (~ k)))
cuteLem₁ (suc n) m (inl x) (inr y) a b =
    ((λ k → cong (Kn→ΩKn+1 _)
        (rUnit
          ((λ j → -ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd-Prop n (evenOrOdd n) (inl y) k) (inl x)
                              (transp (λ i → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (i ∨ k))) k
                                (Kn→ΩKn+1 _ (transp (λ i → coHomK (predℕ (+'-comm (suc (suc m)) (suc (suc n)) (i ∧ k)))) (~ k)
                                  (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣)) j))))
          (~ k))))
  ∙∙ (λ k j → Kn→ΩKn+1 _ ((-ₖ-gen-inl-right (suc (suc n)) (suc (suc m)) (inl y) x
                             (Kn→ΩKn+1 _ (subst coHomK (cong predℕ (+'-comm (suc (suc m)) (suc (suc n))))
                               (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣)) j) k)))
  ∙∙ λ k → cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (-ₖ-gen-inl-right (suc (suc n)) (suc (suc m)) (evenOrOdd n) x -- (suc n) * m
                                             (subst coHomK
                                               (isSetℕ _ _ (cong predℕ (+'-comm (suc (suc m)) (suc (suc n))))
                                                 (cong suc (+-comm (suc m) (suc n))) k)
                                             (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣)) (~ k)))
cuteLem₁ zero m (inr x) (inl y) a b =
  ((λ k → cong (Kn→ΩKn+1 _)
          (rUnit (λ j → -ₖ-gen (suc zero) (suc (suc m)) (inr tt) (inr x)
                      (transp (λ i → coHomK (+'-comm (suc (suc m)) (suc zero) (i ∨ k))) k
                              (Kn→ΩKn+1 _ ((transp (λ i → coHomK (predℕ (+'-comm (suc (suc m)) (suc zero) (i ∧ k)))) (~ k)
                                          (_⌣ₖ_ {n = suc m} {m = (suc zero)} ∣ b ∣ₕ ∣ a ∣))) j))) (~ k))))
  ∙∙ (λ k → cong (Kn→ΩKn+1 _)
                  (cong-ₖ-gen-inr (suc zero) (suc (suc m)) y x
                    (Kn→ΩKn+1 _ (subst coHomK (cong predℕ (+'-comm (suc (suc m)) (suc zero)))
                      (_⌣ₖ_ {n = suc m} {m = (suc zero)} ∣ b ∣ₕ ∣ a ∣))) k))
  ∙∙ (λ k → cong (Kn→ΩKn+1 _)
             (-ₖ-gen-Kn→ΩKn+1 (suc zero) (suc (suc m)) y x
               (subst coHomK (cong predℕ (+'-comm (suc (suc m)) (suc zero)))
                      (_⌣ₖ_ {n = suc m} {m = (suc zero)} ∣ b ∣ₕ ∣ a ∣)) (~ k)))
   ∙ λ k → cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (-ₖ-gen (suc zero) (suc (suc m)) (inr tt) (inr x)
                                             (subst coHomK
                                               (isSetℕ _ _ (cong predℕ (+'-comm (suc (suc m)) (suc zero)))
                                                 (cong suc (+-comm (suc m) zero)) k)
                                             (_⌣ₖ_ {n = suc m} {m = (suc zero)} ∣ b ∣ₕ ∣ a ∣))))
cuteLem₁ (suc n) m (inr x) (inl y) a b =
  ((λ k → cong (Kn→ΩKn+1 _)
          (rUnit (λ j → -ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd-Prop n (evenOrOdd n) (inr y) k) (inr x)
                      (transp (λ i → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (i ∨ k))) k
                              (Kn→ΩKn+1 _ ((transp (λ i → coHomK (predℕ (+'-comm (suc (suc m)) (suc (suc n)) (i ∧ k)))) (~ k)
                                          (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣))) j))) (~ k))))
  ∙∙ (λ k → cong (Kn→ΩKn+1 _)
                  (cong-ₖ-gen-inr (suc (suc n)) (suc (suc m)) y x
                    (Kn→ΩKn+1 _ (subst coHomK (cong predℕ (+'-comm (suc (suc m)) (suc (suc n))))
                      (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣))) k))
  ∙∙ (λ k → cong (Kn→ΩKn+1 _)
             (-ₖ-gen-Kn→ΩKn+1 (suc (suc n)) (suc (suc m)) y x
               (subst coHomK (cong predℕ (+'-comm (suc (suc m)) (suc (suc n))))
                      (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣)) (~ k)))
   ∙ λ k → cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd-Prop n (evenOrOdd n) (inr y) (~ k)) (inr x)
                                             (subst coHomK
                                               (isSetℕ _ _ (cong predℕ (+'-comm (suc (suc m)) (suc (suc n))))
                                                 (cong suc (+-comm (suc m) (suc n))) k)
                                             (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣))))
cuteLem₁ (suc n) m (inr x) (inr y) a b =
     (((λ k → cong (Kn→ΩKn+1 _)
        (rUnit ((λ j → -ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd-Prop n (evenOrOdd n) (inl y) k) (inr x)
                              (transp (λ i → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (i ∨ k))) k
                                (Kn→ΩKn+1 _ (transp (λ i → coHomK (predℕ (+'-comm (suc (suc m)) (suc (suc n)) (i ∧ k)))) (~ k)
                                  (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣)) j)))) (~ k)))))
  ∙∙ (λ k → cong (Kn→ΩKn+1 _)
              λ j → -ₖ-gen-inl-left (suc (suc n)) (suc (suc m)) y (inr x)
                (Kn→ΩKn+1 _ (subst coHomK (cong predℕ (+'-comm (suc (suc m)) (suc (suc n))))
                  (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣)) j) k)
  ∙∙ (λ k → cong (Kn→ΩKn+1 _)
              (Kn→ΩKn+1 _ (-ₖ-gen-inl-left (suc (suc n)) (suc (suc m)) y (inr x)
                (subst coHomK (cong predℕ (+'-comm (suc (suc m)) (suc (suc n))))
                  (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣)) (~ k))))
   ∙ λ k → cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (-ₖ-gen (suc (suc n)) (suc (suc m)) (evenOrOdd-Prop n (evenOrOdd n) (inl y) (~ k)) (inr x)
                                             (subst coHomK
                                               (isSetℕ _ _ (cong predℕ (+'-comm (suc (suc m)) (suc (suc n))))
                                                 (cong suc (+-comm (suc m) (suc n))) k)
                                             (_⌣ₖ_ {n = suc m} {m = (suc (suc n))} ∣ b ∣ₕ ∣ a ∣))))

cuteLem₂ : (n m : ℕ) (p : _) (q : _) (a : _) (b : _) → cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) p q
                      ∘ (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))))
                      (sym (Kn→ΩKn+10ₖ _) ∙∙ (λ i j → Kn→ΩKn+1 _ ((sym (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (testP2 n m))
                                                                     ∙∙ (λ i → -ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                                                                                   (subst coHomK (+'-comm (suc (suc n)) (suc m))
                                                                                     (_⌣ₖ_ {n = suc (suc n)} {m = suc m} ∣ merid a i ∣ₕ ∣ b ∣ₕ)))
                                                                     ∙∙ cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (testP2 n m)) i) j)
                                           ∙∙ Kn→ΩKn+10ₖ _)
             ≡ (sym (Kn→ΩKn+10ₖ _)
            ∙∙ (λ i j → Kn→ΩKn+1 _
                          ((Kn→ΩKn+1 _ (-ₖ-gen (suc (suc n)) (suc (suc m)) p q
                            (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                              (subst coHomK (cong suc (sym (+-suc n m))) (_⌣ₖ_ {n = suc n} {m = suc m} ∣ a ∣ₕ ∣ b ∣ₕ))))) i) j)
            ∙∙ Kn→ΩKn+10ₖ _)
cuteLem₂ n m p q a b =
     cong (cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) p q
                      ∘ (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))))
          (cong (sym (Kn→ΩKn+10ₖ _) ∙∙_∙∙ Kn→ΩKn+10ₖ _)
            (cuteLem₁ m n p q b a))
   ∙ help p q (_⌣ₖ_ {n = suc n} {m = suc m} ∣ a ∣ ∣ b ∣)
  where
  annoying : (x : _)
    → cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))))
         (sym ((Kn→ΩKn+10ₖ _))
      ∙∙ cong (Kn→ΩKn+1 _)
          (Kn→ΩKn+1 (suc (m + suc n))
              (subst coHomK (cong suc (+-comm (suc n) m)) x))
      ∙∙ Kn→ΩKn+10ₖ _)
       ≡ ((sym (Kn→ΩKn+10ₖ _) ∙∙
       (λ i j →
          Kn→ΩKn+1 (suc (suc (n + suc m)))
          (Kn→ΩKn+1 (suc (n + suc m))
             (subst coHomK (cong suc (sym (+-suc n m))) x)
           i)
          j)
       ∙∙ Kn→ΩKn+10ₖ _))
  annoying x =
      ((λ k → transp (λ i → refl {x = 0ₖ ((+'-comm (suc (suc m)) (suc (suc n))) (i ∨  ~ k))}
                            ≡ refl {x = 0ₖ ((+'-comm (suc (suc m)) (suc (suc n))) (i ∨ ~ k))}) (~ k)

                λ i j → transp (λ i → coHomK (+'-comm (suc (suc m)) (suc (suc n)) (i ∧ ~ k))) k
                  ((sym (Kn→ΩKn+10ₖ _)
                  ∙∙ cong (Kn→ΩKn+1 _)
                      (Kn→ΩKn+1 _ (subst coHomK (cong suc (+-comm (suc n) m)) x))
                  ∙∙ Kn→ΩKn+10ₖ _) i j)))
    ∙∙ cong (transport (λ i → refl {x = 0ₖ ((+'-comm (suc (suc m)) (suc (suc n))) i)}
                            ≡ refl {x = 0ₖ ((+'-comm (suc (suc m)) (suc (suc n))) i)}))
            (natTranspLem {A = coHomK} _ _ x _
              (λ _ z → sym (Kn→ΩKn+10ₖ _)  ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ z) ∙∙ Kn→ΩKn+10ₖ _)
               (cong suc (+-comm (suc n) m)))
    ∙∙ sym (substComposite (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n})
           (cong (suc ∘ suc ∘ suc) (+-comm (suc n) m))
           (+'-comm (suc (suc m)) (suc (suc n)))
            (sym (Kn→ΩKn+10ₖ _)  ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ x) ∙∙ Kn→ΩKn+10ₖ _))
    ∙∙ ((λ k → subst (λ n → refl {x = 0ₖ n} ≡ refl {x = 0ₖ n})
                     (isSetℕ _ _
                       (cong (suc ∘ suc ∘ suc) (+-comm (suc n) m) ∙ (+'-comm (suc (suc m)) (suc (suc n))))
                       (cong (suc ∘ suc ∘ suc) (sym (+-suc n m))) k)
               (sym (Kn→ΩKn+10ₖ _)  ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ x) ∙∙ Kn→ΩKn+10ₖ _)))
    ∙∙ sym (natTranspLem {A = coHomK} _ _ x _ (λ _ x → sym (Kn→ΩKn+10ₖ _)
                  ∙∙ cong (Kn→ΩKn+1 _)
                      (Kn→ΩKn+1 _ x)
                  ∙∙ Kn→ΩKn+10ₖ _) (cong suc (sym (+-suc n m))))

  help : (p : _) (q : _) (x : _) →
    (λ i i₁ →
         -ₖ-gen (suc (suc n)) (suc (suc m)) p q
         (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
          (((λ i₂ → Kn→ΩKn+10ₖ (suc (suc (m + suc n))) (~ i₂)) ∙∙
            cong (Kn→ΩKn+1 (suc (suc (m + suc n))))
            (Kn→ΩKn+1 (suc (m + suc n))
             (trMap (-ₖ-helper (suc m) (suc (suc n)) (evenOrOdd (suc m)) p)
              (subst coHomK (cong suc (+-comm (suc n) m)) x)))
            ∙∙ Kn→ΩKn+10ₖ (suc (suc (m + suc n))))
           i i₁)))
      ≡
      (sym (Kn→ΩKn+10ₖ (suc (suc (n + suc m)))) ∙∙
       (λ i j →
          Kn→ΩKn+1 (suc (suc (n + suc m)))
          (Kn→ΩKn+1 (suc (n + suc m))
           (-ₖ-gen (suc (suc n)) (suc (suc m)) p q
            (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
             (subst coHomK (cong suc (sym (+-suc n m))) x)))
           i)
          j)
       ∙∙ Kn→ΩKn+10ₖ (suc (suc (n + suc m))))
  help (inl x) (inl y) z =
    (λ k i i₁ →
         -ₖ-gen-inl-right (suc (suc n)) (suc (suc m)) (inl x) y
         (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
          (((λ i₂ → Kn→ΩKn+10ₖ (suc (suc (m + suc n))) (~ i₂)) ∙∙
            cong (Kn→ΩKn+1 (suc (suc (m + suc n))))
            (Kn→ΩKn+1 (suc (m + suc n))
             (-ₖ-gen-inl-right (suc m) (suc (suc n)) (evenOrOdd (suc m)) x
              (subst coHomK (cong suc (+-comm (suc n) m)) z) k))
            ∙∙ Kn→ΩKn+10ₖ (suc (suc (m + suc n))))
           i i₁)) k)
    ∙∙ annoying z
    ∙∙ λ k → (sym (Kn→ΩKn+10ₖ (suc (suc (n + suc m)))) ∙∙
       (λ i j →
          Kn→ΩKn+1 (suc (suc (n + suc m)))
          (Kn→ΩKn+1 (suc (n + suc m))
           (-ₖ-gen-inl-right (suc (suc n)) (suc (suc m)) (inl x) y
            (-ₖ-gen-inl-right (suc m) (suc (suc n)) (evenOrOdd (suc m)) x
             (subst coHomK (cong suc (sym (+-suc n m))) z) (~ k)) (~ k))
           i)
          j)
       ∙∙ Kn→ΩKn+10ₖ (suc (suc (n + suc m))))
  help (inl x) (inr y) z =
       ((λ k i i₁ →
         -ₖ-gen-inl-left (suc (suc n)) (suc (suc m)) x (inr y)
         (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
          (((λ i₂ → Kn→ΩKn+10ₖ (suc (suc (m + suc n))) (~ i₂)) ∙∙
            cong (Kn→ΩKn+1 (suc (suc (m + suc n))))
            (Kn→ΩKn+1 (suc (m + suc n))
             (-ₖ-gen-inl-right (suc m) (suc (suc n)) (evenOrOdd (suc m)) x
              (subst coHomK (cong suc (+-comm (suc n) m)) z) k))
            ∙∙ Kn→ΩKn+10ₖ (suc (suc (m + suc n))))
           i i₁)) k))
    ∙∙ annoying z
    ∙∙ λ k → (sym (Kn→ΩKn+10ₖ (suc (suc (n + suc m)))) ∙∙
       (λ i j →
          Kn→ΩKn+1 (suc (suc (n + suc m)))
          (Kn→ΩKn+1 (suc (n + suc m))
           (-ₖ-gen-inl-left (suc (suc n)) (suc (suc m)) x (inr y)
            (-ₖ-gen-inl-right (suc m) (suc (suc n)) (evenOrOdd (suc m)) x
             (subst coHomK (cong suc (sym (+-suc n m))) z) (~ k)) (~ k))
           i)
          j)
       ∙∙ Kn→ΩKn+10ₖ (suc (suc (n + suc m))))
  help (inr x) (inl y) z =
       (((λ k i i₁ →
         -ₖ-gen-inl-right (suc (suc n)) (suc (suc m)) (inr x) y
         (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
          (((λ i₂ → Kn→ΩKn+10ₖ (suc (suc (m + suc n))) (~ i₂)) ∙∙
            cong (Kn→ΩKn+1 (suc (suc (m + suc n))))
                 ((Kn→ΩKn+1 (suc (m + suc n))
             (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd-Prop (suc m) (evenOrOdd (suc m)) (inr y) k) (inr x)
              (subst coHomK (cong suc (+-comm (suc n) m)) z))))
            ∙∙ Kn→ΩKn+10ₖ (suc (suc (m + suc n))))
           i i₁)) k)))
    ∙∙ ((λ k i i₁ →
         (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
          (((λ i₂ → Kn→ΩKn+10ₖ (suc (suc (m + suc n))) (~ i₂)) ∙∙
            cong (Kn→ΩKn+1 (suc (suc (m + suc n))))
                 (Kn→ΩKn+1-ₖ' (suc m) (suc (suc n)) y x
                   (subst coHomK (cong suc (+-comm (suc n) m)) z) k)
            ∙∙ Kn→ΩKn+10ₖ (suc (suc (m + suc n))))
           i i₁))))
    ∙∙ cong sym (annoying z)
    ∙∙ (λ k → sym (Kn→ΩKn+10ₖ _)
            ∙∙ cong (Kn→ΩKn+1 _)
                 (Kn→ΩKn+1-ₖ' (suc m) (suc (suc n)) y x
                   (subst coHomK (cong suc (sym (+-suc n m))) z) (~ k))
            ∙∙ Kn→ΩKn+10ₖ _)
    ∙∙ λ k → (sym (Kn→ΩKn+10ₖ (suc (suc (n + suc m)))) ∙∙
       (λ i j →
          Kn→ΩKn+1 (suc (suc (n + suc m)))
          (Kn→ΩKn+1 (suc (n + suc m))
           (-ₖ-gen-inl-right (suc (suc n)) (suc (suc m)) (inr x) y
            (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd-Prop (suc m) (evenOrOdd (suc m)) (inr y) (~ k)) (inr x)
             (subst coHomK (cong suc (sym (+-suc n m))) z)) (~ k)) i) j)
       ∙∙ Kn→ΩKn+10ₖ (suc (suc (n + suc m))))
  help (inr x) (inr y) z =
       (λ k → cong-cong-ₖ-gen-inr (suc (suc n)) (suc (suc m)) x y
         (λ i j → subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
          (((λ i₂ j → ∣ rCancel (merid north) (~ i₂) j ∣) ∙∙
            cong (Kn→ΩKn+1 (suc (suc (m + suc n))))
            (Kn→ΩKn+1 (suc (m + suc n))
             (trMap (-ₖ-helper (suc m) (suc (suc n)) (evenOrOdd-Prop (suc m) (evenOrOdd (suc m)) (inl y) k) (inr x))
              (subst coHomK (cong suc (+-comm (suc n) m)) z)))
            ∙∙ (λ i₂ j → ∣ rCancel (merid north) i₂ j ∣))
           i j)) k)
    ∙∙ ((λ k i j → subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
          (((λ i₂ j → ∣ rCancel (merid north) (~ i₂) j ∣) ∙∙
            cong (Kn→ΩKn+1 (suc (suc (m + suc n))))
            (Kn→ΩKn+1 (suc (m + suc n))
             (-ₖ-gen-inl-left (suc m) (suc (suc n)) y (inr x)
              (subst coHomK (cong suc (+-comm (suc n) m)) z) k))
            ∙∙ (λ i₂ j → ∣ rCancel (merid north) i₂ j ∣))
           (~ i) j)))
    ∙∙ cong sym (annoying z)
    ∙∙ (λ k → (sym (Kn→ΩKn+10ₖ (suc (suc (n + suc m)))) ∙∙
       (λ i j →
          Kn→ΩKn+1 (suc (suc (n + suc m)))
           (Kn→ΩKn+1 _
            (-ₖ-gen-inl-left (suc m) (suc (suc n)) y (inr x)
             (subst coHomK (cong suc (sym (+-suc n m))) z) (~ k))
           (~ i))
          j)
       ∙∙ Kn→ΩKn+10ₖ (suc (suc (n + suc m)))))
    ∙∙ λ k → (sym (Kn→ΩKn+10ₖ (suc (suc (n + suc m)))) ∙∙
       (λ i j →
          Kn→ΩKn+1 (suc (suc (n + suc m)))
          (Kn→ΩKn+1-ₖ' (suc (suc n)) (suc (suc m)) x y (
            (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd-Prop (suc m) (evenOrOdd (suc m)) (inl y) (~ k)) (inr x)
             (subst coHomK (cong suc (sym (+-suc n m))) z))) (~ k)
           i)
          j)
       ∙∙ Kn→ΩKn+10ₖ (suc (suc (n + suc m))))


cuteLem₃ : (n m : ℕ) (p : _) (q : _) (a : _) (b : _) → flipSquare (sym (Kn→ΩKn+10ₖ _)
     ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)
                                           (subst coHomK (cong suc (+-comm (suc m) n))
                                           (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ₕ ∣ a ∣))))
     ∙∙ Kn→ΩKn+10ₖ _)
     ≡ (sym (Kn→ΩKn+10ₖ _)
          ∙∙ (λ i j → Kn→ΩKn+1 _
                        ((Kn→ΩKn+1 _ (-ₖ-gen (suc (suc n)) (suc (suc m)) p q
                          (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                            (subst coHomK (cong suc (sym (+-suc n m)))
                              (-ₖ-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m))
                                (subst coHomK (+'-comm (suc m) (suc n)) (∣ b ∣ₕ ⌣ₖ ∣ a ∣ₕ))))))) i) j)
          ∙∙ Kn→ΩKn+10ₖ _)
cuteLem₃ n m p q a b =
    sym (inst _ (sym (Kn→ΩKn+10ₖ _)
     ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)
                                           (subst coHomK (cong suc (+-comm (suc m) n))
                                           (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ₕ ∣ a ∣))))
     ∙∙ Kn→ΩKn+10ₖ _))
   ∙ cong (sym (Kn→ΩKn+10ₖ _) ∙∙_∙∙ Kn→ΩKn+10ₖ _)
       (cong (cong (Kn→ΩKn+1 _))
         (mainHelp (subst coHomK (cong suc (+-comm (suc m) n)) (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ ∣ a ∣))
           p q
         ∙ cong (Kn→ΩKn+1 _) (sym (help (∣ b ∣ ⌣ₖ ∣ a ∣)))))
  where
  mainHelp : (x : _) (p : _) (q : _) → sym (Kn→ΩKn+1 (suc (n + suc m)) (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd (suc n)) q x))
                     ≡ Kn→ΩKn+1 (suc (n + suc m)) ((-ₖ-gen (suc (suc n)) (suc (suc m)) p q
                        (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                         (-ₖ-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m)) x))))
  mainHelp z (inl x) (inl y) =
       cong (λ x → sym (Kn→ΩKn+1 (suc (n + suc m)) x)) (-ₖ-gen-inl-right (suc n) (suc (suc m)) (evenOrOdd (suc n)) y z)
    ∙∙ sym (Kn→ΩKn+1-ₖ' (suc n) (suc m) x y z)
    ∙∙ λ k → Kn→ΩKn+1 (suc (n + suc m))
      (-ₖ-gen-inl-right (suc (suc n)) (suc (suc m)) (inl x) y
       (-ₖ-gen-inl-right (suc m) (suc (suc n)) (evenOrOdd (suc m)) x
        (-ₖ-gen (suc n) (suc m) (evenOrOdd-Prop (suc n) (inr x) (evenOrOdd (suc n)) k) (evenOrOdd-Prop (suc m) (inr y) (evenOrOdd (suc m)) k)
         z) (~ k)) (~ k))
  mainHelp z (inl x) (inr y) =
       (λ k → sym (Kn→ΩKn+1 (suc (n + suc m))
                    (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd-Prop (suc n) (evenOrOdd (suc n)) (inr x) k) (inr y) z)))
    ∙∙ cong sym (Kn→ΩKn+1-ₖ' (suc n) (suc (suc m)) x y z)
    ∙∙ cong (Kn→ΩKn+1 (suc (n + suc m))) (sym (-ₖ-gen-inl-right (suc n) (suc m) (inr x) y z))
     ∙ λ k → Kn→ΩKn+1 (suc (n + suc m))
      (-ₖ-gen-inl-left (suc (suc n)) (suc (suc m)) x (inr y)
       (-ₖ-gen-inl-right (suc m) (suc (suc n)) (evenOrOdd (suc m)) x
        (-ₖ-gen (suc n) (suc m) (evenOrOdd-Prop (suc n) (inr x) (evenOrOdd (suc n)) k) (evenOrOdd-Prop (suc m) (inl y) (evenOrOdd (suc m)) k)
         z) (~ k)) (~ k))
  mainHelp z (inr x) (inl y) =
       cong (λ x → sym (Kn→ΩKn+1 (suc (n + suc m)) x)) (-ₖ-gen-inl-right (suc n) (suc (suc m)) (evenOrOdd (suc n)) y z)
    ∙∙ (λ k → Kn→ΩKn+1-ₖ' (suc m) (suc (suc n)) y x
                (-ₖ-gen-inl-left (suc n) (suc m) x (inr y) z (~ k)) (~ k))
    ∙∙ λ k → Kn→ΩKn+1 (suc (n + suc m))
               (-ₖ-gen-inl-right (suc (suc n)) (suc (suc m)) (inr x) y
                (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd-Prop (suc m) (inr y) (evenOrOdd (suc m)) k) (inr x)
                 (-ₖ-gen (suc n) (suc m) (evenOrOdd-Prop (suc n) (inl x) (evenOrOdd (suc n)) k)
                   (evenOrOdd-Prop (suc m) (inr y) (evenOrOdd (suc m)) k)
                  z)) (~ k))
  mainHelp z (inr x) (inr y) =
       ((λ k → sym (Kn→ΩKn+1 (suc (n + suc m))
                    (-ₖ-gen (suc n) (suc (suc m)) (evenOrOdd-Prop (suc n) (evenOrOdd (suc n)) (inl x) k) (inr y) z))))
    ∙∙ cong sym (cong (Kn→ΩKn+1 (suc (n + suc m))) (-ₖ-gen-inl-left (suc n) (suc (suc m)) x (inr y) z))
    ∙∙ (λ k → sym (Kn→ΩKn+1 (suc (n + suc m))
                   (-ₖ-gen-inl-left (suc m) (suc (suc n)) y (inr x)
                     (-ₖ-gen-inl-right (suc n) (suc m) (inl x) y z (~ k)) (~ k))))
     ∙ λ k → Kn→ΩKn+1-ₖ' (suc (suc n)) (suc (suc m)) x y
                (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd-Prop (suc m) (inl y) (evenOrOdd (suc m)) k) (inr x)
                 (-ₖ-gen (suc n) (suc m) (evenOrOdd-Prop (suc n) (inl x) (evenOrOdd (suc n)) k)
                                         (evenOrOdd-Prop (suc m) (inl y) (evenOrOdd (suc m)) k)
                  z)) (~ k)

  help : (x : _) →
     (-ₖ-gen (suc (suc n)) (suc (suc m)) p q
                          (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                            (subst coHomK (cong suc (sym (+-suc n m)))
                              (-ₖ-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m))
                                (subst coHomK (+'-comm (suc m) (suc n)) x)))))
   ≡ -ₖ-gen (suc (suc n)) (suc (suc m)) p q
      (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
        (-ₖ-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m))
          (subst coHomK (cong suc (+-comm (suc m) n)) x)))
  help x =
       (λ k → -ₖ-gen (suc (suc n)) (suc (suc m)) p q
                (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                  (transp (λ i → coHomK ((cong suc (sym (+-suc n m))) (i ∨ k))) k
                   (-ₖ-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m))
                     (transp (λ i → coHomK ((cong suc (sym (+-suc n m))) (i ∧ k))) (~ k)
                       (subst coHomK (+'-comm (suc m) (suc n)) x))))))
     ∙ cong (-ₖ-gen (suc (suc n)) (suc (suc m)) p q
               ∘ -ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
               ∘ -ₖ-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m)))
            (sym (substComposite coHomK (+'-comm (suc m) (suc n)) ((cong suc (sym (+-suc n m)))) x)
            ∙ λ k → subst coHomK (isSetℕ _ _ (+'-comm (suc m) (suc n) ∙ cong suc (sym (+-suc n m)))
                      ((cong suc (+-comm (suc m) n))) k) x)

main : (k n m : ℕ) (term : n + m ≡ k) (p : _) (q : _) (a : _) (b : _) →
      (_⌣ₖ_  {n = suc n} {m = (suc m)} ∣ a ∣ₕ ∣ b ∣ₕ)
    ≡ (-ₖ-gen (suc n) (suc m) p q)
       (subst coHomK (+'-comm (suc m) (suc n))
        (_⌣ₖ_  {n = suc m} {m = suc n} ∣ b ∣ₕ ∣ a ∣ₕ))
main k zero zero term p q a b = mainₗ zero p q a b
main k zero (suc m) term (inr tt) q a b = help q ∙ sym (cong (-ₖ-gen 1 (suc (suc m)) (inr tt) q ∘
                                                (subst coHomK (+'-comm (suc (suc m)) 1))) (mainₗ (suc m) q (inr tt) b a))
  where
  help : (q : _) → ∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ ≡
            -ₖ-gen 1 (suc (suc m)) (inr tt) q
            (subst coHomK (+'-comm (suc (suc m)) 1)
             (-ₖ-gen (suc (suc m)) 1 q (inr tt)
              (subst coHomK (+'-comm 1 (suc (suc m))) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ))))
  help (inl x) =
      (sym (transportRefl _)
     ∙ (λ i → subst coHomK (isSetℕ _ _ refl (+'-comm 1 (suc (suc m)) ∙ +'-comm (suc (suc m)) 1) i) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ)))
    ∙∙ substComposite coHomK
         (+'-comm 1 (suc (suc m)))
          (+'-comm (suc (suc m)) 1)
           ((∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ))
    ∙∙ λ i → -ₖ-gen-inl-right (suc zero) (suc (suc m)) (inr tt) x
            ((subst coHomK (+'-comm (suc (suc m)) 1)
             (-ₖ-gen-inl-left (suc (suc m)) 1 x (inr tt)
              (subst coHomK (+'-comm 1 (suc (suc m))) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ)) (~ i)))) (~ i)
  help (inr x) =
       (sym (transportRefl _)
    ∙∙ (λ k → subst coHomK (isSetℕ _ _ refl (+'-comm 1 (suc (suc m)) ∙ +'-comm (suc (suc m)) 1) k) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ))
    ∙∙ sym (-ₖ^2 (subst coHomK (+'-comm 1 (suc (suc m)) ∙ +'-comm (suc (suc m)) 1) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ))))
    ∙∙ (λ i → -ₖ-gen-inr≡-ₖ 1 (suc (suc m)) tt x
                (-ₖ-gen-inr≡-ₖ (suc (suc m)) 1 x tt
                  (substComposite coHomK (+'-comm 1 (suc (suc m))) (+'-comm (suc (suc m)) 1) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ) i)
                  (~ i)) (~ i))
    ∙∙ λ i → (-ₖ-gen 1 (suc (suc m)) (inr tt) (inr x)
                  (transp (λ j → coHomK ((+'-comm (suc (suc m)) 1) (j ∨ ~ i))) (~ i)
                    (-ₖ-gen (suc (suc m)) 1 (inr x) (inr tt)
                      (transp (λ j → coHomK ((+'-comm (suc (suc m)) 1) (j ∧ ~ i))) i
                              ((subst coHomK (+'-comm 1 (suc (suc m))) (∣ a ∣ₕ ⌣ₖ ∣ b ∣ₕ)))))))
main k (suc n) zero term p q a b = mainₗ (suc n) p q a b
main zero (suc n) (suc m) term p q a b = ⊥-rec (snotz (sym (+-suc n m) ∙ cong predℕ term))
main (suc zero) (suc n) (suc m) term p q a b = ⊥-rec (snotz (sym (+-suc n m) ∙ cong predℕ term))
main (suc (suc k)) (suc n) (suc m) term p q north north = refl
main (suc (suc k)) (suc n) (suc m) term p q north south = refl
main (suc (suc k)) (suc n) (suc m) term p q north (merid a i) r =
  trMap (-ₖ-helper (suc (suc n)) (suc (suc m)) p q) (
                (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))
                  ((sym (Kn→ΩKn+10ₖ _)
                  ∙ cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (sym (testP2 n m))
                                     ∙ sym (main (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
                                 (evenOrOdd (suc m)) p a north))) r i))
main (suc (suc k)) (suc n) (suc m) term p q south north = refl
main (suc (suc k)) (suc n) (suc m) term p q south south = refl
main (suc (suc k)) (suc n) (suc m) term p q south (merid a i) r =
  trMap (-ₖ-helper (suc (suc n)) (suc (suc m)) p q) (
                (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))
                  ((sym (Kn→ΩKn+10ₖ _)
                  ∙ cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (sym (testP2 n m))
                                     ∙ sym (main (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
                                 (evenOrOdd (suc m)) p a south))) r i))
main (suc (suc k)) (suc n) (suc m) term p q (merid a i) north r =
    (cong (Kn→ΩKn+1 (suc (suc (n + suc m))))
      (main (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a north
       ∙ cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q))  (testP2 m n))
   ∙' Kn→ΩKn+10ₖ _) r i
main (suc (suc k)) (suc n) (suc m) term p q (merid a i) south r =
    (cong (Kn→ΩKn+1 (suc (suc (n + suc m))))
      (main (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a south
       ∙ cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q))  (testP2 m n))
   ∙' Kn→ΩKn+10ₖ _) r i
main (suc (suc k)) (suc n) (suc m) term p q (merid a i) (merid b j) r =
  hcomp (λ l → λ {(i = i0) → trMap (-ₖ-helper (suc (suc n)) (suc (suc m)) p q) (
                               (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))
                                 ((compPath-filler (sym (Kn→ΩKn+10ₖ _))
                                  (cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (sym (testP2 n m))
                                                    ∙ sym (main (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
                                                (evenOrOdd (suc m)) p b north))) l r j)))
                 ; (i = i1) → trMap (-ₖ-helper (suc (suc n)) (suc (suc m)) p q) (
                               (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))
                                 ((compPath-filler (sym (Kn→ΩKn+10ₖ _))
                                  (cong (Kn→ΩKn+1 _) (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (sym (testP2 n m))
                                                    ∙ sym (main (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
                                                (evenOrOdd (suc m)) p b south))) l r j)))
                 ; (r = i0) → help₁ l i j
                 ; (r = i1) → -ₖ-gen (suc (suc n)) (suc (suc m)) p q
                                 (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
                                  (help₃ l i j))})
        (hcomp (λ l → λ {(i = i0) → -ₖ-gen (suc (suc n)) (suc (suc m)) p q
                                      (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
                                        (Kn→ΩKn+10ₖ _ (~ r ∨ ~ l) j))
                       ; (i = i1) → -ₖ-gen (suc (suc n)) (suc (suc m)) p q
                                      (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
                                        (Kn→ΩKn+10ₖ _ (~ r ∨ ~ l) j))
                       ; (j = i0) → Kn→ΩKn+10ₖ _ r i
                       ; (j = i1) → Kn→ΩKn+10ₖ _ r i
                       ; (r = i0) → help₂ (~ l) j i
                       ; (r = i1) → -ₖ-gen (suc (suc n)) (suc (suc m)) p q
                                      (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
                                        (doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _)) ((λ i j → Kn→ΩKn+1 _ ((sym (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (testP2 n m))
                                                                     ∙∙ (λ i → -ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                                                                                   (subst coHomK (+'-comm (suc (suc n)) (suc m))
                                                                                     (_⌣ₖ_ {n = suc (suc n)} {m = suc m} ∣ merid a i ∣ₕ ∣ b ∣ₕ)))
                                                                     ∙∙ cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (testP2 n m)) i) j))
                                                               (Kn→ΩKn+10ₖ _) (~ l) i j))})
               (hcomp (λ l → λ {(i = i0) → ∣ north ∣
                               ; (i = i1) → ∣ north ∣
                               ; (j = i0) → Kn→ΩKn+10ₖ _ r i
                               ; (j = i1) → Kn→ΩKn+10ₖ _ r i
                               ; (r = i0) → help₂ i1 j i
                               ; (r = i1) → help₄ (~ l) i j})
                               (hcomp (λ l → λ {(i = i0) → ∣ north ∣
                               ; (i = i1) → ∣ north ∣
                               ; (j = i0) → Kn→ΩKn+10ₖ _ (r ∨ ~ l) i
                               ; (j = i1) → Kn→ΩKn+10ₖ _ (r ∨ ~ l) i
                               ; (r = i0) → doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _)) (λ i j → help₂ i1 i j) (Kn→ΩKn+10ₖ _) (~ l) j i
                               ; (r = i1) → (sym (Kn→ΩKn+10ₖ _)
                                           ∙∙ (λ i j → Kn→ΩKn+1 _
                                                         ((Kn→ΩKn+1 _ (-ₖ-gen (suc (suc n)) (suc (suc m)) p q
                                                           (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                                                             (subst coHomK (cong suc (sym (+-suc n m)))
                                                               (main k n m
                                                                 (+-comm n m ∙∙ cong predℕ (+-comm (suc m) n) ∙∙ cong (predℕ ∘ predℕ) term)
                                                                 (evenOrOdd (suc n)) (evenOrOdd (suc m)) a b (~ l)))))) i) j)
                                           ∙∙ Kn→ΩKn+10ₖ _) i j})
                        (final r i j))))
  where
  final : flipSquare (sym (Kn→ΩKn+10ₖ _)
       ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)
                                             (subst coHomK (cong suc (+-comm (suc m) n))
                                             (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ₕ ∣ a ∣))))
       ∙∙ Kn→ΩKn+10ₖ _)
       ≡ (sym (Kn→ΩKn+10ₖ _)
            ∙∙ (λ i j → Kn→ΩKn+1 _
                          ((Kn→ΩKn+1 _ (-ₖ-gen (suc (suc n)) (suc (suc m)) p q
                            (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                              (subst coHomK (cong suc (sym (+-suc n m)))
                                (-ₖ-gen (suc n) (suc m) (evenOrOdd (suc n)) (evenOrOdd (suc m))
                                  (subst coHomK (+'-comm (suc m) (suc n)) (∣ b ∣ₕ ⌣ₖ ∣ a ∣ₕ))))))) i) j)
            ∙∙ Kn→ΩKn+10ₖ _)
  final = cuteLem₃ n m p q a b

  help₄ : cong (cong (-ₖ-gen (suc (suc n)) (suc (suc m)) p q
                      ∘ (subst coHomK (+'-comm (suc (suc m)) (suc (suc n))))))
                      (sym (Kn→ΩKn+10ₖ _) ∙∙ (λ i j → Kn→ΩKn+1 _ ((sym (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (testP2 n m))
                                                                     ∙∙ (λ i → -ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                                                                                   (subst coHomK (+'-comm (suc (suc n)) (suc m))
                                                                                     (_⌣ₖ_ {n = suc (suc n)} {m = suc m} ∣ merid a i ∣ₕ ∣ b ∣ₕ)))
                                                                     ∙∙ cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (testP2 n m)) i) j)
                                           ∙∙ Kn→ΩKn+10ₖ _)
             ≡ (sym (Kn→ΩKn+10ₖ _)
            ∙∙ (λ i j → Kn→ΩKn+1 _
                          ((Kn→ΩKn+1 _ (-ₖ-gen (suc (suc n)) (suc (suc m)) p q
                            (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                              (subst coHomK (cong suc (sym (+-suc n m))) (_⌣ₖ_ {n = suc n} {m = suc m} ∣ a ∣ₕ ∣ b ∣ₕ))))) i) j)
            ∙∙ Kn→ΩKn+10ₖ _)
  help₄ = cuteLem₂ n m p q a b

  help₃ :
    Cube (λ i j → Kn→ΩKn+1 _ ((sym (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (testP2 n m))
                             ∙∙ (λ i → -ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                                           (subst coHomK (+'-comm (suc (suc n)) (suc m))
                                             (_⌣ₖ_ {n = suc (suc n)} {m = suc m} ∣ merid a i ∣ₕ ∣ b ∣ₕ)))
                             ∙∙ cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (testP2 n m)) i) j)
         (λ i j → (_⌣ₖ_ {n = suc (suc m)} {m = suc (suc n)} ∣ merid b j ∣ₕ ∣ merid a i ∣ₕ))
         (λ l j → Kn→ΩKn+1 _ ((cong ((-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p)) (sym (testP2 n m))
                              ∙ sym (main (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
                                                (evenOrOdd (suc m)) p b north)) l) j)
         (λ l j → Kn→ΩKn+1 _ ((cong ((-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p)) (sym (testP2 n m))
                              ∙ sym (main (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
                                                (evenOrOdd (suc m)) p b south)) l) j)
         refl
         refl
  help₃ l i =
    Kn→ΩKn+1 _
      (hcomp (λ r → λ { (i = i0) → compPath-filler' (cong ((-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p)) (sym (testP2 n m)))
                                                            (sym (main (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
                                                                 (evenOrOdd (suc m)) p b north)) r l
                       ; (i = i1) → compPath-filler' (cong ((-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p)) (sym (testP2 n m)))
                                                            (sym (main (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term)
                                                                 (evenOrOdd (suc m)) p b south)) r l
                       ; (l = i0) → doubleCompPath-filler (sym (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (testP2 n m)))
                                                           (λ i → -ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p
                                                                    (subst coHomK (+'-comm (suc (suc n)) (suc m))
                                                                      (_⌣ₖ_ {n = suc (suc n)} {m = suc m} ∣ merid a i ∣ₕ ∣ b ∣ₕ)))
                                                           (cong (-ₖ-gen (suc m) (suc (suc n)) (evenOrOdd (suc m)) p) (testP2 n m)) r i
                       ; (l = i1) → _⌣ₖ_ {n = suc m} {m = suc (suc n)} ∣ b ∣ₕ ∣ merid a i ∣ₕ})
             (main (suc k) m (suc n) (+-suc m n ∙ +-comm (suc m) n ∙ cong predℕ term) (evenOrOdd (suc m)) p b (merid a i) (~ l)))

  help₂ : cong (Kn→ΩKn+1 _) (((sym (cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)) (testP2 m n))
                               ∙∙ (λ j → trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)
                              (subst coHomK (+'-comm (suc (suc m)) (suc n)) (_⌣ₖ_ {n = suc (suc m)} {m = (suc n)} ∣ merid b j ∣ₕ ∣ a ∣)))
                  ∙∙ cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)) (testP2 m n))))
         ≡ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q) -- (suc n) * m
                                             (subst coHomK (cong suc (+-comm (suc m) n))
                                             (_⌣ₖ_ {n = suc m} {m = (suc n)} ∣ b ∣ₕ ∣ a ∣))))
  help₂ = cuteLem₁ n m q p a b

  help₁ : Cube (λ i j → Kn→ΩKn+1 _ ((sym (cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)) (testP2 m n))
            ∙∙ (λ j → trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)
                        (subst coHomK (+'-comm (suc (suc m)) (suc n)) (_⌣ₖ_ {n = suc (suc m)} {m = (suc n)} ∣ merid b j ∣ₕ ∣ a ∣)))
            ∙∙ cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)) (testP2 m n)) j) i)
               (λ i j → Kn→ΩKn+1 _ (_⌣ₖ_ {n = (suc n)} {m = suc (suc m)} ∣ a ∣ ∣ merid b j ∣ₕ) i)
               refl refl
               (λ l → Kn→ΩKn+1 (suc (suc (n + suc m)))
                          ((main (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a north
                           ∙ cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q))  (testP2 m n)) (~ l)))
               (λ l → Kn→ΩKn+1 (suc (suc (n + suc m)))
                          ((main (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a south
                           ∙ cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q))  (testP2 m n)) (~ l)))
  help₁ l i j =
    hcomp (λ r → λ {(i = i0) → ∣ north ∣
                   ; (i = i1) → ∣ north ∣
                   ; (j = i0) →
                     Kn→ΩKn+1 (suc (suc (n + suc m)))
                          (compPath-filler (main (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a north)
                            (cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q))  (testP2 m n)) r (~ l)) i
                   ; (j = i1) →
                        Kn→ΩKn+1 (suc (suc (n + suc m)))
                          (compPath-filler (main (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a south)
                            (cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q))  (testP2 m n)) r (~ l)) i
                   ; (l = i0) →
                     Kn→ΩKn+1 _
                       (doubleCompPath-filler (sym (cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)) (testP2 m n)))
                                              (λ j → trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)
                                                       (subst coHomK (+'-comm (suc (suc m)) (suc n)) (_⌣ₖ_ {n = suc (suc m)} {m = (suc n)} ∣ merid b j ∣ₕ ∣ a ∣)))
                                              (cong (trMap (-ₖ-helper (suc n) (suc (suc m)) (evenOrOdd (suc n)) q)) (testP2 m n)) r j) i
                   ; (l = i1) → Kn→ΩKn+1 _ (_⌣ₖ_ {n = (suc n)} {m = suc (suc m)} ∣ a ∣ ∣ merid b j ∣ₕ) i})
          (hcomp (λ r → λ {(i = i0) → ∣ north ∣
                          ; (i = i1) → ∣ north ∣
                          ; (j = i0) → Kn→ΩKn+1 (suc (suc (n + suc m)))
                                         (main (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a north (~ l ∨ ~ r)) i
                          ; (j = i1) → Kn→ΩKn+1 (suc (suc (n + suc m)))
                                         (main (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a south (~ l ∨ ~ r)) i
                          ; (l = i0) → Kn→ΩKn+1 (suc (suc (n + suc m)))
                                         (main (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a (merid b j) i1) i
                          ; (l = i1) → Kn→ΩKn+1 _ (main (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a (merid b j) (~ r)) i})
                 (Kn→ΩKn+1 (suc (suc (n + suc m)))
                                         (main (suc k) n (suc m) (cong predℕ term) (evenOrOdd (suc n)) q a (merid b j) i1) i))
