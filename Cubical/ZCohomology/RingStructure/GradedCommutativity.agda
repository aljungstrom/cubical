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

-ₖ^_·_ : {k : ℕ} (n m : ℕ) → coHomK k → coHomK k
-ₖ^_·_ {k = zero} n m = -ₖ-helper {k = zero} n m (evenOrOdd n) (evenOrOdd m)
-ₖ^_·_ {k = suc k} n m = trMap (-ₖ-helper n m (evenOrOdd n) (evenOrOdd m))

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

cup∙' : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc n +' suc m)
cup∙' n m = trRec (isOfHLevel↑∙ (suc n) m) {!!}
  where
  cup'' :  coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (n + m)))
  cup'' = trRec (subst (isOfHLevel (3 + m)) (λ i → (S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (+-comm m n i)))))
                (isOfHLevel↑∙' (suc m) n))
                λ b → (λ a → ∪-uncool n m a b) , help n b
    where
    help : (n : ℕ) (b : _) → ∪-uncool n m (snd (S₊∙ (suc n))) b ≡ 0ₖ _
    help zero b = refl
    help (suc n) b = refl

  final : S₊ (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m)))
  fst (final x) y = fst (cup'' y) x
  snd (final x) = {!!}

cup∙ : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m)))
cup∙ n m = trRec (isOfHLevel↑∙ (suc n) m)
                 (sndP n m)
     where

     t₁ : (m : ℕ) → S¹ → coHomK (suc m) → coHomK (suc (suc m))
     F : (m : ℕ) → coHomK (suc m) → 0ₖ (2 + m) ≡ 0ₖ (2 + m)
     t₁ m base y = 0ₖ _
     t₁ m (loop i) y = F m y i
     t : (n : ℕ) (m : ℕ) → S₊ (suc n) → coHomK (suc m) → coHomK (suc (suc (n + m)))
     t zero = t₁
     t (suc n) m north y = 0ₖ _
     t (suc n) m south y = 0ₖ _
     t (suc n) m (merid a i) y =
       t₁ _ (loop i) (t n m a y)

     F zero = trRec (isOfHLevelTrunc 4 _ _)
                 λ {base → refl
                 ; (loop j) i → cong (cong ∣_∣ₕ) (sym (rCancel (merid base))
                             ∙∙ (λ i → merid (loop i) ∙ sym (merid base))
                             ∙∙ rCancel (merid base))  j i}
     F (suc m) = trRec (isOfHLevelTrunc (5 + m) _ _)
                 λ {north → refl
                 ; south → refl
                 ; (merid a j) i → (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (λ i → t₁ m (loop i) ∣ a ∣) ∙∙ Kn→ΩKn+10ₖ _) j i}

     sndP : (n m : ℕ) → S₊ (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m)))
     fst (sndP n m x) = t n m x
     snd (sndP zero m base) = refl
     snd (sndP zero zero (loop i)) = refl
     snd (sndP zero (suc m) (loop i)) = refl
     snd (sndP (suc n) m north) = refl
     snd (sndP (suc n) m south) = refl
     snd (sndP (suc n) m (merid a i)) k = t₁ _ (loop i) (snd (sndP n m a) k)

cup∙∙ : (n m : ℕ) → coHomK-ptd (suc n) →∙ (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m))) ∙)
fst (cup∙∙ n m) = cup∙ n m
snd (cup∙∙ zero m) = refl
snd (cup∙∙ (suc n) m) = refl

_⌣₂_ : {n m : ℕ} → coHomK (suc n) → coHomK (suc m) → coHomK (suc n +' suc m)
_⌣₂_ {n = n} {m = m} a b = fst (cup∙ n m a) b

rUnit-⌣₂ : (n m : ℕ) → (x : coHomK (suc n)) → x ⌣₂ (0ₖ (suc m)) ≡ 0ₖ _
rUnit-⌣₂  n m x = snd (cup∙ n m x)

lUnit-⌣₂ : (n m : ℕ) → (x : coHomK (suc m)) → (0ₖ (suc n)) ⌣₂ x ≡ 0ₖ _
lUnit-⌣₂ n m = funExt⁻ (cong fst (snd (cup∙∙ n m)))


⌣≡⌣₂ : (n m : ℕ) (a : coHomK (suc n)) → ⌣ₖ∙ (suc n) (suc m) a ≡ cup∙ n m a
⌣≡⌣₂ n m =
  trElim {!!} (help n m)
  where
  ⌣' : (n m : ℕ) → coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc n +' suc m)
  ⌣' n m b = (λ a → _⌣ₖ_ {n = suc n} {m = suc m} ∣ a ∣ₕ b) , 0ₖ-⌣ₖ (suc n) (suc m) b

  cup' : (n m : ℕ) → coHomK (suc m) → S₊∙ (suc n) →∙ coHomK-ptd (suc n +' suc m)
  cup' n m b = (λ a → fst (cup∙ n m ∣ a ∣) b) , lUnit-⌣₂ n m b

  mainHelp : (n m : ℕ) (b : coHomK (suc m)) → ⌣' n m b ≡ cup' n m b 
  mainHelp n m =
    trElim {!!}
      λ b → →∙Homogeneous≡ (isHomogeneousKn _) (funExt λ a → help n m a b)
    where
    help : (n m : ℕ) (a : S₊ (suc n)) (b : S₊ (suc m)) → (⌣' n m ∣ b ∣ .fst a) ≡ cup' n m ∣ b ∣ .fst a
    help zero m base b = refl
    help zero zero (loop i) base k = ∣ rCancel (merid base) k i ∣
    help zero zero (loop i) (loop j) k =
      ∣ doubleCompPath-filler (sym (rCancel (merid base)))
                             (λ i → merid (loop i) ∙ sym (merid base))
                             (rCancel (merid base)) k j i ∣
    help zero (suc m) (loop i) north k =
      ∣ rCancel (merid north) k i ∣
    help zero (suc m) (loop i) south k =
      (cong (cong ∣_∣ₕ) (λ i → merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north)) ∙ cong (cong ∣_∣ₕ) (rCancel (merid north))) k i
    help zero (suc m) (loop i) (merid a j) k =
      hcomp (λ r → λ { (i = i0) → 0ₖ _
                      ; (i = i1) → 0ₖ _
                      ; (j = i0) → ∣ rCancel (merid north) (r ∧ k) i ∣
                      ; (j = i1) → compPath-filler (cong (cong ∣_∣ₕ) (λ i → merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north)))
                                                    (cong (cong ∣_∣ₕ) (rCancel (merid north))) r k i
                      ; (k = i0) → ⌣' zero (suc m) ∣ merid a j ∣ .fst (loop i)
                      ; (k = i1) → doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 _) λ i → help zero m (loop i) a r) (Kn→ΩKn+10ₖ _) r j i})
            ∣ (merid (compPath-filler (merid a) (sym (merid (ptSn (suc m)))) k j) ∙ (sym (merid north))) i ∣
    help (suc n) zero north b = refl
    help (suc n) zero south b = refl
    help (suc n) zero (merid a i) base k = {!cup' (suc n) zero ∣ base ∣ .fst (merid a i)!}
    help (suc n) zero (merid a i) (loop j) = {!!}
    help (suc n) (suc m) north b = refl
    help (suc n) (suc m) south b = refl
    help (suc n) (suc m) (merid a i) north = {!!}
      where
      test : cup' (suc n) (suc m) ∣ north ∣ .fst (merid a i) ≡ 0ₖ _
      test = {!)!}
    help (suc n) (suc m) (merid a i) south = {!!}
    help (suc n) (suc m) (merid a i) (merid a₁ i₁) = {!!}

  help : (n m : ℕ) (a : S₊ (suc n)) →
      ⌣ₖ∙ (suc n) (suc m) ∣ a ∣ₕ ≡ cup∙ n m ∣ a ∣ₕ
  help n m a = →∙Homogeneous≡ (isHomogeneousKn _) (funExt λ b → funExt⁻ (cong fst (mainHelp n m b)) a )
    

-- open import Cubical.Foundations.Path

-- gradedComm-helper' : (k n m : ℕ)
--   → n + m ≡ k
--   → (x : S₊ (suc n)) (y : S₊ (suc m))
--   → Path (coHomK ((suc n) +' (suc m)))
--           (∣ x ∣ ⌣ₖ ∣ y ∣)
--           (subst coHomK (+'-comm (suc m) (suc n)) ((-ₖ^ (suc n) · suc m) (∣ y ∣ ⌣ₖ ∣ x ∣)))
-- gradedComm-helper' k zero zero p x y = {!!}
-- gradedComm-helper' k zero (suc m) p x y = {!!}
-- gradedComm-helper' k (suc n) zero p x y = {!!}
-- gradedComm-helper' k (suc n) (suc m) p north north = refl
-- gradedComm-helper' k (suc n) (suc m) p north south = refl
-- gradedComm-helper' k (suc n) (suc m) p north (merid a i) j =
--     (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
--        ((-ₖ^ suc (suc n) · suc (suc m)) (⌣ₖ-0ₖ _ _ ∣ merid a i ∣ (~ j))))
-- gradedComm-helper' k (suc n) (suc m) p south north = refl
-- gradedComm-helper' k (suc n) (suc m) p south south = refl
-- gradedComm-helper' k (suc n) (suc m) p south (merid a i) j =
--   help (~ j) i
--   where
--   help : cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
--         ∘ ((-ₖ^ suc (suc n) · suc (suc m)))) (Kn→ΩKn+1 _ (_⌣ₖ_ {n = (suc m)} {m = suc (suc n)} ∣ a ∣ ∣ south ∣)) ≡ refl
--   help = cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
--         ∘ ((-ₖ^ suc (suc n) · suc (suc m))))) (cong (Kn→ΩKn+1 _) (λ i → _⌣ₖ_ {n = (suc m)} {m = suc (suc n)} ∣ a ∣ ∣ merid (ptSn (suc n)) (~ i) ∣)
--         ∙∙ cong (Kn→ΩKn+1 (suc (suc (m + suc n)))) (⌣ₖ-0ₖ (suc m) (2 + n) ∣ a ∣)
--         ∙∙ Kn→ΩKn+10ₖ _)
-- gradedComm-helper' k (suc n) (suc m) p (merid a i) north = ⌣ₖ-0ₖ (suc (suc n)) (2 + m) ∣ merid a i ∣
-- gradedComm-helper' k (suc n) (suc m) p (merid a i) south j = help j i
--   where
--   help : Kn→ΩKn+1 _ (_⌣ₖ_ {n = (suc n)} {m = 2 + m} ∣ a ∣ ∣ south ∣) ≡ refl
--   help = cong (Kn→ΩKn+1 _) (λ i → _⌣ₖ_ {n = (suc n)} {m = 2 + m} ∣ a ∣ ∣ merid (ptSn (suc m)) (~ i) ∣)
--       ∙∙ cong (Kn→ΩKn+1 _) (⌣ₖ-0ₖ (suc n) (2 + m) ∣ a ∣)
--       ∙∙ Kn→ΩKn+10ₖ _
-- gradedComm-helper' zero (suc n) (suc m) p (merid a i) (merid b j) l = pp i j l
--   where
--   pp : Cube (λ j l → gradedComm-helper' zero (suc n) (suc m) p north (merid b j) l)
--             (λ j l → gradedComm-helper' zero (suc n) (suc m) p south (merid b j) l)
--             (λ i l → gradedComm-helper' zero (suc n) (suc m) p (merid a i) north l)
--             (λ i l → gradedComm-helper' zero (suc n) (suc m) p (merid a i) south l)
--             (λ i j → _⌣ₖ_ {n = 2 + n} {m = 2 + m} ∣ merid a i ∣ ∣ merid b j ∣)
--             (λ i j → subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
--          ((-ₖ^ suc (suc n) · suc (suc m)) (∣ merid b j ∣ ⌣ₖ ∣ merid a i ∣)))
--   pp = ⊥-rec (snotz p)
-- gradedComm-helper' (suc zero) (suc n) (suc m) p (merid a i) (merid b j) l = pp i j l
--   where
--   pp : Cube (λ j l → gradedComm-helper' (suc zero) (suc n) (suc m) p north (merid b j) l)
--             (λ j l → gradedComm-helper' (suc zero) (suc n) (suc m) p south (merid b j) l)
--             (λ i l → gradedComm-helper' (suc zero) (suc n) (suc m) p (merid a i) north l)
--             (λ i l → gradedComm-helper' (suc zero) (suc n) (suc m) p (merid a i) south l)
--             (λ i j → _⌣ₖ_ {n = 2 + n} {m = 2 + m} ∣ merid a i ∣ ∣ merid b j ∣)
--             (λ i j → subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
--          ((-ₖ^ suc (suc n) · suc (suc m)) (∣ merid b j ∣ ⌣ₖ ∣ merid a i ∣)))
--   pp = ⊥-rec (snotz (sym (+-suc n m) ∙ (cong predℕ p)))
-- gradedComm-helper' (suc (suc k)) (suc n) (suc m) p (merid a i) (merid b j) l =
--   hcomp (λ r → λ { (i = i0) → (subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
--                                ((-ₖ^ suc (suc n) · suc (suc m)) {!m-s j i1!}))
--                   ; (i = i1) → {!!}
--                   ; (j = i0) → {!!} -- m-n i (l ∨ ~ r)
--                   ; (j = i1) → {!!} -- m-s (l ∨ ~ r) i
--                   ; (l = i0) →
--                     doubleCompPath-filler
--                       {!λ i j → m-n (~ i) j!}
--                            (cong (λ y → cong (λ x →  _⌣ₖ_ {n = (suc (suc n))} {m = (suc (suc m))} ∣ x ∣ ∣ y ∣) (merid a)) (merid b))
--                            {!!} (~ r) j i
--                   ; (l = i1) → {!!}})
--         {!!}
--   where
--   m-s : _
--   m-s = cong (Kn→ΩKn+1 _) (λ i → _⌣ₖ_ {n = (suc n)} {m = 2 + m} ∣ a ∣ ∣ merid (ptSn (suc m)) (~ i) ∣)
--       ∙∙ cong (Kn→ΩKn+1 _) (⌣ₖ-0ₖ (suc n) (2 + m) ∣ a ∣)
--       ∙∙ Kn→ΩKn+10ₖ _

--   m-n : _
--   m-n = cong (λ x → ⌣ₖ-0ₖ (suc (suc n)) (2 + m) ∣ x ∣) (merid a)

-- {-
-- i = i0 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p north
--          (merid b j) l
-- i = i1 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p south
--          (merid b j) l
-- j = i0 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p
--          (merid a i) north l
-- j = i1 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p
--          (merid a i) south l
-- l = i0 ⊢ ∣ merid a i ∣ ⌣ₖ ∣ merid b j ∣
-- l = i1 ⊢ subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
--          ((-ₖ^ suc (suc n) · suc (suc m)) (∣ merid b j ∣ ⌣ₖ ∣ merid a i ∣))
-- -}
  
  
-- --   id₁ : cong (λ y → cong (λ x →  _⌣ₖ_ {n = (suc (suc n))} {m = (suc (suc m))} ∣ x ∣ ∣ y ∣) (merid a)) (merid b)
-- --       ≡ cong (Kn→ΩKn+1 _) (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north
-- --                         ∙∙ cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- --                        ((-ₖ^ suc n · suc (suc m)))))
-- --                          (Kn→ΩKn+1 _ ((subst coHomK (+'-comm (suc n) (suc m))
-- --                                       ((-ₖ^ suc m · suc n) (∣ a ∣ ⌣ₖ ∣ b ∣)))))
-- --                         ∙∙ sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south))
-- --   id₁ = (λ i → cong (Kn→ΩKn+1 _) (rUnit (cong (λ y → _⌣ₖ_ {n = (suc n)} {m = (suc (suc m))}  ∣ a ∣ ∣ y ∣) (merid b)) i))
-- --      ∙∙ (λ i → (cong (Kn→ΩKn+1 _) ((λ r → gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north (i ∧ r))
-- --                                  ∙∙ (λ j → (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a (merid b j)) i)
-- --                                  ∙∙ λ r → gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south (i ∧ ~ r))))
-- --      ∙∙ (λ i → cong (Kn→ΩKn+1 _)
-- --                (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north
-- --                ∙∙ cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- --                        ((-ₖ^ suc n · suc (suc m)))))
-- --                        (Kn→ΩKn+1 _ (gradedComm-helper' k m n (+-comm m n
-- --                       ∙ cong predℕ (sym (+-suc n m) ∙ (cong predℕ p))) b a i) )
-- --                ∙∙ sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south)))

-- --   lem₁ : (n m : ℕ)  (x : _)
-- --        → Kn→ΩKn+1 _ ((subst coHomK (+'-comm (suc n) (suc m))
-- --                       ((-ₖ^ suc m · suc n) x)))
-- --        ≡ cong (subst coHomK (cong (3 +_) (+-comm n m)) ∘
-- --           (-ₖ^_·_ {k = suc (suc (suc (n + m)))} (suc m) (suc n)))
-- --            (Kn→ΩKn+1 _ x)
-- --   lem₁ n m = {!!}

-- --   id₂' : cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- --                        ((-ₖ^ suc n · suc (suc m)))))
-- --                          (Kn→ΩKn+1 _ ((subst coHomK (+'-comm (suc n) (suc m))
-- --                                       ((-ₖ^ suc m · suc n) (∣ a ∣ ⌣ₖ ∣ b ∣)))))
-- --        ≡ (cong (subst coHomK (+'-comm (suc (suc m)) (suc n))
-- --          ∘ (-ₖ^ suc n · suc (suc m))
-- --           ∘ (subst coHomK (cong (_+_ 3) (+-comm n m)) ∘ (-ₖ^ suc m · suc n))))
-- --             (gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) north b
-- --           ∙∙ (cong (subst coHomK (+'-comm (suc m) (suc (suc n))) ∘
-- --              (-ₖ^ suc (suc n) · suc m)) (λ j → ∣ b ∣ ⌣ₖ ∣ merid a j ∣))
-- --           ∙∙ sym (gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) south b))
-- --   id₂' =
-- --        cong (cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- --                        ((-ₖ^ suc n · suc (suc m))))))
-- --             (lem₁ n m (∣ a ∣ ⌣ₖ ∣ b ∣))
-- --     ∙ cong (cong (subst coHomK (+'-comm (suc (suc m)) (suc n))
-- --          ∘ (-ₖ^ suc n · suc (suc m))
-- --           ∘ (subst coHomK (cong (_+_ 3) (+-comm n m)) ∘ (-ₖ^ suc m · suc n))))
-- --            ((rUnit λ j → _⌣ₖ_ {n = (suc (suc n))} {m = (suc m)}  ∣ merid a j ∣ ∣ b ∣)
-- --           ∙ λ i → (λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) north b (i ∧ j))
-- --                ∙∙ (λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) (merid a j) b i)
-- --                ∙∙ λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) south b (i ∧ ~ j))
-- --     ∙ λ i → (cong (subst coHomK (+'-comm (suc (suc m)) (suc n))
-- --          ∘ (-ₖ^ suc n · suc (suc m))
-- --           ∘ (subst coHomK (cong (_+_ 3) (+-comm n m)) ∘ (-ₖ^ suc m · suc n))))
-- --             (gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) north b
-- --           ∙∙ (λ j → subst coHomK (+'-comm (suc m) (suc (suc n)))
-- --              ((-ₖ^ suc (suc n) · suc m) (∣ b ∣ ⌣ₖ ∣ merid a j ∣)))
-- --           ∙∙ sym (gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) south b))

-- -- --   id'' : cong (λ y → cong (λ x →  _⌣ₖ_ {n = (suc (suc m))} {m = (suc (suc n))} ∣ x ∣ ∣ y ∣) (merid b)) (merid a)
-- -- --        ≡ cong (λ y → cong (λ x →  _⌣ₖ_ {n = (suc (suc m))} {m = (suc (suc n))} ∣ x ∣ ∣ y ∣) (merid b)) (merid a)
-- -- --   id'' k i j = Kn→ΩKn+1 _ (_⌣ₖ_ {n = (suc m)} {m = (suc (suc n))} ∣ b ∣ ∣ merid a i ∣) j

-- -- --   id' : cong (λ y → cong (λ x →  _⌣ₖ_ {n = (suc (suc n))} {m = (suc (suc m))} ∣ x ∣ ∣ y ∣) (merid a)) (merid b)
-- -- --       ≡ {! !}
-- -- --   id' = -- (λ _ i j → _⌣ₖ_ {n = (suc (suc n))} {m = (suc (suc m))} ∣ merid a j ∣ ∣ merid b i ∣)
-- -- --       (λ i → cong (Kn→ΩKn+1 _) (rUnit (cong (λ y → _⌣ₖ_ {n = (suc n)} {m = (suc (suc m))}  ∣ a ∣ ∣ y ∣) (merid b)) i))
-- -- --      ∙∙ (λ i → (cong (Kn→ΩKn+1 _) ((λ r → gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north (i ∧ r))
-- -- --                                  ∙∙ (λ j → (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a (merid b j)) i)
-- -- --                                  ∙∙ λ r → gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south (i ∧ ~ r))))
-- -- --      ∙∙ (λ i → cong (Kn→ΩKn+1 _)
-- -- --                (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north
-- -- --                ∙∙ cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- --                        ((-ₖ^ suc n · suc (suc m)))))
-- -- --                        (Kn→ΩKn+1 _ (gradedComm-helper' k m n (+-comm m n
-- -- --                       ∙ cong predℕ (sym (+-suc n m) ∙ (cong predℕ p))) b a i) )
-- -- --                ∙∙ sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south)))
-- -- --      ∙∙ (λ i → cong (Kn→ΩKn+1 _)
-- -- --                (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north
-- -- --                ∙∙ cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- --                        ((-ₖ^ suc n · suc (suc m)))))
-- -- --                        (Kn→ΩKn+1 _ (
-- -- --        (subst coHomK (+'-comm (suc n) (suc m))
-- -- --         (trMap
-- -- --          (-ₖ-helper (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))
-- -- --           (_⌣ₖ_ {n = (suc n)} {m = (suc m)}  ∣ a ∣ ∣ b ∣)))))
-- -- --                ∙∙ sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south)))
-- -- --      ∙∙ cong-∙∙ (Kn→ΩKn+1 _) (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north)
-- -- --                               (cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- --                        ((-ₖ^ suc n · suc (suc m)))))
-- -- --                        (Kn→ΩKn+1 _ (
-- -- --        (subst coHomK (+'-comm (suc n) (suc m))
-- -- --         (trMap
-- -- --          (-ₖ-helper (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))
-- -- --           (_⌣ₖ_ {n = (suc n)} {m = (suc m)}  ∣ a ∣ ∣ b ∣))))))
-- -- --                               (sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south))
-- -- --      ∙∙ (λ i → cong (Kn→ΩKn+1 _) (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north)
-- -- --              ∙∙ cong (Kn→ΩKn+1 _) ((cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- --                        ((-ₖ^ suc n · suc (suc m))))))
-- -- --                          (lem₁ n m (evenOrOdd (suc m)) (evenOrOdd (suc n))
-- -- --                            (_⌣ₖ_ {n = (suc n)} {m = (suc m)}  ∣ a ∣ ∣ b ∣) i))
-- -- --              ∙∙ cong (Kn→ΩKn+1 _) (sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south)))
-- -- --      ∙∙ (λ i → cong (Kn→ΩKn+1 _) (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north)
-- -- --              ∙∙ cong (Kn→ΩKn+1 _) ((cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- --                        ((-ₖ^ suc n · suc (suc m)))))) -- (1 + n) (2 + m) + (1 + n) (1 + m). Remaining: 1 + n. -- 
-- -- --                          (cong (subst coHomK (cong (3 +_) (+-comm n m)) ∘
-- -- --         (trMap
-- -- --          (-ₖ-helper (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))))
-- -- --            (rUnit (λ j → _⌣ₖ_ {n = (suc (suc n))} {m = (suc m)}  ∣ merid a j ∣ ∣ b ∣) i)))
-- -- --              ∙∙ cong (Kn→ΩKn+1 _) (sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south)))
-- -- --       ∙ (λ i → cong (Kn→ΩKn+1 _) (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north)
-- -- --              ∙∙ cong (Kn→ΩKn+1 _) ((cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- --                        ((-ₖ^ suc n · suc (suc m)))))) -- (1 + n) (2 + m) + (1 + n) (1 + m). Remaining: 1 + n. + (2 + n) (1 + m) =  x(y + 1) + (x + 1)y + x y = xy + x + y
-- -- --                          (cong (subst coHomK (cong (3 +_) (+-comm n m)) ∘
-- -- --         (trMap
-- -- --          (-ₖ-helper (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))))
-- -- --               ((λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) north b (i ∧ j))
-- -- --            ∙∙ ((λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) (merid a j) b i))
-- -- --            ∙∙ λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) south b (i ∧ ~ j))))
-- -- --              ∙∙ cong (Kn→ΩKn+1 _) (sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south)))
-- -- --       ∙ {!λ i → cong (Kn→ΩKn+1 _) (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a north)
-- -- --              ∙∙ cong (Kn→ΩKn+1 _) ((cong ((subst coHomK (+'-comm (suc (suc m)) (suc n)) ∘ 
-- -- --                        ((-ₖ^ suc n · suc (suc m)))))) -- (1 + n) (2 + m) + (1 + n) (1 + m). Remaining: 1 + n. + (2 + n) (1 + m) =  x(y + 1) + (x + 1)y + x y = xy + x + y
-- -- --                          (cong (subst coHomK (cong (3 +_) (+-comm n m)) ∘
-- -- --         (trMap
-- -- --          (-ₖ-helper (suc m) (suc n) (evenOrOdd (suc m)) (evenOrOdd (suc n)))))
-- -- --               ((λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) north b (i ∧ j))
-- -- --            ∙∙ ((λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) (merid a j) b i))
-- -- --            ∙∙ λ j → gradedComm-helper' (suc k) (suc n) m (sym (+-suc n m) ∙ cong predℕ p) south b (i ∧ ~ j))))
-- -- --              ∙∙ cong (Kn→ΩKn+1 _) (sym (gradedComm-helper' (suc k) n (suc m) (cong predℕ p) a south))!}
-- -- --       ∙ ?
-- -- --       -- (1 + n) m + (1 + n) (1 + m) + n (1 + m) = m + mn + 1 + n + m + mn + n + mn =₂ mn + 1
-- -- -- {-
-- -- -- WTS : ∣ merid a i ∣ ⌣ ∣ merid b j ∣ ≡ -ₖ⁽¹⁺ⁿ⁾⁽¹⁺ᵐ⁾⁺¹ (∣ merid b i ∣ ⌣ ∣ merid a j ∣)
-- -- -- case 1:

-- -- -- case 2:
-- -- -- case 3:
-- -- -- case 4: 

-- -- -- -}

-- -- --       where
-- -- --       lem₁ : (n m : ℕ) (p : _) (q : _) (x : _) → Kn→ΩKn+1 _ (
-- -- --        (subst coHomK (+'-comm (suc n) (suc m))
-- -- --         (trMap
-- -- --           (-ₖ-helper (suc m) (suc n) p q) x))) ≡ cong (subst coHomK (cong (3 +_) (+-comm n m)) ∘
-- -- --         (trMap
-- -- --          (-ₖ-helper (suc m) (suc n) p q))) (Kn→ΩKn+1 _ x)
-- -- --       lem₁ = {!!}

-- -- --       lem₂ : {!!}
-- -- --       lem₂ = {!!}

-- -- -- {-
-- -- -- i = i0 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p north
-- -- --          (merid b j) l
-- -- -- i = i1 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p south
-- -- --          (merid b j) l
-- -- -- j = i0 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p
-- -- --          (merid a i) north l
-- -- -- j = i1 ⊢ gradedComm-helper' (suc (suc k)) (suc n) (suc m) p
-- -- --          (merid a i) south l
-- -- -- l = i0 ⊢ ∣ merid a i ∣ ⌣ₖ ∣ merid b j ∣
-- -- -- l = i1 ⊢ subst coHomK (+'-comm (suc (suc m)) (suc (suc n)))
-- -- --          ((-ₖ^ suc (suc n) · suc (suc m)) (∣ merid b j ∣ ⌣ₖ ∣ merid a i ∣))
-- -- -- -}
