-- TODO: uncomment once finished!
-- {-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.Graded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws using (rUnit)

open import Cubical.Relation.Nullary.Base

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.FinData hiding (_==_ ; snotz)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim ; rec to ⊥-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Sum.Base hiding (map)

open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥-rec ; elim to ∥-elim)

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.Group hiding (Bool ; Unit)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.Properties

private
  variable
    ℓ : Level

open AbGroupStr renaming (_+_ to _+G'_)
open RingStr
open IsRing

_==_ : ℕ → ℕ → Bool
x == y = Dec→Bool (discreteℕ x y)

∸Cancel : ∀ n → n ∸ n ≡ 0
∸Cancel zero = refl
∸Cancel (suc n) = ∸Cancel n

isFiniteSubsetℕ : ℙ ℕ → Type₀
isFiniteSubsetℕ X = ∃[ n ∈ ℕ ] ({x : ℕ} → x ∈ X → x < n)

FinSubsetℕ : Type₁
FinSubsetℕ = Σ[ X ∈ ℙ ℕ ] isFiniteSubsetℕ X

∅ : FinSubsetℕ
∅ = (λ _ → ⊥ , λ ()) , ∣ 0 , (λ ()) ∣

_∪ℙ_ : ℙ ℕ → ℙ ℕ → ℙ ℕ
X ∪ℙ Y = λ i → ∥ (i ∈ X) ⊎ (i ∈ Y) ∥ , squash

_×ℙ_ : ℙ ℕ → ℙ ℕ → ℙ (ℕ × ℕ)
X ×ℙ Y = λ i → ∥ (fst i ∈ X) × (snd i ∈ Y) ∥ , squash

asdf : {m n : ℕ} (k : ℕ) → m < n → m < n +ℕ k
asdf {m} {n} k (x , Hx) = x +ℕ k , sym (+-assoc x k (suc m))
                                 ∙ cong (λ y → x +ℕ y) (+-comm k (suc m))
                                 ∙ +-assoc x (suc m) k
                                 ∙ cong (λ x → x +ℕ k) Hx

asdf2 : {m n : ℕ} (k : ℕ) → m < n → m < k +ℕ n
asdf2 {m} {n} k h = subst (λ x → m < x) (+-comm n k) (asdf k h)

_∪_ : FinSubsetℕ → FinSubsetℕ → FinSubsetℕ
(X , HX) ∪ (Y , HY) = (X ∪ℙ Y) , map2 (λ x y → (fst x +ℕ fst y) , foo x y) HX HY
  where
  foo : (x : Σ[ n ∈ ℕ ] ({x : ℕ} → x ∈ X → x < n))
        (y : Σ[ n ∈ ℕ ] ({x : ℕ} → x ∈ Y → x < n))
      → {z : ℕ} → z ∈ (X ∪ℙ Y) → z < fst x +ℕ fst y
  foo (x , Hx) (y , Hy) = ∥-rec m≤n-isProp helper
    where
    helper : {z : ℕ} → (z ∈ X) ⊎ (z ∈ Y) → z < x +ℕ y
    helper (inl h) = asdf y (Hx h)
    helper (inr h) = asdf2 x (Hy h)


_Πℙ_ : ℙ ℕ → ℙ ℕ → ℙ ℕ
X Πℙ Y = λ n → (∃[ ij ∈ (ℕ × ℕ) ] (fst ij ·ℕ snd ij ≡ n) × (fst ij ∈ X) × (snd ij ∈ Y)) , squash

·ℕ<·ℕ : {a b c d : ℕ} → a < c → b < d → a ·ℕ b < c ·ℕ d
·ℕ<·ℕ {a} {b} {c} {d} (x , hx) (y , hy) = z , sym hz
  where
  z : ℕ
  z = (x +ℕ suc a) ·ℕ y +ℕ x ·ℕ suc b +ℕ (b +ℕ a)

  hz : c ·ℕ d ≡ z +ℕ suc (a ·ℕ b)
  hz =
    c ·ℕ d ≡⟨ (λ i → (hx (~ i)) ·ℕ (hy (~ i))) ⟩
    (x +ℕ suc a) ·ℕ (y +ℕ suc b)
      ≡⟨ sym (·-distribˡ (x +ℕ suc a) y (suc b)) ⟩
    ((x +ℕ suc a) ·ℕ y) +ℕ ((x +ℕ suc a) ·ℕ suc b)
      ≡⟨ (λ i → ((x +ℕ suc a) ·ℕ y) +ℕ ·-distribʳ x (suc a) (suc b) (~ i)) ⟩
    ((x +ℕ suc a) ·ℕ y) +ℕ ((x ·ℕ suc b) +ℕ (suc a ·ℕ suc b))
      ≡⟨ +-assoc ((x +ℕ suc a) ·ℕ y) (x ·ℕ suc b) (suc a ·ℕ suc b) ⟩
    ((x +ℕ suc a) ·ℕ y +ℕ x ·ℕ suc b) +ℕ suc a ·ℕ suc b
      ≡⟨ (λ i → (x +ℕ suc a) ·ℕ y +ℕ x ·ℕ suc b +ℕ suc (b +ℕ ·-suc a b i)) ⟩
    (x +ℕ suc a) ·ℕ y +ℕ x ·ℕ suc b +ℕ suc (b +ℕ (a +ℕ a ·ℕ b))
      ≡⟨ (λ i → (x +ℕ suc a) ·ℕ y +ℕ x ·ℕ suc b +ℕ suc (+-assoc b a (a ·ℕ b) i)) ⟩
    (x +ℕ suc a) ·ℕ y +ℕ x ·ℕ suc b +ℕ suc ((b +ℕ a) +ℕ a ·ℕ b)
      ≡⟨ cong ((x +ℕ suc a) ·ℕ y +ℕ x ·ℕ suc b +ℕ_) (sym (+-suc (b +ℕ a) (a ·ℕ b))) ⟩
    ((x +ℕ suc a) ·ℕ y +ℕ x ·ℕ suc b) +ℕ ((b +ℕ a) +ℕ suc (a ·ℕ b))
      ≡⟨ +-assoc ((x +ℕ suc a) ·ℕ y +ℕ x ·ℕ suc b) (b +ℕ a) (suc (a ·ℕ b))  ⟩
    ((x +ℕ suc a) ·ℕ y +ℕ x ·ℕ suc b +ℕ (b +ℕ a)) +ℕ suc (a ·ℕ b) ∎

_Π_ : FinSubsetℕ → FinSubsetℕ → FinSubsetℕ
(X , hX) Π (Y , hY) = (X Πℙ Y , map2 (λ x y → (fst x ·ℕ fst y) , foo x y) hX hY)
  where
  foo : (x : Σ[ n ∈ ℕ ] ({x : ℕ} → x ∈ X → x < n))
        (y : Σ[ n ∈ ℕ ] ({x : ℕ} → x ∈ Y → x < n))
      → {z : ℕ} → z ∈ (X Πℙ Y) → z < fst x ·ℕ fst y
  foo (x , Hx) (y , Hy) = ∥-rec m≤n-isProp helper
    where
    helper : {z : ℕ} → Σ[ ij ∈ ℕ × ℕ ] ((fst ij ·ℕ snd ij ≡ z) × (fst ij ∈ X) × (snd ij ∈ Y)) → z < x ·ℕ y
    helper {z} ((i , j) , h1 , h2 , h3) =
      subst (λ a → a < x ·ℕ y) h1 (·ℕ<·ℕ (Hx h2) (Hy h3))

infix 5 _∉_

_∉_ : {X : Type ℓ} → X → ℙ X → Type ℓ
x ∉ A = ¬ x ∈ A

∉∪ : (x : ℕ) (X Y : FinSubsetℕ) → x ∉ fst (X ∪ Y) → (x ∉ fst X) × (x ∉ fst Y)
∉∪ x X Y H = (λ HX → H ∣ inl HX ∣) , (λ HY → H ∣ inr HY ∣)

module GradedAbGroup (G : ℕ → AbGroup ℓ)
                     (1G : G 0 .fst)
                     (_·G_ : {m n : ℕ} → G m .fst → G n .fst → G (m +ℕ n) .fst)
                     (·G-rid : {m : ℕ} (x : G m .fst) → x ·G 1G ≡ subst (λ y → G y .fst) (sym (+-zero m)) x)
                     (·G-lid : {m : ℕ} (x : G m .fst) → 1G ·G x ≡ x)
                     (·G-assoc : {m n k : ℕ} (x : G m .fst) (y : G n .fst) (z : G k .fst)
                               → x ·G (y ·G z) ≡ subst (λ w → G w .fst) (sym (+-assoc m n k)) ((x ·G y) ·G z))
                     (·G-distRight : {m n : ℕ} (x : G m .fst) (y : G n .fst) (z : G n .fst)
                                   → x ·G (G n .snd ._+G'_ y z) ≡ G (m +ℕ n) .snd ._+G'_ (x ·G y) (x ·G z))
                     (·G-distLeft : {m n : ℕ} (x : G m .fst) (y : G m .fst) (z : G n .fst)
                                  → (G m .snd ._+G'_ x y) ·G z ≡ G (m +ℕ n) .snd ._+G'_ (x ·G z) (y ·G z))
                     -- TODO: are these two needed?
                     (·G-l0g : {m n : ℕ} (x : G m .fst) → x ·G 0g (G n .snd) ≡ 0g (G (m +ℕ n) .snd))
                     (·G-r0g : {m n : ℕ} (x : G n .fst) → 0g (G m .snd) ·G x ≡ 0g (G (m +ℕ n) .snd))
                     where
  _+G_ : {m : ℕ} → (x y : G m .fst) → G m .fst
  _+G_ {m} x y = G m .snd ._+G'_ x y

  0G : {m : ℕ} → G m .fst
  0G {m} = G m .snd .0g

  ⊕G : Type _ -- Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  ⊕G = Σ[ f ∈ ((i : ℕ) → G i .fst) ]
          ∃[ n ∈ ℕ ] ((m : ℕ) → n < m → f m ≡ 0G)

  isSet⊕G : isSet ⊕G
  isSet⊕G = isSetΣ (isSetΠ (λ i → is-set (G i .snd))) λ _ → isProp→isSet squash

  0⊕G : ⊕G
  0⊕G = (λ _ → 0G) , ∣ 0 , (λ _ _ → refl) ∣

  foo : (n m l : ℕ) → (n +ℕ m) < l → (n < l) × (m < l)
  foo n m l = {!!}

  _+⊕G_ : ⊕G → ⊕G → ⊕G
  fst ((f , p) +⊕G (g , q)) m = f m +G g m
  snd ((f , p) +⊕G (g , q)) =
    ∥-rec squash
      (λ p → ∥-rec squash (λ q → ∣ (fst p +ℕ fst q) ,
        (λ m ineq → cong₂ _+G_ (snd p m (foo (fst p) (fst q) m ineq .fst)) (snd q m (foo (fst p) (fst q) m ineq .snd))
                  ∙ lid (snd (G m)) 0G) ∣) q) p

  +⊕G-rid : (x : ⊕G) → x +⊕G 0⊕G ≡ x
  +⊕G-rid (x , _) = Σ≡Prop (λ _ → squash) (funExt (λ i → rid (G i .snd) _))

  +⊕G-comm : (x y : ⊕G) → x +⊕G y ≡ y +⊕G x
  +⊕G-comm (x , _) (y , _) = Σ≡Prop (λ _ → squash) (funExt (λ i → comm (G i .snd) _ _))

  +⊕G-assoc : (x y z : ⊕G) → x +⊕G (y +⊕G z) ≡ (x +⊕G y) +⊕G z
  +⊕G-assoc (x , _) (y , _) (z , _) = Σ≡Prop (λ _ → squash) (funExt (λ i → assoc (G i .snd) _ _ _))

  -⊕G_ : ⊕G → ⊕G
  -⊕G (f , Hf) = (λ i → G i .snd .-_ (f i))
               , map (λ p → fst p , λ m ineq → cong (G m .snd .-_) ((snd p) m ineq) ∙ GroupTheory.inv1g (AbGroup→Group (G m))) Hf

  +-⊕G : (x : ⊕G) → (x +⊕G (-⊕G x)) ≡ 0⊕G
  +-⊕G (x , _) = Σ≡Prop (λ _ → squash) (funExt (λ i → invr (G i .snd) _))

  ⊕G-AbGroup : AbGroup _
  fst ⊕G-AbGroup = ⊕G
  0g (snd ⊕G-AbGroup) = 0⊕G
  _+G'_ (snd ⊕G-AbGroup) = _+⊕G_
  - snd ⊕G-AbGroup = -⊕G_
  isAbGroup (snd ⊕G-AbGroup) = makeIsAbGroup isSet⊕G +⊕G-assoc +⊕G-rid +-⊕G +⊕G-comm

  -- End of direct sum of groups
  1⊕G' : (i : ℕ) → G i .fst
  1⊕G' 0 = 1G
  1⊕G' (suc i) = 0G

  1⊕G : ⊕G
  fst 1⊕G = 1⊕G'
  snd 1⊕G = ∣ 1 , (λ { zero p → ⊥-rec (snotz (sym (+-comm (fst p) 2) ∙ p .snd))
                    ; (suc m) → λ _ → refl}) ∣

--   abstract
--     helper : {n : ℕ} → (i : Fin (suc n)) → toℕ i +ℕ (n ∸ toℕ i) ≡ n
--     helper {n} i = +-comm (toℕ i) _ ∙ ≤-∸-+-cancel {m = toℕ i} (pred-≤-pred (toℕ<n i))

--   -- asdnasd : {n : ℕ} → (i : Fin n) → toℕ i +ℕ (n ∸ toℕ i) ≡ n
--   -- asdnasd {n} i = +-comm (toℕ i) _ ∙ ≤-∸-+-cancel {m = toℕ i} {!toℕ<n i!}

  cast : {m n : ℕ} → m ≡ n → G m .fst → G n .fst
  cast p = subst (λ x → G x .fst) p

  waho : {!!}
  waho = {!!}


  taut : (n m : ℕ) → (n ≡ m) ⊎ (¬ (n ≡ m))
  taut zero zero = inl refl
  taut zero (suc m) = inr λ p → snotz (sym p)
  taut (suc n) zero = inr snotz
  taut (suc n) (suc m) with (taut n m)
  ... | (inl p) = inl (cong suc p)
  ... | (inr p) = inr λ q → p (cong predℕ q)

  propHelp : (n m : ℕ) → isProp ((n ≡ m) ⊎ (¬ (n ≡ m)))
  propHelp = {!!}

  at-help : (f : (m₁ : ℕ) → G m₁ .fst) → (n m : ℕ) → (n ≡ m) ⊎ (¬ (n ≡ m)) → G m .fst
  at-help f n m (inl x) = cast x (f n)
  at-help f n m (inr x) = 0G

  cast0 : {n m : ℕ} (p : n ≡ m) → cast p 0G ≡ 0G
  cast0 {n = n} = J (λ m p → cast p 0G ≡ 0G) (transportRefl 0G)

  at : (n : ℕ) → ⊕G → ⊕G
  fst (at n (f , p)) m = at-help f n m (taut n m)
  snd (at n (f , p)) =
    ∣ (n , λ m p → cong (at-help f n m) (propHelp n m (taut n m) (inr (<→≢ p)))) ∣

  sum' : (f : ℕ → ⊕G) → ℕ → ⊕G
  sum' f zero = f zero
  sum' f (suc n) = (sum' f n) +⊕G f (suc n)

  sumDistr : (f g : ℕ → ⊕G) (n : ℕ) → {!!} -- sum' (λ n → f n +⊕G g n) n ≡ (sum' f n +⊕G sum' g n)
  sumDistr = {!!}

  removeLast' : (f : (m : ℕ) → G m .fst) (n : ℕ) (P : (m : ℕ) → n < m → f m ≡ 0G) → (i : ℕ) → (n ≡ i) ⊎ (¬ (n ≡ i)) → G i .fst
  removeLast' f n P m (inl x) = 0G
  removeLast' f n P m (inr x) = f m

  removeLast : (f : (m : ℕ) → G m .fst) (n : ℕ) (P : (m : ℕ) → n < m → f m ≡ 0G) → ⊕G
  fst (removeLast f n P) i = removeLast' f n P i (taut n i)
  snd (removeLast f n P) = ∣ predℕ n , (λ m Q → help n m P Q) ∣
    where
    help : (n m : ℕ) (P : _) → predℕ n < m → removeLast' f n P m (taut n m) ≡ 0G
    help zero m P p = cong (removeLast' f zero P m) (propHelp zero m (taut zero m) (inr (<→≢ p))) ∙ P m p -- ⊥-rec (¬-<-zero p)
    help (suc n) m P p = help' (taut (suc n) m) p
      where
      help' : (Q : (suc n ≡ m) ⊎ (¬ suc n ≡ m)) (p : n < m) → removeLast' f (suc n) P m Q ≡ 0G
      help' (inl Q) p = refl
      help' (inr Q) (zero , p) = ⊥-rec (Q p)
      help' (inr Q) (suc k , p) = P m (k , +-suc k (suc n) ∙ p)

  wow : (f : (m : ℕ) → G m .fst) (n : ℕ) (P : (m : ℕ) → n < m → f m ≡ 0G)
      → Path ⊕G (f , ∣ n , P ∣) (removeLast f n P +⊕G at n (f , ∣ n , P ∣))
  wow f n P = Σ≡Prop (λ _ → squash) (funExt λ x → hlep x (taut n x))
    where
    hlep : (x : ℕ) → (Q : (n ≡ x) ⊎ (¬ n ≡ x))
      → f x ≡ (removeLast' f n P x Q +G at-help f n x Q)
    hlep x (inl p) = (λ i → transp (λ j → G (p (~ i ∨ j)) .fst) (~ i) (f (p (~ i)))) ∙ sym (lid (snd (G x)) (cast p (f n)))
    hlep x (inr _) = sym (rid (snd (G x)) (f x))

  order : ⊕G → ∥ ℕ ∥
  order = uncurry λ _ → map fst

  respect+ : {P : ⊕G → Type ℓ} (hLev : (x : _) → isProp (P x))
          → ((f : ⊕G) (n : ℕ) → P (at n f))
          → (((f g : ⊕G) → P f → P g → P (f +⊕G g)))
          → (x : _) → P x
  respect+ {P = P} prop at-hyp add-hyp =
    uncurry λ f → ∥-elim (λ _ → prop _) (uncurry λ x p → main x f p)
      where
      help1 : (f : (i : ℕ) → G i .fst) (p : (m : ℕ) → zero < m → f m ≡ 0G)
           → (f , ∣ zero , p ∣) ≡ at zero (f , ∣ zero , p ∣ ) 
      help1 f p = Σ≡Prop (λ _ → squash)
        (funExt λ { zero → sym (transportRefl (f zero))
                  ; (suc x) → p (suc x) (x , +-comm x 1)})

      main :  (x : ℕ)  (f : (i : ℕ) → G i .fst) (y : (m : ℕ) → x < m → f m ≡ 0G) → P (f , ∣ x , y ∣)
      main zero f y = subst P (sym (help1 f y)) (at-hyp (f , ∣ zero , y ∣) zero)
      main (suc x) f y =
        subst P (sym (wow f (suc x) y))
         (add-hyp (removeLast f (suc x) y) (at (suc x) (f , ∣ suc x , y ∣))
          (subst P triv help)
            (at-hyp ((f , ∣ suc x , y ∣)) (suc x)))
        where
        l' : (m : ℕ) → x < m → (Q : _) → removeLast' f (suc x) y m Q ≡ 0G
        l' m (k , p) (inl x) = refl
        l' m (zero , p) (inr x) = ⊥-rec (x p)
        l' m (suc k , p) (inr _) = y m (k , +-suc k (suc x) ∙ p)

        l : (m : ℕ) → x < m → removeLast' f (suc x) y m (taut (suc x) m) ≡ 0G
        l m o = l' m o (taut (suc x) m)

        triv : Path ⊕G ((λ m → removeLast' f (suc x) y m (taut (suc x) m)) , ∣ x , l ∣) (removeLast f (suc x) y)
        triv = Σ≡Prop (λ _ → squash) refl
        help : P _
        help = main x (fst (removeLast f (suc x) y)) l

  +⊕-assoc : (f g h : ⊕G) → (f +⊕G g) +⊕G h ≡ f +⊕G (g +⊕G h)
  +⊕-assoc = {!!}

  bar : (l : ℕ) → (x y z w : G l .fst) → ((x +G z) +G (y +G w)) ≡ ((x +G y) +G (z +G w))
  bar l x y z w =
       sym (assoc (snd (G l)) x z (y +G w))
    ∙∙ cong (x +G_) (assoc (snd (G l)) z y w ∙∙ cong (_+G w) (comm (snd (G l)) z y) ∙∙ sym (assoc (snd (G l)) y z w))
    ∙∙ assoc (snd (G l)) x y (z +G w)

  open import Cubical.Data.Nat renaming (_·_ to _mult_)
  _*_ : (f g : ℕ → ℕ) → (m l n : ℕ) → (n +ℕ l ≡ n) → ℕ 
  (f * g) zero l n p = (f zero) mult f l
  (f * g) (suc m) l n p = (f (suc m) mult g ((suc n))) +ℕ {!!}

  PRE : (f g : ((m : ℕ) → G m .fst)) → (n m l : ℕ) → (m +ℕ l ≡ n) → G n .fst
  PRE f g zero m l p = cast p (f m ·G (g l))
  PRE f g (suc n) m l p =
    cast (+-comm (suc n) zero) (f (suc n) ·G g zero) +G {!!}

--   -- PRE (at n f .fst) (at m g .fst) k zero k p

--   mapToVal : {n : ℕ} (x : G n .fst) → (i : ℕ) → (n ≡ i) ⊎ (¬ n ≡ i) → G i .fst
--   mapToVal x i (inl x₁) = cast x₁ x
--   mapToVal x i (inr x₁) = 0G

--   Pre-at' : {!!}
--   Pre-at' = {!!}

--   tihi : (f g : ⊕G) (n m k l w : ℕ) (p : _)  → PRE (at n f .fst) (at m g .fst) k l w p ≡ mapToVal (at (n +ℕ m) (f +⊕G g) .fst k) _ (taut k w)
--   tihi f g n m zero l w = J (λ w p → PRE (at n f .fst) (at m g .fst) zero l w p ≡ mapToVal (at (n +ℕ m) (f +⊕G g) .fst zero) _ (taut zero w))
--     (transportRefl _ ∙ {!!} ) -- help _ _ _ _)
--     where
--     help : (P : _) (Q : _) (R : _) (S : _)
--       → (at-help (fst f) n zero P ·G
--          at-help (fst g) m l Q)
--         ≡
--         mapToVal
--         (at-help (λ m₁ → fst f m₁ +G fst g m₁) (n +ℕ m) zero
--          S)
--         l R
--     help P Q R (inl x) = {!!}
--     help P (inl x₂) (inl x₁) (inr x) = {!!}
--     help P (inr x₂) (inl x₁) (inr x) = {!!}
--     help (inl x₂) (inl x₃) (inr x₁) (inr x) = {!!}
--     help (inl x₂) (inr x₃) (inr x₁) (inr x) = ·G-l0g (cast x₂ (fst f n))
--     help (inr x₂) Q (inr x₁) (inr x) = ·G-r0g (at-help (fst g) m l Q)
--   tihi f g n m (suc k) l w p = {!!}

--   Pre-at'' : (f g : ⊕G) → (n m n1 m1 : ℕ) (k : ℕ) → (max n m < n1) → (p : _)
--     → {!!}
--     → {!!}
--   Pre-at'' = {!!}

--   Pre-at : (f g : ⊕G) → (n m n1 m1 : ℕ) (k : ℕ) → (n +ℕ m < n1) → (n1 ≤ k)  → (m ≤ k) → (p : _)
--     → PRE (at n f .fst) (at m g .fst) n1 m1 k p
--     ≡ 0G 
--   Pre-at f g n m zero m1 k ineq ineq0 ineq2 = ⊥-rec (snotz (sym (+-suc (fst ineq) (n +ℕ m)) ∙ snd ineq))
--   Pre-at f g n m (suc n1) m1 k ineq0 ineq ineq2 =
--     J (λ k p → PRE (at n f .fst) (at m g .fst) (suc n1) m1 k p ≡ 0G )
--       (cong₂ _+G_ (transportRefl _ ∙ {!cong₂ _·_!}) (transportRefl _ ∙ Pre-at f g n m n1 (suc m1) _ {!!} {!!} {!!} {!!}) ∙ {!ineq!} ∙ {!!})

--   PREDistrᵣ : (f g h : ((m : ℕ) → G m .fst)) → (m l n : ℕ) → (p : (m +ℕ l ≡ n))
--            → PRE h (λ x → f x +G g x) m l n p
--            ≡ (PRE h f m l n p +G PRE h g m l n p)
--   PREDistrᵣ f g h zero l n = J (λ n p → PRE h (λ x → f x +G g x) zero l n p ≡
--       (PRE h f zero l n p +G PRE h g zero l n p))
--       (transportRefl _ ∙∙ (·G-distRight (h zero) (f l) (g l)) ∙∙ cong₂ _+G_  (sym (transportRefl _)) (sym (transportRefl _)))
--   PREDistrᵣ f g h (suc m) l n = J (λ n p → PRE h (λ x → f x +G g x) (suc m) l n p ≡
--       (PRE h f (suc m) l n p +G PRE h g (suc m) l n p))
--       (cong₂ _+G_ (transportRefl _) (transportRefl _)
--       ∙∙ cong₂ _+G_ (·G-distRight (h (suc m)) (f l) (g l)) (PREDistrᵣ f g h m (suc l) (suc (m +ℕ l)) (+-suc m l))
--        ∙ bar _ _ _ _ _
--       ∙∙ λ i → (transportRefl ((h (suc m) ·G f l)) (~ i)
--               +G transportRefl (PRE h f m (suc l) (suc (m +ℕ l)) (+-suc m l)) (~ i))
--               +G (transportRefl (h (suc m) ·G g l) (~ i)
--               +G transportRefl (PRE h g m (suc l) (suc (m +ℕ l)) (+-suc m l)) (~ i)))

--   PREDistrₗ : (f g h : ((m : ℕ) → G m .fst)) → (m l n : ℕ) → (p : (m +ℕ l ≡ n))
--            → PRE (λ x → f x +G g x) h m l n p
--            ≡ (PRE f h m l n p +G PRE g h m l n p)
--   PREDistrₗ f gg h zero l n = J (λ n p → subst (λ n₁ → G n₁ .fst) p ((f zero +G gg zero) ·G h l) ≡
--       (subst (λ n₁ → G n₁ .fst) p (f zero ·G h l) +G
--        subst (λ n₁ → G n₁ .fst) p (gg zero ·G h l)))
--          (transportRefl ((f zero +G gg zero) ·G h l)
--        ∙∙ ·G-distLeft (f zero) (gg zero) (h l)
--        ∙∙ sym (cong₂ _+G_ (transportRefl (f zero ·G h l)) (transportRefl (gg zero ·G h l))))
--   PREDistrₗ f gg h (suc m) l n = J (λ n p → PRE (λ x → f x +G gg x) h (suc m) l n p ≡
--       (PRE f h (suc m) l n p +G PRE gg h (suc m) l n p))
--         (cong₂ _+G_ (transportRefl ((f (suc m) +G gg (suc m)) ·G h l)) (transportRefl ((PRE (λ x → f x +G gg x) h m (suc l) (suc (m +ℕ l)) (+-suc m l))))
--       ∙∙ cong (_+G (PRE (λ x → f x +G gg x) h m (suc l) (suc (m +ℕ l)) (+-suc m l))) (·G-distLeft (f (suc m)) (gg (suc m)) (h l) )
--       ∙∙ cong (((f (suc m) ·G h l) +G (gg (suc m) ·G h l)) +G_)
--             (PREDistrₗ f gg h m (suc l) (suc (m +ℕ l)) (+-suc m l))
--       ∙∙ bar _ _ _ _ _
--       ∙∙ λ i → (transportRefl (f (suc m) ·G h l) (~ i) +G transportRefl (PRE f h m (suc l) (suc (m +ℕ l)) (+-suc m l)) (~ i))
--              +G (transportRefl (gg (suc m) ·G h l) (~ i) +G transportRefl (PRE gg h m (suc l) (suc (m +ℕ l)) (+-suc m l)) (~ i)))
--   PREAssoc : {!!}
--   PREAssoc = {!!}


--   elim< : (n m k : ℕ) → n +ℕ m < k → (n < k) × (m < k)
--   elim< = {!!}

--   premult' : ⊕G → ⊕G → ⊕G
--   fst (premult' (f , p) (g , q)) n = PRE f g n zero n (+-comm n zero)
--   snd (premult' f g) = {!!}
--     where
--     testHelp : {!(f : ℕ) PRE (λ m₁ → at-help (fst f) n m₁ Q)
--       (λ m₁ → at-help (fst g) m m₁ (taut m m₁)) k zero k (+-zero k)
--       ≡ 0G!}
--     testHelp = {!!}

--     test : (f g : ⊕G) → ∃-syntax ℕ  (λ n → (m : ℕ) → n < m → fst (premult' f g) m ≡ 0G)
--     test =
--       respect+ (λ _ → isPropΠ (λ _ → squash))
--         (λ f n
--           → respect+
--                (λ _ → squash)
--                (λ g m → ∣ n +ℕ m , (λ { zero → λ p → ⊥-rec {!!} ; (suc k) p → {!p!}}) ∣)
--                λ f' g' pf1 pf2 → {!!})
--         λ f' g' pf1 pf2 h →
--           ∥-rec squash
--             (λ {(n , p)
--               → map (λ {(m , q) → (n +ℕ m)
--                , λ k P → PREDistrₗ (fst f') (fst g') (fst h) k zero k (+-zero k)
--                ∙ cong₂ _+G_ (p k (elim< n m k P .fst)) (q k (elim< n m k P .snd))
--                ∙ rid (snd (G _)) 0G})
--                 (pf2 h)})
--               (pf1 h) 
--     fun = {!!}

--   test2 : (f g h : _) → premult' (premult' f g) h ≡ premult' f (premult' g h)
--   test2 = respect+ {!!} {!!} {!!}

--   premult : ⊕G → ⊕G → ∥ ⊕G ∥
--   premult =
--     respect+ (λ _ → isPropΠ λ _ → squash)
--       {!λ f → !}
--       λ _ _ _ _ → ∣_∣

--   +⊕-assoc-comm : (f g : ⊕G) → f +⊕G g ≡ g +⊕G f
--   +⊕-assoc-comm = {!!}

--   sumEmUp : (f : ⊕G) → ∃[ n ∈ ℕ ] f ≡ sum' (λ n → at n f) n
--   sumEmUp (f , p) =
--     ∥-elim {P = λ p → ∃[ n ∈ ℕ ] (f , p) ≡ sum' (λ n → at n (f , p)) n}
--         (λ _ → squash) --  (λ {(n , P) → ∣ (n , Σ≡Prop (λ _ → squash) (funExt λ x → {!!})) ∣})
--         (λ {(n , P) → ∣ n , (Σ≡Prop (λ _ → squash) (funExt {!!})) ∣})
--         p
--     where
--     help : (f : (i : ℕ) → G i .fst) (n x : ℕ) → (n ≡ x) ⊎ (¬ (n ≡ x)) → (P : ((m : ℕ) → n < m → f m ≡ 0G)) → f x ≡ sum' (λ n₁ → at n₁ (f , ∣ n , P ∣)) n .fst x
--     help f zero zero z P = sym (transportRefl (f zero))
--     help f zero (suc x) z P = P _ (x , +-comm x 1)
--     help f (suc n) x z P = {!P!}
--       where
--       ok : (n m : ℕ) → n < m → Σ[ k ∈ ℕ ] m ≡ k +ℕ (suc n)
--       ok = {!!}

--       w : (m : ℕ) →  n < m →  (f m +G G m .snd .-_ (at-help f (suc n) m (taut (suc n) m))) ≡ 0G
--       w m (zero , p) = (λ i → (f m +G G m .snd .-_ (at-help f (suc n) m (propHelp (suc n) m (taut (suc n) m) (inl p) i))))
--                      ∙ (λ i → (f m +G G m .snd .-_ (transp (λ j → G (p (i ∨ j)) .fst) i (f (p i)))))
--                      ∙ invr (snd (G m)) (f m)
--       w m (suc k , p) = cong₂ (λ x y → x +G G m .snd .-_ y) (P m (k , +-suc k (suc n) ∙ p))
--                               (cong (at-help f (suc n) m) (propHelp (suc n) m (taut (suc n) m) (inr (<→≢ (k , +-suc k (suc n) ∙ p)))))
--                        ∙ invr (snd (G m)) (0G)
        
--       ok2 : (x : ℕ) → sum'
--                          (λ n₁ →
--                             at n₁
--                             ((λ x₂ →
--                                 f x₂ +G G x₂ .snd .-_ (at-help f (suc n) x₂ (taut (suc n) x₂)))
--                              , ∣ n , w ∣))
--                          n .fst x ≡ fst (sum' (λ n₁ → at n₁ (f , ∣ suc n , P ∣)) n) x
--       ok2 = {!!}
--       h : f x +G G x .snd .-_ (at-help f (suc n) x (taut (suc n) x)) ≡ fst (sum' (λ n₁ → at n₁ (f , ∣ (suc n) , P ∣)) n) x
--       h = help (λ x → f x +G G x .snd .-_ (at-help f (suc n) x (taut (suc n) x))) n x (taut n x) w
--         ∙ ok2 x
--       newMap : (i : ℕ) → (n ≡ x) ⊎ (¬ (n ≡ x)) → G i .fst
--       newMap x = {!!}


-- --   cast·G-right : {m n n' : ℕ} (x : G m .fst) (y : G n .fst) (p : n ≡ n')
-- --                → x ·G cast p y ≡ cast (cong (m +ℕ_) p) (x ·G y)
-- --   cast·G-right {m} x y p =
-- --     J (λ z q → x ·G cast q y ≡ cast (cong (m +ℕ_) q) (x ·G y))
-- --       (cong (x ·G_) (transportRefl y) ∙ sym (transportRefl _)) p

-- --   -- cast·G-left : {m m' n : ℕ} (x : G m .fst) (y : G n .fst) (p : m ≡ m')
-- --   --             → cast p x ·G y ≡ cast (cong (_+ℕ n) p) (x ·G y)
-- --   -- cast·G-left x y p = {!!}

-- --   cast-comp : {m n k : ℕ} (x : G m .fst) (p : n ≡ k) (q : m ≡ n)
-- --               → cast p (cast q x) ≡ cast (q ∙ p) x
-- --   cast-comp x p q = J (λ y r → cast r (cast q x) ≡ cast (q ∙ r) x) rem p
-- --     where
-- --     rem : cast refl (cast q x) ≡ cast (q ∙ refl) x
-- --     rem = transportRefl _ ∙ cong (λ p → cast p x) (rUnit q)

-- --   cast≡ : {m n : ℕ} → (p : m ≡ n) (x : (i : ℕ) → G i .fst) → cast p (x m) ≡ x n
-- --   cast≡ p x = J (λ y q → cast q (x _) ≡ x _) (transportRefl _) p

-- --   cast·≡ : {n : ℕ} → (p : n ≡ n) → (x : G n .fst) → cast p x ≡ x
-- --   cast·≡ {n} p x = subst (λ y → cast y x ≡ x) prefl (transportRefl x)
-- --     where
-- --     prefl : refl ≡ p
-- --     prefl = isSetℕ n n refl p

-- --   cast·0≡ : {n : ℕ} → (x : G n .fst) → cast· zero x ≡ x
-- --   cast·0≡ {n} x = cast·≡ (helper zero) x

-- --     uncurry λ f → ∥-elim (λ _ → squash)
-- --       (uncurry (uncurry λ X
-- --         → ∥-elim (λ f → isPropΠ λ _ → squash)
-- --                  λ y w → ∣ (y .fst) , Σ≡Prop (λ _ → squash) (funExt λ { zero → {!!} ; (suc x) → {!!}}) ∣))
-- --     where
-- --     n : (X        : ℙ ℕ)
-- --         (y  : Σ ℕ (λ n₁ → {x : ℕ} → x ∈ X → x < n₁))
        
-- --         (f        : (i : ℕ) → G i .fst)
-- --         (w : {j : ℕ} → j ∉ X → f j ≡ 0G)
-- --         → f zero ≡
-- --       sum' (λ n₁ → at n₁ (f , ∣ (X , ∣ y ∣) , w ∣)) (y .fst) .fst zero
-- --     n X (zero , p) f w = sym (transportRefl _)
-- --     n X (suc y , p) f w = (n X (y , {!p!}) f w ∙ {!!})
-- --       ∙∙ (λ i → +⊕G-rid (sum' (λ n₁ → at n₁ (f , ∣ (X , ∣ suc y , p ∣) , w ∣)) y) (~ i) .fst zero)
-- --       ∙∙ λ i → (sum' (λ n₁ → at n₁ (f , ∣ (X , ∣ suc y , p ∣) , w ∣)) y +⊕G  help (~ i))  .fst zero
-- --       where
-- --       help : at (suc y) (f , ∣ (X , ∣ suc y , p ∣) , w ∣) ≡ 0⊕G
-- --       help = {!ref!}
-- --       help2 : {!!}
-- --       help2 = {!!}
    
-- --     t : {!∑ ?!}
-- --     t = {!!}

-- -- --   _·⊕G_ : ⊕G → ⊕G → ⊕G
-- -- --   (x , Hx) ·⊕G (y , Hy) = p , q
-- -- --     where
-- -- --     p : (n : ℕ) → G n .fst
-- -- --     p n = ∑ (λ (i : Fin (suc n)) → cast· i (x (toℕ i) ·G y (n ∸ toℕ i)))
-- -- --       where
-- -- --       open MonoidBigOp (Group→Monoid (AbGroup→Group (G n))) renaming (bigOp to ∑)

-- -- --     q : ∃[ I ∈ FinSubsetℕ ] ({j : ℕ} → j ∉ I .fst → p j ≡ 0G)
-- -- --     q = map2 (λ { (I , hI) (J , hJ) → (I Π J) ,
-- -- --                   let suff : (n : ℕ) (i : Fin (suc n)) (hn : n ∉ (I Π J) .fst) → (toℕ i ∉ I .fst) × ((n ∸ toℕ i) ∉ J .fst)
-- -- --                       suff n i hn = (λ x → hn ∣ {!!} ∣) , {!!}

-- -- --                       help : (n : ℕ) (hn : n ∉ (I Π J) .fst) (i : Fin (suc n)) → cast· i (x (toℕ i) ·G y (n ∸ toℕ i)) ≡ 0G
-- -- --                       help n hn i = {!!}

-- -- --                       H : {n : ℕ} → n ∉ (I Π J) .fst → p n ≡ 0G
-- -- --                       H {j} hj = MonoidBigOp.bigOpExt ((Group→Monoid (AbGroup→Group (G j)))) (help j hj)
-- -- --                                ∙ MonoidBigOp.bigOpε (((Group→Monoid (AbGroup→Group (G j))))) (suc j)
-- -- --                   in H
-- -- --                 }) Hx Hy

-- -- --   -- Algebraic properties of ·⊕G

-- -- --   ·⊕G-rid : (x : ⊕G) → x ·⊕G 1⊕G ≡ x
-- -- --   ·⊕G-rid (x , h) = Σ≡Prop (λ _ → squash) (funExt rem)
-- -- --     where
-- -- --     rem : (n : ℕ) → ((x , h) ·⊕G 1⊕G) .fst n ≡ x n
-- -- --     rem n = (∑ λ i → cast· i (x (toℕ i) ·G 1⊕G' _))
-- -- --         ≡⟨ bigOpLast (λ i → cast· i (x (toℕ i) ·G 1⊕G' _)) ⟩
-- -- --              (∑ ((λ i → cast· i (x (toℕ i) ·G 1⊕G' _)) ∘ weakenFin)) +G
-- -- --              cast· (fromℕ n) (x (toℕ (fromℕ n)) ·G 1⊕G' _)
-- -- --         ≡⟨ (λ i → rem0 i +G cast· (fromℕ n) (x (toℕ (fromℕ n)) ·G 1⊕G' _)) ⟩
-- -- --              0G +G cast· (fromℕ n) (x (toℕ (fromℕ n)) ·G 1⊕G' _)
-- -- --         ≡⟨ lid (G n .snd) _ ⟩
-- -- --              cast· (fromℕ n) (x (toℕ (fromℕ n)) ·G 1⊕G' _)
-- -- --         ≡⟨ cong (λ a → cast· (fromℕ n) a) (simpl _ _ (cong (n ∸_) (toFromId n) ∙ ∸Cancel n)) ⟩
-- -- --              cast· (fromℕ n) (x _)
-- -- --         ≡⟨ cast≡ (helper (fromℕ n)) x ⟩
-- -- --              x n  ∎
-- -- --       where
-- -- --       open MonoidBigOp (Group→Monoid (AbGroup→Group (G n))) renaming (bigOp to ∑)

-- -- --       rem0 : (∑ ((λ i → cast· i (x (toℕ i) ·G 1⊕G' _)) ∘ weakenFin)) ≡ 0G
-- -- --       rem0 = bigOpExt path ∙ bigOpε n
-- -- --         where
-- -- --         rem1 : {n : ℕ} (i : Fin n) → 1⊕G' (suc n ∸ suc (toℕ (weakenFin i))) ≡ 0G
-- -- --         rem1 zero = refl
-- -- --         rem1 {suc n} (suc i) = rem1 {n} i

-- -- --         path : (i : Fin n) → cast· (weakenFin i) (x (toℕ (weakenFin i)) ·G 1⊕G' _) ≡ 0G
-- -- --         path i = cast· (weakenFin i) (x (toℕ (weakenFin i)) ·G 1⊕G' _)
-- -- --                ≡⟨ (λ j → cast· (weakenFin i) (x (toℕ (weakenFin i)) ·G rem1 i j)) ⟩
-- -- --                  cast· (weakenFin i) (x (toℕ (weakenFin i)) ·G 0G)
-- -- --                ≡⟨ (λ j → cast· (weakenFin i) (·G-l0g (x (toℕ (weakenFin i))) j)) ⟩
-- -- --                  cast· (weakenFin i) 0G
-- -- --                ≡⟨ cast≡ (helper (weakenFin i)) (λ _ → 0G) ⟩
-- -- --                  0G ∎

-- -- --       simpl : (m n : ℕ) → (h : m ≡ 0) → x n ·G 1⊕G' m ≡ x (n +ℕ m)
-- -- --       simpl zero n h = ·G-rid (x n) ∙ cast≡ (sym (+-zero n)) x
-- -- --       simpl (suc m) n h = ⊥-rec (snotz h)

-- -- --   ·⊕G-lid : (x : ⊕G) → 1⊕G ·⊕G x ≡ x
-- -- --   ·⊕G-lid (x , h) = Σ≡Prop (λ _ → squash) (funExt rem)
-- -- --     where
-- -- --     rem : (n : ℕ) → (1⊕G ·⊕G (x , h)) .fst n ≡ x n
-- -- --     rem n = (∑ λ i → cast· i (1⊕G' (toℕ i) ·G x (n ∸ toℕ i)))
-- -- --           ≡⟨ refl ⟩
-- -- --              cast· zero (1G ·G x n) +G
-- -- --                (∑ (λ i → cast· (suc i) (1⊕G' (toℕ (suc i)) ·G x (n ∸ toℕ (suc i)))))
-- -- --           ≡⟨ (λ i → cast· zero (1G ·G x n) +G rem0 i) ⟩
-- -- --              cast· zero (1G ·G x n) +G 0G
-- -- --           ≡⟨ rid (G n .snd) (cast· zero (1G ·G x n)) ⟩
-- -- --              cast· zero (1G ·G x n)
-- -- --           ≡⟨ cong (cast· zero) (·G-lid (x n)) ⟩
-- -- --              cast· zero (x n)
-- -- --           ≡⟨ cast≡ (helper zero) x ⟩
-- -- --             x n  ∎
-- -- --       where
-- -- --       open MonoidBigOp (Group→Monoid (AbGroup→Group (G n))) renaming (bigOp to ∑)

-- -- --       rem0 : ∑ (λ i → cast· (suc i) (1⊕G' (toℕ (suc i)) ·G x (n ∸ toℕ (suc i)))) ≡ 0G
-- -- --       rem0 = bigOpExt path ∙ bigOpε n
-- -- --         where
-- -- --         path : (i : Fin n) → cast· (suc i) (1⊕G' (toℕ (suc i)) ·G x (n ∸ toℕ (suc i))) ≡ 0G
-- -- --         path i = cong (cast· (suc i)) (·G-r0g (x (n ∸ toℕ (suc i)))) ∙ cast≡ (helper (suc i)) (λ _ → 0G)

-- -- --   -- TODO: upstream?
-- -- --   bigOpExtGen : {n m : ℕ} {V W : Fin m → G n .fst}
-- -- --               → (h : (i : Fin m) → V i ≡ W i)
-- -- --               → foldrFin _+G_ 0G (λ (j : Fin m) → V j)
-- -- --               ≡ foldrFin _+G_ 0G (λ (j : Fin m) → W j)
-- -- --   bigOpExtGen h = cong (foldrFin _+G_ 0G) (funExt h)

-- -- --   ·⊕G-assoc : (x y z : ⊕G) → x ·⊕G (y ·⊕G z) ≡ (x ·⊕G y) ·⊕G z
-- -- --   ·⊕G-assoc (x , hx) (y , hy) (z , hz) = Σ≡Prop (λ _ → squash) (funExt rem)
-- -- --     where
-- -- --     rem : (n : ℕ) → ((x , hx) ·⊕G ((y , hy) ·⊕G (z , hz))) .fst n ≡
-- -- --                     (((x , hx) ·⊕G (y , hy)) ·⊕G (z , hz)) .fst n
-- -- --     rem n = ((x , hx) ·⊕G ((y , hy) ·⊕G (z , hz))) .fst n
-- -- --            ≡⟨ refl ⟩
-- -- --              ∑ (λ (i : Fin (suc n)) →
-- -- --                       cast· i (x (toℕ i) ·G
-- -- --                                foldrFin _+G_ 0G (λ j → cast· j (y (toℕ j) ·G z (n ∸ toℕ i ∸ toℕ j)))))
-- -- --            ≡⟨ bigOpExt (λ i j → cast· i (step1 i j)) ⟩
-- -- --              ∑ (λ i → cast· i (foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ toℕ i))) → x (toℕ i) ·G (cast· j (y (toℕ j) ·G z (n ∸ toℕ i ∸ toℕ j))))))
-- -- --            ≡⟨ bigOpExt (λ i k → cast· i (bigOpExtGen (λ j → cast·G-right (x (toℕ i)) (y (toℕ j) ·G z (n ∸ toℕ i ∸ toℕ j)) (helper j)) k)) ⟩
-- -- --              ∑ (λ (i : Fin (suc n)) → cast· i (foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ toℕ i))) →
-- -- --                                                        cast (cong (toℕ i +ℕ_) (helper j))
-- -- --                                                             (x (toℕ i) ·G (y (toℕ j) ·G z (n ∸ toℕ i ∸ toℕ j))))))
-- -- --            ≡⟨ bigOpExt (λ i k → cast· i (bigOpExtGen (λ j l → cast (cong (toℕ i +ℕ_) (helper j)) (·G-assoc (x (toℕ i)) (y (toℕ j)) (z _) l)) k)) ⟩
-- -- --              ∑ (λ (i : Fin (suc n)) → cast· i (foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ toℕ i))) →
-- -- --                                                        cast (cong (toℕ i +ℕ_) (helper j))
-- -- --                                                             (cast (sym (+-assoc (toℕ i) (toℕ j) (n ∸ toℕ i ∸ toℕ j)))
-- -- --                                                                   ((x (toℕ i) ·G y (toℕ j)) ·G z (n ∸ toℕ i ∸ toℕ j))))))
-- -- --            ≡⟨ bigOpExt (λ i k → cast· i (bigOpExtGen (λ j l → cast-comp ((x (toℕ i) ·G y (toℕ j)) ·G z (n ∸ toℕ i ∸ toℕ j)) (cong (toℕ i +ℕ_) (helper j)) (sym (+-assoc (toℕ i) (toℕ j) (n ∸ toℕ i ∸ toℕ j))) l) k)) ⟩
-- -- --              ∑ (λ (i : Fin (suc n)) → cast· i (foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ toℕ i))) →
-- -- --                                                         cast (helper2 i j)
-- -- --                                                             ((x (toℕ i) ·G y (toℕ j)) ·G z (n ∸ toℕ i ∸ toℕ j)))))
-- -- --            -- ≡⟨ {!!} ⟩
-- -- --            --   ∑ (λ (i : Fin (suc n)) → cast· i (foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ toℕ i))) →
-- -- --            --                                              cast (+-comm (toℕ j) _ ∙ ≤-∸-+-cancel (foo i j))
-- -- --            --                                                   (x (toℕ j) ·G y (toℕ i ∸ toℕ j)) ·G z (n ∸ toℕ i))))
-- -- --            -- ≡⟨ bigOpExt (λ i k → cast· i (final i k)) ⟩
-- -- --            ≡⟨ finalstep ⟩
-- -- --              ∑ (λ (i : Fin (suc n)) → cast· i (foldrFin _+G_ 0G (λ (j : Fin (suc (toℕ i))) →
-- -- --                                                         cast· j (x (toℕ j) ·G y (toℕ i ∸ toℕ j)) ·G z (n ∸ toℕ i))))

-- -- --            ≡⟨ bigOpExt (λ i j → cast· i (laststepGen (suc (toℕ i)) (n ∸ toℕ i) (toℕ i) (z (n ∸ toℕ i))
-- -- --                                                      (λ j → cast· j (x (toℕ j) ·G y (toℕ i ∸ toℕ j))) (~ j))) ⟩
-- -- --              ∑ (λ (i : Fin (suc n)) → cast· i (foldrFin _+G_ 0G (λ (j : Fin (suc (toℕ i))) → cast· j (x (toℕ j) ·G y (toℕ i ∸ toℕ j)))
-- -- --                                              ·G z (n ∸ toℕ i)))
-- -- --            ≡⟨ refl ⟩
-- -- --              (((x , hx) ·⊕G (y , hy)) ·⊕G (z , hz)) .fst n ∎
-- -- --       where
-- -- --       open MonoidBigOp (Group→Monoid (AbGroup→Group (G n))) renaming (bigOp to ∑)

-- -- --       helper2 : {n : ℕ} (i : Fin (suc n)) → (j : Fin (suc (n ∸ toℕ i))) → toℕ i +ℕ toℕ j +ℕ (n ∸ toℕ i ∸ toℕ j) ≡ toℕ i +ℕ (n ∸ toℕ i)
-- -- --       helper2 {n} i j = (sym (+-assoc (toℕ i) (toℕ j) (n ∸ toℕ i ∸ toℕ j)) ∙ cong (toℕ i +ℕ_) (helper j))

-- -- --       finalstepGen : (n : ℕ)
-- -- --                      (p : {n : ℕ} (i : Fin (suc n)) → toℕ i +ℕ (n ∸ toℕ i) ≡ n)
-- -- --                      (q : {n : ℕ} (i : Fin (suc n)) (j : Fin (suc (n ∸ toℕ i))) → toℕ i +ℕ toℕ j +ℕ (n ∸ toℕ i ∸ toℕ j) ≡ toℕ i +ℕ (n ∸ toℕ i))
-- -- --                      (r : {n : ℕ} (i : Fin (suc n)) (j : Fin (suc (toℕ i))) → toℕ j +ℕ (toℕ i ∸ toℕ j) ≡ toℕ i)
-- -- --                 →
-- -- --                   foldrFin _+G_ 0G
-- -- --                     (λ (i : Fin (suc n)) → cast (p i) (foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ toℕ i))) →
-- -- --                                                         cast (q i j) ((x (toℕ i) ·G y (toℕ j)) ·G z (n ∸ toℕ i ∸ toℕ j)))))
-- -- --                 ≡ foldrFin _+G_ 0G
-- -- --                     (λ (i : Fin (suc n)) → cast (p i) (foldrFin _+G_ 0G (λ (j : Fin (suc (toℕ i))) →
-- -- --                                                         cast (r i j) (x (toℕ j) ·G y (toℕ i ∸ toℕ j)) ·G z (n ∸ toℕ i))))
-- -- --       finalstepGen n p q r = goal
-- -- --         where
-- -- --         goal : cast (p zero) (cast (q zero zero) ((x 0 ·G y 0) ·G z n)
-- -- --                  +G foldrFin _+G_ 0G (λ i → cast (q zero (suc i)) ((x 0 ·G y (suc (toℕ i))) ·G z (n ∸ suc (toℕ i)))))
-- -- --              +G foldrFin _+G_ 0G
-- -- --                   (λ (i : Fin n) →
-- -- --                      cast (p (suc i))
-- -- --                           (foldrFin _+G_ 0G
-- -- --                              (λ j → cast (q (suc i) j) ((x (toℕ (suc i)) ·G y (toℕ j)) ·G z (n ∸ toℕ (suc i) ∸ toℕ j)))))
-- -- --              ≡ cast (p zero) ((cast (r zero zero) (x 0 ·G y 0) ·G z n) +G 0G)
-- -- --              +G foldrFin _+G_ 0G
-- -- --                   (λ (i : Fin n) →
-- -- --                      cast (p (suc i))
-- -- --                           (foldrFin _+G_ 0G
-- -- --                              (λ j → cast (r (suc i) j) (x (toℕ j) ·G y (toℕ (suc i) ∸ toℕ j)) ·G z (n ∸ toℕ (suc i)))))
-- -- --         goal = {!!}

-- -- --         -- Have used ∑split here
-- -- --         suff : (n : ℕ) →
-- -- --               foldrFin _+G_ 0G
-- -- --                   (λ (i : Fin n) → cast (q zero (suc i)) ((x 0 ·G y (suc (toℕ i))) ·G z (n ∸ suc (toℕ i))) +G
-- -- --                      cast (p (suc i))
-- -- --                           (foldrFin _+G_ 0G
-- -- --                              (λ (j : Fin (suc (n ∸ suc (toℕ i)))) → cast (q (suc i) j) ((x (suc (toℕ i)) ·G y (toℕ j)) ·G z (n ∸ suc (toℕ i) ∸ toℕ j)))))
-- -- --              ≡ foldrFin _+G_ 0G
-- -- --                   (λ (i : Fin n) →
-- -- --                      cast (p (suc i))
-- -- --                           (foldrFin _+G_ 0G
-- -- --                              (λ (j : Fin (suc (suc (toℕ i)))) → cast (r (suc i) j) (x (toℕ j) ·G y (suc (toℕ i) ∸ toℕ j)) ·G z (n ∸ suc (toℕ i)))))
-- -- --         suff zero = refl
-- -- --         suff (suc n) =
-- -- --           let ih : foldrFin _+G_ 0G (λ (i : Fin n) → cast (q zero (suc i)) ((x 0 ·G y (suc (toℕ i))) ·G z (n ∸ suc (toℕ i)))
-- -- --                                         +G cast (p (suc i))
-- -- --                                                 (foldrFin _+G_ 0G (λ j → cast (q (suc i) j) ((x (suc (toℕ i)) ·G y (toℕ j)) ·G z (n ∸ suc (toℕ i) ∸ toℕ j)))))
-- -- --                      ≡ _
-- -- --               ih = suff n
-- -- --           in
-- -- --           foldrFin _+G_ 0G
-- -- --             (λ (i : Fin (suc n)) → cast (q zero (suc i)) ((x 0 ·G y (suc (toℕ i))) ·G z (suc n ∸ suc (toℕ i)))
-- -- --                 +G cast (p (suc i)) (foldrFin _+G_ 0G (λ j → cast (q (suc i) j) ((x (toℕ (suc i)) ·G y (toℕ j)) ·G z (suc n ∸ toℕ (suc i) ∸ toℕ j)))))
-- -- --             ≡⟨ refl ⟩
-- -- --           (_ +G foldrFin _+G_ 0G (λ (i : Fin n) → cast (q zero (suc (suc i))) ((x 0 ·G y (suc (toℕ (suc i)))) ·G z (suc n ∸ suc (toℕ (suc i))))
-- -- --                                      +G cast (p (suc (suc i))) (foldrFin _+G_ 0G (λ j → cast (q (suc (suc i)) j) ((x (toℕ (suc (suc i))) ·G y (toℕ j)) ·G z (suc n ∸ toℕ (suc (suc i)) ∸ toℕ j))))))
-- -- --             ≡⟨ {!!} ⟩
-- -- --           {!!}
-- -- --             ≡⟨ {!!} ⟩
-- -- --           {!!} ∎

-- -- --       finalstep : ∑ (λ (i : Fin (suc n)) → cast· i (foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ toℕ i))) →
-- -- --                                                         cast (helper2 i j)
-- -- --                                                              ((x (toℕ i) ·G y (toℕ j)) ·G z (n ∸ toℕ i ∸ toℕ j)))))
-- -- --                 ≡ ∑ (λ (i : Fin (suc n)) → cast· i (foldrFin _+G_ 0G (λ (j : Fin (suc (toℕ i))) →
-- -- --                                                         cast· j (x (toℕ j) ·G y (toℕ i ∸ toℕ j)) ·G z (n ∸ toℕ i))))
-- -- --       finalstep = finalstepGen n helper helper2 (λ i j → helper j)



-- -- --       -- finalGen2 : (n m : ℕ) (h : m < suc n)
-- -- --       --            (p : (j : Fin (suc (n ∸ m))) → m +ℕ toℕ j +ℕ (n ∸ m ∸ toℕ j) ≡ m +ℕ (n ∸ m))
-- -- --       --            (q : (j : Fin (suc m)) → toℕ j +ℕ (m ∸ toℕ j) ≡ m)
-- -- --       --       → foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ m))) →
-- -- --       --           cast (p j) ((x m ·G y (toℕ j)) ·G z (n ∸ m ∸ toℕ j)))
-- -- --       --       ≡ foldrFin _+G_ 0G (λ (j : Fin (suc m)) →
-- -- --       --           cast (q j) (x (toℕ j) ·G y (m ∸ toℕ j)) ·G z (n ∸ m))
-- -- --       -- finalGen2 zero zero h p q = {!!}
-- -- --       -- finalGen2 zero (suc m) h p q = ⊥-rec (¬-<-zero (pred-≤-pred h))
-- -- --       -- finalGen2 (suc n) zero h p q = goal
-- -- --       --   where
-- -- --       --   goal : foldrFin _+G_ 0G
-- -- --       --            (λ j → cast (p j) ((x zero ·G y (toℕ j)) ·G z (suc n ∸ zero ∸ toℕ j)))
-- -- --       --        ≡ foldrFin _+G_ 0G
-- -- --       --            (λ j → cast (q j) (x (toℕ j) ·G y (zero ∸ toℕ j)) ·G z (suc n ∸ zero))
-- -- --       --   goal = {!!}
-- -- --       -- finalGen2 (suc n) (suc m) h p q = {!!}

-- -- --       final : (i : Fin (suc n))
-- -- --             → foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ toℕ i))) →
-- -- --                 cast (helper2 i j) ((x (toℕ i) ·G y (toℕ j)) ·G z (n ∸ toℕ i ∸ toℕ j)))
-- -- --             ≡ foldrFin _+G_ 0G (λ (j : Fin (suc (toℕ i))) →
-- -- --                 cast (helper j) (x (toℕ j) ·G y (toℕ i ∸ toℕ j)) ·G z (n ∸ toℕ i))
-- -- --       final i = {!!} -- finalGen2 n (toℕ i) (toℕ<n i) (helper2 i) helper



-- -- --       -- Kan vi vända på den?
-- -- --       -- helper3 : (i : Fin (suc n)) (j : Fin (suc (n ∸ toℕ i))) → toℕ j +ℕ (n ∸ toℕ i ∸ toℕ j) +ℕ (n ∸ (n ∸ toℕ i)) ≡ {!!}
-- -- --       -- helper3 i j = {!!}

-- -- --       -- revstep : ∑ (λ (i : Fin (suc n)) →
-- -- --       --             cast· i (foldrFin _+G_ 0G (λ (j : Fin (suc (toℕ i))) →
-- -- --       --                                        cast· j (x (toℕ j) ·G y (toℕ i ∸ toℕ j)) ·G z (n ∸ toℕ i))))
-- -- --       --         ≡ ∑ (λ (i : Fin (suc n)) →
-- -- --       --              cast· {!!} (foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ toℕ i))) →
-- -- --       --                                           cast (helper3 i j) ((x (toℕ j) ·G y ((n ∸ toℕ i) ∸ toℕ j)) ·G z (n ∸ (n ∸ toℕ i))))))
-- -- --       -- revstep = {!!}


-- -- --       -- foo : (i : Fin (suc n)) (j : Fin (suc (n ∸ toℕ i))) → toℕ j ≤ toℕ i
-- -- --       -- foo i j = {!!}

-- -- --       -- foo2 : (i : Fin (suc n)) (j : Fin (suc (toℕ i))) → toℕ j ≤ toℕ i
-- -- --       -- foo2 i j = {!!}

-- -- --       step1Gen : (m n k : ℕ)
-- -- --                  (x : G n .fst)
-- -- --                  (V : Fin m → G k .fst)
-- -- --                   → x ·G foldrFin _+G_ 0G V ≡ foldrFin _+G_ 0G (λ j → x ·G V j)
-- -- --       step1Gen zero n k x V = ·G-l0g x
-- -- --       step1Gen (suc m) n k x V =
-- -- --         x ·G (V zero +G foldrFin _+G_ 0G (V ∘ suc)) ≡⟨ ·G-distRight x (V zero) (foldrFin _+G_ 0G (V ∘ suc)) ⟩
-- -- --         (x ·G V zero) +G (x ·G foldrFin _+G_ 0G (V ∘ suc)) ≡⟨ (λ i → (x ·G V zero) +G step1Gen m n k x (V ∘ suc) i) ⟩
-- -- --         (x ·G V zero) +G foldrFin _+G_ 0G (λ i → x ·G V (suc i)) ∎

-- -- --       step1 : (i : Fin (suc n)) → x (toℕ i) ·G foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ toℕ i))) → cast· j (y (toℕ j) ·G z (n ∸ toℕ i ∸ toℕ j)))
-- -- --                                 ≡ foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ toℕ i))) → x (toℕ i) ·G (cast· j (y (toℕ j) ·G z (n ∸ toℕ i ∸ toℕ j))))
-- -- --       step1 i = step1Gen _ _ _ (x (toℕ i)) (λ j → cast· j (y (toℕ j) ·G z (n ∸ toℕ i ∸ toℕ j)))

-- -- --       laststepGen : (m n k : ℕ)
-- -- --                  (x : G n .fst)
-- -- --                  (V : Fin m → G k .fst)
-- -- --                   → foldrFin _+G_ 0G V ·G x ≡ foldrFin _+G_ 0G (λ j → V j ·G x)
-- -- --       laststepGen zero n k x V = ·G-r0g x
-- -- --       laststepGen (suc m) n k x V =
-- -- --         (V zero +G foldrFin _+G_ 0G (V ∘ suc)) ·G x ≡⟨ ·G-distLeft (V zero) (foldrFin _+G_ 0G (V ∘ suc)) x ⟩
-- -- --         (V zero ·G x) +G (foldrFin _+G_ 0G (V ∘ suc) ·G x) ≡⟨ (λ i → (V zero ·G x) +G laststepGen m n k x (V ∘ suc) i) ⟩
-- -- --         (V zero ·G x) +G foldrFin _+G_ 0G (λ i → V (suc i) ·G x) ∎

-- -- --       step2 : (i : Fin (suc n))
-- -- --             → foldrFin _+G_ 0G (λ j → x (toℕ i) ·G (cast· j (y (toℕ j) ·G z _)))
-- -- --             ≡ foldrFin _+G_ 0G (λ j → cast (cong (toℕ i +ℕ_) (helper j)) (x (toℕ i) ·G (y (toℕ j) ·G z _)))
-- -- --       step2 i = bigOpExtGen (λ j → cast·G-right (x (toℕ i)) (y (toℕ j) ·G z (n ∸ toℕ i ∸ toℕ j)) (helper j))


-- -- --       -- finalGen2 : (n m : ℕ) (h : m < suc n)
-- -- --       --            (p : (j : Fin (suc (n ∸ m))) → m +ℕ toℕ j +ℕ (n ∸ m ∸ toℕ j) ≡ m +ℕ (n ∸ m))
-- -- --       --            (q : (j : Fin (suc m)) → toℕ j +ℕ (m ∸ toℕ j) ≡ m)
-- -- --       --       → foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ m))) →
-- -- --       --           cast (p j) ((x m ·G y (toℕ j)) ·G z (n ∸ m ∸ toℕ j)))
-- -- --       --       ≡ foldrFin _+G_ 0G (λ (j : Fin (suc m)) →
-- -- --       --           cast (q j) (x (toℕ j) ·G y (m ∸ toℕ j)) ·G z (n ∸ m))
-- -- --       -- finalGen2 zero zero h p q = {!!}
-- -- --       -- finalGen2 zero (suc m) h p q = ⊥-rec (¬-<-zero (pred-≤-pred h))
-- -- --       -- finalGen2 (suc n) zero h p q = goal
-- -- --       --   where
-- -- --       --   goal : foldrFin _+G_ 0G
-- -- --       --            (λ j → cast (p j) ((x zero ·G y (toℕ j)) ·G z (suc n ∸ zero ∸ toℕ j)))
-- -- --       --        ≡ foldrFin _+G_ 0G
-- -- --       --            (λ j → cast (q j) (x (toℕ j) ·G y (zero ∸ toℕ j)) ·G z (suc n ∸ zero))
-- -- --       --   goal = {!!}
-- -- --       -- finalGen2 (suc n) (suc m) h p q = {!!}

-- -- --       -- finalGen : (m n : ℕ) (h : m < suc n)
-- -- --       --            (p : (j : Fin (suc (n ∸ m))) → m +ℕ toℕ j +ℕ (n ∸ m ∸ toℕ j) ≡ m +ℕ (n ∸ m))
-- -- --       --            (q : (j : Fin (suc m)) → toℕ j +ℕ (m ∸ toℕ j) ≡ m)
-- -- --       --       → foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ m))) →
-- -- --       --           cast (p j) ((x m ·G y (toℕ j)) ·G z (n ∸ m ∸ toℕ j)))
-- -- --       --       ≡ foldrFin _+G_ 0G (λ (j : Fin (suc m)) →
-- -- --       --           cast (q j) (x (toℕ j) ·G y (m ∸ toℕ j)) ·G z (n ∸ m))
-- -- --       -- finalGen 0 n h p q = cong₂ _+G_ {!!} rem0
-- -- --       --   where
-- -- --       --   rem0 : foldrFin _+G_ 0G (λ j →
-- -- --       --            cast (p (suc j)) ((x zero ·G y (suc (toℕ j))) ·G z (n ∸ suc (toℕ j)))) ≡ 0G
-- -- --       --   rem0 = {!!}
-- -- --       -- finalGen (suc m) n h p q = {!!}

-- -- --       -- final : (i : Fin (suc n))
-- -- --       --       → foldrFin _+G_ 0G (λ (j : Fin (suc (n ∸ toℕ i))) →
-- -- --       --           cast (helper2 i j) ((x (toℕ i) ·G y (toℕ j)) ·G z (n ∸ toℕ i ∸ toℕ j)))
-- -- --       --       ≡ foldrFin _+G_ 0G (λ (j : Fin (suc (toℕ i))) →
-- -- --       --           cast (helper j) (x (toℕ j) ·G y (toℕ i ∸ toℕ j)) ·G z (n ∸ toℕ i))
-- -- --       -- final i = {!!} -- finalGen2 n (toℕ i) (toℕ<n i) (helper2 i) helper







-- -- -- {-    rem 0 = cong (λ x → G 0 .snd ._+G_ x (G 0 .snd .0g)) goal
-- -- --       where
-- -- --       0G = G 0 .snd .0g
-- -- --       _+G0_ = G 0 .snd ._+G_
-- -- --       rem0 : (x : G 0 .fst) → x +G0 0G ≡ x
-- -- --       rem0 = rid (G 0 .snd)

-- -- --       goal : cast· zero (x 0 ·G (cast· zero (y 0 ·G z 0) +G0 0G))
-- -- --            ≡ cast· zero ((cast· zero (x 0 ·G y 0) +G0 0G) ·G z 0)
-- -- --       goal = cast· zero (x 0 ·G (cast· zero (y 0 ·G z 0) +G0 0G))
-- -- --            ≡⟨ cong (λ w → cast· zero (x 0 ·G w)) (rem0 _) ⟩
-- -- --            cast· zero (x 0 ·G (cast· zero (y 0 ·G z 0)))
-- -- --            ≡⟨ (λ i → cast·0≡ (x 0 ·G cast·0≡ (y 0 ·G z 0) i) i) ⟩
-- -- --            x 0 ·G (y 0 ·G z 0)
-- -- --            ≡⟨ ·G-assoc (x 0) (y 0) (z 0) ⟩
-- -- --            subst (λ w → G w .fst) (sym (+-assoc 0 0 0)) ((x 0 ·G y 0) ·G z 0)
-- -- --            ≡⟨ transportRefl _ ⟩
-- -- --            (x 0 ·G y 0) ·G z 0
-- -- --            ≡⟨ (λ i → cast·0≡ (cast·0≡ (x 0 ·G y 0) (~ i) ·G z 0) (~ i)) ⟩
-- -- --            cast· zero ((cast· zero (x 0 ·G y 0)) ·G z 0)
-- -- --            ≡⟨ cong (λ w → cast· zero (w ·G z 0)) (sym (rem0 _)) ⟩
-- -- --            cast· zero ((cast· zero (x 0 ·G y 0) +G0 0G) ·G z 0) ∎

-- -- --     rem (suc n) = goal
-- -- --       where
-- -- --       open MonoidBigOp (Group→Monoid (AbGroup→Group (G (suc n)))) renaming (bigOp to ∑)
-- -- --       open MonoidBigOp (Group→Monoid (AbGroup→Group (G ( n)))) renaming (bigOp to ∑')

-- -- --       goal : ((x , hx) ·⊕G ((y , hy) ·⊕G (z , hz))) .fst (suc n) ≡ (((x , hx) ·⊕G (y , hy)) ·⊕G (z , hz)) .fst (suc n)
-- -- --       goal =
-- -- -- ---    p n = ∑ (λ (i : Fin (suc n)) → cast· i (x (toℕ i) ·G y (n ∸ toℕ i)))

-- -- --             --   snd (G (suc n)) ._+G_
-- -- --             --     (cast· zero (x 0 ·G snd (G (suc n)) ._+G_ (cast· zero (y 0 ·G z (suc n)))
-- -- --             --                                               (snd (G (suc n)) ._+G_ (cast· (suc zero) (y 1 ·G z n))
-- -- --             --                                               (∑ (λ i → cast· i (y (toℕ i) ·G z (suc n ∸ toℕ i)))))))
-- -- --             --     (snd (G (suc n)) ._+G_
-- -- --             --       (cast· (suc zero) (x 1 ·G snd (G n) ._+G_
-- -- --             --                                   (cast· zero (y 0 ·G z n))
-- -- --             --                                   (∑' (λ i → cast· (suc i) (y (suc (toℕ i)) ·G z (n ∸ suc (toℕ i)))))))
-- -- --             --       (foldrFin (snd (G (suc n)) ._+G_) (snd (G (suc n)) .0g)
-- -- --             --         (λ i → cast· (suc (suc i)) (x (suc (suc (toℕ i))) ·G snd (G (n ∸ suc (toℕ i))) ._+G_ (cast· zero (y 0 ·G z (n ∸ suc (toℕ i))))
-- -- --             -- (foldrFin (snd (G (n ∸ suc (toℕ i))) ._+G_)
-- -- --             --    (snd (G (n ∸ suc (toℕ i))) .0g)
-- -- --             --    (λ j → cast· (suc j) (y (suc (toℕ j)) ·G z (n ∸ suc (toℕ i) ∸ suc (toℕ j)))))))))
-- -- -- -}

-- -- --   ·⊕G-distRight : (x y z : ⊕G) → x ·⊕G (y +⊕G z) ≡ (x ·⊕G y) +⊕G (x ·⊕G z)
-- -- --   ·⊕G-distRight (x , hx) (y , hy) (z , hz) = Σ≡Prop (λ _ → squash) (funExt rem)
-- -- --     where
-- -- --     rem : (n : ℕ) → ((x , hx) ·⊕G ((y , hy) +⊕G (z , hz))) .fst n ≡
-- -- --                     (((x , hx) ·⊕G (y , hy)) +⊕G ((x , hx) ·⊕G (z , hz))) .fst n
-- -- --     rem n = ∑ (λ i → cast· i (x (toℕ i) ·G (y _ +G z _)))
-- -- --           ≡⟨ bigOpExt (λ i j → cast· i (·G-distRight (x (toℕ i)) (y _) (z _) j)) ⟩
-- -- --             ∑ (λ i → cast· i ((x (toℕ i) ·G y _) +G (x (toℕ i) ·G z _)))
-- -- --           ≡⟨ bigOpExt (λ i → help (helper i) (x (toℕ i) ·G y _) (x (toℕ i) ·G z _)) ⟩
-- -- --             ∑ (λ i → cast· i (x (toℕ i) ·G y _) +G cast· i (x (toℕ i) ·G z _))
-- -- --           ≡⟨ bigOpSplit (comm (G n .snd)) (λ i → cast· i ((x (toℕ i) ·G y _)))
-- -- --                                           (λ i → cast· i (x (toℕ i) ·G z _)) ⟩
-- -- --              (∑ (λ i → cast· i ((x (toℕ i) ·G y _)))
-- -- --           +G (∑ (λ i → cast· i ((x (toℕ i) ·G z _))))) ∎
-- -- --        where
-- -- --        open MonoidBigOp (Group→Monoid (AbGroup→Group (G n))) renaming (bigOp to ∑)

-- -- --        help : {m n : ℕ} (p : m ≡ n) (x y : G m .fst) → cast p (x +G y) ≡ cast p x +G cast p y
-- -- --        help p x y = J (λ z q → cast q (x +G y) ≡ cast q x +G cast q y)
-- -- --                       (transportRefl _ ∙ (λ i → transportRefl x (~ i) +G transportRefl y (~ i))) p

-- -- --   ·⊕G-distLeft : (x y z : ⊕G) → (x +⊕G y) ·⊕G z ≡ (x ·⊕G z) +⊕G (y ·⊕G z)
-- -- --   ·⊕G-distLeft (x , hx) (y , hy) (z , hz) = Σ≡Prop (λ _ → squash) (funExt rem)
-- -- --     where
-- -- --     rem : (n : ℕ) → (((x , hx) +⊕G (y , hy)) ·⊕G (z , hz)) .fst n ≡
-- -- --                     (((x , hx) ·⊕G (z , hz)) +⊕G ((y , hy) ·⊕G (z , hz))) .fst n
-- -- --     rem n = ∑ (λ i → cast· i ((x (toℕ i) +G y (toℕ i)) ·G z _))
-- -- --           ≡⟨ bigOpExt (λ i j → cast· i (·G-distLeft (x (toℕ i)) (y (toℕ i)) (z _) j)) ⟩
-- -- --             ∑ (λ i → cast· i ((x (toℕ i) ·G z _) +G (y (toℕ i) ·G z _)))
-- -- --           ≡⟨ bigOpExt (λ i → help (helper i) (x (toℕ i) ·G z _) (y (toℕ i) ·G z _)) ⟩
-- -- --             ∑ (λ i → cast· i (x (toℕ i) ·G z _) +G cast· i (y (toℕ i) ·G z _))
-- -- --           ≡⟨ bigOpSplit (comm (G n .snd)) (λ i → cast· i (x (toℕ i) ·G z _))
-- -- --                                           (λ i → cast· i (y (toℕ i) ·G z _)) ⟩
-- -- --              (∑ (λ i → cast· i ((x (toℕ i) ·G z _)))
-- -- --           +G (∑ (λ i → cast· i ((y (toℕ i) ·G z _))))) ∎
-- -- --        where
-- -- --        open MonoidBigOp (Group→Monoid (AbGroup→Group (G n))) renaming (bigOp to ∑)

-- -- --        help : {m n : ℕ} (p : m ≡ n) (x y : G m .fst) → cast p (x +G y) ≡ cast p x +G cast p y
-- -- --        help p x y = J (λ z q → cast q (x +G y) ≡ cast q x +G cast q y)
-- -- --                       (transportRefl _ ∙ (λ i → transportRefl x (~ i) +G transportRefl y (~ i))) p

-- -- --   R : Ring (ℓ-max (ℓ-suc ℓ-zero) ℓ)
-- -- --   fst R = ⊕G
-- -- --   0r (snd R) = 0⊕G
-- -- --   1r (snd R) = 1⊕G
-- -- --   _+_ (snd R) = _+⊕G_
-- -- --   _·_ (snd R) = _·⊕G_
-- -- --   - snd R = -⊕G_
-- -- --   +IsAbGroup (isRing (snd R)) = makeIsAbGroup isSet⊕G +⊕G-assoc +⊕G-rid +-⊕G +⊕G-comm
-- -- --   ·IsMonoid (isRing (snd R)) = makeIsMonoid isSet⊕G ·⊕G-assoc ·⊕G-rid ·⊕G-lid
-- -- --   fst (dist (isRing (snd R)) x y z) = ·⊕G-distRight x y z
-- -- --   snd (dist (isRing (snd R)) x y z) = ·⊕G-distLeft x y z
