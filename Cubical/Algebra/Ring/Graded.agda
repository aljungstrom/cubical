-- TODO: uncomment once finished!
-- {-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.Graded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary.Base

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.FinData hiding (_==_ ; snotz)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim ; rec to ⊥-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Sum.Base hiding (map)

open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥-rec)

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
      let rem1 : i < x
          rem1 = Hx h2
          rem2 : j < y
          rem2 = Hy h3
          rem3 : i ·ℕ j ≡ z
          rem3 = h1
          apa : i ·ℕ y < x ·ℕ y
          apa = {!!}
          suff : i ·ℕ j < x ·ℕ y
          suff = {!!}
          goal : z < x ·ℕ y
          goal = subst (λ a → a < x ·ℕ y) rem3 suff
      in goal


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

  ⊕G : Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  ⊕G = Σ[ f ∈ ((i : ℕ) → G i .fst) ]
          ∃[ I ∈ FinSubsetℕ ] ({j : ℕ} → (j ∉ I .fst) → f j ≡ 0G)

  isSet⊕G : isSet ⊕G
  isSet⊕G = isSetΣ (isSetΠ (λ i → is-set (G i .snd))) λ _ → isProp→isSet squash

  0⊕G : ⊕G
  0⊕G = (λ _ → 0G) , ∣ ∅ , (λ _ → refl) ∣

  _+⊕G_ : ⊕G → ⊕G → ⊕G
  (f , Hf) +⊕G (g , Hg) = (λ i → f i +G g i) , map2 (λ X Y → (fst X ∪ fst Y) , λ {j} H →
    let hf : f j ≡ 0G
        hf  = snd X (∉∪ j (fst X) (fst Y) H .fst)
        hg : g j ≡ 0G
        hg  = snd Y (∉∪ j (fst X) (fst Y) H .snd)
    in (λ i → hf i +G hg i) ∙ (rid (G j .snd) _)) Hf Hg

  +⊕G-rid : (x : ⊕G) → x +⊕G 0⊕G ≡ x
  +⊕G-rid (x , _) = Σ≡Prop (λ _ → squash) (funExt (λ i → rid (G i .snd) _))

  +⊕G-comm : (x y : ⊕G) → x +⊕G y ≡ y +⊕G x
  +⊕G-comm (x , _) (y , _) = Σ≡Prop (λ _ → squash) (funExt (λ i → comm (G i .snd) _ _))

  +⊕G-assoc : (x y z : ⊕G) → x +⊕G (y +⊕G z) ≡ (x +⊕G y) +⊕G z
  +⊕G-assoc (x , _) (y , _) (z , _) = Σ≡Prop (λ _ → squash) (funExt (λ i → assoc (G i .snd) _ _ _))

  -⊕G_ : ⊕G → ⊕G
  -⊕G (f , Hf) = (λ i → G i .snd .-_ (f i))
               , map (λ X → X .fst , λ {j} H → cong (λ z → G j .snd .-_ z) (X .snd H)
                                             ∙ GroupTheory.inv1g (AbGroup→Group (G j))) Hf

  +-⊕G : (x : ⊕G) → (x +⊕G (-⊕G x)) ≡ 0⊕G
  +-⊕G (x , _) = Σ≡Prop (λ _ → squash) (funExt (λ i → invr (G i .snd) _))

  ⊕G-AbGroup : AbGroup (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  fst ⊕G-AbGroup = ⊕G
  0g (snd ⊕G-AbGroup) = 0⊕G
  _+G'_ (snd ⊕G-AbGroup) = _+⊕G_
  - snd ⊕G-AbGroup = -⊕G_
  isAbGroup (snd ⊕G-AbGroup) = makeIsAbGroup isSet⊕G +⊕G-assoc +⊕G-rid +-⊕G +⊕G-comm

  -- End of direct sum of groups
  1⊕G' : (i : ℕ) → G i .fst
  1⊕G' 0 = 1G
  1⊕G' i = 0G

  1⊕G : ⊕G
  1⊕G = (1⊕G' , ∣ X , hX ∣)
     where
     X : FinSubsetℕ
     X = X' , hX'
       where
       X' : ℙ ℕ
       X' 0 = Unit , isPropUnit
       X' _ = ⊥ , isProp⊥

       hX' : isFiniteSubsetℕ X'
       hX' = ∣ 1 , foo ∣
         where
         foo : {x : ℕ} → x ∈ X' → x < 1
         foo {zero} hx = 0 , refl

     hX : {j : ℕ} → j ∉ X .fst → 1⊕G' j ≡ 0G
     hX {zero} j∉X = ⊥-elim (j∉X tt)
     hX {suc j} j∉X = refl

  abstract
    helper : {n : ℕ} → (i : Fin (suc n)) → toℕ i +ℕ (n ∸ toℕ i) ≡ n
    helper {n} i = +-comm (toℕ i) _ ∙ ≤-∸-+-cancel {m = toℕ i} (pred-≤-pred (toℕ<n i))  -- +-comm (suc (toℕ i)) _ ∙ ≤-∸-+-cancel (toℕ<n i)

  cast : {m n : ℕ} → m ≡ n → G m .fst → G n .fst
  cast p = subst (λ x → G x .fst) p

  cast· : {n : ℕ} → (i : Fin (suc n)) → G (toℕ i +ℕ (n ∸ toℕ i)) .fst → G n .fst
  cast· i = cast (helper i)

  cast·G-right : {m n n' : ℕ} (x : G m .fst) (y : G n .fst) (p : n ≡ n')
               → x ·G cast p y ≡ cast (cong (m +ℕ_) p) (x ·G y)
  cast·G-right {m} x y p = J (λ z q → x ·G cast q y ≡ cast (cong (m +ℕ_) q) (x ·G y)) (cong (x ·G_) (transportRefl y) ∙ sym (transportRefl _)) p

  cast·G-left : {m m' n : ℕ} (x : G m .fst) (y : G n .fst) (p : m ≡ m')
              → cast p x ·G y ≡ cast (cong (_+ℕ n) p) (x ·G y)
  cast·G-left x y p = {!!}


  cast≡ : {m n : ℕ} → (p : m ≡ n) (x : (i : ℕ) → G i .fst) → cast p (x m) ≡ x n
  cast≡ p x = J (λ y q → cast q (x _) ≡ x _) (transportRefl _) p

  cast·≡ : {n : ℕ} → (p : n ≡ n) → (x : G n .fst) → cast p x ≡ x
  cast·≡ {n} p x = subst (λ y → cast y x ≡ x) prefl (transportRefl x)
    where
    prefl : refl ≡ p
    prefl = isSetℕ n n refl p

  cast·0≡ : {n : ℕ} → (x : G n .fst) → cast· zero x ≡ x
  cast·0≡ {n} x = cast·≡ (helper zero) x

  _·⊕G_ : ⊕G → ⊕G → ⊕G
  (x , Hx) ·⊕G (y , Hy) = p , q
    where
    p : (n : ℕ) → G n .fst
--    p 0 = x 0 ·G y 0
    p n = ∑ (λ (i : Fin (suc n)) → cast· i (x (toℕ i) ·G y (n ∸ toℕ i)))
      where
      open MonoidBigOp (Group→Monoid (AbGroup→Group (G n))) renaming (bigOp to ∑)

    postulate
      q : ∃[ I ∈ FinSubsetℕ ] ({j : ℕ} → j ∉ I .fst → p j ≡ 0G)
--    q = map2 (λ { (I , hI) (J , hJ) → (I Π J) , {!!}}) Hx Hy

  -- cast≡Gen : {m n : ℕ} → (p : m ≡ n) (x : G m .fst) (y : G n .fst) (q : PathP (λ i → G (p i) .fst) x y) → cast p x ≡ y
  -- cast≡Gen p x = {!!}

  -- Algebraic properties of ·⊕G

  ·⊕G-rid : (x : ⊕G) → x ·⊕G 1⊕G ≡ x
  ·⊕G-rid (x , h) = Σ≡Prop (λ _ → squash) (funExt rem)
    where
    rem : (n : ℕ) → ((x , h) ·⊕G 1⊕G) .fst n ≡ x n
    rem n = goal
      where
      open MonoidBigOp (Group→Monoid (AbGroup→Group (G n))) renaming (bigOp to ∑)

      goal : (∑ λ i → cast· i (x (toℕ i) ·G 1⊕G' _)) ≡ x n
      goal = (∑ λ i → cast· i (x (toℕ i) ·G 1⊕G' _))
        ≡⟨ bigOpLast (λ i → cast· i (x (toℕ i) ·G 1⊕G' _)) ⟩
             (∑ ((λ i → cast· i (x (toℕ i) ·G 1⊕G' _)) ∘ weakenFin)) +G
             cast· (fromℕ n) (x (toℕ (fromℕ n)) ·G 1⊕G' _)
        ≡⟨ (λ i → rem0 i +G cast· (fromℕ n) (x (toℕ (fromℕ n)) ·G 1⊕G' _)) ⟩
             0G +G cast· (fromℕ n) (x (toℕ (fromℕ n)) ·G 1⊕G' _)
        ≡⟨ lid (G n .snd) _ ⟩
             cast· (fromℕ n) (x (toℕ (fromℕ n)) ·G 1⊕G' _)
        ≡⟨ cong (λ a → cast· (fromℕ n) a) (simpl _ _ (cong (n ∸_) (toFromId n) ∙ ∸Cancel n)) ⟩
             cast· (fromℕ n) (x _)
        ≡⟨ cast≡ (helper (fromℕ n)) x ⟩
             x n  ∎
        where
        rem0 : (∑ ((λ i → cast· i (x (toℕ i) ·G 1⊕G' _)) ∘ weakenFin)) ≡ 0G
        rem0 = bigOpExt path ∙ bigOpε n
          where
          rem1 : {n : ℕ} (i : Fin n) → 1⊕G' (suc n ∸ suc (toℕ (weakenFin i))) ≡ 0G
          rem1 zero = refl
          rem1 {suc n} (suc i) = rem1 {n} i

          path : (i : Fin n) → cast· (weakenFin i) (x (toℕ (weakenFin i)) ·G 1⊕G' _) ≡ 0G
          path i = cast· (weakenFin i) (x (toℕ (weakenFin i)) ·G 1⊕G' _)
                 ≡⟨ (λ j → cast· (weakenFin i) (x (toℕ (weakenFin i)) ·G rem1 i j)) ⟩
                   cast· (weakenFin i) (x (toℕ (weakenFin i)) ·G 0G)
                 ≡⟨ (λ j → cast· (weakenFin i) (·G-l0g (x (toℕ (weakenFin i))) j)) ⟩
                   cast· (weakenFin i) 0G
                ≡⟨ cast≡ (helper (weakenFin i)) (λ _ → 0G) ⟩
                   0G ∎

        simpl : (m n : ℕ) → (h : m ≡ 0) → x n ·G 1⊕G' m ≡ x (n +ℕ m)
        simpl zero n h = ·G-rid (x n) ∙ cast≡ (sym (+-zero n)) x
        simpl (suc m) n h = ⊥-rec (snotz h)

  ·⊕G-lid : (x : ⊕G) → 1⊕G ·⊕G x ≡ x
  ·⊕G-lid (x , h) = Σ≡Prop (λ _ → squash) (funExt rem)
    where
    rem : (n : ℕ) → (1⊕G ·⊕G (x , h)) .fst n ≡ x n
    rem n = goal
      where
      open MonoidBigOp (Group→Monoid (AbGroup→Group (G n))) renaming (bigOp to ∑)

      goal : (∑ λ i → cast· i (1⊕G' (toℕ i) ·G x _)) ≡ x n
      goal = (∑ λ i → cast· i (1⊕G' (toℕ i) ·G x (n ∸ toℕ i)))
              ≡⟨ refl ⟩
                cast· zero (1G ·G x n) +G
                (∑ (λ i → cast· (suc i) (1⊕G' (toℕ (suc i)) ·G x (n ∸ toℕ (suc i)))))
              ≡⟨ (λ i → cast· zero (1G ·G x n) +G rem0 i) ⟩
                cast· zero (1G ·G x n) +G 0G
              ≡⟨ rid (G n .snd) (cast· zero (1G ·G x n)) ⟩
              cast· zero (1G ·G x n)
              ≡⟨ cong (cast· zero) (·G-lid (x n)) ⟩
              cast· zero (x n)
             ≡⟨ cast≡ (helper zero) x ⟩
              x n  ∎
        where
        rem0 : ∑ (λ i → cast· (suc i) (1⊕G' (toℕ (suc i)) ·G x (n ∸ toℕ (suc i)))) ≡ 0G
        rem0 = bigOpExt path ∙ bigOpε n
          where
          path : (i : Fin n) → cast· (suc i) (1⊕G' (toℕ (suc i)) ·G x (n ∸ toℕ (suc i))) ≡ 0G
          path i = cong (cast· (suc i)) (·G-r0g (x (n ∸ toℕ (suc i)))) ∙ cast≡ (helper (suc i)) (λ _ → 0G)

  -- TODO: do I really need to do induction here?
  ·⊕G-assoc : (x y z : ⊕G) → x ·⊕G (y ·⊕G z) ≡ (x ·⊕G y) ·⊕G z
  ·⊕G-assoc (x , hx) (y , hy) (z , hz) = {!!}
  {- Σ≡Prop (λ _ → squash) (funExt rem)
    where
    rem : (n : ℕ) → ((x , hx) ·⊕G ((y , hy) ·⊕G (z , hz))) .fst n ≡
                    (((x , hx) ·⊕G (y , hy)) ·⊕G (z , hz)) .fst n
    rem 0 = cong (λ x → G 0 .snd ._+G_ x (G 0 .snd .0g)) goal
      where
      0G = G 0 .snd .0g
      _+G0_ = G 0 .snd ._+G_
      rem0 : (x : G 0 .fst) → x +G0 0G ≡ x
      rem0 = rid (G 0 .snd)

      goal : cast· zero (x 0 ·G (cast· zero (y 0 ·G z 0) +G0 0G))
           ≡ cast· zero ((cast· zero (x 0 ·G y 0) +G0 0G) ·G z 0)
      goal = cast· zero (x 0 ·G (cast· zero (y 0 ·G z 0) +G0 0G))
           ≡⟨ cong (λ w → cast· zero (x 0 ·G w)) (rem0 _) ⟩
           cast· zero (x 0 ·G (cast· zero (y 0 ·G z 0)))
           ≡⟨ (λ i → cast·0≡ (x 0 ·G cast·0≡ (y 0 ·G z 0) i) i) ⟩
           x 0 ·G (y 0 ·G z 0)
           ≡⟨ ·G-assoc (x 0) (y 0) (z 0) ⟩
           subst (λ w → G w .fst) (sym (+-assoc 0 0 0)) ((x 0 ·G y 0) ·G z 0)
           ≡⟨ transportRefl _ ⟩
           (x 0 ·G y 0) ·G z 0
           ≡⟨ (λ i → cast·0≡ (cast·0≡ (x 0 ·G y 0) (~ i) ·G z 0) (~ i)) ⟩
           cast· zero ((cast· zero (x 0 ·G y 0)) ·G z 0)
           ≡⟨ cong (λ w → cast· zero (w ·G z 0)) (sym (rem0 _)) ⟩
           cast· zero ((cast· zero (x 0 ·G y 0) +G0 0G) ·G z 0) ∎

    rem (suc n) = goal
      where
      open MonoidBigOp (Group→Monoid (AbGroup→Group (G (suc n)))) renaming (bigOp to ∑)
      open MonoidBigOp (Group→Monoid (AbGroup→Group (G ( n)))) renaming (bigOp to ∑')

      goal : ((x , hx) ·⊕G ((y , hy) ·⊕G (z , hz))) .fst (suc n) ≡ (((x , hx) ·⊕G (y , hy)) ·⊕G (z , hz)) .fst (suc n)
      goal = ((x , hx) ·⊕G ((y , hy) ·⊕G (z , hz))) .fst (suc n)
           ≡⟨ refl ⟩
             ∑ (λ (i : Fin (suc (suc n))) →
                      cast· i (x (toℕ i) ·G
                               foldrFin (snd (G (suc n ∸ toℕ i)) ._+G_) (snd (G (suc n ∸ toℕ i)) .0g)
                                        (λ (j : Fin (suc (suc n ∸ toℕ i))) → cast· j (y (toℕ j) ·G z (suc n ∸ toℕ i ∸ toℕ j)))))
           ≡⟨ {!!} ⟩
             ∑ (λ (i : Fin (suc (suc n))) →
                      cast· i (
                               foldrFin (snd (G (toℕ i +ℕ (suc n ∸ toℕ i))) ._+G_) (snd (G (toℕ i +ℕ (suc n ∸ toℕ i))) .0g)
                                        (λ (j : Fin (suc (suc n ∸ toℕ i))) → x (toℕ i) ·G (cast· j (y (toℕ j) ·G z (suc n ∸ toℕ i ∸ toℕ j))))))

           ≡⟨ {!!} ⟩
             ∑ (λ (i : Fin (suc (suc n))) →
                      cast· i (
                               foldrFin (snd (G (toℕ i +ℕ (suc n ∸ toℕ i))) ._+G_) (snd (G (toℕ i +ℕ (suc n ∸ toℕ i))) .0g)
                                        (λ (j : Fin (suc (suc n ∸ toℕ i))) →
                                           cast (cong (toℕ i +ℕ_) (helper j))
                                                (x (toℕ i) ·G (y (toℕ j) ·G z (suc n ∸ toℕ i ∸ toℕ j))))))

           ≡⟨ {!!} ⟩
             ∑ (λ (i : Fin (suc (suc n))) →
                      cast· i (
                               foldrFin (snd (G (toℕ i +ℕ (suc n ∸ toℕ i))) ._+G_) (snd (G (toℕ i +ℕ (suc n ∸ toℕ i))) .0g)
                                        (λ (j : Fin (suc (suc n ∸ toℕ i))) →
                                           cast (cong (toℕ i +ℕ_) (helper j))
                                                (cast (sym (+-assoc (toℕ i) (toℕ j) (suc n ∸ toℕ i ∸ toℕ j)))
                                                      ((x (toℕ i) ·G y (toℕ j)) ·G z (suc n ∸ toℕ i ∸ toℕ j))))))
           ≡⟨ {!!} ⟩
             ∑ (λ (i : Fin (suc (suc n))) →
                      cast· i (
                               foldrFin (snd (G (toℕ i +ℕ (suc n ∸ toℕ i))) ._+G_) (snd (G (toℕ i +ℕ (suc n ∸ toℕ i))) .0g)
                                        (λ (j : Fin (suc (suc n ∸ toℕ i))) →
                                           cast (cong (_+ℕ (suc n ∸ toℕ i)) refl)
                                             (cast (+-comm (toℕ j) _ ∙ (≤-∸-+-cancel {m = toℕ j} {n = toℕ i} {!!})) (x (toℕ j) ·G y (toℕ i ∸ toℕ j)) ·G z (suc n ∸ toℕ i)))))

           ≡⟨ {!!} ⟩
             ∑ (λ (i : Fin (suc (suc n))) →
                      cast· i (
                               foldrFin (snd (G (toℕ i +ℕ (suc n ∸ toℕ i))) ._+G_) (snd (G (toℕ i +ℕ (suc n ∸ toℕ i))) .0g)
                                        (λ (j : Fin (suc (suc n ∸ toℕ i))) →
                                             (cast (+-comm (toℕ j) _ ∙ (≤-∸-+-cancel {m = toℕ j} {n = toℕ i} {!!}))
                                                   (x (toℕ j) ·G y (toℕ i ∸ toℕ j))) ·G z (suc n ∸ toℕ i))))
           ≡⟨ {!!} ⟩
             {!!}
           ≡⟨ {!!} ⟩
             ∑ (λ (j : Fin (suc (suc n))) →
               cast· j (foldrFin (snd (G (toℕ j)) ._+G_) (snd (G (toℕ j)) .0g)
                                 (λ (i : Fin (suc (toℕ j))) → cast· i (x (toℕ i) ·G y (toℕ j ∸ toℕ i)))
                        ·G z (suc n ∸ toℕ j)))
           ≡⟨ refl ⟩
             (((x , hx) ·⊕G (y , hy)) ·⊕G (z , hz)) .fst (suc n) ∎

---    p n = ∑ (λ (i : Fin (suc n)) → cast· i (x (toℕ i) ·G y (n ∸ toℕ i)))

            --   snd (G (suc n)) ._+G_
            --     (cast· zero (x 0 ·G snd (G (suc n)) ._+G_ (cast· zero (y 0 ·G z (suc n)))
            --                                               (snd (G (suc n)) ._+G_ (cast· (suc zero) (y 1 ·G z n))
            --                                               (∑ (λ x₁ → cast· x₁ (y (toℕ x₁) ·G z (suc n ∸ toℕ x₁)))))))
            --     (snd (G (suc n)) ._+G_
            --       (cast· (suc zero) (x 1 ·G snd (G n) ._+G_
            --                                   (cast· zero (y 0 ·G z n))
            --                                   (∑' (λ x₁ → cast· (suc x₁) (y (suc (toℕ x₁)) ·G z (n ∸ suc (toℕ x₁)))))))
            --       (foldrFin (snd (G (suc n)) ._+G_) (snd (G (suc n)) .0g)
            --         (λ x₁ → cast· (suc (suc x₁)) (x (suc (suc (toℕ x₁))) ·G snd (G (n ∸ suc (toℕ x₁))) ._+G_ (cast· zero (y 0 ·G z (n ∸ suc (toℕ x₁))))
            -- (foldrFin (snd (G (n ∸ suc (toℕ x₁))) ._+G_)
            --    (snd (G (n ∸ suc (toℕ x₁))) .0g)
            --    (λ x₂ → cast· (suc x₂) (y (suc (toℕ x₂)) ·G z (n ∸ suc (toℕ x₁) ∸ suc (toℕ x₂)))))))))
-}

  ·⊕G-distRight : (x y z : ⊕G) → x ·⊕G (y +⊕G z) ≡ (x ·⊕G y) +⊕G (x ·⊕G z)
  ·⊕G-distRight (x , hx) (y , hy) (z , hz) = Σ≡Prop (λ _ → squash) (funExt rem)
    where
    rem : (n : ℕ) → ((x , hx) ·⊕G ((y , hy) +⊕G (z , hz))) .fst n ≡
                    (((x , hx) ·⊕G (y , hy)) +⊕G ((x , hx) ·⊕G (z , hz))) .fst n
    rem n = ∑ (λ i → cast· i (x (toℕ i) ·G (y _ +G z _)))
          ≡⟨ bigOpExt (λ i j → cast· i (·G-distRight (x (toℕ i)) (y _) (z _) j)) ⟩
            ∑ (λ i → cast· i ((x (toℕ i) ·G y _) +G (x (toℕ i) ·G z _)))
          ≡⟨ bigOpExt (λ i → help (helper i) (x (toℕ i) ·G y _) (x (toℕ i) ·G z _)) ⟩
            ∑ (λ i → cast· i (x (toℕ i) ·G y _) +G cast· i (x (toℕ i) ·G z _))
          ≡⟨ bigOpSplit (comm (G n .snd)) (λ i → cast· i ((x (toℕ i) ·G y _)))
                                          (λ i → cast· i (x (toℕ i) ·G z _)) ⟩
             (∑ (λ i → cast· i ((x (toℕ i) ·G y _)))
          +G (∑ (λ i → cast· i ((x (toℕ i) ·G z _))))) ∎
       where
       open MonoidBigOp (Group→Monoid (AbGroup→Group (G n))) renaming (bigOp to ∑)

       help : {m n : ℕ} (p : m ≡ n) (x y : G m .fst) → cast p (x +G y) ≡ cast p x +G cast p y
       help p x y = J (λ z q → cast q (x +G y) ≡ cast q x +G cast q y)
                      (transportRefl _ ∙ (λ i → transportRefl x (~ i) +G transportRefl y (~ i))) p

  ·⊕G-distLeft : (x y z : ⊕G) → (x +⊕G y) ·⊕G z ≡ (x ·⊕G z) +⊕G (y ·⊕G z)
  ·⊕G-distLeft (x , hx) (y , hy) (z , hz) = Σ≡Prop (λ _ → squash) (funExt rem)
    where
    rem : (n : ℕ) → (((x , hx) +⊕G (y , hy)) ·⊕G (z , hz)) .fst n ≡
                    (((x , hx) ·⊕G (z , hz)) +⊕G ((y , hy) ·⊕G (z , hz))) .fst n
    rem n = ∑ (λ i → cast· i ((x (toℕ i) +G y (toℕ i)) ·G z _))
          ≡⟨ bigOpExt (λ i j → cast· i (·G-distLeft (x (toℕ i)) (y (toℕ i)) (z _) j)) ⟩
            ∑ (λ i → cast· i ((x (toℕ i) ·G z _) +G (y (toℕ i) ·G z _)))
          ≡⟨ bigOpExt (λ i → help (helper i) (x (toℕ i) ·G z _) (y (toℕ i) ·G z _)) ⟩
            ∑ (λ i → cast· i (x (toℕ i) ·G z _) +G cast· i (y (toℕ i) ·G z _))
          ≡⟨ bigOpSplit (comm (G n .snd)) (λ i → cast· i (x (toℕ i) ·G z _))
                                          (λ i → cast· i (y (toℕ i) ·G z _)) ⟩
             (∑ (λ i → cast· i ((x (toℕ i) ·G z _)))
          +G (∑ (λ i → cast· i ((y (toℕ i) ·G z _))))) ∎
       where
       open MonoidBigOp (Group→Monoid (AbGroup→Group (G n))) renaming (bigOp to ∑)

       help : {m n : ℕ} (p : m ≡ n) (x y : G m .fst) → cast p (x +G y) ≡ cast p x +G cast p y
       help p x y = J (λ z q → cast q (x +G y) ≡ cast q x +G cast q y)
                      (transportRefl _ ∙ (λ i → transportRefl x (~ i) +G transportRefl y (~ i))) p

  R : Ring (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  fst R = ⊕G
  0r (snd R) = 0⊕G
  1r (snd R) = 1⊕G
  _+_ (snd R) = _+⊕G_
  _·_ (snd R) = _·⊕G_
  - snd R = -⊕G_
  +IsAbGroup (isRing (snd R)) = makeIsAbGroup isSet⊕G +⊕G-assoc +⊕G-rid +-⊕G +⊕G-comm
  ·IsMonoid (isRing (snd R)) = makeIsMonoid isSet⊕G ·⊕G-assoc ·⊕G-rid ·⊕G-lid
  fst (dist (isRing (snd R)) x y z) = ·⊕G-distRight x y z
  snd (dist (isRing (snd R)) x y z) = ·⊕G-distLeft x y z
