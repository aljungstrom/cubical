{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Delooping.n.base where

open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Nat.Order
open import Cubical.Foundations.Everything


open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty

open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Induction.WellFounded
open import Cubical.Data.Nat.Divisibility

_mod_ : (x n : ℕ) → ℕ
x mod zero = 0
x mod (suc n) = (+induction n (λ _ → ℕ) (λ x _ → x) λ _ x → x) x

mod< : (n x : ℕ) → x mod (suc n) < (suc n)
mod< n =
  +induction n (λ x → x mod (suc n) < suc n)
               (λ x base → fst base
                         , (cong (λ x → fst base + suc x)
                                 (+inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x base)
                          ∙ snd base))
               λ x ind → fst ind
                        , cong (λ x → fst ind + suc x)
                               (+inductionStep n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x) ∙ snd ind

mod-rUnit : (n x : ℕ) → x mod n ≡ ((x + n) mod n)
mod-rUnit zero x = refl
mod-rUnit (suc n) x =
    sym (+inductionStep n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x)
  ∙ cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁)) (+-comm (suc n) x)

mod-lUnit : (n x : ℕ) → x mod n ≡ ((n + x) mod n)
mod-lUnit zero _ = refl
mod-lUnit (suc n) x = sym (+inductionStep n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x)

mod+mod≡mod : (n x y : ℕ) → (x + y) mod n ≡ (((x mod n) + (y mod n)) mod n)
mod+mod≡mod zero _ _ = refl
mod+mod≡mod (suc n) =
  +induction n
    (λ z → (x : ℕ) → ((z + x) mod (suc n)) ≡ (((z mod (suc n)) + (x mod (suc n))) mod (suc n)))
    (λ x p → +induction n _
                (λ y q → cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                               (sym (cong₂  _+_ (+inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x p)
                               (+inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) y q))))
                λ y ind → cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                                (cong (x +_) (+-comm (suc n) y) ∙ (+-assoc x y (suc n)))
                             ∙∙ sym (mod-rUnit (suc n) (x + y))
                             ∙∙ ind
                              ∙ cong (λ z → +induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁)
                                            ((+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x + z)))
                                     (mod-rUnit (suc n) y ∙ cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                                                            (+-comm y (suc n))))
    λ x p y → cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                                (cong suc (sym (+-assoc n x y)))
                 ∙∙ sym (mod-lUnit (suc n) (x + y))
                 ∙∙ p y
                  ∙ sym (cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                        (cong (_+ +induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) y)
                        (cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                        (+-comm (suc n) x) ∙ sym (mod-rUnit (suc n) x))))

mod-idempotent : {n : ℕ} → (x : ℕ) → (x mod n) mod n ≡ x mod n
mod-idempotent {n = zero} _ = refl
mod-idempotent {n = suc n} =
  +induction n (λ x → (x mod suc n) mod (suc n) ≡ x mod (suc n))
             (λ x p → cong (_mod (suc n))
                            (+inductionBase n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x p))
              λ x p → cong (_mod (suc n))
                            (+inductionStep n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x)
                             ∙∙ p
                             ∙∙ mod-rUnit (suc n) x
                              ∙ (cong (_mod (suc n)) (+-comm x (suc n)))

mod-rCancel : (n x y : ℕ) → (x + y) mod n ≡ (x + y mod n) mod n
mod-rCancel zero x y = refl
mod-rCancel (suc n) x =
  +induction n _
    (λ y p → cong (λ z → (x + z) mod (suc n))
                   (sym (+inductionBase n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) y p)))
     λ y p → cong (_mod suc n) (+-assoc x (suc n) y
                             ∙∙ (cong (_+ y) (+-comm x (suc n)))
                             ∙∙ sym (+-assoc (suc n) x y))
          ∙∙ sym (mod-lUnit (suc n) (x + y))
          ∙∙ (p ∙ cong (λ z → (x + z) mod suc n) (mod-lUnit (suc n) y))

mod-lCancel : (n x y : ℕ) → (x + y) mod n ≡ (x mod n + y) mod n
mod-lCancel n x y =
     cong (_mod n) (+-comm x y)
  ∙∙ mod-rCancel n y x
  ∙∙ cong (_mod n) (+-comm y (x mod n))

zero-charac : (n : ℕ) → n mod n ≡ 0
zero-charac zero = refl
zero-charac (suc n) = cong (_mod suc n) (+-comm 0 (suc n))
                  ∙∙ +inductionStep n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) 0
                  ∙∙ +inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) 0 (n , (+-comm n 1))

-- Addition and subtraction
_+ₘ_ : {n : ℕ} → Fin (suc n) → Fin (suc n) → Fin (suc n)
_+ₘ_ {n = n} x y = (((fst x) + (fst y)) mod (suc n)) , mod< _ ((fst x) + (fst y))

-ₘ_ : {n : ℕ} → (x : Fin (suc n)) → Fin (suc n)
fst (-ₘ_ {n = n} x) = (+induction n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) λ _ x → x) (fst x)
snd (-ₘ_ {n = n} x) = lem (fst x)
  where
  ≡<-trans : {x y z : ℕ} → x < y → x ≡ z → z < y
  ≡<-trans (k , p) q = k , cong (λ x → k + suc x) (sym q) ∙ p

  lem : {n : ℕ} (x : ℕ)
     → (+induction n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) λ _ x → x) x < suc n
  lem {n = n} =
    +induction n _
      (λ x p → ≡<-trans (mod< n (suc n ∸ x))
                         (sym (+inductionBase n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) (λ _ x → x) x p)))
       λ x p → ≡<-trans p (sym (+inductionStep n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) (λ _ x → x) x))

_-ₘ_ : {n : ℕ} → (x y : Fin (suc n)) → Fin (suc n)
_-ₘ_ x y = x +ₘ (-ₘ y)

-- Group laws
+ₘ-assoc : {n : ℕ} (x y z : Fin (suc n)) → (x +ₘ y) +ₘ z ≡ (x +ₘ (y +ₘ z))
+ₘ-assoc {n = n} x y z =
  Σ≡Prop (λ _ → m<n-isProp)
       ((mod-rCancel (suc n) ((fst x + fst y) mod (suc n)) (fst z))
    ∙∙ sym (mod+mod≡mod (suc n) (fst x + fst y) (fst z))
    ∙∙ cong (_mod suc n) (sym (+-assoc (fst x) (fst y) (fst z)))
    ∙∙ mod+mod≡mod (suc n) (fst x) (fst y + fst z)
    ∙∙ sym (mod-lCancel (suc n) (fst x) ((fst y + fst z) mod suc n)))

+ₘ-comm : {n : ℕ} (x y : Fin (suc n)) → (x +ₘ y) ≡ (y +ₘ x)
+ₘ-comm {n = n} x y = Σ≡Prop (λ _ → m<n-isProp) (cong (_mod suc n) (+-comm (fst x) (fst y)))

+ₘ-lUnit : {n : ℕ} (x : Fin (suc n)) → 0 +ₘ x ≡ x
+ₘ-lUnit {n = n} (x , p) = Σ≡Prop (λ _ → m<n-isProp) (+inductionBase n _ _ _ x p)

+ₘ-rUnit : {n : ℕ} (x : Fin (suc n)) → x +ₘ 0 ≡ x
+ₘ-rUnit x = +ₘ-comm x 0 ∙ (+ₘ-lUnit x)

+ₘ-rCancel : {n : ℕ} (x : Fin (suc n)) → x -ₘ x ≡ 0
+ₘ-rCancel {n = n} x =
  Σ≡Prop (λ _ → m<n-isProp)
      (cong (λ z → (fst x + z) mod (suc n))
            (+inductionBase n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) (λ _ x → x) (fst x) (snd x)) 
    ∙∙ sym (mod-rCancel (suc n) (fst x) ((suc n) ∸ (fst x)))
    ∙∙ cong (_mod (suc n)) (+-comm (fst x) ((suc n) ∸ (fst x)))
    ∙∙ cong (_mod (suc n)) (≤-∸-+-cancel (<-weaken (snd x)))
    ∙∙ zero-charac (suc n))

+ₘ-lCancel : {n : ℕ} (x : Fin (suc n)) → (-ₘ x) +ₘ x ≡ 0
+ₘ-lCancel {n = n} x = +ₘ-comm (-ₘ x) x ∙ +ₘ-rCancel x


-- remainder and quotient after division by n
remainder_/suc_ : (x n : ℕ) → ℕ
remainder x /suc n = x mod (suc n)

quotient_/suc_ : (x n : ℕ) → ℕ
quotient x /suc n = +induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x

-- Allowing for zero-division for nicer syntax
remainder/quotient : (n x : ℕ) → ℕ × ℕ
remainder/quotient zero x = x , 0
remainder/quotient (suc n) x = (remainder x /suc n) , (quotient x /suc n)

rem+quot-mod≡ : (n x : ℕ) → fst (remainder/quotient n x) + n · snd (remainder/quotient n x) ≡ x
rem+quot-mod≡ zero x = +-comm x 0
rem+quot-mod≡ (suc n) =
  +induction n
    (λ x → fst (remainder/quotient (suc n) x) + (suc n) · snd (remainder/quotient (suc n) x) ≡ x)
    (λ x base → cong₂ _+_ (+inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x base)
                           (cong ((suc n) ·_) (+inductionBase n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x base))
              ∙∙ cong (x +_) (·-comm n 0)
              ∙∙ +-comm x 0)
     λ x ind → cong₂ _+_ (+inductionStep n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x)
                        (cong ((suc n) ·_) (+inductionStep n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x))
          ∙∙ cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x +_)
                  (·-suc (suc n) (+induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x))
          ∙∙ cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x +_)
                  (+-comm (suc n) ((suc n) · (+induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x)))
          ∙∙ +-assoc (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x)
                     ((suc n) · +induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x)
                     (suc n)
          ∙∙ cong (_+ suc n) ind
           ∙ +-comm x (suc n)
