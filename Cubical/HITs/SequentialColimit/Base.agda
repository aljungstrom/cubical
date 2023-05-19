{-# OPTIONS --safe #-}
module Cubical.HITs.SequentialColimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

private
  variable
    ℓ : Level

record Sequence (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    space : ℕ → Type ℓ
    map : {n : ℕ} → space n → space (1 + n)

open Sequence

data Lim→ (X : Sequence ℓ) : Type ℓ where
  inl : {n : ℕ} → X .space n → Lim→ X
  push : {n : ℕ}(x : X .space n) → inl x ≡ inl (X .map x)

open import Cubical.HITs.Join

j : Type → ℕ → Type
j A zero = A
j A (suc n) = join A (j A n)

joinSeq : (A : Type) → Sequence ℓ-zero
space (joinSeq x) = j x
map (joinSeq x) = inr

open import Cubical.Foundations.Pointed

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma



open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.PropositionalTruncation as PT
module _ (A : Type) where
  A^ = Lim→ (joinSeq A)
  ps : (n : ℕ) (a : A)
    → Path A^ (inl {n = 1} (inr a)) (inl {n = suc n} (inl a))
  ps zero a i = inl {n = 1} (push a a (~ i))
  ps (suc n) a =
    ps n a
    ∙ ((λ j → inl {n = suc n} (inl a))
    ∙∙ push (inl a)
    ∙∙ λ j → inl {n = suc (suc n)} (push a (inl a) (~ j)))


  isC : (a : A) (x : A^) → inl {n = zero} a ≡ x
  isC a (inl {n = n} x) =
       push a
    ∙∙ (ps n a ∙ (λ i → inl {n = suc n} (push a x i)))
    ∙∙ sym (push x)
  isC a (push {n = n} x i) j =
    hcomp (λ k → λ {(i = i1) → ((λ i → push {n = zero} a (i ∨ ~ k))
                                 ∙∙ ((ps n a ∙ h) ∙ h₂)
                                 ∙∙ (sym (push (inr x)))) j
                   ; (i = i0) → doubleCompPath-filler (push a)
                                    (ps n a
                                  ∙ λ i₁ → inl (push a x i₁))
                                    (sym (push x)) k j
                   ; (j = i0) → push a (~ k)
                   ; (j = i1) → push x (i ∨ ~ k)})
    (hcomp (λ k → λ {(i = i1) → ((compPath-filler' (ps n a) h k ∙ h₂)
                                 ∙ sym (push (inr x))) j
                 ; (i = i0) → compPath-filler' (ps n a)
                                (λ i₁ → inl (push a x i₁)) k j
                 ; (j = i0) → ps n a (~ k)
                 ; (j = i1) → inl (inr x)})
     (hcomp (λ k → λ {(i = i1)
       → ((h ∙ λ j → inl {n = 2 + n} (push a (push a x k) j))
              ∙ sym (push {n = suc n} (push a x k))) j
           ; (i = i0) → inl {n = suc n} (push a x (j ∧ k))
           ; (j = i0) → inl {n = suc n} (inl a)
           ; (j = i1) → inl {n = suc n} (push a x k)})
       (h* (~ i) j)))
    where
    h : Path A^ (inl {n = suc n} (inl a)) (inl {n = 2 + n} (inl a))
    h = push {n = suc n} (inl a)
      ∙ λ j₁ → inl {n = 2 + n} (push a (inl a) (~ j₁))

    h₂ : Path A^ (inl {n = 2 + n} (inl a))
                 (inl {n = 2 + n} (inr (inr x)))
    h₂ i = inl {n = 2 + n} (push a (inr x) i)

    h* : (h
      ∙ (λ j₁ → inl {n = 2 + n} (push a (inl a) j₁)))
      ∙ sym (push (inl a))
      ≡ refl
    h* = cong (_∙ sym (push (inl a)))
            (sym (assoc _ _ _)
           ∙ cong (push {n = suc n} (inl a) ∙_)
               (rCancel _)
           ∙ sym (rUnit (push (inl a))))
        ∙ rCancel _

  isContr-∞join : (a : ∥ A ∥₁) → isContr A^
  isContr-∞join = PT.rec isPropIsContr λ a → (inl a) , isC a

{-
  A∞-map : ∀ {ℓ} {B : Type ℓ} (t : A^ → B) → (x : _) → t x ≡ {!!}
  A∞-map = {!!}
-}


module _ (A B : Type) (a' : ∥ A ∥₁) (f : A → Pointed₀) (fc : (a b : A) → isContr (f a ≡ f b))  where

  asd : A^ A → Type
  asd' : (x y : A^ A) → asd x ≡ asd y
  asd (inl {n = zero} x) = f x .fst
  asd (inl {n = suc n} (inl x)) = f x .fst
  asd (inl {n = suc n} (inr x)) = asd (inl {n = n} x)
  asd (inl {n = suc n} (push a b i)) = asd' (inl {n = zero} a) (inl b) i
  asd (push {n = n} x i) = {!!}
  asd' x y i = {!!} -- asd (isContr→isProp (isContr-∞join A a') x y i)

  U = Σ[ A ∈ Pointed₀ ] ((x : _) → isProp (A ≡ x))

  F : (x : A) → U
  fst (F x) = f x
  snd (F x) = J> (isContr→isProp (fc x x) refl)

  isSetU : isSet U
  fst (isSetU P Q t s i j) =
    P .snd (fst Q) (cong fst t) (cong fst s) i j
  snd (isSetU P Q t s i j) m = help i j
    where
    help : SquareP (λ i j → isProp (fst (isSetU P Q t s i j) ≡ m))
                   (λ j x y → snd (t j) m x y)
                   (λ j x y → snd (s j) m x y)
                   (λ i x y → snd P m x y)
                   λ i x y → snd Q m x y
    help =
     toPathP
      (isOfHLevelPath' 0 (isOfHLevelPathP 1 isPropIsProp _ _) _ _ .fst)

  t2 : (n : ℕ) → j A n → U
  t2-coh : (n : ℕ) (a : A) (b : j A n) → F a ≡ t2 n b
  t2 zero = F
  t2 (suc n) (inl x) = F x
  t2 (suc n) (inr x) = t2 n x
  t2 (suc n) (push a b i) = t2-coh n a b i
  t2-coh zero a b =
    Σ≡Prop (λ _ → isPropΠ λ _ → isPropIsProp) (fc a b .fst)
  t2-coh (suc n) a (inl x) =
    Σ≡Prop (λ _ → isPropΠ λ _ → isPropIsProp) (fc a x .fst)
  t2-coh (suc n) a (inr x) = t2-coh n a x
  t2-coh (suc n) a (push c d i) j =
   isSet→isSet' isSetU
    (Σ≡Prop (λ z → isPropΠ (λ z₁ → isPropIsProp)) (fc a c .fst))
     (t2-coh n a d) (λ _ → F a) (t2-coh n c d) i j


  joinSeq→ : Lim→ (joinSeq A) → Pointed₀
  joinSeq→ (inl x) = t2 _ x .fst
  joinSeq→ (push x i) = t2 _ x .fst



  -- module _ (B : Pointed₀)
  --   (p : (x : _) → joinSeq→ (inl {n = zero} x) ≡ B)
  --          (e : {!p!}) where

  -- batw : {!!}
  -- batw = {!!}

  -- joinSeq→ : (n : ℕ) → j A n → B
  -- joinSeq→' : (n : ℕ) (a : A) (b : j A n) → joinSeq→ n b ≡ f a
  -- joinSeq→ zero = f
  -- joinSeq→ (suc n) (inl x) = f x
  -- joinSeq→ (suc n) (inr x) = joinSeq→ n x
  -- joinSeq→ (suc n) (push a b i) = joinSeq→' n a b (~ i)
  -- joinSeq→' zero a b = fc b a
  -- joinSeq→' (suc n) a (inl x) = fc x a
  -- joinSeq→' (suc n) a (inr x) = joinSeq→' n a x
  -- joinSeq→' (suc n) a (push a₁ b i) = {!!}

