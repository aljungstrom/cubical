{-

This file contains:
  - Path lemmas used in the colimit equivalence proof.

Very long, indeed. But should be simple.
The length mainly thanks to:
  - Refls, lots of refls, and they lead to much degeneracy.
     Maybe one has regularity or something could make them all trivial;

  - No pattern matching for J rule or any sytactically convenient way
     to apply it. So when you deal with complicated composite functions
     it needs too many helper functions.

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.James.Inductive.Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function

private
  variable
    ℓ ℓ' : Level


-- Lots of degenerate cubes used as intial input to J rule

private
  module _
    {A : Type ℓ}{B : Type ℓ'}(a : A)(f : A → B) where

    degenerate1 : (i j k : I) → A
    degenerate1 i j k =
      hfill (λ k → λ
        { (i = i0) → a
        ; (i = i1) → doubleCompPath-filler (refl {x = a}) refl refl k j
        ; (j = i0) → a
        ; (j = i1) → a})
      (inS a) k

    degenerate1' : (i j k : I) → A
    degenerate1' i j k =
      hfill (λ k → λ
        { (i = i0) → a
        ; (i = i1) → compPath-filler (refl {x = a}) refl k j
        ; (j = i0) → a
        ; (j = i1) → a})
      (inS a) k

    degenerate1'' : (i j k : I) → A
    degenerate1'' i j k =
      hfill (λ k → λ
        { (i = i0) → a
        ; (i = i1) → compPath-filler (refl {x = a}) (refl ∙ refl) k j
        ; (j = i0) → a
        ; (j = i1) → degenerate1 i k i1})
      (inS a) k

    degenerate2 : (i j k : I) → B
    degenerate2 i j k =
      hfill (λ k → λ
        { (i = i0) → f a
        ; (i = i1) → doubleCompPath-filler (refl {x = f a}) refl refl k j
        ; (j = i0) → f a
        ; (j = i1) → f a })
      (inS (f a)) k

    degenerate3 : (i j k : I) → B
    degenerate3 i j k =
      hfill (λ k → λ
        { (i = i0) → f (doubleCompPath-filler (refl {x = a}) refl refl k j)
        ; (i = i1) → doubleCompPath-filler (refl {x = f a}) refl refl k j
        ; (j = i0) → f a
        ; (j = i1) → f a })
      (inS (f a)) k

    degenerate4 : (i j k : I) → A
    degenerate4 i j k =
      hfill (λ k → λ
        { (i = i0) → compPath-filler (refl {x = a}) (refl ∙∙ refl ∙∙ refl) k j
        ; (i = i1) → doubleCompPath-filler (refl {x = a}) refl refl j k
        ; (j = i0) → a
        ; (j = i1) → (refl {x = a} ∙∙ refl ∙∙ refl) k })
      (inS a) k

    degenerate5 :
      SquareP
        (λ i j → a ≡ degenerate4 i j i1)
        (λ i j → compPath-filler (refl {x = a}) (refl ∙∙ refl ∙∙ refl) j i)
        (λ i j → a) (λ i j → a)
        (λ i j → doubleCompPath-filler (refl {x = a}) refl refl (~ i) j)
    degenerate5 i j k =
      hcomp (λ l → λ
        { (i = i0) → compPath-filler (refl {x = a}) (refl ∙∙ refl ∙∙ refl) k j
        ; (i = i1) → doubleCompPath-filler (refl {x = a}) refl refl (j ∧ ~ l) k
        ; (j = i0) → a
        ; (j = i1) → doubleCompPath-filler (refl {x = a}) refl refl (~ i ∨ ~ l) k
        ; (k = i0) → a
        ; (k = i1) → degenerate4 i j i1 })
      (degenerate4 i j k)

    degenerate5' :
      (i j k : I) → A
    degenerate5' i j k =
      hfill (λ k → λ
        { (i = i0) → doubleCompPath-filler (refl {x = a}) refl (refl ∙ refl) k j
        ; (i = i1) → a
        ; (j = i0) → a
        ; (j = i1) → compPath-filler (refl {x = a}) refl (~ i) k })
      (inS a) k

    someCommonDegenerateCube :
      (i j k : I) → B
    someCommonDegenerateCube i j k =
      hcomp (λ l → λ
        { (i = i0) → f a
        ; (i = i1) → degenerate3 k j l
        ; (j = i0) → f a
        ; (j = i1) → f a
        ; (k = i0) → f (degenerate1 i j l)
        ; (k = i1) → degenerate2 i j l })
      (f a)


-- Cubes of which mostly are constructed by J rule

coh-helper-refl : {A : Type ℓ}{a : A}(q' : a ≡ a)
  → refl ≡ q'
  → refl ≡ refl ∙∙ refl ∙∙ q'
coh-helper-refl {a = a} q' h i j =
  hcomp (λ k → λ
    { (i = i0) → a
    ; (i = i1) → doubleCompPath-filler refl refl q' k j
    ; (j = i0) → a
    ; (j = i1) → h i k })
  a

coh-helper'-filler : {A : Type ℓ}{a c : A}(q q' : a ≡ c)
  → PathP (λ i → a ≡ q i) refl q'
  → I → I → I → A
coh-helper'-filler {a = a} q q' pq i j r =
  hfill (λ k → λ
    { (i = i0) → q' (k ∨ ~ j)
    ; (i = i1) → doubleCompPath-filler (sym q) refl q' k j
    ; (j = i0) → q (k ∨ ~ i)
    ; (j = i1) → q' k })
  (inS (pq (~ i) (~ j)))
  r

coh-helper' : {A : Type ℓ}{a c : A}(q q' : a ≡ c)
  → PathP (λ i → a ≡ q i) refl q'
  → refl ≡ (sym q) ∙∙ refl ∙∙ q'
coh-helper' q q' pq i j = coh-helper'-filler q q' pq i j i1

convPathP-filler : {A : Type ℓ}{a b c : A}(p : a ≡ b)(q q' : b ≡ c)
  → PathP (λ i → p i ≡ q i) p q'
  → I → I → I → A
convPathP-filler p q q' sq i j k =
  hfill (λ r → λ
    { (i = i0) → p (r ∨ j)
    ; (i = i1) → sq r j
    ; (j = i0) →  p r
    ; (j = i1) → q (i ∧ r) })
      (inS (p j))
      k

convPathP : {A : Type ℓ}{a b c : A}(p : a ≡ b)(q q' : b ≡ c)
  → PathP (λ i → p i ≡ q i) p q' → PathP (λ i → b ≡ q i) refl q'
convPathP {b = b} p q q' sq i j = convPathP-filler p q q' sq i j i1

coh-helper : {A : Type ℓ}{a b c : A}(p : a ≡ b)(q q' : b ≡ c)
  → PathP (λ i → p i ≡ q i) p q'
  → refl ≡ (sym q) ∙∙ refl ∙∙ q'
coh-helper {A = A} {a = a} p q q' pq =
  coh-helper' q q' (convPathP p q q' pq)

coh-helper-refl-helper : {A : Type ℓ}{a : A}(q' : a ≡ a)
  → (sq : refl ≡ q')
  → coh-helper refl refl q' sq ≡ coh-helper' refl q' sq
coh-helper-refl-helper {a = a} q' sq =
  cong (coh-helper' refl q') h
  where
  h : convPathP refl refl q' sq ≡ sq
  h i j k =
    hcomp (λ r → λ {(i = i1) → sq (j ∧ r) k
                 ; (j = i0) → a
                 ; (j = i1) → sq r k
                 ; (k = i0) → a
                 ; (k = i1) → a})
            a


coh-helper-Refl : {A : Type ℓ}{a : A}
    (q' : a ≡ a)
  → (sqr : refl ≡ q')
  → coh-helper-refl q' sqr ≡ coh-helper refl refl q' sqr
coh-helper-Refl {A = A} {a = a} q' sqr =
  help ∙ sym (coh-helper-refl-helper q' sqr)
  where
  help : coh-helper-refl q' sqr ≡ coh-helper' refl q' sqr
  help i j k =
    hcomp (λ r → λ {(j = i0) → sqr i (r ∨ ~ k)
                 ; (j = i1) → compPath-filler refl q' r k
                 ; (k = i0) → a
                 ; (k = i1) → sqr (j ∨ i) r})
            (sqr (i ∧ ~ j) (~ k))

doubleCompPath-cong-filler : {A : Type ℓ}{B : Type ℓ'}
    {a b c d : A}{a' b' c' d' : B}
    (f : A → B)
  → {pa : f a ≡ a'}{pb : f b ≡ b'}{pc : f c ≡ c'}{pd : f d ≡ d'}
  → (p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
  → {p' : a' ≡ b'}{q' : b' ≡ c'}{r' : c' ≡ d'}
  → (h   : PathP (λ i → pa i ≡ pb i) (cong f p) p')
  → (h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q')
  → (h'' : PathP (λ i → pc i ≡ pd i) (cong f r) r')
  → (i j k : I) → B
doubleCompPath-cong-filler f p q r {p' = p'} {q' = q'} {r' = r'}  h h' h'' i j k =
  hfill (λ k → λ
    { (i = i0) → f (doubleCompPath-filler p q r k j)
    ; (i = i1) → doubleCompPath-filler p' q' r' k j
    ; (j = i0) → h   i (~ k)
    ; (j = i1) → h'' i  k })
  (inS (h' i j)) k

doubleCompPath-cong : {A : Type ℓ}{B : Type ℓ'}{a b c d : A}
    (f : A → B)
  → (p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
  → cong f (p ∙∙ q ∙∙ r) ≡ cong f p ∙∙ cong f q ∙∙ cong f r
doubleCompPath-cong f p q r i j =
  doubleCompPath-cong-filler f
    {pa = refl} {pb = refl} {pc = refl} {pd = refl}
    p q r refl refl refl i j i1

comp-cong-square-filler : {A : Type ℓ}{B : Type ℓ'}{a b c : A}
    (f : A → B)
  → (p : a ≡ b)(q : b ≡ c)
  → I → I → I → B
comp-cong-square-filler {a = a} f p q i j r =
  hfill (λ k → λ
    { (i = i0) → f (compPath-filler p q k j)
    ; (i = i1) → compPath-filler (cong f p) (cong f q) k j
    ; (j = i0) → f a
    ; (j = i1) → f (q k) })
  (inS (f (p j))) r

comp-cong-square : {A : Type ℓ}{B : Type ℓ'}{a b c : A}
    (f : A → B)
  → (p : a ≡ b)(q : b ≡ c)
  → cong f (p ∙ q) ≡ cong f p ∙ cong f q
comp-cong-square {a = a} f p q i j =
  hcomp (λ k → λ
    { (i = i0) → f (compPath-filler p q k j)
    ; (i = i1) → compPath-filler (cong f p) (cong f q) k j
    ; (j = i0) → f a
    ; (j = i1) → f (q k) })
  (f (p j))

comp-cong-square'-filler : {A : Type ℓ}{a b c : A}
    (p : a ≡ b)(q : a ≡ c)(r : b ≡ c)
  → (h : r ≡ sym p ∙∙ refl ∙∙ q)
  → I → I → I → A
comp-cong-square'-filler {a = a} p q r h i j k =
  hfill (λ k → λ
    { (i = i0) → compPath-filler p r k j
    ; (i = i1) → doubleCompPath-filler (sym p) refl q j k
    ; (j = i0) → a
    ; (j = i1) → h i k })
  (inS (p j)) k

comp-cong-square' : {A : Type ℓ}{a b c : A}
    (p : a ≡ b)(q : a ≡ c)(r : b ≡ c)
  → (h : r ≡ sym p ∙∙ refl ∙∙ q)
  → p ∙ r ≡ q
comp-cong-square' {a = a} p q r h i j = comp-cong-square'-filler p q r h i j i1

comp-cong-helper-filler : {A : Type ℓ}{B : Type ℓ'}{a b c : A}
    (f : A → B)
  → (p : a ≡ b)(q : f a ≡ f c)(r : b ≡ c)
  → (h : cong f r ≡ sym (cong f p) ∙∙ refl ∙∙ q)
  → (i j k : I) → B
comp-cong-helper-filler {a = a} {c = c} f p q r h i j k =
  hfill (λ k → λ
    { (i = i0) → comp-cong-square f p r (~ k) j
    ; (i = i1) → q j
    ; (j = i0) → f a
    ; (j = i1) → f c })
  (inS (comp-cong-square' _ _ _ h i j)) k

comp-cong-helper : {A : Type ℓ}{B : Type ℓ'}{a b c : A}
    (f : A → B)
  → (p : a ≡ b)(q : f a ≡ f c)(r : b ≡ c)
  → (h : cong f r ≡ sym (cong f p) ∙∙ refl ∙∙ q)
  → cong f (p ∙ r) ≡ q
comp-cong-helper {a = a} f p q r h i j =
  comp-cong-helper-filler f p q r h i j i1

push-helper-refl-fill : {A : Type ℓ}{c : A} → (q' : c ≡ c)
  → refl ≡ q'
  → I → I → I → A
push-helper-refl-fill {c = c} q' h i j r =
  hfill (λ k → λ
    { (i = i0) → c
    ; (i = i1) → compPath-filler refl q' k j
    ; (j = i0) → c
    ; (j = i1) → h i k })
  (inS c) r

push-helper-refl : {A : Type ℓ}{c : A} → (q' : c ≡ c)
  → refl ≡ q'
  → refl ≡ refl ∙ q'
push-helper-refl q' h i j = push-helper-refl-fill q' h i j i1

push-helper'-filler : {A : Type ℓ}{a c : A} → (q : a ≡ c)(q' : c ≡ c)
  → refl ≡ q'
  → I → I → I → A
push-helper'-filler q q' p i j r =
  hfill (λ k → λ
    { (i = i0) → q (~ k)
    ; (i = i1) → compPath-filler' q q' k j
    ; (j = i0) → q (~ k)
    ; (j = i1) → q (i ∨ ~ k) })
      (inS (p i j)) r

push-helper' : {A : Type ℓ}{a c : A} → (q : a ≡ c)(q' : c ≡ c)
  → refl ≡ q'
  → PathP (λ i → a ≡ q i) refl (q ∙ q')
push-helper' q q' p i j = push-helper'-filler q q' p i j i1

{-
  J (λ c q → (q' : c ≡ c) → refl ≡ q' → PathP (λ i → a ≡ q i) refl (q ∙ q'))
    push-helper-refl
-}

push-helper-filler : {A : Type ℓ}{a b c : A}
    (p : a ≡ b)(q : b ≡ c)(q' : c ≡ c)
  → refl ≡ q'
  → I → I → I → A
push-helper-filler p q q' P i j r =
  hfill (λ k → λ
    { (i = i0) → p (j ∨ ~ k)
    ; (i = i1) → (q ∙ q') j
    ; (j = i0) → p (i ∨ ~ k)
    ; (j = i1) → q i })
      (inS (push-helper' q q' P i j))
      r

push-helper : {A : Type ℓ}{a b c : A}
    (p : a ≡ b)(q : b ≡ c)(q' : c ≡ c)
  → refl ≡ q'
  → PathP (λ i → p i ≡ q i) p (q ∙ q')
push-helper {A = A} p q q' P i j =
  push-helper-filler p q q' P i j i1

push-helper-Refl : {A : Type ℓ}{c : A}
    (q' : c ≡ c)
  → (h : refl ≡ q')
  → push-helper-refl q' h ≡ push-helper refl refl q' h
push-helper-Refl {A = A} {c = a} q' h i j k = 
  hcomp (λ r → λ {(i = i0) → push-helper-refl (h r) (λ j → h (r ∧ j)) j k
                 ; (i = i1) → push-helper refl refl (h r) (λ j → h (r ∧ j)) j k
                 ; (j = i0) → a
                 ; (j = i1) → (refl ∙ h r) k
                 ; (k = i0) → a 
                 ; (k = i1) → a})
        (hcomp (λ r → λ {(i = i0) → push-helper-refl-fill (λ _ → a) refl j k r
                 ; (i = i1) → push-helper-filler refl refl (λ _ → a) refl j k r
                 ; (j = i0) → a
                 ; (j = i1) → compPath-filler (λ _ → a) (λ _ → a) (r ∨ i) k
                 ; (k = i0) → a 
                 ; (k = i1) → a})
               (hcomp (λ r → λ {(i = i0) → a
                 ; (i = i1) → push-helper'-filler refl (λ _ → a) refl j k r
                 ; (j = i0) → a
                 ; (j = i1) → compPath-filler (λ _ → a) (λ _ → a) (r ∧ i) k
                 ; (k = i0) → a 
                 ; (k = i1) → a})
                    a))

module _
  {A : Type ℓ}{B : Type ℓ'}{a : A}(f : A → B) where

    push-helper-cong-refl' :
      SquareP
        (λ i j → f (push-helper-refl _ (λ i j → a) i j)
          ≡ push-helper-refl _ (λ i j → f a) i j)
        (λ i j → f a)
        (λ i j → comp-cong-square f (refl {x = a}) refl j i)
        (λ i j → f a) (λ i j → f a)
    push-helper-cong-refl' i j k =
      someCommonDegenerateCube a f i j k

    push-helper-cong-refl :
      SquareP
        (λ i j → f (push-helper refl refl _ (λ i j → a) i j)
          ≡ push-helper refl refl _ (λ i j → f a) i j)
        (λ i j → f a)
        (λ i j → comp-cong-square f (refl {x = a}) refl j i)
        (λ i j → f a) (λ i j → f a)
    push-helper-cong-refl i j k =
      hcomp (λ r → λ {(i = i0) → f a
                     ; (i = i1) → comp-cong-square {a = a} f refl refl k j
                     ; (j = i0) → f a
                     ; (j = i1) → f a
                     ; (k = i0) → f (push-helper-filler refl refl (λ j₁ → a) (λ i₁ j₁ → a) i j r)
                     ; (k = i1) → push-helper-filler refl refl (λ j₁ → f a) (λ i₁ j₁ → f a) i j r})
            (hcomp (λ r → λ {(i = i0) → f a
                     ; (i = i1) → comp-cong-square-filler {a = a} f refl refl k j r
                     ; (j = i0) → f a
                     ; (j = i1) → f a
                     ; (k = i0) → f (push-helper'-filler {a = a} refl refl refl i j r)
                     ; (k = i1) → push-helper'-filler {a = f a} refl refl refl i j r})
                   (f a))

    push-helper-cong' :
        (b : A)(p : a ≡ b)
        (c : A)(q : b ≡ c)
        (q' : c ≡ c)(sqr : refl ≡ q')
      → SquareP
        (λ i j → f (push-helper p q _ sqr i j)
          ≡ push-helper (cong f p) (cong f q) _ (λ i j → f (sqr i j)) i j)
        (λ i j → f (p i))
        (λ i j → comp-cong-square f q q' j i)
        (λ i j → f (p i)) (λ i j → f (q i))
    push-helper-cong' b p c q q' sqr i j k =
      hcomp (λ r → λ {(i = i0) → f (p (j ∨ ~ r))
                     ; (i = i1) → comp-cong-square f q q' k j
                     ; (j = i0) → f (p (i ∨ ~ r))
                     ; (j = i1) → f (q i)
                     ; (k = i0) → f (push-helper-filler p q q' sqr i j r)
                     ; (k = i1) → push-helper-filler (cong f p) (cong f q) (λ j₁ → f (q' j₁)) (λ i₁ j₁ → f (sqr i₁ j₁)) i j r})
        (hcomp (λ r → λ {(i = i0) → f (q (~ r))
                     ; (i = i1) → cube r j k
                     ; (j = i0) → f (q (~ r))
                     ; (j = i1) → f (q (i ∨ ~ r))
                     ; (k = i0) → f (push-helper'-filler q q' sqr i j r)
                     ; (k = i1) → push-helper'-filler (cong f q) (λ j₁ → f (q' j₁)) (λ i₁ j₁ → f (sqr i₁ j₁)) i j r})
                (f (sqr i j)))
       where
       cube : Cube (λ k j → f (q' k)) (λ j k → comp-cong-square f q q' k j)
                   (λ r k → f (q (~ r))) (λ r k → f c)
                   (λ r j → f (compPath-filler' q q' r j))
                   λ r j → compPath-filler' (cong f q) (cong f q') r j
       cube i j k =
         hcomp (λ r → λ {(i = i0) → f (q' (j ∧ r))
                     ; (i = i1) → comp-cong-square-filler f q q' k j r
                     ; (j = i0) → f (q (~ i))
                     ; (j = i1) → f (q' r)
                     ; (k = i0) → f (compPath-filler'-filler q q' i j r)
                     ; (k = i1) → compPath-filler'-filler (cong f q) (cong f q') i j r})
               (f (q (j ∨ ~ i)))

push-helper-cong : {A : Type ℓ}{B : Type ℓ'}{a b c : A}
    (f : A → B)
  → (p : a ≡ b)(q : b ≡ c)(q' : c ≡ c)
  → (sqr : refl ≡ q')
  → SquareP
      (λ i j → f (push-helper p q _ sqr i j)
          ≡ push-helper (cong f p) (cong f q) _ (λ i j → f (sqr i j)) i j)
      (λ i j → f (p i))
      (λ i j → comp-cong-square f q q' j i)
      (λ i j → f (p i)) (λ i j → f (q i))
push-helper-cong f p q q' sqr = push-helper-cong' f _ p _ q q' sqr


module _
  {A : Type ℓ}{a : A} where

  push-coh-helper-refl' :
    SquareP
      (λ i j → push-helper-refl _ (coh-helper-refl _ (λ i j → a)) i j ≡ a)
      (λ i j → a)
      (λ i j → comp-cong-square' (refl {x = a}) refl _ refl j i)
      (λ i j → a)
      (λ i j → a)
  push-coh-helper-refl' i j k =
    hcomp (λ l → λ
      { (i = i0) → a
      ; (i = i1) → degenerate5 a (idfun _) k j l
      ; (j = i0) → a
      ; (j = i1) → degenerate1 a (idfun _) i l (~ k)
      ; (k = i0) → degenerate1'' a (idfun _) i j l
      ; (k = i1) → a })
    a

  push-coh-helper-refl :
    SquareP
      (λ i j → push-helper refl refl _ (coh-helper _ _ _ (λ i j → a)) i j ≡ a)
      (λ i j → a)
      (λ i j → comp-cong-square' (refl {x = a}) refl _ refl j i)
      (λ i j → a)
      (λ i j → a)
  push-coh-helper-refl =
    transport (λ t →
      SquareP
      (λ i j → push-helper-Refl _ (coh-helper-Refl _ (λ i j → a) t) t i j ≡ a)
      (λ i j → a)
      (λ i j → comp-cong-square' (refl {x = a}) refl _ refl j i)
      (λ i j → a) (λ i j → a)) push-coh-helper-refl'
      

  push-coh-helper' :
      (b : A)(p : a ≡ b)
      (c : A)(q : b ≡ c)
      (q' : b ≡ c)(sqr : PathP (λ i → p i ≡ q i) p q')
    → SquareP
      (λ i j → push-helper p q _ (coh-helper _ _ _ sqr) i j ≡ sqr i j)
      (λ i j → p i)
      (λ i j → comp-cong-square' q q' _ refl j i)
      (λ i j → p i)
      (λ i j → q i)
  push-coh-helper' b p c q q' sqr i j k =
    hcomp (λ r → λ {(i = i0) → p (j ∧ r)
                 ; (i = i1) → comp-cong-square' (λ j → sqr (j ∧ r) r) (λ i → sqr r (i ∧ r))
                                                 (sym (λ j₁ → sqr (j₁ ∧ r) r) ∙∙ refl ∙∙ (λ i₁ → sqr r (i₁ ∧ r)))
                                                 refl k j
                 ; (j = i0) → p (i ∧ r)
                 ; (j = i1) → sqr (i ∧ r) r
                 ; (k = i0) → push-helper (λ i → p (i ∧ r)) (λ j → sqr (j ∧ r) r)
                                 (sym (λ j₁ → sqr (j₁ ∧ r) r) ∙∙ refl ∙∙ (λ i₁ → sqr r (i₁ ∧ r)))
                                 (coh-helper (λ i → p (i ∧ r)) (λ j → sqr (j ∧ r) r)
                                             (λ i₁ → sqr r (i₁ ∧ r)) (λ i j → sqr (i ∧ r) (j ∧ r))) i j
                 ; (k = i1) → sqr (i ∧ r) (j ∧ r)})
     (push-coh-helper-refl i j k)


push-coh-helper : {A : Type ℓ}{a b c : A}
    (p : a ≡ b)(q q' : b ≡ c)
  → (sqr : PathP (λ i → p i ≡ q i) p q')
  → SquareP
      (λ i j → push-helper p q _ (coh-helper _ _ _ sqr) i j ≡ sqr i j)
      (λ i j → p i)
      (λ i j → comp-cong-square' q q' _ refl j i)
      (λ i j → p i)
      (λ i j → q i)
push-coh-helper p q q' sqr = push-coh-helper' _ p _ q q' sqr


push-square-helper-refl : {A : Type ℓ}{a : A}
  → refl ∙∙ refl ∙∙ (refl ∙ refl) ≡ refl {x = a}
push-square-helper-refl {a = a} i j = degenerate5' a (idfun _) i j i1

push-square-helper' : {A : Type ℓ}{a c : A}
  → (q' : a ≡ c)
  → refl ∙∙ refl ∙∙ (refl ∙ q') ≡ q'
push-square-helper' {a = a} =
  J (λ _ q' → refl ∙∙ refl ∙∙ (refl ∙ q') ≡ q') push-square-helper-refl

push-square-helper : {A : Type ℓ}{a b c : A}
  → (q : a ≡ b)(q' : b ≡ c)
  → sym q ∙∙ refl ∙∙ (q ∙ q') ≡ q'
push-square-helper {A = A} p =
  J (λ b q → {c : A}(q' : b ≡ c) → sym q ∙∙ refl ∙∙ (q ∙ q') ≡ q') push-square-helper' p

push-square-helper-Refl : {A : Type ℓ}{a : A}
  → push-square-helper-refl {a = a} ≡ push-square-helper refl refl
push-square-helper-Refl {A = A} = sym (
    (λ i → JRefl (λ b q → {c : A}(q' : b ≡ c) → sym q ∙∙ refl ∙∙ (q ∙ q') ≡ q')
      push-square-helper' i refl)
  ∙ (λ i → JRefl (λ _ q' → refl ∙∙ refl ∙∙ (refl ∙ q') ≡ q')
      push-square-helper-refl i))

coh-cube-helper-refl : {A : Type ℓ} {a : A}
  →
  SquareP
    (λ i j → coh-helper _ _ _ (push-helper refl refl refl (λ i j → a)) i j ≡ a)
    (λ i j → a)
    (λ i j → push-square-helper (refl {x = a}) refl j i)
    (λ i j → a) (λ i j → a)
coh-cube-helper-refl {a = a} i j k =
  hcomp (λ r → λ {(i = i0) → a
                 ; (i = i1) → push-square-helper-Refl {a = a} r k j
                 ; (j = i0) → a
                 ; (j = i1) → a
                 ; (k = i0) → coh-helper-Refl (refl ∙ refl)
                                (push-helper-Refl refl (λ i j → a) r) r i j
                 ; (k = i1) → a})
        (hcomp (λ l → λ
    { (i = i0) → a
    ; (i = i1) → degenerate5' a (idfun _) k j l
    ; (j = i0) → a
    ; (j = i1) → degenerate1' a (idfun _) i l (~ k)
    ; (k = i0) → degenerate1'' a (idfun _) i j l
    ; (k = i1) → a })
  a)

coh-cube-helper : {A : Type ℓ}{a b c : A} → (p : a ≡ b)(q : b ≡ c)(q' : c ≡ c)
  → (sqr : refl ≡ q')
  → SquareP
      (λ i j → coh-helper _ _ _ (push-helper p q q' sqr) i j ≡ sqr i j)
      (λ i j → c)
      (λ i j → push-square-helper q q' j i)
      (λ i j → c)
      (λ i j → c)
coh-cube-helper {b = b} {c = c} p q q' sqr i j k =
  hcomp (λ r → λ {(i = i0) → c
                 ; (i = i1) → push-square-helper q (sqr r) k j
                 ; (j = i0) → c
                 ; (j = i1) → c
                 ; (j = i1) → c
                 ; (k = i0) → coh-helper p q (q ∙ (sqr r))
                                 (push-helper p q (sqr r) (λ i → sqr (i ∧ r))) i j
                 ; (k = i1) → sqr (i ∧ r) j})
     (hcomp (λ r → λ {(i = i0) → q r
                 ; (i = i1) → push-square-helper (λ i → q (i ∧ r)) refl k j
                 ; (j = i0) → q r
                 ; (j = i1) → q r
                 ; (j = i1) → q r
                 ; (k = i0) → coh-helper (λ i → p (i ∨ ~ r)) (λ i → q (i ∧ r))
                                 ((λ i → q (i ∧ r)) ∙ refl)
                                 (push-helper (λ i → p (i ∨ ~ r)) (λ i → q (i ∧ r))
                                              refl refl) i j
                 ; (k = i1) → q r})
            (coh-cube-helper-refl {a = b} i j k))


coh-helper-cong : {A : Type ℓ}{B : Type ℓ'}{a b c : A}{a' b' c' : B}
    (f : A → B)
  → {pa : f a ≡ a'}{pb : f b ≡ b'}{pc : f c ≡ c'}
  → (p  : a  ≡ b )(q  r  : b  ≡ c )
  → {p' : a' ≡ b'}{q' r' : b' ≡ c'}
  → {h   : PathP (λ i → pa i ≡ pb i) (cong f p) p'}
  → {h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q'}
  → {h'' : PathP (λ i → pb i ≡ pc i) (cong f r) r'}
  → (sqr  : PathP (λ i → p  i ≡ q  i) p  r)
  → {sqr' : PathP (λ i → p' i ≡ q' i) p' r'}
  → (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
              (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
  → SquareP
      (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
      (λ i j → pc j)
      (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
      (λ i j → pc j)
      (λ i j → pc j)
coh-helper-cong f p q r {p' = p'} {q' = q'} {r' = r'} {h = h} {h' = h'} {h'' = h''} sqr {sqr' = sqr'} hsqr i j k =
  hcomp (λ s → λ {(i = i0) → h'' k (s ∨ ~ j)
               ; (j = i0) → h' k (s ∨ ~ i)
               ; (j = i1) → h'' k s
               ; (k = i0) → f (coh-helper'-filler q r (convPathP p q r sqr) i j s)
               ; (k = i1) → coh-helper'-filler q' r' (convPathP p'  q' r' sqr') i j s})
      (hcomp (λ s → λ {(i = i0) → hsqr s (~ j) k
               ; (i = i1) → h k (s ∨ ~ j)
               ; (j = i0) → h' k (~ i ∧ s)
               ; (j = i1) → h k s
               ; (k = i0) → f (convPathP-filler p q r sqr (~ i) (~ j) s)
               ; (k = i1) → convPathP-filler p'  q' r' sqr' (~ i) (~ j) s})
             (h k (~ j)))
