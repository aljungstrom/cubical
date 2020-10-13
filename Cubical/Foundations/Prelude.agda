{-

This file proves a variety of basic results about paths:

- refl, sym, cong and composition of paths. This is used to set up
  equational reasoning.

- Transport, subst and functional extensionality

- J and its computation rule (up to a path)

- Σ-types and contractibility of singletons

- Converting PathP to and from a homogeneous path with transp

- Direct definitions of lower h-levels

- Export natural numbers

- Export universe lifting

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Prelude where

open import Cubical.Core.Primitives public

infixr 30 _∙_
infix  3 _∎
infixr 2 _≡⟨_⟩_
infixr 2.5 _≡⟨_⟩≡⟨_⟩_

-- Basic theory about paths. These proofs should typically be
-- inlined. This module also makes equational reasoning work with
-- (non-dependent) paths.

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : A → Type ℓ
    x y z w : A

refl : x ≡ x
refl {x = x} = λ _ → x
{-# INLINE refl #-}

sym : x ≡ y → y ≡ x
sym p i = p (~ i)
{-# INLINE sym #-}

symP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} →
       (p : PathP A x y) → PathP (λ i → A (~ i)) y x
symP p j = p (~ j)

cong : ∀ (f : (a : A) → B a) (p : x ≡ y) →
       PathP (λ i → B (p i)) (f x) (f y)
cong f p i = f (p i)
{-# INLINE cong #-}

cong₂ : ∀ {C : (a : A) → (b : B a) → Type ℓ} →
        (f : (a : A) → (b : B a) → C a b) →
        (p : x ≡ y) →
        {u : B x} {v : B y} (q : PathP (λ i → B (p i)) u v) →
        PathP (λ i → C (p i) (q i)) (f x u) (f y v)
cong₂ f p q i = f (p i) (q i)
{-# INLINE cong₂ #-}

{- The most natural notion of homogenous path composition
    in a cubical setting is double composition:

       x ∙ ∙ ∙ > w
       ^         ^
   p⁻¹ |         | r        ^
       |         |        j |
       y — — — > z          ∙ — >
            q                 i

   `p ∙∙ q ∙∙ r` gives the line at the top,
   `doubleCompPath-filler p q r` gives the whole square
-}

doubleComp-faces : {x y z w : A } (p : x ≡ y) (r : z ≡ w)
                 → (i : I) (j : I) → Partial (i ∨ ~ i) A
doubleComp-faces p r i j (i = i0) = p (~ j)
doubleComp-faces p r i j (i = i1) = r j

_∙∙_∙∙_ : w ≡ x → x ≡ y → y ≡ z → w ≡ z
(p ∙∙ q ∙∙ r) i =
  hcomp (doubleComp-faces p r i) (q i)

doubleCompPath-filler : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
                      → PathP (λ j → p (~ j) ≡ r j) q (p ∙∙ q ∙∙ r)
doubleCompPath-filler p q r j i =
  hfill (doubleComp-faces p r i) (inS (q i)) j

-- any two definitions of double composition are equal
compPath-unique : ∀ (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
                  → (α β : Σ[ s ∈ x ≡ w ] PathP (λ j → p (~ j) ≡ r j) q s)
                  → α ≡ β
compPath-unique p q r (α , α-filler) (β , β-filler) t
  = (λ i → cb i1 i) , (λ j i → cb j i)
  where cb : I → I → _
        cb j i = hfill (λ j → λ { (t = i0) → α-filler j i
                                ; (t = i1) → β-filler j i
                                ; (i = i0) → p (~ j)
                                ; (i = i1) → r j })
                       (inS (q i)) j

{- For single homogenous path composition, we take `p = refl`:

     x ∙ ∙ ∙ > z
     ‖         ^
     ‖         | r        ^
     ‖         |        j |
     x — — — > y          ∙ — >
          q                 i

   `q ∙ r` gives the line at the top,
   `compPath-filler q r` gives the whole square
-}

_∙_ : x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ∙∙ p ∙∙ q

compPath-filler : (p : x ≡ y) (q : y ≡ z) → PathP (λ j → x ≡ q j) p (p ∙ q)
compPath-filler p q = doubleCompPath-filler refl p q

-- We could have also defined single composition by taking `r = refl`:

_∙'_ : x ≡ y → y ≡ z → x ≡ z
p ∙' q = p ∙∙ q ∙∙ refl

compPath'-filler : (p : x ≡ y) (q : y ≡ z) → PathP (λ j → p (~ j) ≡ z) q (p ∙' q)
compPath'-filler p q = doubleCompPath-filler p q refl

-- It's easy to show that `p ∙ q` also has such a filler:
compPath-filler' : (p : x ≡ y) (q : y ≡ z) → PathP (λ j → p (~ j) ≡ z) q (p ∙ q)
compPath-filler' {z = z} p q j i =
  hcomp (λ k → λ { (i = i0) → p (~ j)
                 ; (i = i1) → q k
                 ; (j = i0) → q (i ∧ k) })
        (p (i ∨ ~ j))
-- Note: We can omit a (j = i1) case here since when (j = i1), the whole expression is
--  definitionally equal to `p ∙ q`. (Notice that `p ∙ q` is also an hcomp.) Nevertheless,
--  we could have given `compPath-filler p q k i` as the (j = i1) case.

-- From this, we can show that these two notions of composition are the same
compPath≡compPath' : (p : x ≡ y) (q : y ≡ z) → p ∙ q ≡ p ∙' q
compPath≡compPath' p q j =
  compPath-unique p q refl (p ∙ q  , compPath-filler' p q)
                           (p ∙' q , compPath'-filler p q) j .fst

-- Heterogeneous path composition and its filler:

compPathP : ∀ {A : I → Type ℓ} {x : A i0} {y : A i1} {B_i1 : Type ℓ} {B : (A i1) ≡ B_i1} {z : B i1}
            → PathP A x y → PathP (λ i → B i) y z → PathP (λ j → ((λ i → A i) ∙ B) j) x z
compPathP {A = A} {x = x} {B = B} p q i =
  comp (λ j → compPath-filler (λ i → A i) B j i)
       (λ j → λ { (i = i0) → x ;
                  (i = i1) → q j })
       (p i)


compPathP' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y z : A} {x' : B x} {y' : B y} {z' : B z} {p : x ≡ y} {q : y ≡ z}
             (P : PathP (λ i → B (p i)) x' y') (Q : PathP (λ i → B (q i)) y' z')
          → PathP (λ i → B ((p ∙ q) i)) x' z'
compPathP' {B = B} {x' = x'} {p = p} {q = q} P Q i =
  comp (λ j → B (compPath-filler p q j i))
       (λ j → λ { (i = i0) → x'  ;
                  (i = i1) → Q j })
       (P i)


compPathP-filler : ∀ {A : I → Type ℓ} {x : A i0} {y : A i1} {B_i1 : Type ℓ} {B : A i1 ≡ B_i1} {z : B i1}
                   → (p : PathP A x y) (q : PathP (λ i → B i) y z)
                   → PathP (λ j → PathP (λ k → (compPath-filler (λ i → A i) B j k)) x (q j)) p (compPathP p q)
compPathP-filler {A = A} {x = x} {B = B} p q j i =
  fill (λ j → compPath-filler (λ i → A i) B j i)
       (λ j → λ { (i = i0) → x ;
                  (i = i1) → q j })
       (inS (p i)) j



compPathP'-filler : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y z : A} {x' : B x} {y' : B y} {z' : B z} {p : x ≡ y} {q : y ≡ z}
             (P : PathP (λ i → B (p i)) x' y') (Q : PathP (λ i → B (q i)) y' z')
          → PathP (λ j → PathP (λ i → B (compPath-filler p q j i)) x' (Q j)) P (compPathP' {x = x} {y = y} {x' = x'} {y' = y'} P Q)
compPathP'-filler {B = B} {x' = x'} {p = p} {q = q} P Q j i =
  fill (λ j → B (compPath-filler p q j i))
       (λ j → λ { (i = i0) → x'  ;
                  (i = i1) → Q j })
       (inS (P i))
       j

_≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z

≡⟨⟩-syntax : (x : A) → x ≡ y → y ≡ z → x ≡ z
≡⟨⟩-syntax = _≡⟨_⟩_
infixr 2 ≡⟨⟩-syntax
syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y

≡⟨⟩⟨⟩-syntax : (x y : A) → x ≡ y → y ≡ z → z ≡ w → x ≡ w
≡⟨⟩⟨⟩-syntax x y p q r = p ∙∙ q ∙∙ r
infixr 3 ≡⟨⟩⟨⟩-syntax
syntax ≡⟨⟩⟨⟩-syntax x y B C = x ≡⟨ B ⟩≡ y ≡⟨ C ⟩≡

_≡⟨_⟩≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → z ≡ w → x ≡ w
_ ≡⟨ x≡y ⟩≡⟨ y≡z ⟩ z≡w = x≡y ∙∙ y≡z ∙∙ z≡w

_∎ : (x : A) → x ≡ x
_ ∎ = refl


-- Transport, subst and functional extensionality

-- transport is a special case of transp
transport : {A B : Type ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

-- Transporting in a constant family is the identity function (up to a
-- path). If we would have regularity this would be definitional.
transportRefl : (x : A) → transport refl x ≡ x
transportRefl {A = A} x i = transp (λ _ → A) i x

transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : A)
                   → PathP (λ i → p i) x (transport p x)
transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x

-- We want B to be explicit in subst
subst : (B : A → Type ℓ') (p : x ≡ y) → B x → B y
subst B p pa = transport (λ i → B (p i)) pa

substRefl : (px : B x) → subst B refl px ≡ px
substRefl px = transportRefl px

funExt : {B : A → I → Type ℓ'}
  {f : (x : A) → B x i0} {g : (x : A) → B x i1}
  → ((x : A) → PathP (B x) (f x) (g x))
  → PathP (λ i → (x : A) → B x i) f g
funExt p i x = p x i

implicitFunExt : {B : A → I → Type ℓ'}
  {f : {x : A} → B x i0} {g : {x : A} → B x i1}
  → ({x : A} → PathP (B x) (f {x}) (g {x}))
  → PathP (λ i → {x : A} → B x i) f g
implicitFunExt p i {x} = p {x} i

-- the inverse to funExt (see Functions.FunExtEquiv), converting paths
-- between functions to homotopies; `funExt⁻` is called `happly` and
-- defined by path induction in the HoTT book (see function 2.9.2 in
-- section 2.9)
funExt⁻ : {B : A → I → Type ℓ'}
  {f : (x : A) → B x i0} {g : (x : A) → B x i1}
  → PathP (λ i → (x : A) → B x i) f g
  → ((x : A) → PathP (B x) (f x) (g x))
funExt⁻ eq x i = eq i x

-- J for paths and its computation rule

module _ (P : ∀ y → x ≡ y → Type ℓ') (d : P x refl) where
  J : (p : x ≡ y) → P y p
  J p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

  JRefl : J refl ≡ d
  JRefl = transportRefl d

  J-∙ : (p : x ≡ y) (q : y ≡ z)
    → J (p ∙ q) ≡ transport (λ i → P (q i) (λ j → compPath-filler p q i j)) (J p)
  J-∙ p q k =
    transp
      (λ i → P (q (i ∨ ~ k))
      (λ j → compPath-filler p q (i ∨ ~ k) j)) (~ k)
      (J (λ j → compPath-filler p q (~ k) j))

-- Converting to and from a PathP

module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where
  toPathP : transp (\ i → A i) i0 x ≡ y → PathP A x y
  toPathP p i = hcomp (λ j → λ { (i = i0) → x
                               ; (i = i1) → p j })
                      (transp (λ j → A (i ∧ j)) (~ i) x)

  fromPathP : PathP A x y → transp (\ i → A i) i0 x ≡ y
  fromPathP p i = transp (λ j → A (i ∨ j)) i (p i)

-- Whiskering a dependent path by a path

_◁_ : ∀ {ℓ} {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ : A i1}
  → a₀ ≡ a₀' → PathP A a₀' a₁ → PathP A a₀ a₁
(p ◁ q) i =
  hcomp (λ j → λ {(i = i0) → p (~ j); (i = i1) → q i1}) (q i)

_▷_ : ∀ {ℓ} {A : I → Type ℓ} {a₀ : A i0} {a₁ a₁' : A i1}
  → PathP A a₀ a₁ → a₁ ≡ a₁' → PathP A a₀ a₁'
(p ▷ q) i =
  hcomp (λ j → λ {(i = i0) → p i0; (i = i1) → q j}) (p i)

-- Direct definitions of lower h-levels

isContr : Type ℓ → Type ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)

isGroupoid : Type ℓ → Type ℓ
isGroupoid A = ∀ a b → isSet (Path A a b)

is2Groupoid : Type ℓ → Type ℓ
is2Groupoid A = ∀ a b → isGroupoid (Path A a b)

-- Contractibility of singletons

singl : (a : A) → Type _
singl {A = A} a = Σ[ x ∈ A ] (a ≡ x)

isContrSingl : (a : A) → isContr (singl a)
isContrSingl a = (a , refl) , λ p i → p .snd i , λ j → p .snd (i ∧ j)

isContrSinglP : (A : I → Type ℓ) (a : A i0) → isContr (Σ[ x ∈ A i1 ] PathP A a x)
isContrSinglP A a .fst = _ , transport-filler (λ i → A i) a
isContrSinglP A a .snd (x , p) i =
  _ , λ j → fill (\ i → A i) (λ j → λ {(i = i0) → transport-filler (λ i → A i) a j; (i = i1) → p j}) (inS a) j

SquareP :
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → Type ℓ
SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

Square :
  {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  → Type _
Square a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋

isSet' : Type ℓ → Type ℓ
isSet' A =
  {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  → Square a₀₋ a₁₋ a₋₀ a₋₁

Cube :
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
  → Type _
Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
  PathP (λ i → Square (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) (a₋₋₁ i)) a₀₋₋ a₁₋₋

isGroupoid' : Type ℓ → Type ℓ
isGroupoid' A =
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
  → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁

4Cube :
  {a₀₀₀₀ a₁₀₀₀ : A}
  {a₀₁₀₀ a₁₁₀₀ : A}
  {a₀₀₁₀ a₁₀₁₀ : A}
  {a₀₁₁₀ a₁₁₁₀ : A}
  {a₀₀₀₁ a₁₀₀₁ : A}
  {a₀₁₀₁ a₁₁₀₁ : A}
  {a₀₀₁₁ a₁₀₁₁ : A}
  {a₀₁₁₁ a₁₁₁₁ : A}
  {a₀₀₀₋ : Path A a₀₀₀₀ a₀₀₀₁}
  {a₁₀₀₋ : Path A a₁₀₀₀ a₁₀₀₁}
  {a₀₁₀₋ : Path A a₀₁₀₀ a₀₁₀₁}
  {a₁₁₀₋ : Path A a₁₁₀₀ a₁₁₀₁}
  {a₀₀₁₋ : Path A a₀₀₁₀ a₀₀₁₁}
  {a₁₀₁₋ : Path A a₁₀₁₀ a₁₀₁₁}
  {a₀₁₁₋ : Path A a₀₁₁₀ a₀₁₁₁}
  {a₁₁₁₋ : Path A a₁₁₁₀ a₁₁₁₁}
  {a₀₀₋₀ : Path A a₀₀₀₀ a₀₀₁₀}
  {a₁₀₋₀ : Path A a₁₀₀₀ a₁₀₁₀}
  {a₀₁₋₀ : Path A a₀₁₀₀ a₀₁₁₀}
  {a₁₁₋₀ : Path A a₁₁₀₀ a₁₁₁₀}
  {a₀₋₀₀ : Path A a₀₀₀₀ a₀₁₀₀}
  {a₁₋₀₀ : Path A a₁₀₀₀ a₁₁₀₀}
  {a₋₀₀₀ : Path A a₀₀₀₀ a₁₀₀₀}
  {a₋₁₀₀ : Path A a₀₁₀₀ a₁₁₀₀}
  {a₀₋₁₀ : Path A a₀₀₁₀ a₀₁₁₀}
  {a₁₋₁₀ : Path A a₁₀₁₀ a₁₁₁₀}
  {a₋₀₁₀ : Path A a₀₀₁₀ a₁₀₁₀}
  {a₋₁₁₀ : Path A a₀₁₁₀ a₁₁₁₀}
  {a₀₀₋₁ : Path A a₀₀₀₁ a₀₀₁₁}
  {a₁₀₋₁ : Path A a₁₀₀₁ a₁₀₁₁}
  {a₀₁₋₁ : Path A a₀₁₀₁ a₀₁₁₁}
  {a₁₁₋₁ : Path A a₁₁₀₁ a₁₁₁₁}
  {a₀₋₀₁ : Path A a₀₀₀₁ a₀₁₀₁}
  {a₁₋₀₁ : Path A a₁₀₀₁ a₁₁₀₁}
  {a₋₀₀₁ : Path A a₀₀₀₁ a₁₀₀₁}
  {a₋₁₀₁ : Path A a₀₁₀₁ a₁₁₀₁}
  {a₀₋₁₁ : Path A a₀₀₁₁ a₀₁₁₁}
  {a₁₋₁₁ : Path A a₁₀₁₁ a₁₁₁₁}
  {a₋₀₁₁ : Path A a₀₀₁₁ a₁₀₁₁}
  {a₋₁₁₁ : Path A a₀₁₁₁ a₁₁₁₁}
  {a₀₀₋₋ : Square a₀₀₀₋ a₀₀₁₋ a₀₀₋₀ a₀₀₋₁}
  {a₁₀₋₋ : Square a₁₀₀₋ a₁₀₁₋ a₁₀₋₀ a₁₀₋₁}
  {a₀₁₋₋ : Square a₀₁₀₋ a₀₁₁₋ a₀₁₋₀ a₀₁₋₁}
  {a₁₁₋₋ : Square a₁₁₀₋ a₁₁₁₋ a₁₁₋₀ a₁₁₋₁}
  {a₀₋₀₋ : Square a₀₀₀₋ a₀₁₀₋ a₀₋₀₀ a₀₋₀₁}
  {a₁₋₀₋ : Square a₁₀₀₋ a₁₁₀₋ a₁₋₀₀ a₁₋₀₁}
  {a₋₀₀₋ : Square a₀₀₀₋ a₁₀₀₋ a₋₀₀₀ a₋₀₀₁}
  {a₋₁₀₋ : Square a₀₁₀₋ a₁₁₀₋ a₋₁₀₀ a₋₁₀₁}
  {a₀₋₁₋ : Square a₀₀₁₋ a₀₁₁₋ a₀₋₁₀ a₀₋₁₁}
  {a₁₋₁₋ : Square a₁₀₁₋ a₁₁₁₋ a₁₋₁₀ a₁₋₁₁}
  {a₋₀₁₋ : Square a₀₀₁₋ a₁₀₁₋ a₋₀₁₀ a₋₀₁₁}
  {a₋₁₁₋ : Square a₀₁₁₋ a₁₁₁₋ a₋₁₁₀ a₋₁₁₁}
  {a₀₋₋₀ : Square a₀₀₋₀ a₀₁₋₀ a₀₋₀₀ a₀₋₁₀}
  {a₁₋₋₀ : Square a₁₀₋₀ a₁₁₋₀ a₁₋₀₀ a₁₋₁₀}
  {a₋₀₋₀ : Square a₀₀₋₀ a₁₀₋₀ a₋₀₀₀ a₋₀₁₀}
  {a₋₁₋₀ : Square a₀₁₋₀ a₁₁₋₀ a₋₁₀₀ a₋₁₁₀}
  {a₋₋₀₀ : Square a₀₋₀₀ a₁₋₀₀ a₋₀₀₀ a₋₁₀₀}
  {a₋₋₁₀ : Square a₀₋₁₀ a₁₋₁₀ a₋₀₁₀ a₋₁₁₀}
  {a₀₋₋₁ : Square a₀₀₋₁ a₀₁₋₁ a₀₋₀₁ a₀₋₁₁}
  {a₁₋₋₁ : Square a₁₀₋₁ a₁₁₋₁ a₁₋₀₁ a₁₋₁₁}
  {a₋₀₋₁ : Square a₀₀₋₁ a₁₀₋₁ a₋₀₀₁ a₋₀₁₁}
  {a₋₁₋₁ : Square a₀₁₋₁ a₁₁₋₁ a₋₁₀₁ a₋₁₁₁}
  {a₋₋₀₁ : Square a₀₋₀₁ a₁₋₀₁ a₋₀₀₁ a₋₁₀₁}
  {a₋₋₁₁ : Square a₀₋₁₁ a₁₋₁₁ a₋₀₁₁ a₋₁₁₁}
  (a₀₋₋₋ : Cube a₀₀₋₋ a₀₁₋₋ a₀₋₀₋ a₀₋₁₋ a₀₋₋₀ a₀₋₋₁)
  (a₁₋₋₋ : Cube a₁₀₋₋ a₁₁₋₋ a₁₋₀₋ a₁₋₁₋ a₁₋₋₀ a₁₋₋₁)
  (a₋₀₋₋ : Cube a₀₀₋₋ a₁₀₋₋ a₋₀₀₋ a₋₀₁₋ a₋₀₋₀ a₋₀₋₁)
  (a₋₁₋₋ : Cube a₀₁₋₋ a₁₁₋₋ a₋₁₀₋ a₋₁₁₋ a₋₁₋₀ a₋₁₋₁)
  (a₋₋₀₋ : Cube a₀₋₀₋ a₁₋₀₋ a₋₀₀₋ a₋₁₀₋ a₋₋₀₀ a₋₋₀₁)
  (a₋₋₁₋ : Cube a₀₋₁₋ a₁₋₁₋ a₋₀₁₋ a₋₁₁₋ a₋₋₁₀ a₋₋₁₁)
  (a₋₋₋₀ : Cube a₀₋₋₀ a₁₋₋₀ a₋₀₋₀ a₋₁₋₀ a₋₋₀₀ a₋₋₁₀)
  (a₋₋₋₁ : Cube a₀₋₋₁ a₁₋₋₁ a₋₀₋₁ a₋₁₋₁ a₋₋₀₁ a₋₋₁₁)
  → Type _
4Cube a₀₋₋₋ a₁₋₋₋ a₋₀₋₋ a₋₁₋₋ a₋₋₀₋ a₋₋₁₋ a₋₋₋₀ a₋₋₋₁ = PathP (λ i → (Cube (a₋₀₋₋ i) (a₋₁₋₋ i) (a₋₋₀₋ i) (a₋₋₁₋ i) (a₋₋₋₀ i) (a₋₋₋₁ i))) a₀₋₋₋ a₁₋₋₋

is2Groupoid' : Type ℓ → Type ℓ
is2Groupoid' A =
  {a₀₀₀₀ a₁₀₀₀ : A}
  {a₀₁₀₀ a₁₁₀₀ : A}
  {a₀₀₁₀ a₁₀₁₀ : A}
  {a₀₁₁₀ a₁₁₁₀ : A}
  {a₀₀₀₁ a₁₀₀₁ : A}
  {a₀₁₀₁ a₁₁₀₁ : A}
  {a₀₀₁₁ a₁₀₁₁ : A}
  {a₀₁₁₁ a₁₁₁₁ : A}
  {a₀₀₀₋ : Path A a₀₀₀₀ a₀₀₀₁}
  {a₁₀₀₋ : Path A a₁₀₀₀ a₁₀₀₁}
  {a₀₁₀₋ : Path A a₀₁₀₀ a₀₁₀₁}
  {a₁₁₀₋ : Path A a₁₁₀₀ a₁₁₀₁}
  {a₀₀₁₋ : Path A a₀₀₁₀ a₀₀₁₁}
  {a₁₀₁₋ : Path A a₁₀₁₀ a₁₀₁₁}
  {a₀₁₁₋ : Path A a₀₁₁₀ a₀₁₁₁}
  {a₁₁₁₋ : Path A a₁₁₁₀ a₁₁₁₁}
  {a₀₀₋₀ : Path A a₀₀₀₀ a₀₀₁₀}
  {a₁₀₋₀ : Path A a₁₀₀₀ a₁₀₁₀}
  {a₀₁₋₀ : Path A a₀₁₀₀ a₀₁₁₀}
  {a₁₁₋₀ : Path A a₁₁₀₀ a₁₁₁₀}
  {a₀₋₀₀ : Path A a₀₀₀₀ a₀₁₀₀}
  {a₁₋₀₀ : Path A a₁₀₀₀ a₁₁₀₀}
  {a₋₀₀₀ : Path A a₀₀₀₀ a₁₀₀₀}
  {a₋₁₀₀ : Path A a₀₁₀₀ a₁₁₀₀}
  {a₀₋₁₀ : Path A a₀₀₁₀ a₀₁₁₀}
  {a₁₋₁₀ : Path A a₁₀₁₀ a₁₁₁₀}
  {a₋₀₁₀ : Path A a₀₀₁₀ a₁₀₁₀}
  {a₋₁₁₀ : Path A a₀₁₁₀ a₁₁₁₀}
  {a₀₀₋₁ : Path A a₀₀₀₁ a₀₀₁₁}
  {a₁₀₋₁ : Path A a₁₀₀₁ a₁₀₁₁}
  {a₀₁₋₁ : Path A a₀₁₀₁ a₀₁₁₁}
  {a₁₁₋₁ : Path A a₁₁₀₁ a₁₁₁₁}
  {a₀₋₀₁ : Path A a₀₀₀₁ a₀₁₀₁}
  {a₁₋₀₁ : Path A a₁₀₀₁ a₁₁₀₁}
  {a₋₀₀₁ : Path A a₀₀₀₁ a₁₀₀₁}
  {a₋₁₀₁ : Path A a₀₁₀₁ a₁₁₀₁}
  {a₀₋₁₁ : Path A a₀₀₁₁ a₀₁₁₁}
  {a₁₋₁₁ : Path A a₁₀₁₁ a₁₁₁₁}
  {a₋₀₁₁ : Path A a₀₀₁₁ a₁₀₁₁}
  {a₋₁₁₁ : Path A a₀₁₁₁ a₁₁₁₁}
  {a₀₀₋₋ : Square a₀₀₀₋ a₀₀₁₋ a₀₀₋₀ a₀₀₋₁}
  {a₁₀₋₋ : Square a₁₀₀₋ a₁₀₁₋ a₁₀₋₀ a₁₀₋₁}
  {a₀₁₋₋ : Square a₀₁₀₋ a₀₁₁₋ a₀₁₋₀ a₀₁₋₁}
  {a₁₁₋₋ : Square a₁₁₀₋ a₁₁₁₋ a₁₁₋₀ a₁₁₋₁}
  {a₀₋₀₋ : Square a₀₀₀₋ a₀₁₀₋ a₀₋₀₀ a₀₋₀₁}
  {a₁₋₀₋ : Square a₁₀₀₋ a₁₁₀₋ a₁₋₀₀ a₁₋₀₁}
  {a₋₀₀₋ : Square a₀₀₀₋ a₁₀₀₋ a₋₀₀₀ a₋₀₀₁}
  {a₋₁₀₋ : Square a₀₁₀₋ a₁₁₀₋ a₋₁₀₀ a₋₁₀₁}
  {a₀₋₁₋ : Square a₀₀₁₋ a₀₁₁₋ a₀₋₁₀ a₀₋₁₁}
  {a₁₋₁₋ : Square a₁₀₁₋ a₁₁₁₋ a₁₋₁₀ a₁₋₁₁}
  {a₋₀₁₋ : Square a₀₀₁₋ a₁₀₁₋ a₋₀₁₀ a₋₀₁₁}
  {a₋₁₁₋ : Square a₀₁₁₋ a₁₁₁₋ a₋₁₁₀ a₋₁₁₁}
  {a₀₋₋₀ : Square a₀₀₋₀ a₀₁₋₀ a₀₋₀₀ a₀₋₁₀}
  {a₁₋₋₀ : Square a₁₀₋₀ a₁₁₋₀ a₁₋₀₀ a₁₋₁₀}
  {a₋₀₋₀ : Square a₀₀₋₀ a₁₀₋₀ a₋₀₀₀ a₋₀₁₀}
  {a₋₁₋₀ : Square a₀₁₋₀ a₁₁₋₀ a₋₁₀₀ a₋₁₁₀}
  {a₋₋₀₀ : Square a₀₋₀₀ a₁₋₀₀ a₋₀₀₀ a₋₁₀₀}
  {a₋₋₁₀ : Square a₀₋₁₀ a₁₋₁₀ a₋₀₁₀ a₋₁₁₀}
  {a₀₋₋₁ : Square a₀₀₋₁ a₀₁₋₁ a₀₋₀₁ a₀₋₁₁}
  {a₁₋₋₁ : Square a₁₀₋₁ a₁₁₋₁ a₁₋₀₁ a₁₋₁₁}
  {a₋₀₋₁ : Square a₀₀₋₁ a₁₀₋₁ a₋₀₀₁ a₋₀₁₁}
  {a₋₁₋₁ : Square a₀₁₋₁ a₁₁₋₁ a₋₁₀₁ a₋₁₁₁}
  {a₋₋₀₁ : Square a₀₋₀₁ a₁₋₀₁ a₋₀₀₁ a₋₁₀₁}
  {a₋₋₁₁ : Square a₀₋₁₁ a₁₋₁₁ a₋₀₁₁ a₋₁₁₁}
  (a₀₋₋₋ : Cube a₀₀₋₋ a₀₁₋₋ a₀₋₀₋ a₀₋₁₋ a₀₋₋₀ a₀₋₋₁)
  (a₁₋₋₋ : Cube a₁₀₋₋ a₁₁₋₋ a₁₋₀₋ a₁₋₁₋ a₁₋₋₀ a₁₋₋₁)
  (a₋₀₋₋ : Cube a₀₀₋₋ a₁₀₋₋ a₋₀₀₋ a₋₀₁₋ a₋₀₋₀ a₋₀₋₁)
  (a₋₁₋₋ : Cube a₀₁₋₋ a₁₁₋₋ a₋₁₀₋ a₋₁₁₋ a₋₁₋₀ a₋₁₋₁)
  (a₋₋₀₋ : Cube a₀₋₀₋ a₁₋₀₋ a₋₀₀₋ a₋₁₀₋ a₋₋₀₀ a₋₋₀₁)
  (a₋₋₁₋ : Cube a₀₋₁₋ a₁₋₁₋ a₋₀₁₋ a₋₁₁₋ a₋₋₁₀ a₋₋₁₁)
  (a₋₋₋₀ : Cube a₀₋₋₀ a₁₋₋₀ a₋₀₋₀ a₋₁₋₀ a₋₋₀₀ a₋₋₁₀)
  (a₋₋₋₁ : Cube a₀₋₋₁ a₁₋₋₁ a₋₀₋₁ a₋₁₋₁ a₋₋₀₁ a₋₋₁₁)
  → 4Cube a₀₋₋₋ a₁₋₋₋ a₋₀₋₋ a₋₁₋₋ a₋₋₀₋ a₋₋₁₋ a₋₋₋₀ a₋₋₋₁
{-
5Cube :
  {a₀₀₀₀₀ a₁₀₀₀₀ : A}
  {a₀₁₀₀₀ a₁₁₀₀₀ : A}
  {a₀₀₁₀₀ a₁₀₁₀₀ : A}
  {a₀₁₁₀₀ a₁₁₁₀₀ : A}
  {a₀₀₀₁₀ a₁₀₀₁₀ : A}
  {a₀₁₀₁₀ a₁₁₀₁₀ : A}
  {a₀₀₁₁₀ a₁₀₁₁₀ : A}
  {a₀₁₁₁₀ a₁₁₁₁₀ : A}
  {a₀₀₀₀₁ a₁₀₀₀₁ : A}
  {a₀₁₀₀₁ a₁₁₀₀₁ : A}
  {a₀₀₁₀₁ a₁₀₁₀₁ : A}
  {a₀₁₁₀₁ a₁₁₁₀₁ : A}
  {a₀₀₀₁₁ a₁₀₀₁₁ : A}
  {a₀₁₀₁₁ a₁₁₀₁₁ : A}
  {a₀₀₁₁₁ a₁₀₁₁₁ : A}
  {a₀₁₁₁₁ a₁₁₁₁₁ : A}
  {a₀₀₀₀₋ : Path A a₀₀₀₀₀ a₀₀₀₀₁}
  {a₁₀₀₀₋ : Path A a₁₀₀₀₀ a₁₀₀₀₁}
  {a₀₁₀₀₋ : Path A a₀₁₀₀₀ a₀₁₀₀₁}
  {a₁₁₀₀₋ : Path A a₁₁₀₀₀ a₁₁₀₀₁}
  {a₀₀₁₀₋ : Path A a₀₀₁₀₀ a₀₀₁₀₁}
  {a₁₀₁₀₋ : Path A a₁₀₁₀₀ a₁₀₁₀₁}
  {a₀₁₁₀₋ : Path A a₀₁₁₀₀ a₀₁₁₀₁}
  {a₁₁₁₀₋ : Path A a₁₁₁₀₀ a₁₁₁₀₁}
  {a₀₀₀₁₋ : Path A a₀₀₀₁₀ a₀₀₀₁₁}
  {a₁₀₀₁₋ : Path A a₁₀₀₁₀ a₁₀₀₁₁}
  {a₀₁₀₁₋ : Path A a₀₁₀₁₀ a₀₁₀₁₁}
  {a₁₁₀₁₋ : Path A a₁₁₀₁₀ a₁₁₀₁₁}
  {a₀₀₁₁₋ : Path A a₀₀₁₁₀ a₀₀₁₁₁}
  {a₁₀₁₁₋ : Path A a₁₀₁₁₀ a₁₀₁₁₁}
  {a₀₁₁₁₋ : Path A a₀₁₁₁₀ a₀₁₁₁₁}
  {a₁₁₁₁₋ : Path A a₁₁₁₁₀ a₁₁₁₁₁}
  {a₀₀₀₋₀ : Path A a₀₀₀₀₀ a₀₀₀₁₀}
  {a₁₀₀₋₀ : Path A a₁₀₀₀₀ a₁₀₀₁₀}
  {a₀₁₀₋₀ : Path A a₀₁₀₀₀ a₀₁₀₁₀}
  {a₁₁₀₋₀ : Path A a₁₁₀₀₀ a₁₁₀₁₀}
  {a₀₀₁₋₀ : Path A a₀₀₁₀₀ a₀₀₁₁₀}
  {a₁₀₁₋₀ : Path A a₁₀₁₀₀ a₁₀₁₁₀}
  {a₀₁₁₋₀ : Path A a₀₁₁₀₀ a₀₁₁₁₀}
  {a₁₁₁₋₀ : Path A a₁₁₁₀₀ a₁₁₁₁₀}
  {a₀₀₋₀₀ : Path A a₀₀₀₀₀ a₀₀₁₀₀}
  {a₁₀₋₀₀ : Path A a₁₀₀₀₀ a₁₀₁₀₀}
  {a₀₁₋₀₀ : Path A a₀₁₀₀₀ a₀₁₁₀₀}
  {a₁₁₋₀₀ : Path A a₁₁₀₀₀ a₁₁₁₀₀}
  {a₀₋₀₀₀ : Path A a₀₀₀₀₀ a₀₁₀₀₀}
  {a₁₋₀₀₀ : Path A a₁₀₀₀₀ a₁₁₀₀₀}
  {a₋₀₀₀₀ : Path A a₀₀₀₀₀ a₁₀₀₀₀}
  {a₋₁₀₀₀ : Path A a₀₁₀₀₀ a₁₁₀₀₀}
  {a₀₋₁₀₀ : Path A a₀₀₁₀₀ a₀₁₁₀₀}
  {a₁₋₁₀₀ : Path A a₁₀₁₀₀ a₁₁₁₀₀}
  {a₋₀₁₀₀ : Path A a₀₀₁₀₀ a₁₀₁₀₀}
  {a₋₁₁₀₀ : Path A a₀₁₁₀₀ a₁₁₁₀₀}
  {a₀₀₋₁₀ : Path A a₀₀₀₁₀ a₀₀₁₁₀}
  {a₁₀₋₁₀ : Path A a₁₀₀₁₀ a₁₀₁₁₀}
  {a₀₁₋₁₀ : Path A a₀₁₀₁₀ a₀₁₁₁₀}
  {a₁₁₋₁₀ : Path A a₁₁₀₁₀ a₁₁₁₁₀}
  {a₀₋₀₁₀ : Path A a₀₀₀₁₀ a₀₁₀₁₀}
  {a₁₋₀₁₀ : Path A a₁₀₀₁₀ a₁₁₀₁₀}
  {a₋₀₀₁₀ : Path A a₀₀₀₁₀ a₁₀₀₁₀}
  {a₋₁₀₁₀ : Path A a₀₁₀₁₀ a₁₁₀₁₀}
  {a₀₋₁₁₀ : Path A a₀₀₁₁₀ a₀₁₁₁₀}
  {a₁₋₁₁₀ : Path A a₁₀₁₁₀ a₁₁₁₁₀}
  {a₋₀₁₁₀ : Path A a₀₀₁₁₀ a₁₀₁₁₀}
  {a₋₁₁₁₀ : Path A a₀₁₁₁₀ a₁₁₁₁₀}
  {a₀₀₀₋₁ : Path A a₀₀₀₀₁ a₀₀₀₁₁}
  {a₁₀₀₋₁ : Path A a₁₀₀₀₁ a₁₀₀₁₁}
  {a₀₁₀₋₁ : Path A a₀₁₀₀₁ a₀₁₀₁₁}
  {a₁₁₀₋₁ : Path A a₁₁₀₀₁ a₁₁₀₁₁}
  {a₀₀₁₋₁ : Path A a₀₀₁₀₁ a₀₀₁₁₁}
  {a₁₀₁₋₁ : Path A a₁₀₁₀₁ a₁₀₁₁₁}
  {a₀₁₁₋₁ : Path A a₀₁₁₀₁ a₀₁₁₁₁}
  {a₁₁₁₋₁ : Path A a₁₁₁₀₁ a₁₁₁₁₁}
  {a₀₀₋₀₁ : Path A a₀₀₀₀₁ a₀₀₁₀₁}
  {a₁₀₋₀₁ : Path A a₁₀₀₀₁ a₁₀₁₀₁}
  {a₀₁₋₀₁ : Path A a₀₁₀₀₁ a₀₁₁₀₁}
  {a₁₁₋₀₁ : Path A a₁₁₀₀₁ a₁₁₁₀₁}
  {a₀₋₀₀₁ : Path A a₀₀₀₀₁ a₀₁₀₀₁}
  {a₁₋₀₀₁ : Path A a₁₀₀₀₁ a₁₁₀₀₁}
  {a₋₀₀₀₁ : Path A a₀₀₀₀₁ a₁₀₀₀₁}
  {a₋₁₀₀₁ : Path A a₀₁₀₀₁ a₁₁₀₀₁}
  {a₀₋₁₀₁ : Path A a₀₀₁₀₁ a₀₁₁₀₁}
  {a₁₋₁₀₁ : Path A a₁₀₁₀₁ a₁₁₁₀₁}
  {a₋₀₁₀₁ : Path A a₀₀₁₀₁ a₁₀₁₀₁}
  {a₋₁₁₀₁ : Path A a₀₁₁₀₁ a₁₁₁₀₁}
  {a₀₀₋₁₁ : Path A a₀₀₀₁₁ a₀₀₁₁₁}
  {a₁₀₋₁₁ : Path A a₁₀₀₁₁ a₁₀₁₁₁}
  {a₀₁₋₁₁ : Path A a₀₁₀₁₁ a₀₁₁₁₁}
  {a₁₁₋₁₁ : Path A a₁₁₀₁₁ a₁₁₁₁₁}
  {a₀₋₀₁₁ : Path A a₀₀₀₁₁ a₀₁₀₁₁}
  {a₁₋₀₁₁ : Path A a₁₀₀₁₁ a₁₁₀₁₁}
  {a₋₀₀₁₁ : Path A a₀₀₀₁₁ a₁₀₀₁₁}
  {a₋₁₀₁₁ : Path A a₀₁₀₁₁ a₁₁₀₁₁}
  {a₀₋₁₁₁ : Path A a₀₀₁₁₁ a₀₁₁₁₁}
  {a₁₋₁₁₁ : Path A a₁₀₁₁₁ a₁₁₁₁₁}
  {a₋₀₁₁₁ : Path A a₀₀₁₁₁ a₁₀₁₁₁}
  {a₋₁₁₁₁ : Path A a₀₁₁₁₁ a₁₁₁₁₁}
  {a₀₀₀₋₋ : Square a₀₀₀₀₋ a₀₀₀₁₋ a₀₀₀₋₀ a₀₀₀₋₁}
  {a₁₀₀₋₋ : Square a₁₀₀₀₋ a₁₀₀₁₋ a₁₀₀₋₀ a₁₀₀₋₁}
  {a₀₁₀₋₋ : Square a₀₁₀₀₋ a₀₁₀₁₋ a₀₁₀₋₀ a₀₁₀₋₁}
  {a₁₁₀₋₋ : Square a₁₁₀₀₋ a₁₁₀₁₋ a₁₁₀₋₀ a₁₁₀₋₁}
  {a₀₀₁₋₋ : Square a₀₀₁₀₋ a₀₀₁₁₋ a₀₀₁₋₀ a₀₀₁₋₁}
  {a₁₀₁₋₋ : Square a₁₀₁₀₋ a₁₀₁₁₋ a₁₀₁₋₀ a₁₀₁₋₁}
  {a₀₁₁₋₋ : Square a₀₁₁₀₋ a₀₁₁₁₋ a₀₁₁₋₀ a₀₁₁₋₁}
  {a₁₁₁₋₋ : Square a₁₁₁₀₋ a₁₁₁₁₋ a₁₁₁₋₀ a₁₁₁₋₁}
  {a₀₀₋₀₋ : Square a₀₀₀₀₋ a₀₀₁₀₋ a₀₀₋₀₀ a₀₀₋₀₁}
  {a₁₀₋₀₋ : Square a₁₀₀₀₋ a₁₀₁₀₋ a₁₀₋₀₀ a₁₀₋₀₁}
  {a₀₁₋₀₋ : Square a₀₁₀₀₋ a₀₁₁₀₋ a₀₁₋₀₀ a₀₁₋₀₁}
  {a₁₁₋₀₋ : Square a₁₁₀₀₋ a₁₁₁₀₋ a₁₁₋₀₀ a₁₁₋₀₁}
  {a₀₋₀₀₋ : Square a₀₀₀₀₋ a₀₁₀₀₋ a₀₋₀₀₀ a₀₋₀₀₁}
  {a₁₋₀₀₋ : Square a₁₀₀₀₋ a₁₁₀₀₋ a₁₋₀₀₀ a₁₋₀₀₁}
  {a₋₀₀₀₋ : Square a₀₀₀₀₋ a₁₀₀₀₋ a₋₀₀₀₀ a₋₀₀₀₁}
  {a₋₁₀₀₋ : Square a₀₁₀₀₋ a₁₁₀₀₋ a₋₁₀₀₀ a₋₁₀₀₁}
  {a₀₋₁₀₋ : Square a₀₀₁₀₋ a₀₁₁₀₋ a₀₋₁₀₀ a₀₋₁₀₁}
  {a₁₋₁₀₋ : Square a₁₀₁₀₋ a₁₁₁₀₋ a₁₋₁₀₀ a₁₋₁₀₁}
  {a₋₀₁₀₋ : Square a₀₀₁₀₋ a₁₀₁₀₋ a₋₀₁₀₀ a₋₀₁₀₁}
  {a₋₁₁₀₋ : Square a₀₁₁₀₋ a₁₁₁₀₋ a₋₁₁₀₀ a₋₁₁₀₁}
  {a₀₀₋₁₋ : Square a₀₀₀₁₋ a₀₀₁₁₋ a₀₀₋₁₀ a₀₀₋₁₁}
  {a₁₀₋₁₋ : Square a₁₀₀₁₋ a₁₀₁₁₋ a₁₀₋₁₀ a₁₀₋₁₁}
  {a₀₁₋₁₋ : Square a₀₁₀₁₋ a₀₁₁₁₋ a₀₁₋₁₀ a₀₁₋₁₁}
  {a₁₁₋₁₋ : Square a₁₁₀₁₋ a₁₁₁₁₋ a₁₁₋₁₀ a₁₁₋₁₁}
  {a₀₋₀₁₋ : Square a₀₀₀₁₋ a₀₁₀₁₋ a₀₋₀₁₀ a₀₋₀₁₁}
  {a₁₋₀₁₋ : Square a₁₀₀₁₋ a₁₁₀₁₋ a₁₋₀₁₀ a₁₋₀₁₁}
  {a₋₀₀₁₋ : Square a₀₀₀₁₋ a₁₀₀₁₋ a₋₀₀₁₀ a₋₀₀₁₁}
  {a₋₁₀₁₋ : Square a₀₁₀₁₋ a₁₁₀₁₋ a₋₁₀₁₀ a₋₁₀₁₁}
  {a₀₋₁₁₋ : Square a₀₀₁₁₋ a₀₁₁₁₋ a₀₋₁₁₀ a₀₋₁₁₁}
  {a₁₋₁₁₋ : Square a₁₀₁₁₋ a₁₁₁₁₋ a₁₋₁₁₀ a₁₋₁₁₁}
  {a₋₀₁₁₋ : Square a₀₀₁₁₋ a₁₀₁₁₋ a₋₀₁₁₀ a₋₀₁₁₁}
  {a₋₁₁₁₋ : Square a₀₁₁₁₋ a₁₁₁₁₋ a₋₁₁₁₀ a₋₁₁₁₁}
  {a₀₀₋₋₀ : Square a₀₀₀₋₀ a₀₀₁₋₀ a₀₀₋₀₀ a₀₀₋₁₀}
  {a₁₀₋₋₀ : Square a₁₀₀₋₀ a₁₀₁₋₀ a₁₀₋₀₀ a₁₀₋₁₀}
  {a₀₁₋₋₀ : Square a₀₁₀₋₀ a₀₁₁₋₀ a₀₁₋₀₀ a₀₁₋₁₀}
  {a₁₁₋₋₀ : Square a₁₁₀₋₀ a₁₁₁₋₀ a₁₁₋₀₀ a₁₁₋₁₀}
  {a₀₋₀₋₀ : Square a₀₀₀₋₀ a₀₁₀₋₀ a₀₋₀₀₀ a₀₋₀₁₀}
  {a₁₋₀₋₀ : Square a₁₀₀₋₀ a₁₁₀₋₀ a₁₋₀₀₀ a₁₋₀₁₀}
  {a₋₀₀₋₀ : Square a₀₀₀₋₀ a₁₀₀₋₀ a₋₀₀₀₀ a₋₀₀₁₀}
  {a₋₁₀₋₀ : Square a₀₁₀₋₀ a₁₁₀₋₀ a₋₁₀₀₀ a₋₁₀₁₀}
  {a₀₋₁₋₀ : Square a₀₀₁₋₀ a₀₁₁₋₀ a₀₋₁₀₀ a₀₋₁₁₀}
  {a₁₋₁₋₀ : Square a₁₀₁₋₀ a₁₁₁₋₀ a₁₋₁₀₀ a₁₋₁₁₀}
  {a₋₀₁₋₀ : Square a₀₀₁₋₀ a₁₀₁₋₀ a₋₀₁₀₀ a₋₀₁₁₀}
  {a₋₁₁₋₀ : Square a₀₁₁₋₀ a₁₁₁₋₀ a₋₁₁₀₀ a₋₁₁₁₀}
  {a₀₋₋₀₀ : Square a₀₀₋₀₀ a₀₁₋₀₀ a₀₋₀₀₀ a₀₋₁₀₀}
  {a₁₋₋₀₀ : Square a₁₀₋₀₀ a₁₁₋₀₀ a₁₋₀₀₀ a₁₋₁₀₀}
  {a₋₀₋₀₀ : Square a₀₀₋₀₀ a₁₀₋₀₀ a₋₀₀₀₀ a₋₀₁₀₀}
  {a₋₁₋₀₀ : Square a₀₁₋₀₀ a₁₁₋₀₀ a₋₁₀₀₀ a₋₁₁₀₀}
  {a₋₋₀₀₀ : Square a₀₋₀₀₀ a₁₋₀₀₀ a₋₀₀₀₀ a₋₁₀₀₀}
  {a₋₋₁₀₀ : Square a₀₋₁₀₀ a₁₋₁₀₀ a₋₀₁₀₀ a₋₁₁₀₀}
  {a₀₋₋₁₀ : Square a₀₀₋₁₀ a₀₁₋₁₀ a₀₋₀₁₀ a₀₋₁₁₀}
  {a₁₋₋₁₀ : Square a₁₀₋₁₀ a₁₁₋₁₀ a₁₋₀₁₀ a₁₋₁₁₀}
  {a₋₀₋₁₀ : Square a₀₀₋₁₀ a₁₀₋₁₀ a₋₀₀₁₀ a₋₀₁₁₀}
  {a₋₁₋₁₀ : Square a₀₁₋₁₀ a₁₁₋₁₀ a₋₁₀₁₀ a₋₁₁₁₀}
  {a₋₋₀₁₀ : Square a₀₋₀₁₀ a₁₋₀₁₀ a₋₀₀₁₀ a₋₁₀₁₀}
  {a₋₋₁₁₀ : Square a₀₋₁₁₀ a₁₋₁₁₀ a₋₀₁₁₀ a₋₁₁₁₀}
  {a₀₀₋₋₁ : Square a₀₀₀₋₁ a₀₀₁₋₁ a₀₀₋₀₁ a₀₀₋₁₁}
  {a₁₀₋₋₁ : Square a₁₀₀₋₁ a₁₀₁₋₁ a₁₀₋₀₁ a₁₀₋₁₁}
  {a₀₁₋₋₁ : Square a₀₁₀₋₁ a₀₁₁₋₁ a₀₁₋₀₁ a₀₁₋₁₁}
  {a₁₁₋₋₁ : Square a₁₁₀₋₁ a₁₁₁₋₁ a₁₁₋₀₁ a₁₁₋₁₁}
  {a₀₋₀₋₁ : Square a₀₀₀₋₁ a₀₁₀₋₁ a₀₋₀₀₁ a₀₋₀₁₁}
  {a₁₋₀₋₁ : Square a₁₀₀₋₁ a₁₁₀₋₁ a₁₋₀₀₁ a₁₋₀₁₁}
  {a₋₀₀₋₁ : Square a₀₀₀₋₁ a₁₀₀₋₁ a₋₀₀₀₁ a₋₀₀₁₁}
  {a₋₁₀₋₁ : Square a₀₁₀₋₁ a₁₁₀₋₁ a₋₁₀₀₁ a₋₁₀₁₁}
  {a₀₋₁₋₁ : Square a₀₀₁₋₁ a₀₁₁₋₁ a₀₋₁₀₁ a₀₋₁₁₁}
  {a₁₋₁₋₁ : Square a₁₀₁₋₁ a₁₁₁₋₁ a₁₋₁₀₁ a₁₋₁₁₁}
  {a₋₀₁₋₁ : Square a₀₀₁₋₁ a₁₀₁₋₁ a₋₀₁₀₁ a₋₀₁₁₁}
  {a₋₁₁₋₁ : Square a₀₁₁₋₁ a₁₁₁₋₁ a₋₁₁₀₁ a₋₁₁₁₁}
  {a₀₋₋₀₁ : Square a₀₀₋₀₁ a₀₁₋₀₁ a₀₋₀₀₁ a₀₋₁₀₁}
  {a₁₋₋₀₁ : Square a₁₀₋₀₁ a₁₁₋₀₁ a₁₋₀₀₁ a₁₋₁₀₁}
  {a₋₀₋₀₁ : Square a₀₀₋₀₁ a₁₀₋₀₁ a₋₀₀₀₁ a₋₀₁₀₁}
  {a₋₁₋₀₁ : Square a₀₁₋₀₁ a₁₁₋₀₁ a₋₁₀₀₁ a₋₁₁₀₁}
  {a₋₋₀₀₁ : Square a₀₋₀₀₁ a₁₋₀₀₁ a₋₀₀₀₁ a₋₁₀₀₁}
  {a₋₋₁₀₁ : Square a₀₋₁₀₁ a₁₋₁₀₁ a₋₀₁₀₁ a₋₁₁₀₁}
  {a₀₋₋₁₁ : Square a₀₀₋₁₁ a₀₁₋₁₁ a₀₋₀₁₁ a₀₋₁₁₁}
  {a₁₋₋₁₁ : Square a₁₀₋₁₁ a₁₁₋₁₁ a₁₋₀₁₁ a₁₋₁₁₁}
  {a₋₀₋₁₁ : Square a₀₀₋₁₁ a₁₀₋₁₁ a₋₀₀₁₁ a₋₀₁₁₁}
  {a₋₁₋₁₁ : Square a₀₁₋₁₁ a₁₁₋₁₁ a₋₁₀₁₁ a₋₁₁₁₁}
  {a₋₋₀₁₁ : Square a₀₋₀₁₁ a₁₋₀₁₁ a₋₀₀₁₁ a₋₁₀₁₁}
  {a₋₋₁₁₁ : Square a₀₋₁₁₁ a₁₋₁₁₁ a₋₀₁₁₁ a₋₁₁₁₁}
  {a₀₀₋₋₋ : Cube a₀₀₀₋₋ a₀₀₁₋₋ a₀₀₋₀₋ a₀₀₋₁₋ a₀₀₋₋₀ a₀₀₋₋₁}
  {a₁₀₋₋₋ : Cube a₁₀₀₋₋ a₁₀₁₋₋ a₁₀₋₀₋ a₁₀₋₁₋ a₁₀₋₋₀ a₁₀₋₋₁}
  {a₀₁₋₋₋ : Cube a₀₁₀₋₋ a₀₁₁₋₋ a₀₁₋₀₋ a₀₁₋₁₋ a₀₁₋₋₀ a₀₁₋₋₁}
  {a₁₁₋₋₋ : Cube a₁₁₀₋₋ a₁₁₁₋₋ a₁₁₋₀₋ a₁₁₋₁₋ a₁₁₋₋₀ a₁₁₋₋₁}
  {a₀₋₀₋₋ : Cube a₀₀₀₋₋ a₀₁₀₋₋ a₀₋₀₀₋ a₀₋₀₁₋ a₀₋₀₋₀ a₀₋₀₋₁}
  {a₁₋₀₋₋ : Cube a₁₀₀₋₋ a₁₁₀₋₋ a₁₋₀₀₋ a₁₋₀₁₋ a₁₋₀₋₀ a₁₋₀₋₁}
  {a₋₀₀₋₋ : Cube a₀₀₀₋₋ a₁₀₀₋₋ a₋₀₀₀₋ a₋₀₀₁₋ a₋₀₀₋₀ a₋₀₀₋₁}
  {a₋₁₀₋₋ : Cube a₀₁₀₋₋ a₁₁₀₋₋ a₋₁₀₀₋ a₋₁₀₁₋ a₋₁₀₋₀ a₋₁₀₋₁}
  {a₀₋₁₋₋ : Cube a₀₀₁₋₋ a₀₁₁₋₋ a₀₋₁₀₋ a₀₋₁₁₋ a₀₋₁₋₀ a₀₋₁₋₁}
  {a₁₋₁₋₋ : Cube a₁₀₁₋₋ a₁₁₁₋₋ a₁₋₁₀₋ a₁₋₁₁₋ a₁₋₁₋₀ a₁₋₁₋₁}
  {a₋₀₁₋₋ : Cube a₀₀₁₋₋ a₁₀₁₋₋ a₋₀₁₀₋ a₋₀₁₁₋ a₋₀₁₋₀ a₋₀₁₋₁}
  {a₋₁₁₋₋ : Cube a₀₁₁₋₋ a₁₁₁₋₋ a₋₁₁₀₋ a₋₁₁₁₋ a₋₁₁₋₀ a₋₁₁₋₁}
  {a₀₋₋₀₋ : Cube a₀₀₋₀₋ a₀₁₋₀₋ a₀₋₀₀₋ a₀₋₁₀₋ a₀₋₋₀₀ a₀₋₋₀₁}
  {a₁₋₋₀₋ : Cube a₁₀₋₀₋ a₁₁₋₀₋ a₁₋₀₀₋ a₁₋₁₀₋ a₁₋₋₀₀ a₁₋₋₀₁}
  {a₋₀₋₀₋ : Cube a₀₀₋₀₋ a₁₀₋₀₋ a₋₀₀₀₋ a₋₀₁₀₋ a₋₀₋₀₀ a₋₀₋₀₁}
  {a₋₁₋₀₋ : Cube a₀₁₋₀₋ a₁₁₋₀₋ a₋₁₀₀₋ a₋₁₁₀₋ a₋₁₋₀₀ a₋₁₋₀₁}
  {a₋₋₀₀₋ : Cube a₀₋₀₀₋ a₁₋₀₀₋ a₋₀₀₀₋ a₋₁₀₀₋ a₋₋₀₀₀ a₋₋₀₀₁}
  {a₋₋₁₀₋ : Cube a₀₋₁₀₋ a₁₋₁₀₋ a₋₀₁₀₋ a₋₁₁₀₋ a₋₋₁₀₀ a₋₋₁₀₁}
  {a₀₋₋₁₋ : Cube a₀₀₋₁₋ a₀₁₋₁₋ a₀₋₀₁₋ a₀₋₁₁₋ a₀₋₋₁₀ a₀₋₋₁₁}
  {a₁₋₋₁₋ : Cube a₁₀₋₁₋ a₁₁₋₁₋ a₁₋₀₁₋ a₁₋₁₁₋ a₁₋₋₁₀ a₁₋₋₁₁}
  {a₋₀₋₁₋ : Cube a₀₀₋₁₋ a₁₀₋₁₋ a₋₀₀₁₋ a₋₀₁₁₋ a₋₀₋₁₀ a₋₀₋₁₁}
  {a₋₁₋₁₋ : Cube a₀₁₋₁₋ a₁₁₋₁₋ a₋₁₀₁₋ a₋₁₁₁₋ a₋₁₋₁₀ a₋₁₋₁₁}
  {a₋₋₀₁₋ : Cube a₀₋₀₁₋ a₁₋₀₁₋ a₋₀₀₁₋ a₋₁₀₁₋ a₋₋₀₁₀ a₋₋₀₁₁}
  {a₋₋₁₁₋ : Cube a₀₋₁₁₋ a₁₋₁₁₋ a₋₀₁₁₋ a₋₁₁₁₋ a₋₋₁₁₀ a₋₋₁₁₁}
  {a₀₋₋₋₀ : Cube a₀₀₋₋₀ a₀₁₋₋₀ a₀₋₀₋₀ a₀₋₁₋₀ a₀₋₋₀₀ a₀₋₋₁₀}
  {a₁₋₋₋₀ : Cube a₁₀₋₋₀ a₁₁₋₋₀ a₁₋₀₋₀ a₁₋₁₋₀ a₁₋₋₀₀ a₁₋₋₁₀}
  {a₋₀₋₋₀ : Cube a₀₀₋₋₀ a₁₀₋₋₀ a₋₀₀₋₀ a₋₀₁₋₀ a₋₀₋₀₀ a₋₀₋₁₀}
  {a₋₁₋₋₀ : Cube a₀₁₋₋₀ a₁₁₋₋₀ a₋₁₀₋₀ a₋₁₁₋₀ a₋₁₋₀₀ a₋₁₋₁₀}
  {a₋₋₀₋₀ : Cube a₀₋₀₋₀ a₁₋₀₋₀ a₋₀₀₋₀ a₋₁₀₋₀ a₋₋₀₀₀ a₋₋₀₁₀}
  {a₋₋₁₋₀ : Cube a₀₋₁₋₀ a₁₋₁₋₀ a₋₀₁₋₀ a₋₁₁₋₀ a₋₋₁₀₀ a₋₋₁₁₀}
  {a₋₋₋₀₀ : Cube a₀₋₋₀₀ a₁₋₋₀₀ a₋₀₋₀₀ a₋₁₋₀₀ a₋₋₀₀₀ a₋₋₁₀₀}
  {a₋₋₋₁₀ : Cube a₀₋₋₁₀ a₁₋₋₁₀ a₋₀₋₁₀ a₋₁₋₁₀ a₋₋₀₁₀ a₋₋₁₁₀}
  {a₀₋₋₋₁ : Cube a₀₀₋₋₁ a₀₁₋₋₁ a₀₋₀₋₁ a₀₋₁₋₁ a₀₋₋₀₁ a₀₋₋₁₁}
  {a₁₋₋₋₁ : Cube a₁₀₋₋₁ a₁₁₋₋₁ a₁₋₀₋₁ a₁₋₁₋₁ a₁₋₋₀₁ a₁₋₋₁₁}
  {a₋₀₋₋₁ : Cube a₀₀₋₋₁ a₁₀₋₋₁ a₋₀₀₋₁ a₋₀₁₋₁ a₋₀₋₀₁ a₋₀₋₁₁}
  {a₋₁₋₋₁ : Cube a₀₁₋₋₁ a₁₁₋₋₁ a₋₁₀₋₁ a₋₁₁₋₁ a₋₁₋₀₁ a₋₁₋₁₁}
  {a₋₋₀₋₁ : Cube a₀₋₀₋₁ a₁₋₀₋₁ a₋₀₀₋₁ a₋₁₀₋₁ a₋₋₀₀₁ a₋₋₀₁₁}
  {a₋₋₁₋₁ : Cube a₀₋₁₋₁ a₁₋₁₋₁ a₋₀₁₋₁ a₋₁₁₋₁ a₋₋₁₀₁ a₋₋₁₁₁}
  {a₋₋₋₀₁ : Cube a₀₋₋₀₁ a₁₋₋₀₁ a₋₀₋₀₁ a₋₁₋₀₁ a₋₋₀₀₁ a₋₋₁₀₁}
  {a₋₋₋₁₁ : Cube a₀₋₋₁₁ a₁₋₋₁₁ a₋₀₋₁₁ a₋₁₋₁₁ a₋₋₀₁₁ a₋₋₁₁₁}
  (a₀₋₋₋₋ : 4Cube a₀₀₋₋₋ a₀₁₋₋₋ a₀₋₀₋₋ a₀₋₁₋₋ a₀₋₋₀₋ a₀₋₋₁₋ a₀₋₋₋₀ a₀₋₋₋₁)
  (a₁₋₋₋₋ : 4Cube a₁₀₋₋₋ a₁₁₋₋₋ a₁₋₀₋₋ a₁₋₁₋₋ a₁₋₋₀₋ a₁₋₋₁₋ a₁₋₋₋₀ a₁₋₋₋₁)
  (a₋₀₋₋₋ : 4Cube a₀₀₋₋₋ a₁₀₋₋₋ a₋₀₀₋₋ a₋₀₁₋₋ a₋₀₋₀₋ a₋₀₋₁₋ a₋₀₋₋₀ a₋₀₋₋₁)
  (a₋₁₋₋₋ : 4Cube a₀₁₋₋₋ a₁₁₋₋₋ a₋₁₀₋₋ a₋₁₁₋₋ a₋₁₋₀₋ a₋₁₋₁₋ a₋₁₋₋₀ a₋₁₋₋₁)
  (a₋₋₀₋₋ : 4Cube a₀₋₀₋₋ a₁₋₀₋₋ a₋₀₀₋₋ a₋₁₀₋₋ a₋₋₀₀₋ a₋₋₀₁₋ a₋₋₀₋₀ a₋₋₀₋₁)
  (a₋₋₁₋₋ : 4Cube a₀₋₁₋₋ a₁₋₁₋₋ a₋₀₁₋₋ a₋₁₁₋₋ a₋₋₁₀₋ a₋₋₁₁₋ a₋₋₁₋₀ a₋₋₁₋₁)
  (a₋₋₋₀₋ : 4Cube a₀₋₋₀₋ a₁₋₋₀₋ a₋₀₋₀₋ a₋₁₋₀₋ a₋₋₀₀₋ a₋₋₁₀₋ a₋₋₋₀₀ a₋₋₋₀₁)
  (a₋₋₋₁₋ : 4Cube a₀₋₋₁₋ a₁₋₋₁₋ a₋₀₋₁₋ a₋₁₋₁₋ a₋₋₀₁₋ a₋₋₁₁₋ a₋₋₋₁₀ a₋₋₋₁₁)
  (a₋₋₋₋₀ : 4Cube a₀₋₋₋₀ a₁₋₋₋₀ a₋₀₋₋₀ a₋₁₋₋₀ a₋₋₀₋₀ a₋₋₁₋₀ a₋₋₋₀₀ a₋₋₋₁₀)
  (a₋₋₋₋₁ : 4Cube a₀₋₋₋₁ a₁₋₋₋₁ a₋₀₋₋₁ a₋₁₋₋₁ a₋₋₀₋₁ a₋₋₁₋₁ a₋₋₋₀₁ a₋₋₋₁₁)
  → Type _
5Cube a₀₋₋₋₋ a₁₋₋₋₋ a₋₀₋₋₋ a₋₁₋₋₋ a₋₋₀₋₋ a₋₋₁₋₋ a₋₋₋₀₋ a₋₋₋₁₋ a₋₋₋₋₀ a₋₋₋₋₁ = {!
  PathP (λ i → (4Cube (a₋₀₋₋₋ i) (a₋₁₋₋₋ i) (a₋₋₀₋₋ i) (a₋₋₁₋₋ i) (a₋₋₋₀₋ i) (a₋₋₋₁₋ i) (a₋₋₋₋₀ i) (a₋₋₋₋₁ i)))
        a₀₋₋₋₋ a₁₋₋₋₋ !}


is3Groupoid' : Type ℓ → Type ℓ
is3Groupoid' A =
  {a₀₀₀₀₀ a₁₀₀₀₀ : A}
  {a₀₁₀₀₀ a₁₁₀₀₀ : A}
  {a₀₀₁₀₀ a₁₀₁₀₀ : A}
  {a₀₁₁₀₀ a₁₁₁₀₀ : A}
  {a₀₀₀₁₀ a₁₀₀₁₀ : A}
  {a₀₁₀₁₀ a₁₁₀₁₀ : A}
  {a₀₀₁₁₀ a₁₀₁₁₀ : A}
  {a₀₁₁₁₀ a₁₁₁₁₀ : A}
  {a₀₀₀₀₁ a₁₀₀₀₁ : A}
  {a₀₁₀₀₁ a₁₁₀₀₁ : A}
  {a₀₀₁₀₁ a₁₀₁₀₁ : A}
  {a₀₁₁₀₁ a₁₁₁₀₁ : A}
  {a₀₀₀₁₁ a₁₀₀₁₁ : A}
  {a₀₁₀₁₁ a₁₁₀₁₁ : A}
  {a₀₀₁₁₁ a₁₀₁₁₁ : A}
  {a₀₁₁₁₁ a₁₁₁₁₁ : A}
  {a₀₀₀₀₋ : Path A a₀₀₀₀₀ a₀₀₀₀₁}
  {a₁₀₀₀₋ : Path A a₁₀₀₀₀ a₁₀₀₀₁}
  {a₀₁₀₀₋ : Path A a₀₁₀₀₀ a₀₁₀₀₁}
  {a₁₁₀₀₋ : Path A a₁₁₀₀₀ a₁₁₀₀₁}
  {a₀₀₁₀₋ : Path A a₀₀₁₀₀ a₀₀₁₀₁}
  {a₁₀₁₀₋ : Path A a₁₀₁₀₀ a₁₀₁₀₁}
  {a₀₁₁₀₋ : Path A a₀₁₁₀₀ a₀₁₁₀₁}
  {a₁₁₁₀₋ : Path A a₁₁₁₀₀ a₁₁₁₀₁}
  {a₀₀₀₁₋ : Path A a₀₀₀₁₀ a₀₀₀₁₁}
  {a₁₀₀₁₋ : Path A a₁₀₀₁₀ a₁₀₀₁₁}
  {a₀₁₀₁₋ : Path A a₀₁₀₁₀ a₀₁₀₁₁}
  {a₁₁₀₁₋ : Path A a₁₁₀₁₀ a₁₁₀₁₁}
  {a₀₀₁₁₋ : Path A a₀₀₁₁₀ a₀₀₁₁₁}
  {a₁₀₁₁₋ : Path A a₁₀₁₁₀ a₁₀₁₁₁}
  {a₀₁₁₁₋ : Path A a₀₁₁₁₀ a₀₁₁₁₁}
  {a₁₁₁₁₋ : Path A a₁₁₁₁₀ a₁₁₁₁₁}
  {a₀₀₀₋₀ : Path A a₀₀₀₀₀ a₀₀₀₁₀}
  {a₁₀₀₋₀ : Path A a₁₀₀₀₀ a₁₀₀₁₀}
  {a₀₁₀₋₀ : Path A a₀₁₀₀₀ a₀₁₀₁₀}
  {a₁₁₀₋₀ : Path A a₁₁₀₀₀ a₁₁₀₁₀}
  {a₀₀₁₋₀ : Path A a₀₀₁₀₀ a₀₀₁₁₀}
  {a₁₀₁₋₀ : Path A a₁₀₁₀₀ a₁₀₁₁₀}
  {a₀₁₁₋₀ : Path A a₀₁₁₀₀ a₀₁₁₁₀}
  {a₁₁₁₋₀ : Path A a₁₁₁₀₀ a₁₁₁₁₀}
  {a₀₀₋₀₀ : Path A a₀₀₀₀₀ a₀₀₁₀₀}
  {a₁₀₋₀₀ : Path A a₁₀₀₀₀ a₁₀₁₀₀}
  {a₀₁₋₀₀ : Path A a₀₁₀₀₀ a₀₁₁₀₀}
  {a₁₁₋₀₀ : Path A a₁₁₀₀₀ a₁₁₁₀₀}
  {a₀₋₀₀₀ : Path A a₀₀₀₀₀ a₀₁₀₀₀}
  {a₁₋₀₀₀ : Path A a₁₀₀₀₀ a₁₁₀₀₀}
  {a₋₀₀₀₀ : Path A a₀₀₀₀₀ a₁₀₀₀₀}
  {a₋₁₀₀₀ : Path A a₀₁₀₀₀ a₁₁₀₀₀}
  {a₀₋₁₀₀ : Path A a₀₀₁₀₀ a₀₁₁₀₀}
  {a₁₋₁₀₀ : Path A a₁₀₁₀₀ a₁₁₁₀₀}
  {a₋₀₁₀₀ : Path A a₀₀₁₀₀ a₁₀₁₀₀}
  {a₋₁₁₀₀ : Path A a₀₁₁₀₀ a₁₁₁₀₀}
  {a₀₀₋₁₀ : Path A a₀₀₀₁₀ a₀₀₁₁₀}
  {a₁₀₋₁₀ : Path A a₁₀₀₁₀ a₁₀₁₁₀}
  {a₀₁₋₁₀ : Path A a₀₁₀₁₀ a₀₁₁₁₀}
  {a₁₁₋₁₀ : Path A a₁₁₀₁₀ a₁₁₁₁₀}
  {a₀₋₀₁₀ : Path A a₀₀₀₁₀ a₀₁₀₁₀}
  {a₁₋₀₁₀ : Path A a₁₀₀₁₀ a₁₁₀₁₀}
  {a₋₀₀₁₀ : Path A a₀₀₀₁₀ a₁₀₀₁₀}
  {a₋₁₀₁₀ : Path A a₀₁₀₁₀ a₁₁₀₁₀}
  {a₀₋₁₁₀ : Path A a₀₀₁₁₀ a₀₁₁₁₀}
  {a₁₋₁₁₀ : Path A a₁₀₁₁₀ a₁₁₁₁₀}
  {a₋₀₁₁₀ : Path A a₀₀₁₁₀ a₁₀₁₁₀}
  {a₋₁₁₁₀ : Path A a₀₁₁₁₀ a₁₁₁₁₀}
  {a₀₀₀₋₁ : Path A a₀₀₀₀₁ a₀₀₀₁₁}
  {a₁₀₀₋₁ : Path A a₁₀₀₀₁ a₁₀₀₁₁}
  {a₀₁₀₋₁ : Path A a₀₁₀₀₁ a₀₁₀₁₁}
  {a₁₁₀₋₁ : Path A a₁₁₀₀₁ a₁₁₀₁₁}
  {a₀₀₁₋₁ : Path A a₀₀₁₀₁ a₀₀₁₁₁}
  {a₁₀₁₋₁ : Path A a₁₀₁₀₁ a₁₀₁₁₁}
  {a₀₁₁₋₁ : Path A a₀₁₁₀₁ a₀₁₁₁₁}
  {a₁₁₁₋₁ : Path A a₁₁₁₀₁ a₁₁₁₁₁}
  {a₀₀₋₀₁ : Path A a₀₀₀₀₁ a₀₀₁₀₁}
  {a₁₀₋₀₁ : Path A a₁₀₀₀₁ a₁₀₁₀₁}
  {a₀₁₋₀₁ : Path A a₀₁₀₀₁ a₀₁₁₀₁}
  {a₁₁₋₀₁ : Path A a₁₁₀₀₁ a₁₁₁₀₁}
  {a₀₋₀₀₁ : Path A a₀₀₀₀₁ a₀₁₀₀₁}
  {a₁₋₀₀₁ : Path A a₁₀₀₀₁ a₁₁₀₀₁}
  {a₋₀₀₀₁ : Path A a₀₀₀₀₁ a₁₀₀₀₁}
  {a₋₁₀₀₁ : Path A a₀₁₀₀₁ a₁₁₀₀₁}
  {a₀₋₁₀₁ : Path A a₀₀₁₀₁ a₀₁₁₀₁}
  {a₁₋₁₀₁ : Path A a₁₀₁₀₁ a₁₁₁₀₁}
  {a₋₀₁₀₁ : Path A a₀₀₁₀₁ a₁₀₁₀₁}
  {a₋₁₁₀₁ : Path A a₀₁₁₀₁ a₁₁₁₀₁}
  {a₀₀₋₁₁ : Path A a₀₀₀₁₁ a₀₀₁₁₁}
  {a₁₀₋₁₁ : Path A a₁₀₀₁₁ a₁₀₁₁₁}
  {a₀₁₋₁₁ : Path A a₀₁₀₁₁ a₀₁₁₁₁}
  {a₁₁₋₁₁ : Path A a₁₁₀₁₁ a₁₁₁₁₁}
  {a₀₋₀₁₁ : Path A a₀₀₀₁₁ a₀₁₀₁₁}
  {a₁₋₀₁₁ : Path A a₁₀₀₁₁ a₁₁₀₁₁}
  {a₋₀₀₁₁ : Path A a₀₀₀₁₁ a₁₀₀₁₁}
  {a₋₁₀₁₁ : Path A a₀₁₀₁₁ a₁₁₀₁₁}
  {a₀₋₁₁₁ : Path A a₀₀₁₁₁ a₀₁₁₁₁}
  {a₁₋₁₁₁ : Path A a₁₀₁₁₁ a₁₁₁₁₁}
  {a₋₀₁₁₁ : Path A a₀₀₁₁₁ a₁₀₁₁₁}
  {a₋₁₁₁₁ : Path A a₀₁₁₁₁ a₁₁₁₁₁}
  {a₀₀₀₋₋ : Square a₀₀₀₀₋ a₀₀₀₁₋ a₀₀₀₋₀ a₀₀₀₋₁}
  {a₁₀₀₋₋ : Square a₁₀₀₀₋ a₁₀₀₁₋ a₁₀₀₋₀ a₁₀₀₋₁}
  {a₀₁₀₋₋ : Square a₀₁₀₀₋ a₀₁₀₁₋ a₀₁₀₋₀ a₀₁₀₋₁}
  {a₁₁₀₋₋ : Square a₁₁₀₀₋ a₁₁₀₁₋ a₁₁₀₋₀ a₁₁₀₋₁}
  {a₀₀₁₋₋ : Square a₀₀₁₀₋ a₀₀₁₁₋ a₀₀₁₋₀ a₀₀₁₋₁}
  {a₁₀₁₋₋ : Square a₁₀₁₀₋ a₁₀₁₁₋ a₁₀₁₋₀ a₁₀₁₋₁}
  {a₀₁₁₋₋ : Square a₀₁₁₀₋ a₀₁₁₁₋ a₀₁₁₋₀ a₀₁₁₋₁}
  {a₁₁₁₋₋ : Square a₁₁₁₀₋ a₁₁₁₁₋ a₁₁₁₋₀ a₁₁₁₋₁}
  {a₀₀₋₀₋ : Square a₀₀₀₀₋ a₀₀₁₀₋ a₀₀₋₀₀ a₀₀₋₀₁}
  {a₁₀₋₀₋ : Square a₁₀₀₀₋ a₁₀₁₀₋ a₁₀₋₀₀ a₁₀₋₀₁}
  {a₀₁₋₀₋ : Square a₀₁₀₀₋ a₀₁₁₀₋ a₀₁₋₀₀ a₀₁₋₀₁}
  {a₁₁₋₀₋ : Square a₁₁₀₀₋ a₁₁₁₀₋ a₁₁₋₀₀ a₁₁₋₀₁}
  {a₀₋₀₀₋ : Square a₀₀₀₀₋ a₀₁₀₀₋ a₀₋₀₀₀ a₀₋₀₀₁}
  {a₁₋₀₀₋ : Square a₁₀₀₀₋ a₁₁₀₀₋ a₁₋₀₀₀ a₁₋₀₀₁}
  {a₋₀₀₀₋ : Square a₀₀₀₀₋ a₁₀₀₀₋ a₋₀₀₀₀ a₋₀₀₀₁}
  {a₋₁₀₀₋ : Square a₀₁₀₀₋ a₁₁₀₀₋ a₋₁₀₀₀ a₋₁₀₀₁}
  {a₀₋₁₀₋ : Square a₀₀₁₀₋ a₀₁₁₀₋ a₀₋₁₀₀ a₀₋₁₀₁}
  {a₁₋₁₀₋ : Square a₁₀₁₀₋ a₁₁₁₀₋ a₁₋₁₀₀ a₁₋₁₀₁}
  {a₋₀₁₀₋ : Square a₀₀₁₀₋ a₁₀₁₀₋ a₋₀₁₀₀ a₋₀₁₀₁}
  {a₋₁₁₀₋ : Square a₀₁₁₀₋ a₁₁₁₀₋ a₋₁₁₀₀ a₋₁₁₀₁}
  {a₀₀₋₁₋ : Square a₀₀₀₁₋ a₀₀₁₁₋ a₀₀₋₁₀ a₀₀₋₁₁}
  {a₁₀₋₁₋ : Square a₁₀₀₁₋ a₁₀₁₁₋ a₁₀₋₁₀ a₁₀₋₁₁}
  {a₀₁₋₁₋ : Square a₀₁₀₁₋ a₀₁₁₁₋ a₀₁₋₁₀ a₀₁₋₁₁}
  {a₁₁₋₁₋ : Square a₁₁₀₁₋ a₁₁₁₁₋ a₁₁₋₁₀ a₁₁₋₁₁}
  {a₀₋₀₁₋ : Square a₀₀₀₁₋ a₀₁₀₁₋ a₀₋₀₁₀ a₀₋₀₁₁}
  {a₁₋₀₁₋ : Square a₁₀₀₁₋ a₁₁₀₁₋ a₁₋₀₁₀ a₁₋₀₁₁}
  {a₋₀₀₁₋ : Square a₀₀₀₁₋ a₁₀₀₁₋ a₋₀₀₁₀ a₋₀₀₁₁}
  {a₋₁₀₁₋ : Square a₀₁₀₁₋ a₁₁₀₁₋ a₋₁₀₁₀ a₋₁₀₁₁}
  {a₀₋₁₁₋ : Square a₀₀₁₁₋ a₀₁₁₁₋ a₀₋₁₁₀ a₀₋₁₁₁}
  {a₁₋₁₁₋ : Square a₁₀₁₁₋ a₁₁₁₁₋ a₁₋₁₁₀ a₁₋₁₁₁}
  {a₋₀₁₁₋ : Square a₀₀₁₁₋ a₁₀₁₁₋ a₋₀₁₁₀ a₋₀₁₁₁}
  {a₋₁₁₁₋ : Square a₀₁₁₁₋ a₁₁₁₁₋ a₋₁₁₁₀ a₋₁₁₁₁}
  {a₀₀₋₋₀ : Square a₀₀₀₋₀ a₀₀₁₋₀ a₀₀₋₀₀ a₀₀₋₁₀}
  {a₁₀₋₋₀ : Square a₁₀₀₋₀ a₁₀₁₋₀ a₁₀₋₀₀ a₁₀₋₁₀}
  {a₀₁₋₋₀ : Square a₀₁₀₋₀ a₀₁₁₋₀ a₀₁₋₀₀ a₀₁₋₁₀}
  {a₁₁₋₋₀ : Square a₁₁₀₋₀ a₁₁₁₋₀ a₁₁₋₀₀ a₁₁₋₁₀}
  {a₀₋₀₋₀ : Square a₀₀₀₋₀ a₀₁₀₋₀ a₀₋₀₀₀ a₀₋₀₁₀}
  {a₁₋₀₋₀ : Square a₁₀₀₋₀ a₁₁₀₋₀ a₁₋₀₀₀ a₁₋₀₁₀}
  {a₋₀₀₋₀ : Square a₀₀₀₋₀ a₁₀₀₋₀ a₋₀₀₀₀ a₋₀₀₁₀}
  {a₋₁₀₋₀ : Square a₀₁₀₋₀ a₁₁₀₋₀ a₋₁₀₀₀ a₋₁₀₁₀}
  {a₀₋₁₋₀ : Square a₀₀₁₋₀ a₀₁₁₋₀ a₀₋₁₀₀ a₀₋₁₁₀}
  {a₁₋₁₋₀ : Square a₁₀₁₋₀ a₁₁₁₋₀ a₁₋₁₀₀ a₁₋₁₁₀}
  {a₋₀₁₋₀ : Square a₀₀₁₋₀ a₁₀₁₋₀ a₋₀₁₀₀ a₋₀₁₁₀}
  {a₋₁₁₋₀ : Square a₀₁₁₋₀ a₁₁₁₋₀ a₋₁₁₀₀ a₋₁₁₁₀}
  {a₀₋₋₀₀ : Square a₀₀₋₀₀ a₀₁₋₀₀ a₀₋₀₀₀ a₀₋₁₀₀}
  {a₁₋₋₀₀ : Square a₁₀₋₀₀ a₁₁₋₀₀ a₁₋₀₀₀ a₁₋₁₀₀}
  {a₋₀₋₀₀ : Square a₀₀₋₀₀ a₁₀₋₀₀ a₋₀₀₀₀ a₋₀₁₀₀}
  {a₋₁₋₀₀ : Square a₀₁₋₀₀ a₁₁₋₀₀ a₋₁₀₀₀ a₋₁₁₀₀}
  {a₋₋₀₀₀ : Square a₀₋₀₀₀ a₁₋₀₀₀ a₋₀₀₀₀ a₋₁₀₀₀}
  {a₋₋₁₀₀ : Square a₀₋₁₀₀ a₁₋₁₀₀ a₋₀₁₀₀ a₋₁₁₀₀}
  {a₀₋₋₁₀ : Square a₀₀₋₁₀ a₀₁₋₁₀ a₀₋₀₁₀ a₀₋₁₁₀}
  {a₁₋₋₁₀ : Square a₁₀₋₁₀ a₁₁₋₁₀ a₁₋₀₁₀ a₁₋₁₁₀}
  {a₋₀₋₁₀ : Square a₀₀₋₁₀ a₁₀₋₁₀ a₋₀₀₁₀ a₋₀₁₁₀}
  {a₋₁₋₁₀ : Square a₀₁₋₁₀ a₁₁₋₁₀ a₋₁₀₁₀ a₋₁₁₁₀}
  {a₋₋₀₁₀ : Square a₀₋₀₁₀ a₁₋₀₁₀ a₋₀₀₁₀ a₋₁₀₁₀}
  {a₋₋₁₁₀ : Square a₀₋₁₁₀ a₁₋₁₁₀ a₋₀₁₁₀ a₋₁₁₁₀}
  {a₀₀₋₋₁ : Square a₀₀₀₋₁ a₀₀₁₋₁ a₀₀₋₀₁ a₀₀₋₁₁}
  {a₁₀₋₋₁ : Square a₁₀₀₋₁ a₁₀₁₋₁ a₁₀₋₀₁ a₁₀₋₁₁}
  {a₀₁₋₋₁ : Square a₀₁₀₋₁ a₀₁₁₋₁ a₀₁₋₀₁ a₀₁₋₁₁}
  {a₁₁₋₋₁ : Square a₁₁₀₋₁ a₁₁₁₋₁ a₁₁₋₀₁ a₁₁₋₁₁}
  {a₀₋₀₋₁ : Square a₀₀₀₋₁ a₀₁₀₋₁ a₀₋₀₀₁ a₀₋₀₁₁}
  {a₁₋₀₋₁ : Square a₁₀₀₋₁ a₁₁₀₋₁ a₁₋₀₀₁ a₁₋₀₁₁}
  {a₋₀₀₋₁ : Square a₀₀₀₋₁ a₁₀₀₋₁ a₋₀₀₀₁ a₋₀₀₁₁}
  {a₋₁₀₋₁ : Square a₀₁₀₋₁ a₁₁₀₋₁ a₋₁₀₀₁ a₋₁₀₁₁}
  {a₀₋₁₋₁ : Square a₀₀₁₋₁ a₀₁₁₋₁ a₀₋₁₀₁ a₀₋₁₁₁}
  {a₁₋₁₋₁ : Square a₁₀₁₋₁ a₁₁₁₋₁ a₁₋₁₀₁ a₁₋₁₁₁}
  {a₋₀₁₋₁ : Square a₀₀₁₋₁ a₁₀₁₋₁ a₋₀₁₀₁ a₋₀₁₁₁}
  {a₋₁₁₋₁ : Square a₀₁₁₋₁ a₁₁₁₋₁ a₋₁₁₀₁ a₋₁₁₁₁}
  {a₀₋₋₀₁ : Square a₀₀₋₀₁ a₀₁₋₀₁ a₀₋₀₀₁ a₀₋₁₀₁}
  {a₁₋₋₀₁ : Square a₁₀₋₀₁ a₁₁₋₀₁ a₁₋₀₀₁ a₁₋₁₀₁}
  {a₋₀₋₀₁ : Square a₀₀₋₀₁ a₁₀₋₀₁ a₋₀₀₀₁ a₋₀₁₀₁}
  {a₋₁₋₀₁ : Square a₀₁₋₀₁ a₁₁₋₀₁ a₋₁₀₀₁ a₋₁₁₀₁}
  {a₋₋₀₀₁ : Square a₀₋₀₀₁ a₁₋₀₀₁ a₋₀₀₀₁ a₋₁₀₀₁}
  {a₋₋₁₀₁ : Square a₀₋₁₀₁ a₁₋₁₀₁ a₋₀₁₀₁ a₋₁₁₀₁}
  {a₀₋₋₁₁ : Square a₀₀₋₁₁ a₀₁₋₁₁ a₀₋₀₁₁ a₀₋₁₁₁}
  {a₁₋₋₁₁ : Square a₁₀₋₁₁ a₁₁₋₁₁ a₁₋₀₁₁ a₁₋₁₁₁}
  {a₋₀₋₁₁ : Square a₀₀₋₁₁ a₁₀₋₁₁ a₋₀₀₁₁ a₋₀₁₁₁}
  {a₋₁₋₁₁ : Square a₀₁₋₁₁ a₁₁₋₁₁ a₋₁₀₁₁ a₋₁₁₁₁}
  {a₋₋₀₁₁ : Square a₀₋₀₁₁ a₁₋₀₁₁ a₋₀₀₁₁ a₋₁₀₁₁}
  {a₋₋₁₁₁ : Square a₀₋₁₁₁ a₁₋₁₁₁ a₋₀₁₁₁ a₋₁₁₁₁}
  {a₀₀₋₋₋ : Cube a₀₀₀₋₋ a₀₀₁₋₋ a₀₀₋₀₋ a₀₀₋₁₋ a₀₀₋₋₀ a₀₀₋₋₁}
  {a₁₀₋₋₋ : Cube a₁₀₀₋₋ a₁₀₁₋₋ a₁₀₋₀₋ a₁₀₋₁₋ a₁₀₋₋₀ a₁₀₋₋₁}
  {a₀₁₋₋₋ : Cube a₀₁₀₋₋ a₀₁₁₋₋ a₀₁₋₀₋ a₀₁₋₁₋ a₀₁₋₋₀ a₀₁₋₋₁}
  {a₁₁₋₋₋ : Cube a₁₁₀₋₋ a₁₁₁₋₋ a₁₁₋₀₋ a₁₁₋₁₋ a₁₁₋₋₀ a₁₁₋₋₁}
  {a₀₋₀₋₋ : Cube a₀₀₀₋₋ a₀₁₀₋₋ a₀₋₀₀₋ a₀₋₀₁₋ a₀₋₀₋₀ a₀₋₀₋₁}
  {a₁₋₀₋₋ : Cube a₁₀₀₋₋ a₁₁₀₋₋ a₁₋₀₀₋ a₁₋₀₁₋ a₁₋₀₋₀ a₁₋₀₋₁}
  {a₋₀₀₋₋ : Cube a₀₀₀₋₋ a₁₀₀₋₋ a₋₀₀₀₋ a₋₀₀₁₋ a₋₀₀₋₀ a₋₀₀₋₁}
  {a₋₁₀₋₋ : Cube a₀₁₀₋₋ a₁₁₀₋₋ a₋₁₀₀₋ a₋₁₀₁₋ a₋₁₀₋₀ a₋₁₀₋₁}
  {a₀₋₁₋₋ : Cube a₀₀₁₋₋ a₀₁₁₋₋ a₀₋₁₀₋ a₀₋₁₁₋ a₀₋₁₋₀ a₀₋₁₋₁}
  {a₁₋₁₋₋ : Cube a₁₀₁₋₋ a₁₁₁₋₋ a₁₋₁₀₋ a₁₋₁₁₋ a₁₋₁₋₀ a₁₋₁₋₁}
  {a₋₀₁₋₋ : Cube a₀₀₁₋₋ a₁₀₁₋₋ a₋₀₁₀₋ a₋₀₁₁₋ a₋₀₁₋₀ a₋₀₁₋₁}
  {a₋₁₁₋₋ : Cube a₀₁₁₋₋ a₁₁₁₋₋ a₋₁₁₀₋ a₋₁₁₁₋ a₋₁₁₋₀ a₋₁₁₋₁}
  {a₀₋₋₀₋ : Cube a₀₀₋₀₋ a₀₁₋₀₋ a₀₋₀₀₋ a₀₋₁₀₋ a₀₋₋₀₀ a₀₋₋₀₁}
  {a₁₋₋₀₋ : Cube a₁₀₋₀₋ a₁₁₋₀₋ a₁₋₀₀₋ a₁₋₁₀₋ a₁₋₋₀₀ a₁₋₋₀₁}
  {a₋₀₋₀₋ : Cube a₀₀₋₀₋ a₁₀₋₀₋ a₋₀₀₀₋ a₋₀₁₀₋ a₋₀₋₀₀ a₋₀₋₀₁}
  {a₋₁₋₀₋ : Cube a₀₁₋₀₋ a₁₁₋₀₋ a₋₁₀₀₋ a₋₁₁₀₋ a₋₁₋₀₀ a₋₁₋₀₁}
  {a₋₋₀₀₋ : Cube a₀₋₀₀₋ a₁₋₀₀₋ a₋₀₀₀₋ a₋₁₀₀₋ a₋₋₀₀₀ a₋₋₀₀₁}
  {a₋₋₁₀₋ : Cube a₀₋₁₀₋ a₁₋₁₀₋ a₋₀₁₀₋ a₋₁₁₀₋ a₋₋₁₀₀ a₋₋₁₀₁}
  {a₀₋₋₁₋ : Cube a₀₀₋₁₋ a₀₁₋₁₋ a₀₋₀₁₋ a₀₋₁₁₋ a₀₋₋₁₀ a₀₋₋₁₁}
  {a₁₋₋₁₋ : Cube a₁₀₋₁₋ a₁₁₋₁₋ a₁₋₀₁₋ a₁₋₁₁₋ a₁₋₋₁₀ a₁₋₋₁₁}
  {a₋₀₋₁₋ : Cube a₀₀₋₁₋ a₁₀₋₁₋ a₋₀₀₁₋ a₋₀₁₁₋ a₋₀₋₁₀ a₋₀₋₁₁}
  {a₋₁₋₁₋ : Cube a₀₁₋₁₋ a₁₁₋₁₋ a₋₁₀₁₋ a₋₁₁₁₋ a₋₁₋₁₀ a₋₁₋₁₁}
  {a₋₋₀₁₋ : Cube a₀₋₀₁₋ a₁₋₀₁₋ a₋₀₀₁₋ a₋₁₀₁₋ a₋₋₀₁₀ a₋₋₀₁₁}
  {a₋₋₁₁₋ : Cube a₀₋₁₁₋ a₁₋₁₁₋ a₋₀₁₁₋ a₋₁₁₁₋ a₋₋₁₁₀ a₋₋₁₁₁}
  {a₀₋₋₋₀ : Cube a₀₀₋₋₀ a₀₁₋₋₀ a₀₋₀₋₀ a₀₋₁₋₀ a₀₋₋₀₀ a₀₋₋₁₀}
  {a₁₋₋₋₀ : Cube a₁₀₋₋₀ a₁₁₋₋₀ a₁₋₀₋₀ a₁₋₁₋₀ a₁₋₋₀₀ a₁₋₋₁₀}
  {a₋₀₋₋₀ : Cube a₀₀₋₋₀ a₁₀₋₋₀ a₋₀₀₋₀ a₋₀₁₋₀ a₋₀₋₀₀ a₋₀₋₁₀}
  {a₋₁₋₋₀ : Cube a₀₁₋₋₀ a₁₁₋₋₀ a₋₁₀₋₀ a₋₁₁₋₀ a₋₁₋₀₀ a₋₁₋₁₀}
  {a₋₋₀₋₀ : Cube a₀₋₀₋₀ a₁₋₀₋₀ a₋₀₀₋₀ a₋₁₀₋₀ a₋₋₀₀₀ a₋₋₀₁₀}
  {a₋₋₁₋₀ : Cube a₀₋₁₋₀ a₁₋₁₋₀ a₋₀₁₋₀ a₋₁₁₋₀ a₋₋₁₀₀ a₋₋₁₁₀}
  {a₋₋₋₀₀ : Cube a₀₋₋₀₀ a₁₋₋₀₀ a₋₀₋₀₀ a₋₁₋₀₀ a₋₋₀₀₀ a₋₋₁₀₀}
  {a₋₋₋₁₀ : Cube a₀₋₋₁₀ a₁₋₋₁₀ a₋₀₋₁₀ a₋₁₋₁₀ a₋₋₀₁₀ a₋₋₁₁₀}
  {a₀₋₋₋₁ : Cube a₀₀₋₋₁ a₀₁₋₋₁ a₀₋₀₋₁ a₀₋₁₋₁ a₀₋₋₀₁ a₀₋₋₁₁}
  {a₁₋₋₋₁ : Cube a₁₀₋₋₁ a₁₁₋₋₁ a₁₋₀₋₁ a₁₋₁₋₁ a₁₋₋₀₁ a₁₋₋₁₁}
  {a₋₀₋₋₁ : Cube a₀₀₋₋₁ a₁₀₋₋₁ a₋₀₀₋₁ a₋₀₁₋₁ a₋₀₋₀₁ a₋₀₋₁₁}
  {a₋₁₋₋₁ : Cube a₀₁₋₋₁ a₁₁₋₋₁ a₋₁₀₋₁ a₋₁₁₋₁ a₋₁₋₀₁ a₋₁₋₁₁}
  {a₋₋₀₋₁ : Cube a₀₋₀₋₁ a₁₋₀₋₁ a₋₀₀₋₁ a₋₁₀₋₁ a₋₋₀₀₁ a₋₋₀₁₁}
  {a₋₋₁₋₁ : Cube a₀₋₁₋₁ a₁₋₁₋₁ a₋₀₁₋₁ a₋₁₁₋₁ a₋₋₁₀₁ a₋₋₁₁₁}
  {a₋₋₋₀₁ : Cube a₀₋₋₀₁ a₁₋₋₀₁ a₋₀₋₀₁ a₋₁₋₀₁ a₋₋₀₀₁ a₋₋₁₀₁}
  {a₋₋₋₁₁ : Cube a₀₋₋₁₁ a₁₋₋₁₁ a₋₀₋₁₁ a₋₁₋₁₁ a₋₋₀₁₁ a₋₋₁₁₁}
  (a₀₋₋₋₋ : 4Cube a₀₀₋₋₋ a₀₁₋₋₋ a₀₋₀₋₋ a₀₋₁₋₋ a₀₋₋₀₋ a₀₋₋₁₋ a₀₋₋₋₀ a₀₋₋₋₁)
  (a₁₋₋₋₋ : 4Cube a₁₀₋₋₋ a₁₁₋₋₋ a₁₋₀₋₋ a₁₋₁₋₋ a₁₋₋₀₋ a₁₋₋₁₋ a₁₋₋₋₀ a₁₋₋₋₁)
  (a₋₀₋₋₋ : 4Cube a₀₀₋₋₋ a₁₀₋₋₋ a₋₀₀₋₋ a₋₀₁₋₋ a₋₀₋₀₋ a₋₀₋₁₋ a₋₀₋₋₀ a₋₀₋₋₁)
  (a₋₁₋₋₋ : 4Cube a₀₁₋₋₋ a₁₁₋₋₋ a₋₁₀₋₋ a₋₁₁₋₋ a₋₁₋₀₋ a₋₁₋₁₋ a₋₁₋₋₀ a₋₁₋₋₁)
  (a₋₋₀₋₋ : 4Cube a₀₋₀₋₋ a₁₋₀₋₋ a₋₀₀₋₋ a₋₁₀₋₋ a₋₋₀₀₋ a₋₋₀₁₋ a₋₋₀₋₀ a₋₋₀₋₁)
  (a₋₋₁₋₋ : 4Cube a₀₋₁₋₋ a₁₋₁₋₋ a₋₀₁₋₋ a₋₁₁₋₋ a₋₋₁₀₋ a₋₋₁₁₋ a₋₋₁₋₀ a₋₋₁₋₁)
  (a₋₋₋₀₋ : 4Cube a₀₋₋₀₋ a₁₋₋₀₋ a₋₀₋₀₋ a₋₁₋₀₋ a₋₋₀₀₋ a₋₋₁₀₋ a₋₋₋₀₀ a₋₋₋₀₁)
  (a₋₋₋₁₋ : 4Cube a₀₋₋₁₋ a₁₋₋₁₋ a₋₀₋₁₋ a₋₁₋₁₋ a₋₋₀₁₋ a₋₋₁₁₋ a₋₋₋₁₀ a₋₋₋₁₁)
  (a₋₋₋₋₀ : 4Cube a₀₋₋₋₀ a₁₋₋₋₀ a₋₀₋₋₀ a₋₁₋₋₀ a₋₋₀₋₀ a₋₋₁₋₀ a₋₋₋₀₀ a₋₋₋₁₀)
  (a₋₋₋₋₁ : 4Cube a₀₋₋₋₁ a₁₋₋₋₁ a₋₀₋₋₁ a₋₁₋₋₁ a₋₋₀₋₁ a₋₋₁₋₁ a₋₋₋₀₁ a₋₋₋₁₁)
  → 5Cube a₀₋₋₋₋ a₁₋₋₋₋ a₋₀₋₋₋ a₋₁₋₋₋ a₋₋₀₋₋ a₋₋₁₋₋ a₋₋₋₀₋ a₋₋₋₁₋ a₋₋₋₋₀ a₋₋₋₋₁
-}

-- Essential consequences of isProp and isContr
isProp→PathP : ∀ {B : I → Type ℓ} → ((i : I) → isProp (B i))
               → (b0 : B i0) (b1 : B i1)
               → PathP (λ i → B i) b0 b1
isProp→PathP hB b0 b1 = toPathP (hB _ _ _)

isPropIsContr : isProp (isContr A)
isPropIsContr z0 z1 j =
  ( z0 .snd (z1 .fst) j
  , λ x i → hcomp (λ k → λ { (i = i0) → z0 .snd (z1 .fst) j
                           ; (i = i1) → z0 .snd x (j ∨ k)
                           ; (j = i0) → z0 .snd x (i ∧ k)
                           ; (j = i1) → z1 .snd x i })
                  (z0 .snd (z1 .snd x i) j))

isContr→isProp : isContr A → isProp A
isContr→isProp (x , p) a b i =
  hcomp (λ j → λ { (i = i0) → p a j
                 ; (i = i1) → p b j }) x

isProp→isSet : isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a

isProp→isSet' : isProp A → isSet' A
isProp→isSet' h {a} p q r s i j =
  hcomp (λ k → λ { (i = i0) → h a (p j) k
                 ; (i = i1) → h a (q j) k
                 ; (j = i0) → h a (r i) k
                 ; (j = i1) → h a (s i) k}) a

isPropIsProp : isProp (isProp A)
isPropIsProp f g i a b = isProp→isSet f a b (f a b) (g a b) i

-- Universe lifting

record Lift {i j} (A : Type i) : Type (ℓ-max i j) where
  constructor lift
  field
    lower : A

open Lift public

liftExt : ∀ {A : Type ℓ} {a b : Lift {ℓ} {ℓ'} A} → (lower a ≡ lower b) → a ≡ b
liftExt x i = lift (x i)

doubleCompPath-filler∙ : {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
                       → PathP (λ i → p i ≡ r (~ i)) (p ∙ q ∙ r) q
doubleCompPath-filler∙ {A = A} {b = b} p q r j i =
  hcomp (λ k → λ { (i = i0) → p j
                  ; (i = i1) → side j k
                  ; (j = i1) → q (i ∧ k)})
        (p (j ∨ i))
  where
  side : I → I → A
  side i j =
    hcomp (λ k → λ { (i = i1) → q j
                    ; (j = i0) → b
                    ; (j = i1) → r (~ i ∧ k)})
          (q j)

PathP→compPathL : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
           → PathP (λ i → p i ≡ q i) r s
           → sym p ∙ r ∙ q ≡ s
PathP→compPathL {p = p} {q = q} {r = r} {s = s} P j i =
  hcomp (λ k → λ { (i = i0) → p (j ∨ k)
                  ; (i = i1) → q (j ∨ k)
                  ; (j = i0) → doubleCompPath-filler∙ (sym p) r q (~ k) i
                  ; (j = i1) → s i })
        (P j i)

PathP→compPathR : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
           → PathP (λ i → p i ≡ q i) r s
           → r ≡ p ∙ s ∙ sym q
PathP→compPathR {p = p} {q = q} {r = r} {s = s} P j i =
  hcomp (λ k → λ { (i = i0) → p (j ∧ (~ k))
                  ; (i = i1) → q (j ∧ (~ k))
                  ; (j = i0) → r i
                  ; (j = i1) → doubleCompPath-filler∙ p s (sym q) (~ k) i})
        (P j i)


-- otherdir

compPathL→PathP : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
           → sym p ∙ r ∙ q ≡ s
           → PathP (λ i → p i ≡ q i) r s
compPathL→PathP {p = p} {q = q} {r = r} {s = s} P j i =
  hcomp (λ k → λ { (i = i0) → p (~ k ∨ j)
                  ; (i = i1) → q (~ k ∨ j)
                  ; (j = i0) → doubleCompPath-filler∙ (sym p) r q k i
                  ; (j = i1) → s i})
        (P j i)

compPathR→PathP : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
                → r ≡ p ∙ s ∙ sym q
                → PathP (λ i → p i ≡ q i) r s
compPathR→PathP {p = p} {q = q} {r = r} {s = s} P j i =
  hcomp (λ k → λ { (i = i0) → p (k ∧ j)
                  ; (i = i1) → q (k ∧ j)
                  ; (j = i0) → r i
                  ; (j = i1) → doubleCompPath-filler∙  p s (sym q) k i})
        (P j i)
