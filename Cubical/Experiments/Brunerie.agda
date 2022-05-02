
{-# OPTIONS --safe #-}
module Cubical.Experiments.Brunerie where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.HITs.S1 hiding (encode)
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Join
open import Cubical.HITs.SetTruncation as SetTrunc
open import Cubical.HITs.GroupoidTruncation as GroupoidTrunc
open import Cubical.HITs.2GroupoidTruncation as 2GroupoidTrunc
open import Cubical.HITs.Truncation as Trunc
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Hopf
open S¹Hopf

-- This code is adapted from examples/brunerie3.ctt on the pi4s3_nobug branch of cubicaltt

Bool∙ S¹∙ S³∙ : Pointed₀
Bool∙ = (Bool , true)
S¹∙ = (S¹ , base)
S³∙ = (S³ , base)

∥_∥₃∙ ∥_∥₄∙ : Pointed₀ → Pointed₀
∥ A , a ∥₃∙ = ∥ A ∥₃ , ∣ a ∣₃
∥ A , a ∥₄∙ = ∥ A ∥₄ , ∣ a ∣₄

join∙ : Pointed₀ → Type₀ → Pointed₀
join∙ (A , a) B = join A B , inl a

Ω² Ω³ : Pointed₀ → Pointed₀
Ω² = Ω^ 2
Ω³ = Ω^ 3

mapΩrefl : {A : Pointed₀} {B : Type₀} (f : A .fst → B) → Ω A .fst → Ω (B , f (pt A)) .fst
mapΩrefl f p i = f (p i)

mapΩ²refl : {A : Pointed₀} {B : Type₀} (f : A .fst → B) → Ω² A .fst → Ω² (B , f (pt A)) .fst
mapΩ²refl f p i j = f (p i j)

mapΩ³refl : {A : Pointed₀} {B : Type₀} (f : A .fst → B) → Ω³ A .fst → Ω³ (B , f (pt A)) .fst
mapΩ³refl f p i j k = f (p i j k)

meridS² : S¹ → Path S² base base
meridS² base _ = base
meridS² (loop i) j = surf i j

alpha : join S¹ S¹ → S²
alpha (inl x) = base
alpha (inr y) = base
alpha (push x y i) = (meridS² y ∙ meridS² x) i

connectionBoth : {A : Type₀} {a : A} (p : Path A a a) → PathP (λ i → Path A (p i) (p i)) p p
connectionBoth {a = a} p i j =
  hcomp
    (λ k → λ
      { (i = i0) → p (j ∨ ~ k)
      ; (i = i1) → p (j ∧ k)
      ; (j = i0) → p (i ∨ ~ k)
      ; (j = i1) → p (i ∧ k)
      })
    a

data PostTotalHopf : Type₀ where
  base : S¹ → PostTotalHopf
  loop : (x : S¹) → PathP (λ i → Path PostTotalHopf (base x) (base (rotLoop x (~ i)))) refl refl

tee12 : (x : S²) → HopfS² x → PostTotalHopf
tee12 base y = base y
tee12 (surf i j) y =
  hcomp
    (λ k → λ
      { (i = i0) → base y
      ; (i = i1) → base y
      ; (j = i0) → base y
      ; (j = i1) → base (rotLoopInv y (~ i) k)
      })
    (loop (unglue (i ∨ ~ i ∨ j ∨ ~ j) y) i j)

tee34 : PostTotalHopf → join S¹ S¹
tee34 (base x) = inl x
tee34 (loop x i j) =
  hcomp
    (λ k → λ
      { (i = i0) → push x x (j ∧ ~ k)
      ; (i = i1) → push x x (j ∧ ~ k)
      ; (j = i0) → inl x
      ; (j = i1) → push (rotLoop x (~ i)) x (~ k)
      })
    (push x x j)

tee : (x : S²) → HopfS² x → join S¹ S¹
tee x y = tee34 (tee12 x y)

fibΩ : {B : Pointed₀} (P : B .fst → Type₀) → P (pt B) → Ω B .fst → Type₀
fibΩ P f p = PathP (λ i → P (p i)) f f

fibΩ² : {B : Pointed₀} (P : B .fst → Type₀) → P (pt B) → Ω² B .fst → Type₀
fibΩ² P f = fibΩ (fibΩ P f) refl

fibΩ³ : {B : Pointed₀} (P : B .fst → Type₀) → P (pt B) → Ω³ B .fst → Type₀
fibΩ³ P f = fibΩ² (fibΩ P f) refl

Ω³Hopf : Ω³ S²∙ .fst → Type₀
Ω³Hopf = fibΩ³ HopfS² base

fibContrΩ³Hopf : ∀ p → Ω³Hopf p
fibContrΩ³Hopf p i j k =
  hcomp
    (λ m → λ
      { (i = i0) → base
      ; (i = i1) → base
      ; (j = i0) → base
      ; (j = i1) → base
      ; (k = i0) → base
      ; (k = i1) →
        isSetΩS¹ refl refl
          (λ i j → transp (λ n → HopfS² (p i j n)) (i ∨ ~ i ∨ j ∨ ~ j) base)
          (λ _ _ → base)
          m i j
      })
    (transp (λ n → HopfS² (p i j (k ∧ n))) (i ∨ ~ i ∨ j ∨ ~ j ∨ ~ k) base)

h : Ω³ S²∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
h p i j k = tee (p i j k) (fibContrΩ³Hopf p i j k)

multTwoAux : (x : S²) → Path (Path ∥ S² ∥₄ ∣ x ∣₄ ∣ x ∣₄) refl refl
multTwoAux base i j = ∣ surf i j ∣₄
multTwoAux (surf k l) i j =
  hcomp
    (λ m → λ
      { (i = i0) → ∣ surf k l ∣₄
      ; (i = i1) → ∣ surf k l ∣₄
      ; (j = i0) → ∣ surf k l ∣₄
      ; (j = i1) → ∣ surf k l ∣₄
      ; (k = i0) → ∣ surf i j ∣₄
      ; (k = i1) → ∣ surf i j ∣₄
      ; (l = i0) → ∣ surf i j ∣₄
      ; (l = i1) → squash₄ _ _ _ _ _ _ (λ k i j → step₁ k i j) refl m k i j
      })
    (step₁ k i j)

  where
  step₁ : I → I → I → ∥ S² ∥₄
  step₁ k i j =
    hcomp {A = ∥ S² ∥₄}
      (λ m → λ
        { (i = i0) → ∣ surf k (l ∧ m) ∣₄
        ; (i = i1) → ∣ surf k (l ∧ m) ∣₄
        ; (j = i0) → ∣ surf k (l ∧ m) ∣₄
        ; (j = i1) → ∣ surf k (l ∧ m) ∣₄
        ; (k = i0) → ∣ surf i j ∣₄
        ; (k = i1) → ∣ surf i j ∣₄
        ; (l = i0) → ∣ surf i j ∣₄
        })
     ∣ surf i j ∣₄

multTwoTildeAux : (t : ∥ S² ∥₄) → Path (Path ∥ S² ∥₄ t t) refl refl
multTwoTildeAux ∣ x ∣₄ = multTwoAux x
multTwoTildeAux (squash₄ _ _ _ _ _ _ t u k l m n) i j =
  squash₄ _ _ _ _ _ _
    (λ k l m → multTwoTildeAux (t k l m) i j)
    (λ k l m → multTwoTildeAux (u k l m) i j)
    k l m n

multTwoEquivAux : Path (Path (∥ S² ∥₄ ≃ ∥ S² ∥₄) (idEquiv _) (idEquiv _)) refl refl
multTwoEquivAux i j =
  ( f i j
  , hcomp
      (λ l → λ
        { (i = i0) → isPropIsEquiv _ (idIsEquiv _) (idIsEquiv _) l
        ; (i = i1) → isPropIsEquiv _ (idIsEquiv _) (idIsEquiv _) l
        ; (j = i0) → isPropIsEquiv _ (idIsEquiv _) (idIsEquiv _) l
        ; (j = i1) →
          isPropIsEquiv _
            (transp (λ k → isEquiv (f i k)) (i ∨ ~ i) (idIsEquiv _))
            (idIsEquiv _)
            l
        })
      (transp (λ k → isEquiv (f i (j ∧ k))) (i ∨ ~ i ∨ ~ j) (idIsEquiv _))
  )
  where
  f : I → I → ∥ S² ∥₄ → ∥ S² ∥₄
  f i j t = multTwoTildeAux t i j

tHopf³ : S³ → Type₀
tHopf³ base = ∥ S² ∥₄
tHopf³ (surf i j k) =
  Glue ∥ S² ∥₄
    (λ { (i = i0) → (∥ S² ∥₄ , idEquiv _)
       ; (i = i1) → (∥ S² ∥₄ , idEquiv _)
       ; (j = i0) → (∥ S² ∥₄ , idEquiv _)
       ; (j = i1) → (∥ S² ∥₄ , idEquiv _)
       ; (k = i0) → (∥ S² ∥₄ , multTwoEquivAux i j)
       ; (k = i1) → (∥ S² ∥₄ , idEquiv _)
       })

π₃S³ : Ω³ S³∙ .fst → Ω² ∥ S²∙ ∥₄∙ .fst
π₃S³ p i j = transp (λ k → tHopf³ (p j k i)) i0 ∣ base ∣₄

codeS² : S² → hGroupoid _
codeS² s = ∥ HopfS² s ∥₃ , squash₃

codeTruncS² : ∥ S² ∥₄ → hGroupoid _
codeTruncS² = 2GroupoidTrunc.rec (isOfHLevelTypeOfHLevel 3) codeS²

encodeTruncS² : Ω ∥ S²∙ ∥₄∙ .fst → ∥ S¹ ∥₃
encodeTruncS² p = transp (λ i → codeTruncS² (p i) .fst) i0 ∣ base ∣₃

codeS¹ : S¹ → hSet _
codeS¹ s = ∥ helix s ∥₂ , squash₂

codeTruncS¹ : ∥ S¹ ∥₃ → hSet _
codeTruncS¹ = GroupoidTrunc.rec (isOfHLevelTypeOfHLevel 2) codeS¹

encodeTruncS¹ : Ω ∥ S¹∙ ∥₃∙ .fst → ∥ ℤ ∥₂
encodeTruncS¹ p = transp (λ i → codeTruncS¹ (p i) .fst) i0 ∣ pos zero ∣₂


-- THE BIG GAME

f3 : Ω³ S³∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
f3 = mapΩ³refl S³→joinS¹S¹

f4 : Ω³ (join∙ S¹∙ S¹) .fst → Ω³ S²∙ .fst
f4 = mapΩ³refl alpha

f5 : Ω³ S²∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
f5 = h

f6 : Ω³ (join∙ S¹∙ S¹) .fst → Ω³ S³∙ .fst
f6 = mapΩ³refl joinS¹S¹→S³

f7 : Ω³ S³∙ .fst → Ω² ∥ S²∙ ∥₄∙ .fst
f7 = π₃S³

g8 : Ω² ∥ S²∙ ∥₄∙ .fst → Ω ∥ S¹∙ ∥₃∙ .fst
g8 = mapΩrefl encodeTruncS²

g9 : Ω ∥ S¹∙ ∥₃∙ .fst → ∥ ℤ ∥₂
g9 = encodeTruncS¹

g10 : ∥ ℤ ∥₂ → ℤ
g10 = SetTrunc.rec isSetℤ (idfun ℤ)

-- don't run me
brunerie : ℤ
brunerie = g10 (g9 (g8 (f7 (f6 (f5 (f4 (f3 (λ i j k → surf i j k))))))))

-- simpler tests

test63 : ℕ → ℤ
test63 n = g10 (g9 (g8 (f7 (63n n))))
  where
  63n : ℕ → Ω³ S³∙ .fst
  63n zero i j k = surf i j k
  63n (suc n) = f6 (f3 (63n n))

foo : Ω³ S²∙ .fst
foo i j k =
  hcomp
    (λ l → λ
      { (i = i0) → surf l l
      ; (i = i1) → surf l l
      ; (j = i0) → surf l l
      ; (j = i1) → surf l l
      ; (k = i0) → surf l l
      ; (k = i1) → surf l l
      })
    base

sorghum : Ω³ S²∙ .fst
sorghum i j k =
  hcomp
    (λ l → λ
      { (i = i0) → surf j l
      ; (i = i1) → surf k (~ l)
      ; (j = i0) → surf k (i ∧ ~ l)
      ; (j = i1) → surf k (i ∧ ~ l)
      ; (k = i0) → surf j (i ∨ l)
      ; (k = i1) → surf j (i ∨ l)
      })
    (hcomp
      (λ l → λ
        { (i = i0) → base
        ; (i = i1) → surf j l
        ; (j = i0) → surf k i
        ; (j = i1) → surf k i
        ; (k = i0) → surf j (i ∧ l)
        ; (k = i1) → surf j (i ∧ l)
        })
      (surf k i))

goo : Ω³ S²∙ .fst → ℤ
goo x = g10 (g9 (g8 (f7 (f6 (f5 x)))))


{- Computation of an alternative definition of the Brunerie number
based on https://github.com/agda/cubical/pull/741. One should note
that this computation by no means is comparable to the one of the term
"brunerie" defined above. This computation starts in π₃S³ rather than
π₃S². -}

open import Cubical.Homotopy.Group.Pi4S3.QuickProof renaming (η₃ to η₃old)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

K₂ = ∥ S² ∥₄
module f7stuff where
  _+₂_ : K₂ → K₂ → K₂
  _+₂_ = 2GroupoidTrunc.elim (λ _ → isOfHLevelΠ 4 λ _ → squash₄)
          λ { base x → x
          ; (surf i j) x → surfc x i j}
    where
    surfc : (x : K₂) → typ ((Ω^ 2) (K₂ , x))
    surfc =
      2GroupoidTrunc.elim
        (λ _ → isOfHLevelPath 4 (isOfHLevelPath 4 squash₄ _ _) _ _)
        (S²ToSetElim (λ _ → squash₄ _ _ _ _) λ i j → ∣ surf i j ∣₄)

  +₂-comm : (x y : K₂) → (x +₂ y) ≡ (y +₂ x)
  +₂-comm = 2GroupoidTrunc.elim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelPath 4 squash₄ _ _)
            λ x → 2GroupoidTrunc.elim ( λ _ → isOfHLevelPath 4 squash₄ _ _)
              λ y → main x y
    where
    main : (x y : S²) → (∣ x ∣₄ +₂ ∣ y ∣₄) ≡ (∣ y ∣₄ +₂ ∣ x ∣₄)
    main = wedgeconFunS² (λ _ _ → isOfHLevelPath 4 squash₄ _ _ )
             (λ { base → refl ; (surf i i₁) → refl})
             (λ { base → refl ; (surf i i₁) → refl})
             refl

  0₂ : K₂
  0₂ = ∣ base ∣₄

  -₂ : K₂ → K₂
  -₂ = 2GroupoidTrunc.elim (λ _ → squash₄) λ { base → ∣ base ∣₄ ; (surf i i₁) → ∣ surf (~ i) i₁ ∣₄}

  rCancel₂ : (x : K₂) → (x +₂ -₂ x) ≡ 0₂
  rCancel₂ = 2GroupoidTrunc.elim (λ _ → isOfHLevelPath 4 squash₄ _ _)
             λ { base → refl
               ; (surf i i₁) k → help k i i₁}
    where
    help : cong₂ {A = Path S² base base} {B = λ  _ → Path S² base base}
                 (λ x y → cong₂ _+₂_ (cong ∣_∣₄ x) (cong -₂ (cong {A = S²} ∣_∣₄ y))) surf surf
                 ≡ refl
    help = cong₂Funct (λ x y → cong₂ _+₂_ (cong ∣_∣₄ x) (cong -₂ (cong {A = S²} ∣_∣₄ y))) surf surf
        ∙∙ (λ k → (λ i j → +₂-comm ∣ surf i j ∣₄ ∣ base ∣₄ k)
                  ∙ λ i j → ∣ surf (~ i) j ∣₄)
        ∙∙ rCancel _

  lCancel₂ : (x : K₂) → ((-₂ x) +₂ x) ≡ 0₂
  lCancel₂ x = +₂-comm (-₂ x) x ∙' rCancel₂ x

  rUnit₂ : (x : K₂) → x +₂ 0₂ ≡ x
  rUnit₂ = 2GroupoidTrunc.elim (λ _ → isOfHLevelPath 4 squash₄ _ _)
           λ { base → refl ; (surf i i₁) → refl}

  lUnit₂ : (x : K₂) → 0₂ +₂ x ≡ x
  lUnit₂ = 2GroupoidTrunc.elim (λ _ → isOfHLevelPath 4 squash₄ _ _) λ _ → refl

  assoc₂ : (x y z : K₂) → (x +₂ (y +₂ z)) ≡ ((x +₂ y) +₂ z)
  assoc₂ =
    2GroupoidTrunc.elim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelPath 4 squash₄ _ _)
      λ x → 2GroupoidTrunc.elim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelPath 4 squash₄ _ _)
        λ y → 2GroupoidTrunc.elim (λ _ → isOfHLevelPath 4 squash₄ _ _)
          λ z → main x y z
    where
    main : (x y z : S²) → (∣ x ∣₄ +₂ (∣ y ∣₄ +₂ ∣ z ∣₄)) ≡  ((∣ x ∣₄ +₂ ∣ y ∣₄) +₂ ∣ z ∣₄)
    main = wedgeconFunS² (λ _ _ → isOfHLevelΠ 4 (λ _ → isOfHLevelPath 4 squash₄ _ _ ))
           (λ x z → λ i → ((rUnit₂ ∣ x ∣₄ (~ i)) +₂ ∣ z ∣₄))
           (λ x z → lUnit₂ (∣ x ∣₄ +₂ ∣ z ∣₄))
           refl

  IsoK₂ : (x : S²) → Iso K₂ K₂
  Iso.fun (IsoK₂ x) z = z +₂ ∣ x ∣₄
  Iso.inv (IsoK₂ x) = _+₂ -₂ ∣ x ∣₄
  Iso.rightInv (IsoK₂ x) z = sym (assoc₂ z (-₂ ∣ x ∣₄) ∣ x ∣₄) ∙∙ cong (z +₂_) (lCancel₂ ∣ x ∣₄) ∙∙ rUnit₂ z
  Iso.leftInv (IsoK₂ x) z = sym (assoc₂ z ∣ x ∣₄ (-₂ ∣ x ∣₄)) ∙∙ cong (z +₂_) (rCancel₂ ∣ x ∣₄) ∙∙ rUnit₂ z



  K₂≃K₂ : (x : S²) → K₂ ≃ K₂
  fst (K₂≃K₂ x) y = ∣ x ∣₄ +₂ y
  snd (K₂≃K₂ x) = help x
    where
    help : (x : _) → isEquiv (λ y → ∣ x ∣₄ +₂ y)
    help = S²ToSetElim (λ _ → isProp→isSet (isPropIsEquiv _))
                       (idEquiv _ .snd)

  Code : Susp S² → Type ℓ-zero
  Code north = K₂
  Code south = K₂
  Code (merid a i) = isoToPath (invIso (IsoK₂ a)) i

  encode : (x : Susp S²) →  north ≡ x → Code x
  encode x = J (λ x p → Code x) ∣ base ∣₄


ηIso : Iso ((join S¹ S¹ , inl base) →∙ (Susp S² , north))
       ((join S¹ S¹ , inl base) →∙ (Susp (Susp S¹) , north))
ηIso = compIso (invIso (Σ-cong-iso-fst {B = λ f → f (inl base) ≡ north}  is1))
               (Σ-cong-iso-snd l2)
  where
  is1 : Iso (join S¹ S¹ → Susp (Susp S¹)) (join S¹ S¹ → Susp S²) 
  is1 = invIso (codomainIso (congSuspIso (equivToIso S²≃SuspS¹)))
  open import Cubical.Foundations.Equiv.HalfAdjoint

  l2 : (f : join S¹ S¹ → Susp (Susp S¹)) →
      Iso (Iso.fun is1 f (inl base) ≡ north)
      (f (inl base) ≡ north)
  l2 f = invIso (congIso {x = f (inl base)} {y = north} (congSuspIso (invIso (equivToIso S²≃SuspS¹))))






S¹×S¹→S²' : S¹ → S¹ → S²
S¹×S¹→S²' base y = base
S¹×S¹→S²' (loop i) base = base
S¹×S¹→S²' (loop i) (loop j) = surf j i
-- The brunerie element can be shown to correspond to the following map
η₃ : (join S¹ S¹ , inl base) →∙ (Susp S² , north)
fst η₃ (inl x) = north
fst η₃ (inr x) = north
fst η₃ (push a b i) =
  (sym (σ (S² , base) (S¹×S¹→S²' a b)) ∙ sym (σ (S² , base) (S¹×S¹→S²' a b))) i
snd η₃ = refl


open import Cubical.HITs.S1 renaming (encode to encode' ; _·_ to _*_)
open import Cubical.HITs.Sn using (S¹×S¹→S²)

ηIsopresη : Iso.inv ηIso η₃-raw ≡ η₃
ηIsopresη =
  ΣPathP ((funExt (λ { (inl x) → refl
                     ; (inr x) → refl
                     ; (push a b i) j → h3 a b j i}))
         , refl)
  where
  h3 : (a b : S¹) → cong (fst (Iso.inv ηIso η₃-raw)) (push a b)
                  ≡ (sym (σ (S² , base) (S¹×S¹→S²' a b)) ∙ sym (σ (S² , base) (S¹×S¹→S²' a b)))
  h3 a b = cong-∙ (suspFun SuspS¹→S²) (sym (σ (Susp∙ S¹) (S¹×S¹→S² a b))) (sym (σ (Susp∙ S¹) (S¹×S¹→S² a b)))
         ∙ cong (λ x → sym x ∙ sym x) (zz (S¹×S¹→S² a b) ∙ cong (σ S²∙) (help a b))
    where
    zz : (a : Susp S¹) → cong (suspFun SuspS¹→S²) (σ (Susp∙ S¹) a)
                       ≡ σ S²∙ (SuspS¹→S² a)
    zz a = cong-∙ (suspFun SuspS¹→S²) (merid a) (sym (merid north))

    help : (a b : S¹) → SuspS¹→S² (S¹×S¹→S² a b) ≡ S¹×S¹→S²' a b
    help base b = refl
    help (loop i) base = refl
    help (loop i) (loop j) k =
      hcomp (λ r → λ {(i = i0) → SuspS¹→S² (rCancel (merid base) (r ∨ k) j)
                     ; (i = i1) → SuspS¹→S² (rCancel (merid base) (r ∨ k) j)
                     ; (j = i0) → base
                     ; (j = i1) → base
                     ; (k = i0) → SuspS¹→S²
                                     (doubleCompPath-filler (sym (rCancel (merid base)))
                                       (λ i → merid (loop i) ∙ sym (merid base))
                                       (rCancel (merid base)) r i j)
                     ; (k = i1) → surf j i})
            (hcomp (λ r → λ {(i = i0) → SuspS¹→S² (rCancel-filler (merid base) r k j)
                     ; (i = i1) → SuspS¹→S² (rCancel-filler (merid base) r k j)
                     ; (j = i0) → base
                     ; (j = i1) → base
                     ; (k = i0) → SuspS¹→S²
                                     (compPath-filler (merid (loop i)) (sym (merid base)) r j)
                     ; (k = i1) → surf j i})
                   (surf j i))


S²Code : S² → Type
S²Code base = Ω S²∙ .fst
S²Code (surf i j) =
  Glue (Ω S²∙ .fst)
       λ {(i = i0) → (Ω S²∙ .fst) , idEquiv _
        ; (i = i1) → Ω S²∙ .fst , idEquiv _
        ; (j = i0) → Ω S²∙ .fst , he i
        ; (j = i1) → Ω S²∙ .fst , idEquiv _}
  where
  hehe : (y : S²) → (p : base ≡ y) → p ≡ p
  hehe y = J (λ y p → p ≡ p) surf

  he : idEquiv (Ω S²∙ .fst) ≡ idEquiv (Ω S²∙ .fst)
  he = Σ≡Prop (λ _ → isPropIsEquiv _) (funExt (hehe base))

S²Code3 : Susp S¹ → Type
S²Code3 north = Susp S¹
S²Code3 south = Susp S¹
S²Code3 (merid a i) = ua (_ , iseq a) i
  where
  help : (b : S¹) → Susp S¹ → Susp S¹
  help b north = north
  help b south = south
  help b (merid a i) = merid (invLooper b * a) i

  isEquiv-h : help base ≡ idfun _
  isEquiv-h x north = north
  isEquiv-h x south = south
  isEquiv-h x (merid a i) = merid a i

  iseq : (a : S¹) → isEquiv (help a)
  iseq =
    toPropElim (λ _ → isPropIsEquiv _)
      (subst isEquiv (sym isEquiv-h)
        (idEquiv _ .snd))

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties


ΩS²→ : Ω (Susp∙ S¹) →∙ Susp∙ S¹ 
ΩS²→ = (λ p → subst S²Code3 p north) , refl

Ω²S²→ : Ω³ (Susp∙ S¹) .fst → Ω² (Susp∙ S¹) .fst
Ω²S²→ = mapΩ²refl (fst ΩS²→)

hitler : Ω² (Susp∙ S¹) .fst → ℤ
hitler p = ΩKn+1→Kn 0 λ i → ΩKn+1→Kn 1 λ j → ∣ p i j ∣ₕ

hess : Ω³ (Susp∙ S¹) .fst → ℤ
hess = hitler ∘ Ω²S²→

zz : Ω³ (Susp∙ S¹) .fst
zz = mapΩ³refl S²→SuspS¹ d
  where
  d : Ω³ (S² , base) .fst
  d = sorghum -- sym (rCancel surf) ∙∙ EH 0 surf (sym surf) ∙∙ lCancel surf

S²→S¹ : S² → Type
S²→S¹ base = S¹
S²→S¹ (surf i j) =
  Glue S¹
       λ {(i = i0) → S¹ , idEquiv _
        ; (i = i1) → S¹ , idEquiv _
        ; (j = i0) → S¹ , idEquiv _
        ; (j = i1) → S¹ , he i}
  where
  he : idEquiv S¹ ≡ idEquiv S¹
  he = Σ≡Prop (λ _ → isPropIsEquiv _)
              (funExt λ { base → loop
                        ; (loop i) j → loop i * loop j})
  asd : {!(x : S¹) → base ≡ x!}
  asd = {!!}

S²→ℤ : S² → Type
S²→ℤ base = ℤ
S²→ℤ (surf i j) =
  Glue ℤ
       λ {(i = i0) → ℤ , isoToEquiv (iso sucℤ predℤ sucPred predSuc)
        ; (i = i1) → ℤ , isoToEquiv (iso sucℤ predℤ sucPred predSuc)
        ; (j = i0) → ℤ , isoToEquiv (iso sucℤ predℤ sucPred predSuc)
        ; (j = i1) → ℤ , isoToEquiv (iso sucℤ predℤ sucPred predSuc)}

S²→ℤ' : (x : S²) → base ≡ x → Type
S²→ℤ' base p = ℤ
S²→ℤ' (surf i j) p =
  Glue (S²→ℤ (surf i j))
       λ {(i = i0) → ℤ , idEquiv _
        ; (i = i1) → ℤ , idEquiv _
        ; (j = i0) → ℤ , idEquiv _
        ; (j = i1) → ℤ , idEquiv _}
  where
  r : isEquiv (subst S²→ℤ (sym p))
  r = {!!}

{-
subst S²→ℤ (sym p) ?
-}

S²→S¹' : ∥ S² ∥₄ → Type
S²→S¹' x =
       2GroupoidTrunc.rec {B = TypeOfHLevel ℓ-zero 3}
       (isOfHLevelTypeOfHLevel 3)
       (λ x → S²→S¹ x , l x) x .fst
  where
  l : (x : _) → isOfHLevel 3 (S²→S¹ x)
  l = S²ToSetElim (λ _ → isProp→isSet (isPropIsOfHLevel 3)) isGroupoidS¹

p2 : Ω ∥ S²∙ ∥₄∙ .fst → S¹
p2 x = subst S²→S¹' x base

→ℤ : Ω² ∥ S²∙ ∥₄∙ .fst →  ℤ
→ℤ p = winding (mapΩrefl p2 p) -- winding λ i → {!mapΩrefl p2 ?!} -- winding (mapΩrefl p2 p)





kr : (x : S²) → (base ≡ x) → S²
kr base p = base
kr (surf i j) p = {!p!}

S²Code2s : K₂ → S² → Type
S²Code2s x base = ∥ S² ∥₄
S²Code2s x (surf i j) =
  Glue ∥ S² ∥₄
       λ {(i = i0) → ∥ S² ∥₄ , idEquiv _
        ; (i = i1) → ∥ S² ∥₄ , idEquiv _
        ; (j = i0) → ∥ S² ∥₄ , {!idEquiv _!}
        ; (j = i1) → ∥ S² ∥₄ , {!!}}
  where
  _+₂_ : K₂ → K₂ → K₂
  _+₂_ = 2GroupoidTrunc.elim (λ _ → isOfHLevelΠ 4 λ _ → squash₄)
          λ { base x → x
          ; (surf i j) x → surfc x i j}
    where
    surfc : (x : K₂) → typ ((Ω^ 2) (K₂ , x))
    surfc =
      2GroupoidTrunc.elim
        (λ _ → isOfHLevelPath 4 (isOfHLevelPath 4 squash₄ _ _) _ _)
        (S²ToSetElim (λ _ → squash₄ _ _ _ _) λ i j → ∣ surf i j ∣₄)

  asd : (x : K₂) (p : ∣ base ∣₄ ≡ x) → {!x +₂ x)!}
  asd = {!!}


  isEq : (x : K₂) → isEquiv (x +₂_)
  isEq = 2GroupoidTrunc.elim (λ _ → isProp→isOfHLevelSuc 3 (isPropIsEquiv _))
           (S²ToSetElim (λ _ → isProp→isSet (isPropIsEquiv _))
             (idEquiv _ .snd))


S²→ΩS³ : S² → Ω S³∙ .fst
S²→ΩS³ base = refl
S²→ΩS³ (surf i j) k = surf i j k

Ω²s : Ω S²∙ .fst → Ω S³∙ .fst
Ω²s p = {!cong S²→ΩS³ p!}

S³Code : S³ → Type
S³Code base = {!S³!}
S³Code (surf i j k) = {!!}

S²Code? : S² → Type
S²Code? base = Ω S³∙ .fst × S²
S²Code? (surf i j) =
  Glue (Ω S³∙ .fst × S²)
    λ {(i = i0) → Ω S³∙ .fst × S² , idEquiv _
        ; (i = i1) → Ω S³∙ .fst × S² , idEquiv _
        ; (j = i0) → Ω S³∙ .fst × S² , idEquiv _
        ; (j = i1) → Ω S³∙ .fst × S² , {!!}} 
  where

  h2 : (p : Path S³ base base) (x : S²) → p ≡ p
  h2 p base = refl
  h2 p (surf i j) k = sss k i j
    where
    sss : refl {x = refl {x = p}} ≡ refl {x = refl {x = p}}
    sss = {!!} ∙ {!S²→ΩS³ ?!} ∙ {!!}

  ttt : idEquiv (Ω S³∙ .fst × S²) ≡ idEquiv (Ω S³∙ .fst × S²)
  ttt = Σ≡Prop (λ _ → isPropIsEquiv _) (funExt λ p → ΣPathP (h2 (fst p) (snd p) , refl))

S²CodeR : S² → Type
S²CodeR base = S¹ × ∥ S² ∥₄
S²CodeR (surf i j) =
  Glue (S¹ × ∥ S² ∥₄)
       λ {(i = i0) → (S¹ × ∥ S² ∥₄) , {!!}
        ; (i = i1) → (S¹ × ∥ S² ∥₄) , {!!}
        ; (j = i0) → (S¹ × ∥ S² ∥₄) , {!!}
        ; (j = i1) → (S¹ × ∥ S² ∥₄) , {!!}}
  where
  _+₂_ : K₂ → K₂ → K₂
  _+₂_ = 2GroupoidTrunc.elim (λ _ → isOfHLevelΠ 4 λ _ → squash₄)
          λ { base x → x
          ; (surf i j) x → surfc x i j}
    where
    surfc : (x : K₂) → typ ((Ω^ 2) (K₂ , x))
    surfc =
      2GroupoidTrunc.elim
        (λ _ → isOfHLevelPath 4 (isOfHLevelPath 4 squash₄ _ _) _ _)
        (S²ToSetElim (λ _ → squash₄ _ _ _ _) λ i j → ∣ surf i j ∣₄)

  thef : S¹ →  ∥ S² ∥₄ → ∥ S² ∥₄
  thef x =
    2GroupoidTrunc.rec squash₄
      λ { base → {!!}
        ; (surf i j) → {!!}}

--   isEq-thef : (x y : S¹) → isEquiv (thef x y)
--   isEq-thef = toPropElim (λ _ → isPropΠ λ _ → isPropIsEquiv _)
--                 (toPropElim (λ _ → isPropIsEquiv _)
--                   (idEquiv _ .snd))

--   l : Iso (S¹ × S¹ × ∥ S² ∥₄) (S¹ × S¹ × ∥ S² ∥₄)
--   Iso.fun l (x , y , z) = x , y , (thef x y z)
--   Iso.inv l (x , y , z) = x , y , invEq (_ , isEq-thef x y) z
--   Iso.rightInv l (x , y , z) = ΣPathP (refl , (ΣPathP (refl , secEq (_ , isEq-thef x y) z)))
--   Iso.leftInv l (x , y , z) = ΣPathP (refl , (ΣPathP (refl , retEq (_ , isEq-thef x y) z)))

-- -- tt123 : (x : S²) → base ≡ x → S²CodeR x
-- -- tt123 p = J (λ p _ → S²CodeR p) (base , base , ∣ p ∣₄)

-- -- grr : Ω S²∙ .fst → ∥ S² ∥₄
-- -- grr p = tt123 base p .snd .snd

-- -- grr2 : Ω³ S²∙ .fst → Ω² ∥ S²∙ ∥₄∙ .fst
-- -- grr2 = mapΩ²refl grr


-- -- S²Code2 : S² → Type
-- -- S²Code2 base = ∥ S² ∥₄
-- -- S²Code2 (surf i j) =
-- --   Glue ∥ S² ∥₄
-- --        λ {(i = i0) → ∥ S² ∥₄ , idEquiv _
-- --         ; (i = i1) → ∥ S² ∥₄ , idEquiv _
-- --         ; (j = i0) → ∥ S² ∥₄ , idEqK i
-- --         ; (j = i1) → ∥ S² ∥₄ , idEquiv _}
-- --   where
-- --   _+₂_ : K₂ → K₂ → K₂
-- --   _+₂_ = 2GroupoidTrunc.elim (λ _ → isOfHLevelΠ 4 λ _ → squash₄)
-- --           λ { base x → x
-- --           ; (surf i j) x → surfc x i j}
-- --     where
-- --     surfc : (x : K₂) → typ ((Ω^ 2) (K₂ , x))
-- --     surfc =
-- --       2GroupoidTrunc.elim
-- --         (λ _ → isOfHLevelPath 4 (isOfHLevelPath 4 squash₄ _ _) _ _)
-- --         (S²ToSetElim (λ _ → squash₄ _ _ _ _) λ i j → ∣ surf i j ∣₄)


-- --   h2 : (x : K₂) → x ≡ x
-- --   h2 = 2GroupoidTrunc.elim
-- --         (λ _ → isOfHLevelPath 4 squash₄ _ _)
-- --           λ { base → refl
-- --           ; (surf i j) k → ∣ surf i j ∣₄ +₂ ∣ foo i j k ∣₄}


-- --   h2s : (x : K₂) → h2 x ≡ refl
-- --   h2s = 2GroupoidTrunc.elim
-- --         (λ _ → isOfHLevelPath 4 (isOfHLevelPath 4 squash₄ _ _) _ _)
-- --         (S²ToSetElim (λ _ → squash₄ _ _ _ _) refl)

-- --   idEqK : idEquiv K₂ ≡ idEquiv _
-- --   idEqK = Σ≡Prop (λ _ → isPropIsEquiv _)
-- --               (funExt h2)


-- -- s2 : (x : _) → (base ≡ x) → S²Code2s ∣ x ∣₄ x
-- -- s2 x p = transport (cong (λ x → S²Code2s ∣ x ∣₄ x) p) ∣ base ∣₄

-- -- z3 : Ω³ S²∙ .fst → Ω² ∥ S²∙ ∥₄∙ .fst
-- -- z3 = mapΩ²refl (s2 base)

-- -- →ℤt : Ω³ S²∙ .fst  → ℤ -- →ℤ (surf ∙ surf) ≡ -2
-- -- →ℤt x = g10 (g9 (g8 (z3 sorghum))) -- →ℤ (z3 sorghum)

-- -- tt2 : Ω² S²∙ .fst → Ω² S²∙ .fst
-- -- tt2 p = sym (transportRefl refl) ∙∙ (λ i → transport (λ j → S²Code (p i j)) refl) ∙∙ transportRefl refl


-- -- -- We will need a map Ω (Susp S²) → K₂. It turns out that the
-- -- -- following map is fast. It need a bit of work, however. It's
-- -- -- esentially the same map as you find in ZCohomology from ΩKₙ₊₁ to
-- -- -- Kₙ. This gives another definition of f7 which appears to work better.

-- -- -- We now get an alternative definition of f7
-- -- f7' : typ (Ω (Susp∙ S²)) → K₂
-- -- f7' = f7stuff.encode north

-- -- makeFun : {A : Type} (x : A) → Ω³ (A , x) .fst → join S¹ S¹ → A
-- -- makeFun x p (inl x₁) = x
-- -- makeFun x p (inr x₁) = x
-- -- makeFun x p (push base b i) = x
-- -- makeFun x p (push (loop i₁) base i) = x
-- -- makeFun x p (push (loop i₁) (loop i₂) i) = p i₁ i₂ i


-- -- makeFun⁻ : {A : Type} (x : A) → ((join S¹ S¹ , inl base) →∙ (A , x)) → Ω³ (A , x) .fst
-- -- makeFun⁻ x l i j k =
-- --   hcomp (λ r → λ {(i = i0) → {!!}
-- --                       ; (i = i1) → {!!}
-- --                       ; (j = i0) → {!!}
-- --                       ; (j = i1) → {!!}
-- --                       ; (k = i0) → {!!}
-- --                       ; (k = i1) → {!!}})
-- --      (fst l (push (loop i) (loop j) k))

-- -- indLem : {A : Type} (x : A) (p : Ω³ (A , x) .fst) → isOfHLevel 5 A → ∥ {!makeFun x p ≡ ?!} ∥₂
-- -- indLem = {!!}


-- -- mappie : π₃*S³ .fst → ∥ Ω² (K₂ , ∣ base ∣₄) .fst ∥₂
-- -- mappie =
-- --   SetTrunc.map
-- --     λ f → mapΩ²refl f7'
-- --       λ i j k → hcomp (λ r → λ {(i = i0) → {!!}
-- --                                ; (i = i1) → {!!}
-- --                                ; (j = i0) → {!!}
-- --                                ; (j = i1) → {!suspFun (SuspS¹→S²) (η₃-raw .fst (push (loop i) (loop j) k!}
-- --                                ; (k = i0) → {!!}
-- --                                ; (k = i1) → {!suspFun (SuspS¹→S²) (η₃-raw .fst (push (loop i) (loop j) r))!}})
-- --                   (suspFun (SuspS¹→S²) (f .fst (push (loop i) (loop j) k))) -- Ω³ (Susp S²)

-- -- -- We can define the Brunerie number by
-- -- brunerie' : ℤ
-- -- brunerie' = →ℤ (λ i j → f7' λ k → η₃ .fst (push (loop i) (loop j) k))

-- -- brunerie'' : ℤ
-- -- brunerie'' = g10 (g9 (g8 (grr2 foo))) -- →ℤ (λ i j → f7' λ k → suspFun (SuspS¹→S²) (η₃-raw .fst (push (loop i) (loop j) k))) -- λ i j → f7' λ k → suspFun (SuspS¹→S²) (η₃-raw .fst (push (loop i) (loop j) k))))

-- -- -- Computing it takes ~1s
-- -- brunerie'≡-2 : brunerie'' ≡ -1
-- -- brunerie'≡-2 = {!g10 (g9 (g8 (grr2 foo)))!} -- refl -- refl

-- -- -- open import Cubical.HITs.Sn


-- -- -- S²Code3' : S₊ 2 → Type
-- -- -- S²Code3' north = coHomK 2
-- -- -- S²Code3' south = coHomK 2
-- -- -- S²Code3' (merid a i) = isoToPath (IsK a) i -- ua (brr a , isEqbrr a) (~ i)
-- -- --   where
-- -- --   brr-raw : (a : S¹) → Susp S¹ → ∥ Susp S¹ ∥ 4
-- -- --   brr-raw a north = 0ₖ 2
-- -- --   brr-raw a south = 0ₖ 2
-- -- --   brr-raw a (merid b i) = ∣ (merid b ∙ sym (merid a)) i ∣ₕ

-- -- --   brr : (a : S¹) → coHomK 2 → coHomK 2
-- -- --   brr a = Trunc.rec (isOfHLevelTrunc 4)
-- -- --                     (brr-raw a)

-- -- --   IsK : (a : S¹) → Iso (coHomK 2) (coHomK 2)
-- -- --   Iso.fun (IsK a) = brr a
-- -- --   Iso.inv (IsK a) = brr (invLooper a)
-- -- --   Iso.rightInv (IsK a) = {!!}
-- -- --   Iso.leftInv (IsK a) = {!!}

-- -- --   brr≡id : (x : _) → brr base x ≡ x 
-- -- --   brr≡id = Trunc.elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
-- -- --                       λ { north → refl
-- -- --                         ; south i → ∣ merid base i ∣ₕ
-- -- --                         ; (merid a i) j → ∣ compPath-filler (merid a) (sym (merid base)) (~ j) i ∣ₕ}

-- -- --   isEqbrr : (a : S¹) → isEquiv (brr a)
-- -- --   isEqbrr = sphereElim 0 (λ _ → isPropIsEquiv _) (subst isEquiv (sym (funExt brr≡id)) (idEquiv _ .snd))

-- -- -- ΩS²→ : Ω (S₊∙ 2) .fst → coHomK-ptd 2 .fst
-- -- -- ΩS²→ p = transport (cong S²Code3' p) (0ₖ 2)

-- -- -- ΩS²→gen : (x : S₊ 2) → (north ≡ x) → S²Code3' x
-- -- -- ΩS²→gen x p = transport (cong S²Code3' p) (0ₖ 2)

-- -- -- Ω³S²→ : Ω³ (S₊∙ 2) .fst → Ω² (coHomK-ptd 2) .fst
-- -- -- Ω³S²→ = mapΩ²refl ΩS²→


-- -- -- Ω³' : Ω³ (S₊∙ 2) .fst
-- -- -- Ω³' i j k = (S²→ΩS² ∘ S³→joinS¹S¹) (surf i j k)
-- -- --   where
-- -- --   S²→ΩS² : join S¹ S¹ → S₊ 2
-- -- --   S²→ΩS² (inl x) = north
-- -- --   S²→ΩS² (inr x) = north
-- -- --   S²→ΩS² (push a b i) = σ S¹∙ (invLooper b * a) i

-- -- --   hpf : join S¹ S¹ → S₊ 2
-- -- --   hpf (inl x) = north
-- -- --   hpf (inr x) = north
-- -- --   hpf (push a b i) = σ S¹∙ (invLooper b * a) i

-- -- -- br : ℤ
-- -- -- br = ΩKn+1→Kn 0 (cong (ΩKn+1→Kn 1) (Ω³S²→ Ω³'))

-- -- -- S²Code3 : S² → Type
-- -- -- S²Code3 base = K₂
-- -- -- S²Code3 (surf i j) =
-- -- --   Glue K₂
-- -- --        λ {(i = i0) → K₂ , idEquiv _
-- -- --         ; (i = i1) → K₂ , idEquiv _
-- -- --         ; (j = i0) → K₂ , ss i
-- -- --         ; (j = i1) → K₂ , idEquiv _}
-- -- --   where
-- -- --   h3 : Iso K₂ K₂
-- -- --   h3 = {!!}

-- -- --   h2 : (x : K₂) → x ≡ x
-- -- --   h2 x = cong (f7stuff._+₂ x) (help x)
-- -- --     where
-- -- --     help : (x : K₂) → Path K₂ ∣ base ∣₄ ∣ base ∣₄
-- -- --     help = 2GroupoidTrunc.rec (isOfHLevelPath 4 squash₄ _ _)
-- -- --            λ { base → refl
-- -- --             ; (surf i j) k → ∣ f4 (f3 (λ i j k → surf i j k)) i j k ∣₄}

-- -- --   ss : idEquiv K₂ ≡ idEquiv K₂
-- -- --   ss = Σ≡Prop (λ _ → isPropIsEquiv _) (funExt h2)

-- -- -- tmap : Ω² S²∙ .fst → Ω (K₂ , ∣ base ∣₄) .fst
-- -- -- tmap p = sym (transportRefl ∣ base ∣₄)
-- -- --       ∙∙ (λ i → transport (λ j → S²Code3 (p i j)) ∣ base ∣₄)
-- -- --       ∙∙ transportRefl ∣ base ∣₄

-- -- -- f5' : Ω³ S²∙ .fst → Ω² (K₂ , ∣ base ∣₄) .fst
-- -- -- f5' p = sym (∙∙lCancel (transportRefl ∣ base ∣₄)) ∙∙ mapΩrefl tmap p ∙∙ ∙∙lCancel (transportRefl ∣ base ∣₄)

-- -- -- brunerie1 : ℤ
-- -- -- brunerie1 = g10 (g9 (g8 (λ i j → {!transport (λ j → S²Code3 (surf i j)) ∣ base ∣₄!})))
