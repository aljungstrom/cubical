{-# OPTIONS --safe #-}
module Cubical.Experiments.Brunerie where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Join
open import Cubical.HITs.SetTruncation as SetTrunc
open import Cubical.HITs.GroupoidTruncation as GroupoidTrunc
open import Cubical.HITs.2GroupoidTruncation as 2GroupoidTrunc
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

K₂ = ∥ S² ∥₄

4TruncElim : ∀ {ℓ}{A : Type ℓ} {P : ∥ A ∥₄ → Type} → ((x : _) → isOfHLevel 4 (P x))
  → ((x : _) → P ∣ x ∣₄)
  → (x : _) → P x
4TruncElim {P = P} hlev b ∣ x ∣₄ = b x
4TruncElim {P = P} hlev b (squash₄ x y p q r s t u i j k l) = help i j k l
  where
  help : PathP (λ i → PathP (λ j → PathP (λ k → PathP (λ l → P (squash₄ x y p q r s t u i j k l))
               (4TruncElim hlev b x) (4TruncElim hlev b y))
               (λ l → 4TruncElim hlev b (p l))
               λ l → 4TruncElim hlev b (q l))
               (λ k l → 4TruncElim hlev b (r k l)) λ k l → 4TruncElim hlev b (s k l))
               (λ j k l → 4TruncElim hlev b (t j k l)) λ j k l → 4TruncElim hlev b (u j k l)
  help = toPathP (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (hlev _) _ _) _ _) _ _ _ _)

_+₂_ : K₂ → K₂ → K₂
_+₂_ = 4TruncElim (λ _ → isOfHLevelΠ 4 λ _ → squash₄)
               λ x → 4TruncElim (λ _ → squash₄)
                 λ y → wedgeconFunS² (λ _ _ → squash₄) ∣_∣₄ ∣_∣₄ refl x y


private
  sillyfill : I → I → I → K₂
  sillyfill k i j =
    hfill (λ k → λ { (i = i0) → ∣ base ∣₄
                     ; (i = i1) → ∣ base ∣₄
                     ; (j = i0) → ∣ base ∣₄
                     ; (j = i1) → ∣ base ∣₄})
           (inS (∣ surf i j ∣₄)) k

+₂-comm : (x y : K₂) → (x +₂ y) ≡ (y +₂ x)
+₂-comm = 4TruncElim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelPath 4 squash₄ _ _)
          λ x → 4TruncElim ( λ _ → isOfHLevelPath 4 squash₄ _ _)
            λ y → main x y
  where
  main : (x y : S²) → (∣ x ∣₄ +₂ ∣ y ∣₄) ≡ (∣ y ∣₄ +₂ ∣ x ∣₄)
  main = wedgeconFunS² (λ _ _ → isOfHLevelPath 4 squash₄ _ _ )
           (λ { base → refl ; (surf i i₁) k → sillyfill (~ k) i i₁})
           (λ { base → refl ; (surf i i₁) k → sillyfill k i i₁})
           refl

0₂ : K₂
0₂ = ∣ base ∣₄

-₂ : K₂ → K₂
-₂ = 4TruncElim (λ _ → squash₄) λ { base → ∣ base ∣₄ ; (surf i i₁) → ∣ surf (~ i) i₁ ∣₄}

rCancel₂ : (x : K₂) → (x +₂ -₂ x) ≡ 0₂
rCancel₂ = 4TruncElim (λ _ → isOfHLevelPath 4 squash₄ _ _)
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
rUnit₂ = 4TruncElim (λ _ → isOfHLevelPath 4 squash₄ _ _)
         λ { base → refl ; (surf i i₁) k → sillyfill (~ k) i i₁}

lUnit₂ : (x : K₂) → 0₂ +₂ x ≡ x
lUnit₂ = 4TruncElim (λ _ → isOfHLevelPath 4 squash₄ _ _) λ _ → refl

assoc₂ : (x y z : K₂) → (x +₂ (y +₂ z)) ≡ ((x +₂ y) +₂ z)
assoc₂ =
  4TruncElim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelPath 4 squash₄ _ _)
    λ x → 4TruncElim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelPath 4 squash₄ _ _)
      λ y → 4TruncElim (λ _ → isOfHLevelPath 4 squash₄ _ _)
        λ z → main x y z
  where
  main : (x y z : S²) → (∣ x ∣₄ +₂ (∣ y ∣₄ +₂ ∣ z ∣₄)) ≡  ((∣ x ∣₄ +₂ ∣ y ∣₄) +₂ ∣ z ∣₄)
  main = wedgeconFunS² (λ _ _ → isOfHLevelΠ 4 (λ _ → isOfHLevelPath 4 squash₄ _ _ ))
         (λ x z → λ i → ((rUnit₂ ∣ x ∣₄ (~ i)) +₂ ∣ z ∣₄))
         (λ x z → lUnit₂ (∣ x ∣₄ +₂ ∣ z ∣₄))
         refl

S¹×S¹→S² : S¹ → S¹ → S²
S¹×S¹→S² base y = base
S¹×S¹→S² (loop i) base = base
S¹×S¹→S² (loop i) (loop i₁) = surf i i₁

IsoK₂ : (x : S²) → Iso K₂ K₂
Iso.fun (IsoK₂ x) z = z +₂ ∣ x ∣₄
Iso.inv (IsoK₂ x) = _+₂ -₂ ∣ x ∣₄
Iso.rightInv (IsoK₂ x) z = sym (assoc₂ z (-₂ ∣ x ∣₄) ∣ x ∣₄) ∙∙ cong (z +₂_) (lCancel₂ ∣ x ∣₄) ∙∙ rUnit₂ z
Iso.leftInv (IsoK₂ x) z = sym (assoc₂ z ∣ x ∣₄ (-₂ ∣ x ∣₄)) ∙∙ cong (z +₂_) (rCancel₂ ∣ x ∣₄) ∙∙ rUnit₂ z


open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as Trunc
Code-raw : Susp S² → Type ℓ-zero
Code-raw north = K₂
Code-raw south = K₂
Code-raw (merid a i) = isoToPath (IsoK₂ a) i

is4C : (x : Susp S²) → isOfHLevel 4 (Code-raw x)
is4C = suspToPropElim base (λ _ → isPropIsOfHLevel 4) squash₄

CODE : hLevelTrunc 5 (Susp S²) → Type ℓ-zero
CODE x = (Trunc.rec (isOfHLevelTypeOfHLevel 4) λ x → (Code-raw x) , (is4C x)) x .fst

encode' : (x : hLevelTrunc 5 (Susp S²)) →  ∣ north ∣ₕ ≡ x → CODE x
encode' x = J (λ x p → CODE x) ∣ base ∣₄

f7' : typ (Ω ((hLevelTrunc 5 (Susp S²)) , ∣ north ∣ₕ)) → K₂
f7' = encode' ∣ north ∣ₕ

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

f6' : Ω³ (join∙ S¹∙ S¹) .fst → Ω³ (Susp S² , north) .fst
f6' = mapΩ³refl λ { (inl x) → north ; (inr x) → south ; (push a b i) → merid (S¹×S¹→S² a b) i}

f7'' : Ω³ (Susp S² , north) .fst → Ω² ∥ S²∙ ∥₄∙ .fst
f7'' = mapΩ²refl f7' ∘ mapΩ²refl (cong ∣_∣ₕ)

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

brunerie' : ℤ
brunerie' = g10 (g9 (g8 (f7'' (f6' (f5 (f4 (f3 (λ i j k → surf i j k))))))))


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
