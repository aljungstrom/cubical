{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Hopf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function

open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Join
open import Cubical.HITs.Interval
  renaming ( zero to I0 ; one to I1 )

Border : (x : S¹) → (j : I) → Partial (j ∨ ~ j) (Σ Type₀ (λ T → T ≃ S¹))
Border x j (j = i0) = S¹ , (x ·_) , rotIsEquiv x
Border x j (j = i1) = S¹ , idEquiv S¹

-- Hopf fibration using SuspS¹
HopfSuspS¹ : SuspS¹ → Type₀
HopfSuspS¹ north = S¹
HopfSuspS¹ south = S¹
HopfSuspS¹ (merid x j) = Glue S¹ (Border x j)

-- Hopf fibration using S²
-- TODO : prove that it is equivalent to HopfSuspS¹
HopfS² : S² → Type₀
HopfS² base = S¹
HopfS² (surf i j) = Glue S¹ (λ { (i = i0) → _ , idEquiv S¹
                               ; (i = i1) → _ , idEquiv S¹
                               ; (j = i0) → _ , idEquiv S¹
                               ; (j = i1) → _ , _ , rotIsEquiv (loop i) } )

-- Hopf fibration using more direct definition of the rot equivalence
-- TODO : prove that it is equivalent to HopfSuspS¹
HopfS²' : S² → Type₀
HopfS²' base = S¹
HopfS²' (surf i j) = Glue S¹ (λ { (i = i0) → _ , rotLoopEquiv i0
                                ; (i = i1) → _ , rotLoopEquiv i0
                                ; (j = i0) → _ , rotLoopEquiv i0
                                ; (j = i1) → _ , rotLoopEquiv i } )

-- Total space of the fibration
TotalHopf : Type₀
TotalHopf = Σ SuspS¹ HopfSuspS¹

-- Forward direction
filler-1 : I → (j : I) → (y : S¹) → Glue S¹ (Border y j) → join S¹ S¹
filler-1 i j y x = hfill (λ t → λ { (j = i0) → inl (rotInv-1 x y t)
                                  ; (j = i1) → inr x })
                         (inS (push ((unglue (j ∨ ~ j) x) · invLooper y) (unglue (j ∨ ~ j) x) j)) i

TotalHopf→JoinS¹S¹ : TotalHopf → join S¹ S¹
TotalHopf→JoinS¹S¹ (north , x) = inl x
TotalHopf→JoinS¹S¹ (south , x) = inr x
TotalHopf→JoinS¹S¹ (merid y j , x) = filler-1 i1 j y x

-- Backward direction
JoinS¹S¹→TotalHopf : join S¹ S¹ → TotalHopf
JoinS¹S¹→TotalHopf (inl x) = (north , x)
JoinS¹S¹→TotalHopf (inr x) = (south , x)
JoinS¹S¹→TotalHopf (push y x j) =
  (merid (invLooper y · x) j
  , glue (λ { (j = i0) → y ; (j = i1) → x }) (rotInv-2 x y j))

-- Now for the homotopies, we will need to fill squares indexed by x y : S¹ with value in S¹
-- Some will be extremeley tough, but happen to be easy when x = y = base
-- therefore, we fill them for x = y = base and then use the connectedness of S¹ × S¹ and
-- the discreteness of ΩS¹ to get general fillers.

-- To proceed with that strategy, we first need a lemma :
-- the sections of the trivial fibration λ (_ : S¹) (_ : S¹) → Int are constant

-- this should be generalized to a constant fibration over a connected space with
-- discrete fiber
fibInt : S¹ → S¹ → Type₀
fibInt _ _ = Int

S¹→HSet : (A : Type₀) (p : isSet A) (F : S¹ → A) (x : S¹) → F base ≡ F x
S¹→HSet A p F base = refl {x = F base}
S¹→HSet A p F (loop i) = f' i
  where
  f : PathP (λ i → F base ≡ F (loop i)) refl (cong F loop)
  f i = λ j → F (loop (i ∧ j))
  L : cong F loop ≡ refl
  L = p (F base) (F base) (f i1) refl
  f' : PathP (λ i → F base ≡ F (loop i)) (refl {x = F base}) (refl {x = F base})
  f' = transport (λ i → PathP (λ j → F base ≡ F (loop j)) refl (L i)) f

constant-loop : (F : S¹ → S¹ → Int) → (x y : S¹) → F base base ≡ F x y
constant-loop F x y = L0 ∙ L1
  where
  p : isSet (S¹ → Int)
  p = isSetΠ (λ _ → isSetInt)
  L : F base ≡ F x
  L = S¹→HSet (S¹ → Int) p F x
  L0 : F base base ≡ F x base
  L0 i = L i base
  L1 : F x base ≡ F x y
  L1 = S¹→HSet Int isSetInt (F x) y

discretefib : (F : S¹ → S¹ → Type₀) → Type₀
discretefib F = (a : (x y : S¹) → F x y) →
        (b : (x y : S¹) → F x y) →
        (a base base ≡ b base base) →
        (x y : S¹) → a x y ≡ b x y

discretefib-fibInt : discretefib fibInt
discretefib-fibInt a b h x y i =
  hcomp (λ t → λ { (i = i0) → constant-loop a x y t
                 ; (i = i1) → constant-loop b x y t })
        (h i)

-- first homotopy

assocFiller-3-aux : I → I → I → I → S¹
assocFiller-3-aux x y j i =
  hfill (λ t → λ { (i = i0) → rotInv-1 (loop y) (loop (~ y) · loop x) t
                 ; (i = i1) → rotInv-3 (loop y) (loop x) t
                 ; (x = i0) (y = i0) → base
                 ; (x = i0) (y = i1) → base
                 ; (x = i1) (y = i0) → base
                 ; (x = i1) (y = i1) → base })
        (inS ((rotInv-2 (loop x) (loop y) i) · (invLooper (loop (~ y) · loop x)))) j

-- assocFiller-3-endpoint is used only in the type of the next function, to specify the
-- second endpoint.
-- However, I only need the first endpoint, but I cannot specify only one of them as is.
-- TODO : use cubical extension types when available to remove assocFiller-3-endpoint
assocFiller-3-endpoint : (x : S¹) → (y : S¹) → y ≡ y
assocFiller-3-endpoint base base i = base
assocFiller-3-endpoint (loop x) base i = assocFiller-3-aux x i0 i1 i
assocFiller-3-endpoint base (loop y) i = assocFiller-3-aux i0 y i1 i
assocFiller-3-endpoint (loop x) (loop y) i = assocFiller-3-aux x y i1 i

assocFiller-3 : (x : S¹) → (y : S¹) →
                PathP (λ j → rotInv-1 y (invLooper y · x) j ≡ rotInv-3 y x j)
                      (λ i → ((rotInv-2 x y i) · (invLooper (invLooper y · x))))
                      (assocFiller-3-endpoint x y)
assocFiller-3 base base j i = base
assocFiller-3 (loop x) base j i = assocFiller-3-aux x i0 j i
assocFiller-3 base (loop y) j i = assocFiller-3-aux i0 y j i
assocFiller-3 (loop x) (loop y) j i = assocFiller-3-aux x y j i

assoc-3 : (_ y : S¹) → basedΩS¹ y
assoc-3 x y i = assocFiller-3 x y i1 i

fibInt≡fibAssoc-3 : fibInt ≡ (λ _ y → basedΩS¹ y)
fibInt≡fibAssoc-3 i = λ x y → basedΩS¹≡Int y (~ i)

discretefib-fibAssoc-3 : discretefib (λ _ y → basedΩS¹ y)
discretefib-fibAssoc-3 =
  transp (λ i → discretefib (fibInt≡fibAssoc-3 i)) i0 discretefib-fibInt

assocConst-3 : (x y : S¹) → assoc-3 x y ≡ refl
assocConst-3 x y = discretefib-fibAssoc-3 assoc-3 (λ _ _ → refl) refl x y

assocSquare-3 : I → I → S¹ → S¹ → S¹
assocSquare-3 i j x y = hcomp (λ t → λ { (i = i0) → assocFiller-3 x y j i0
                                       ; (i = i1) → assocFiller-3 x y j i1
                                       ; (j = i0) → assocFiller-3 x y i0 i
                                       ; (j = i1) → assocConst-3 x y t i })
                            (assocFiller-3 x y j i)

filler-3 : I → I → S¹ → S¹ → join S¹ S¹
filler-3 i j y x =
  hcomp (λ t → λ { (i = i0) → filler-1 t j (invLooper y · x)
                                           (glue (λ { (j = i0) → y ; (j = i1) → x })
                                                 (rotInv-2 x y j))
                 ; (i = i1) → push (rotInv-3 y x t) x j
                 ; (j = i0) → inl (assocSquare-3 i t x y)
                 ; (j = i1) → inr x })
        (push ((rotInv-2 x y (i ∨ j)) · (invLooper (invLooper y · x))) (rotInv-2 x y (i ∨ j)) j)

JoinS¹S¹→TotalHopf→JoinS¹S¹ : ∀ x → TotalHopf→JoinS¹S¹ (JoinS¹S¹→TotalHopf x) ≡ x
JoinS¹S¹→TotalHopf→JoinS¹S¹ (inl x) i = inl x
JoinS¹S¹→TotalHopf→JoinS¹S¹ (inr x) i = inr x
JoinS¹S¹→TotalHopf→JoinS¹S¹ (push y x j) i = filler-3 i j y x

-- Second homotopy

-- This HIT is the total space of the Hopf fibration but the ends of SuspS¹ have not been
-- glued together yet — which makes it into a cylinder.
-- This allows to write compositions that do not properly match at the endpoints. However,
-- I suspect it is unnecessary. TODO : do without PseudoHopf

PseudoHopf : Type₀
PseudoHopf = (S¹ × Interval) × S¹

PseudoHopf-π1 : PseudoHopf → S¹
PseudoHopf-π1 ((y , _) , _) = y

PseudoHopf-π2 : PseudoHopf → S¹
PseudoHopf-π2 (_ , x) = x

assocFiller-4-aux : I → I → I → I → S¹
assocFiller-4-aux x y j i =
  hfill (λ t → λ { (i = i0) → ((invLooper (loop y · loop x · loop (~ y))) · (loop y · loop x))
                              · (rotInv-1 (loop x) (loop y) t)
                 ; (i = i1) → (rotInv-4 (loop y) (loop y · loop x) (~ t)) · loop x
                 ; (x = i0) (y = i0) → base
                 ; (x = i0) (y = i1) → base
                 ; (x = i1) (y = i0) → base
                 ; (x = i1) (y = i1) → base })
        (inS (rotInv-2 (loop y · loop x) (loop y · loop x · loop (~ y)) i)) j

-- See assocFiller-3-endpoint
-- TODO : use cubical extension types when available to remove assocFiller-4-endpoint
assocFiller-4-endpoint : (x y : S¹) → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x)
assocFiller-4-endpoint base base i = base
assocFiller-4-endpoint (loop x) base i = assocFiller-4-aux x i0 i1 i
assocFiller-4-endpoint base (loop y) i = assocFiller-4-aux i0 y i1 i
assocFiller-4-endpoint (loop x) (loop y) i = assocFiller-4-aux x y i1 i

assocFiller-4 : (x y : S¹) →
                PathP (λ j → ((invLooper (y · x · invLooper y)) · (y · x)) · (rotInv-1 x y j) ≡ (rotInv-4 y (y · x) (~ j)) · x)
                      (λ i → (rotInv-2 (y · x) (y · x · invLooper y) i))
                      (assocFiller-4-endpoint x y)
assocFiller-4 base base j i = base
assocFiller-4 (loop x) base j i = assocFiller-4-aux x i0 j i
assocFiller-4 base (loop y) j i = assocFiller-4-aux i0 y j i
assocFiller-4 (loop x) (loop y) j i = assocFiller-4-aux x y j i

assoc-4 : (x y : S¹) → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x)
assoc-4 x y i = assocFiller-4 x y i1 i

fibInt≡fibAssoc-4 : fibInt ≡ (λ x y → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x))
fibInt≡fibAssoc-4 i = λ x y → basedΩS¹≡Int (((invLooper (y · x · invLooper y)) · (y · x)) · x) (~ i)

discretefib-fibAssoc-4 : discretefib (λ x y → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x))
discretefib-fibAssoc-4 =
  transp (λ i → discretefib (fibInt≡fibAssoc-4 i)) i0 discretefib-fibInt

assocConst-4 : (x y : S¹) → assoc-4 x y ≡ refl
assocConst-4 x y = discretefib-fibAssoc-4 assoc-4 (λ _ _ → refl) refl x y

assocSquare-4 : I → I → S¹ → S¹ → S¹
assocSquare-4 i j x y =
  hcomp (λ t → λ { (i = i0) → assocFiller-4 x y j i0
                 ; (i = i1) → assocFiller-4 x y j i1
                 ; (j = i0) → assocFiller-4 x y i0 i
                 ; (j = i1) → assocConst-4 x y t i })
        (assocFiller-4 x y j i)

filler-4-0 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
filler-4-0 i j y x =
  let x' = unglue (j ∨ ~ j) x in
  hfill (λ t → λ { (j = i0) → ((invLooper (y · x · invLooper y) · (y · x) , I0)
                              , invLooper (y · x · invLooper y) · (y · x) · (rotInv-1 x y t))
                 ; (j = i1) → ((invLooper (x · invLooper y) · x , I1) , x) })
        (inS ((invLooper (x' · invLooper y) · x' , seg j) , rotInv-2 x' (x' · invLooper y) j)) i

filler-4-1 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
filler-4-1 i j y x =
  let x' = unglue (j ∨ ~ j) x in
  hfill (λ t → λ { (j = i0) → ((invLooper (y · x · invLooper y) · (y · x) , I0)
                              , (rotInv-4 y (y · x) (~ t)) · x)
                 ; (j = i1) → ((invLooper (x · invLooper y) · x , I1) , x) })
        (inS ((invLooper (x' · invLooper y) · x' , seg j) , unglue (j ∨ ~ j) x)) i

filler-4-2 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → TotalHopf
filler-4-2 i j y x =
  let x' = unglue (j ∨ ~ j) x in
  hcomp (λ t → λ { (i = i0) → JoinS¹S¹→TotalHopf (filler-1 t j y x)
                 ; (i = i1) → (merid (PseudoHopf-π1 (filler-4-0 t j y x)) j
                              , glue (λ { (j = i0) → rotInv-1 x y t ; (j = i1) → x })
                                     (PseudoHopf-π2 (filler-4-0 t j y x)))
                 ; (j = i0) → (north , rotInv-1 x y t)
                 ; (j = i1) → (south , x) })
        (merid (invLooper (x' · invLooper y) · x') j
        , glue (λ { (j = i0) → y · x · invLooper y ; (j = i1) → x }) (rotInv-2 x' (x' · invLooper y) j))

filler-4-3 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
filler-4-3 i j y x =
  let x' = unglue (j ∨ ~ j) x in
  hcomp (λ t → λ { (i = i0) → filler-4-0 t j y x
                 ; (i = i1) → filler-4-1 t j y x
                 ; (j = i0) → ((invLooper (y · x · invLooper y) · (y · x) , I0) , assocSquare-4 i t x y)
                 ; (j = i1) → ((invLooper (x · invLooper y) · x , I1) , x) })
        ((invLooper (x' · invLooper y) · x' , seg j) , rotInv-2 x' (x' · invLooper y) (i ∨ j))

filler-4-4 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
filler-4-4 i j y x =
  let x' = unglue (j ∨ ~ j) x in
  hcomp (λ t → λ { (i = i0) → filler-4-1 t j y x
                 ; (i = i1) → ((y , seg j) , unglue (j ∨ ~ j) x)
                 ; (j = i0) → ((rotInv-4 y (y · x) i , I0)
                              , (rotInv-4 y (y · x) (i ∨ ~ t)) · x)
                 ; (j = i1) → ((rotInv-4 y x i , I1) , x) })
        ((rotInv-4 y x' i , seg j) , x')

filler-4-5 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → TotalHopf
filler-4-5 i j y x =
  hcomp (λ t → λ { (i = i0) → filler-4-2 (~ t) j y x
                 ; (i = i1) → (merid (PseudoHopf-π1 (filler-4-4 t j y x)) j
                              , glue (λ { (j = i0) → x ; (j = i1) → x })
                                     (PseudoHopf-π2 (filler-4-4 t j y x)))
                 ; (j = i0) → (north , x)
                 ; (j = i1) → (south , x) })
        (merid (PseudoHopf-π1 (filler-4-3 i j y x)) j
        , glue (λ { (j = i0) → x ; (j = i1) → x }) (PseudoHopf-π2 (filler-4-3 i j y x)))

TotalHopf→JoinS¹S¹→TotalHopf : ∀ x → JoinS¹S¹→TotalHopf (TotalHopf→JoinS¹S¹ x) ≡ x
TotalHopf→JoinS¹S¹→TotalHopf (north , x) i = (north , x)
TotalHopf→JoinS¹S¹→TotalHopf (south , x) i = (south , x)
TotalHopf→JoinS¹S¹→TotalHopf (merid y j , x) i = filler-4-5 i j y x


JoinS¹S¹≡TotalHopf : join S¹ S¹ ≡ TotalHopf
JoinS¹S¹≡TotalHopf = isoToPath (iso JoinS¹S¹→TotalHopf
                                    TotalHopf→JoinS¹S¹
                                    TotalHopf→JoinS¹S¹→TotalHopf
                                    JoinS¹S¹→TotalHopf→JoinS¹S¹)

S³≡TotalHopf : S³ ≡ TotalHopf
S³≡TotalHopf = S³≡joinS¹S¹ ∙ JoinS¹S¹≡TotalHopf

open Iso
IsoS³TotalHopf : Iso (S₊ 3) TotalHopf
fun IsoS³TotalHopf x = JoinS¹S¹→TotalHopf (S³→joinS¹S¹ (inv IsoS³S3 x))
inv IsoS³TotalHopf x = fun IsoS³S3 (joinS¹S¹→S³ (TotalHopf→JoinS¹S¹ x))
rightInv IsoS³TotalHopf x =
     cong (JoinS¹S¹→TotalHopf ∘ S³→joinS¹S¹)
          (leftInv IsoS³S3 (joinS¹S¹→S³ (TotalHopf→JoinS¹S¹ x)))
  ∙∙ cong JoinS¹S¹→TotalHopf
          (joinS¹S¹→S³→joinS¹S¹ (TotalHopf→JoinS¹S¹ x))
  ∙∙ TotalHopf→JoinS¹S¹→TotalHopf x
leftInv IsoS³TotalHopf x =
     cong (fun IsoS³S3 ∘ joinS¹S¹→S³)
          (JoinS¹S¹→TotalHopf→JoinS¹S¹ (S³→joinS¹S¹ (inv IsoS³S3 x)))
  ∙∙ cong (fun IsoS³S3) (S³→joinS¹S¹→S³ (inv IsoS³S3 x))
  ∙∙ Iso.rightInv IsoS³S3 x



--


open import Cubical.Foundations.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.HomotopyGroup
open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Join
open import Cubical.HITs.Sn
open import Cubical.HITs.SetTruncation as SetTrunc
open import Cubical.HITs.GroupoidTruncation as GroupoidTrunc
open import Cubical.HITs.2GroupoidTruncation as 2GroupoidTrunc
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation renaming (rec to REC)

-- This code is adapted from examples/brunerie3.ctt on the pi4s3_nobug branch of cubicaltt

Bool∙ S¹∙ S²∙ S³∙ : Pointed₀
Bool∙ = (Bool , true)
S¹∙ = (S¹ , base)
S²∙ = (S² , base)
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

encodeTruncS¹ : Ω ∥ S¹∙ ∥₃∙ .fst → ∥ Int ∥₂
encodeTruncS¹ p = transp (λ i → codeTruncS¹ (p i) .fst) i0 ∣ pos zero ∣₂


-- THE BIG GAME

test : ∀ {ℓ }
test = {!!}

f3 : Ω³ S³∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
f3 = mapΩ³refl S³→joinS¹S¹

f4 : Ω³ (join∙ S¹∙ S¹) .fst → Ω³ S²∙ .fst
f4 = mapΩ³refl alpha

f5 : Ω³ S²∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
f5 = h

f6 : Ω³ (join∙ S¹∙ S¹) .fst → Ω³ S³∙ .fst
f6 = mapΩ³refl joinS¹S¹→S³

f7pre : Ω³ S³∙ .fst → Ω³ (hLevelTrunc 5 (S₊ 3) , ∣ north ∣) .fst
f7pre = mapΩ³refl λ x → ∣ Iso.fun (congSuspIso S²IsoSuspS¹) (S³→SuspS² x) ∣

f7mid : Ω³ (hLevelTrunc 5 (S₊ 3) , ∣ north ∣) .fst → Ω² (hLevelTrunc 4 (S₊ 2) , ∣ north ∣) .fst -- Ω³ S³∙ .fst → Ω² ∥ S²∙ ∥₄∙ .fst
f7mid = mapΩ²refl λ p → Iso.inv (stabSpheres-n≥2 0) (Iso.fun (PathIdTruncIso 4) p)

f7post : Ω² (hLevelTrunc 4 (S₊ 2) , ∣ north ∣) .fst → Ω² ∥ S²∙ ∥₄∙ .fst
f7post = mapΩ²refl (REC squash₄ λ x → ∣ SuspS¹→S² x ∣₄)

f7 : Ω³ S³∙ .fst → Ω² ∥ S²∙ ∥₄∙ .fst
f7 = f7post ∘ f7mid ∘ f7pre

g8 : Ω² ∥ S²∙ ∥₄∙ .fst → Ω ∥ S¹∙ ∥₃∙ .fst
g8 = mapΩrefl encodeTruncS²

g9 : Ω ∥ S¹∙ ∥₃∙ .fst → ∥ Int ∥₂
g9 = encodeTruncS¹

g10 : ∥ Int ∥₂ → Int
g10 = SetTrunc.rec isSetInt (idfun Int)

-- don't run me
brunerie : Int
brunerie = g10 (g9 (g8 (f7 (f6 (f5 (f4 (f3 (λ i j k → surf i j k))))))))
