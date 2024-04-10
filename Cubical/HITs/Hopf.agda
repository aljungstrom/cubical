{-# OPTIONS --safe #-}
module Cubical.HITs.Hopf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int hiding (_·_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function

open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Join hiding (joinS¹S¹→S³)
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
fibℤ : S¹ → S¹ → Type₀
fibℤ _ _ = ℤ

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

constant-loop : (F : S¹ → S¹ → ℤ) → (x y : S¹) → F base base ≡ F x y
constant-loop F x y = L0 ∙ L1
  where
  p : isSet (S¹ → ℤ)
  p = isSetΠ (λ _ → isSetℤ)
  L : F base ≡ F x
  L = S¹→HSet (S¹ → ℤ) p F x
  L0 : F base base ≡ F x base
  L0 i = L i base
  L1 : F x base ≡ F x y
  L1 = S¹→HSet ℤ isSetℤ (F x) y

discretefib : (F : S¹ → S¹ → Type₀) → Type₀
discretefib F = (a : (x y : S¹) → F x y) →
        (b : (x y : S¹) → F x y) →
        (a base base ≡ b base base) →
        (x y : S¹) → a x y ≡ b x y

discretefib-fibℤ : discretefib fibℤ
discretefib-fibℤ a b h x y i =
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

fibℤ≡fibAssoc-3 : fibℤ ≡ (λ _ y → basedΩS¹ y)
fibℤ≡fibAssoc-3 i = λ x y → basedΩS¹≡ℤ y (~ i)

discretefib-fibAssoc-3 : discretefib (λ _ y → basedΩS¹ y)
discretefib-fibAssoc-3 =
  transp (λ i → discretefib (fibℤ≡fibAssoc-3 i)) i0 discretefib-fibℤ

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

fibℤ≡fibAssoc-4 : fibℤ ≡ (λ x y → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x))
fibℤ≡fibAssoc-4 i = λ x y → basedΩS¹≡ℤ (((invLooper (y · x · invLooper y)) · (y · x)) · x) (~ i)

discretefib-fibAssoc-4 : discretefib (λ x y → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x))
discretefib-fibAssoc-4 =
  transp (λ i → discretefib (fibℤ≡fibAssoc-4 i)) i0 discretefib-fibℤ

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

-- open Iso
-- IsoS³TotalHopf : Iso (S₊ 3) TotalHopf
-- fun IsoS³TotalHopf x = JoinS¹S¹→TotalHopf (S³→joinS¹S¹ (inv IsoS³S3 x))
-- inv IsoS³TotalHopf x = fun IsoS³S3 (joinS¹S¹→S³ (TotalHopf→JoinS¹S¹ x))
-- rightInv IsoS³TotalHopf x =
--      cong (JoinS¹S¹→TotalHopf ∘ S³→joinS¹S¹)
--           (leftInv IsoS³S3 (joinS¹S¹→S³ (TotalHopf→JoinS¹S¹ x)))
--   ∙∙ cong JoinS¹S¹→TotalHopf
--           (joinS¹S¹→S³→joinS¹S¹ (TotalHopf→JoinS¹S¹ x))
--   ∙∙ TotalHopf→JoinS¹S¹→TotalHopf x
-- leftInv IsoS³TotalHopf x =
--      cong (fun IsoS³S3 ∘ joinS¹S¹→S³)
--           (JoinS¹S¹→TotalHopf→JoinS¹S¹ (S³→joinS¹S¹ (inv IsoS³S3 x)))
--   ∙∙ cong (fun IsoS³S3) (S³→joinS¹S¹→S³ (inv IsoS³S3 x))
--   ∙∙ Iso.rightInv IsoS³S3 x




-- variable
--   ℓ : Level
-- susp* : ∀ {ℓ}{A : Type ℓ} (invol : A → A) → Susp A → Susp A
-- susp* invol north = north
-- susp* invol south = south
-- susp* invol (merid a i) = merid (invol a) i

-- susp- : ∀ {ℓ}{A : Type ℓ} (invol : A → A) → Susp A → Susp A
-- susp- invol north = south
-- susp- invol south = north
-- susp- invol (merid a i) = merid (invol a) (~ i)

-- module _ (A : Type ℓ) (invol : A → A) (_·A_ : Susp A → Susp A → Susp A) where
--   A- = susp- invol
--   A* = susp* invol
 
--   has-distr = (x y : Susp A) → x ·A A- y ≡ A- (x ·A y)
--   has*Unit = (x : Susp A) → x ·A A* x ≡ north
--   has*distr = (x y : Susp A) → A* (x ·A y) ≡ (A* y ·A A* x)

-- record isHSpace {ℓ : Level} (carrier : Type ℓ) (0h : carrier) (μ : carrier → carrier → carrier) : Type ℓ where
--   field
--     μₗ : (x : carrier) → μ 0h x ≡ x
--     μᵣ : (x : carrier) → μ x 0h ≡ x

-- isImaginaroid : Type ℓ → Type ℓ
-- isImaginaroid A =
--   Σ[ invol ∈ (A → A) ]
--     Σ[ _·A_ ∈ (Susp A → Susp A → Susp A) ]
--         (has-distr A invol _·A_
--        × has*Unit A invol _·A_
--        × has*distr A invol _·A_
--        × (isHSpace (Susp A) north _·A_))

-- isAssocImaginaroid : Type ℓ → Type ℓ
-- isAssocImaginaroid A =
--   Σ[ e ∈ isImaginaroid A ] ((x y z : Susp A) → fst (snd e) x (fst (snd e) y z) ≡ fst (snd e) (fst (snd e) x y) z)
-- open import Cubical.HITs.Join

-- join→prop : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
--           → {P : join (Susp A) (Susp B) → Type ℓ''}
--           → A
--           → P (inl north)
--           → (((x : _) → isProp (P x)))
--           → (x : _) → P x
-- join→prop  {P = P} a b prop = main
--   where
--   inl-c : (x : _) → P (inl x)
--   inl-c = suspToPropElim a (λ _ → prop _) b

--   main : (x : join (Susp _) (Susp _)) → P x
--   main (inl x) = inl-c x
--   main (inr x) = subst P (push north x) b
--   main (push x y i) =
--     isProp→PathP {B = λ i → P (push x y i)} (λ _ → prop _)
--                   (inl-c x) (subst P (push north y) b) i

-- joinFun : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
--            (f : A → B) (g : C → D)
--          → join A C → join B D
-- joinFun f g (inl x) = inl (f x)
-- joinFun f g (inr x) = inr (g x)
-- joinFun f g (push a b i) = push (f a) (g b) i

-- module joinHSpace {ℓ : Level} (A : Type ℓ) (e' : isAssocImaginaroid A) (invol-proof : fst (fst e') ∘ fst (fst e') ≡ idfun _) where
--   e = fst e'
--   invol = fst e
--   _·A_ = fst (snd e)
--   -distr = fst (snd (snd e))
--   *unit = fst (snd (snd (snd e)))
--   *distr = fst (snd (snd (snd (snd e))))
--   lUnitA = isHSpace.μₗ (snd (snd (snd (snd (snd e)))))
--   rUnitA = isHSpace.μᵣ (snd (snd (snd (snd (snd e)))))
  
--   assocA = snd e'

--   _* = susp* invol
--   -A = susp- invol

--   SA*SA = join (Susp A) (Susp A)
  
--   open import Cubical.Data.Sum
--   diamondType : {A B : Type ℓ}
--                 → (a a' : A) (b b' : B) → Type _
--   diamondType {A = A} {B = B} a a' b b' =
--     Square {A = join A B} (push a b) (sym (push a' b'))
--                           (push a b') (sym (push a' b))

--   diamondSol' : {A : Type ℓ}
--                 → (a a' : A) (b b' : A) → (a' ≡ b)
--                 → diamondType a a' b b'
--   diamondSol' a a' b b' =
--     J (λ b _ → diamondType a a' b b')
--       {!diamondType a a' a' b'!}

--   diamondSol : {A B : Type ℓ}
--                 → (a a' : A) (b b' : B) → (a ≡ a') ⊎ (b ≡ b')
--                 → diamondType a a' b b'
--   diamondSol a a' b b' (inl x) =
--     J (λ a' _ → Square (push a b) (sym (push a' b')) (push a b')
--       (sym (push a' b)))
--         (λ i j → hcomp (λ k → λ { (i = i0) → push a b j
--                                   ; (i = i1) → push a b' (~ j ∧ k)
--                                   ; (j = i0) → push a b' (i ∧ k)
--                                   ; (j = i1) → push a b (~ i)})
--                         (push a b (~ i ∧ j))) x
--   diamondSol a a' b b' (inr x) =
--     J (λ b' _ → Square (push a b) (sym (push a' b')) (push a b')
--       (sym (push a' b)))
--       (λ i j → hcomp (λ k → λ { (i = i0) → push a b j
--                                 ; (i = i1) → push a' b (~ j ∨ ~ k)
--                                 ; (j = i0) → push a b i
--                                 ; (j = i1) → push a' b (~ i ∨ ~ k)})
--                       (push a b (i ∨ j))) x


-- --   mysquare : {A₁ A₂ B₁ B₂ : Type ℓ}
-- --           → (f : A₁ → A₂) (g : B₁ → B₂)
-- --           → (a a' : A₁) (b b' : B₁)
-- --           → diamondType a a' b b'
-- --           → diamondType (f a) (f a') (g b) (g b')
-- --   mysquare f g a a' b b' sq i j = joinFun f g (sq i j)

-- --   f : (a b c d : Susp A) → Susp A → Susp A
-- --   f a b c d x = -A a ·A (c ·A x)

-- --   g : (a b c d : Susp A) → Susp A → Susp A
-- --   g a b c d x = c ·A (x ·A b)

-- --   f*g : (a b c d : Susp A) → SA*SA → SA*SA
-- --   f*g a b c d (inl x) = inl (f a b c d x)
-- --   f*g a b c d (inr x) = inr (g a b c d x)
-- --   f*g a b c d (push a₁ b₁ i) = push (f a b c d a₁) (g a b c d b₁) i

-- --   *² : (x : Susp A) → ((x *) *) ≡ x
-- --   *² north = refl
-- --   *² south = refl
-- --   *² (merid a i) j = merid (invol-proof j a) i

-- --   -² : (x : Susp A) → -A (-A x) ≡ x
-- --   -² north = refl
-- --   -² south = refl
-- --   -² (merid a i) j = merid (invol-proof j a) i

-- --   -* : (x : Susp A) → ((-A x) *) ≡ -A (x *)
-- --   -* north = refl
-- --   -* south = refl
-- --   -* (merid a i) = refl

-- --   lem123 : (x y : Susp A) → (-A x) ·A y ≡ -A (x ·A y)
-- --   lem123 x y =
-- --        sym (*² (-A x ·A y))
-- --     ∙∙ cong _* (*distr (-A x) y ∙∙ cong ((y *) ·A_) (-* x) ∙∙ -distr (y *) (x *))
-- --     ∙∙ -* ((y *) ·A (x *))
-- --      ∙ cong -A
-- --           ((λ i → ((y *) ·A (x *)) *)
-- --         ∙∙ *distr (y *) (x *)
-- --         ∙∙ cong₂ _·A_ (*² x) (*² y))


-- --   unit*l : (x : Susp A) → (x *) ·A x ≡ north 
-- --   unit*l x =
-- --        cong (_·A x) (sym (-² (x *)) ∙ cong -A (sym (-* x)))
-- --     ∙∙ lem123 (-A x *) x
-- --     ∙∙ cong -A (cong ((-A x *) ·A_) (sym (*² x))
-- --              ∙∙ sym (*distr (x *) (-A x))
-- --              ∙∙ cong (_*) (-distr (x *) x)
-- --              ∙ -* ((x *) ·A x)) -- cong (_*) (λ i → (x *) ·A x)
-- --     ∙∙ -² (((x *) ·A x) *)
-- --     ∙∙ *distr (x *) x
-- --      ∙ *unit (x *)

-- --   f-1 : (a b c d : Susp A) → f a b c d south ≡ (a ·A c)
-- --   f-1 a b c d =
-- --        cong (-A a ·A_) (-distr c north ∙ cong -A (rUnitA c))
-- --     ∙∙ -distr (-A a) c
-- --     ∙∙ cong -A (lem123 a c)
-- --      ∙ -² (a ·A c)

-- --   f-big : (a b c d : _) → f a b c d ((c *) ·A ((a *) ·A (d ·A (b *)))) ≡ -A (d ·A (b *))
-- --   f-big a b c d =
-- --        cong (-A a ·A_) (assocA c (c *) (((a *) ·A (d ·A (b *))))
-- --                      ∙∙ cong (_·A ((a *) ·A (d ·A (b *)))) (*unit c)
-- --                      ∙∙ lUnitA ((a *) ·A (d ·A (b *))))
-- --     ∙∙ lem123 a ((a *) ·A (d ·A (b *)))
-- --     ∙∙ cong -A (assocA a (a *) (d ·A (b *))
-- --              ∙∙ cong (_·A (d ·A (b *))) (*unit a)
-- --              ∙∙ lUnitA (d ·A (b *)))

-- --   g-1 : (a b c d : _) → g a b c d north ≡ (c ·A b)
-- --   g-1 a b c d i = c ·A (lUnitA b i)

-- --   g-big : (a b c d : _) → g a b c d ((c *) ·A ((a *) ·A (d ·A (b *)))) ≡ ((a *) ·A d)
-- --   g-big a b c d =
-- --        assocA c ((c *) ·A ((a *) ·A (d ·A (b *)))) b
-- --     ∙∙ cong (_·A b) (assocA c (c *) ((a *) ·A (d ·A (b *)))
-- --                     ∙∙ cong (_·A ((a *) ·A (d ·A (b *)))) (*unit c)
-- --                     ∙∙ lUnitA ((a *) ·A (d ·A (b *))))
-- --     ∙∙ sym (assocA (a *) (d ·A (b *)) b)
-- --      ∙ cong ((a *) ·A_) (sym (assocA d (b *) b)
-- --           ∙∙ cong (d ·A_) (unit*l b)
-- --           ∙∙ rUnitA d)

-- --   n-fill : (x y : Susp A) → I → I → I → join (Susp A) (Susp A)
-- --   n-fill x y i j k =
-- --     hfill (λ k → λ { (i = i0) → push y x j
-- --                     ; (i = i1) → push x x (~ j ∨ ~ k)
-- --                     ; (j = i0) → push y x i
-- --                     ; (j = i1) → push x x (~ i ∨ ~ k)})
-- --           (inS (push y x (i ∨ j))) k

-- --   s-fill : (x y : Susp A) → I → I → I → join (Susp A) (Susp A)
-- --   s-fill x y i j k = hfill (λ k → λ { (i = i0) → push y y (j ∧ k)
-- --                                   ; (i = i1) → push y x (~ j)
-- --                                   ; (j = i0) → push y x i
-- --                                   ; (j = i1) → push y y (~ i ∧ k)})
-- --                         (inS (push y x (i ∧ ~ j))) k

-- --   coolDiamond : (x : Susp A) → diamondType {A = Susp A} {B = Susp A} south x x north
-- --   coolDiamond north i j = n-fill north south i j i1
-- --   coolDiamond south i j = s-fill north south i j i1
-- --   coolDiamond (merid a r) i j = lel south (merid a) r i j
-- --     where
-- --     lelTyp : (y : Susp A) (p : north ≡ y) → Type _
-- --     lelTyp y p =
-- --       Cube (λ i j → n-fill north y i j i1)
-- --            (λ i j → s-fill north y i j i1)
-- --            (λ r j → push y (p r) j)
-- --            (λ r j → push (p r) north (~ j))
-- --            (λ r → push y north)
-- --            λ r i → push (p r) (p r) (~ i)

-- --     giveUpType : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → Type _
-- --     giveUpType {x = x} p =
-- --       Cube (λ j r → p (((~ j ∧ ~ r)) ∧ j))
-- --                     (λ j r → p (~ j))
-- --                     (λ i r → p i)
-- --                     (λ i r → x)
-- --                     (λ i j → p (~ j ∧ i ∨ j))
-- --                     λ i j → p (i ∧ ~ j)

-- --     iGiveUp : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y)
-- --             → giveUpType p
-- --     iGiveUp = J (λ y p → giveUpType p) refl

-- --     lel-refl : lelTyp north refl
-- --     lel-refl r i j =
-- --       hcomp (λ k → λ { (i = i0) → push north north j
-- --                       ; (i = i1) → push north north ((~ j) ∨ (~ k ∧ ~ r))
-- --                       ; (j = i0) → push north north i
-- --                       ; (j = i1) → push north north (~ i ∨ (~ k ∧ ~ r))
-- --                       ; (r = i0) → n-fill north north i j k
-- --                       ; (r = i1) → s-fill north north i j i1})
-- --             (hcomp (λ k → λ { (i = i0) → push north north (((~ j ∧ ~ r) ∨ k) ∧ j)
-- --                       ; (i = i1) → push north north ((~ j ∨ (~ r ∧ k)))
-- --                       ; (j = i0) → push north north i
-- --                       ; (j = i1) → push north north ((~ i ∨ ~ r) ∧ k)
-- --                       ; (r = i0) → push north north ((~ j ∨ k) ∧ (i ∨ j))
-- --                       ; (r = i1) → s-fill north north i j k})
-- --                    (iGiveUp (push north north) i j r))

-- --     lel : (y : Susp A) (p : north ≡ y) → lelTyp y p
-- --     lel y = J (λ y p → lelTyp y p) lel-refl

-- --   massive : (a b c d : Susp A) → Susp A
-- --   massive a b c d = (c *) ·A ((a *) ·A (d ·A (b *)))

-- --   massivelem : (a b : Susp A) → massive a b a b ≡ (a ·A a) * 
-- --   massivelem a b =
-- --        cong ((a *) ·A_) (cong ((a *) ·A_) (*unit b) ∙ rUnitA (a *))
-- --      ∙ sym (*distr a a)

-- --   haha : (a b : Susp A) → mysquare (f a b a b) (g a b a b)
-- --               south (massive a b a b) (massive a b a b) north (coolDiamond (massive a b a b))
-- --               ≡ {!!}
-- --   haha = {!!}

-- --   ·joinSquare : (a b c d : Susp A) → I → I → I → SA*SA
-- --   ·joinSquare a b c d i j k =
-- --     hfill (λ k → λ { (i = i0) → push (f-1 a b c d k) (g-big a b c d k) j
-- --                       ; (i = i1) → push (f-big a b c d k) (g-1 a b c d k) (~ j)
-- --                       ; (j = i0) → push (f-1 a b c d k) (g-1 a b c d k) i
-- --                       ; (j = i1) → push (f-big a b c d k) (g-big a b c d k) (~ i)})
-- --             (inS (mysquare (f a b c d) (g a b c d)
-- --               south massive' massive' north (coolDiamond massive') i j))
-- --             k
-- --     where
-- --     massive' = massive a b c d

-- --   _·join_ : SA*SA → SA*SA → SA*SA
-- --   inl a ·join inl c = inl (a ·A c)
-- --   inl a ·join inr d = inr ((a *) ·A d)
-- --   inl a ·join push c d i = push (a ·A c) ((a *) ·A d) i
-- --   inr b ·join inl c = inr (c ·A b)
-- --   inr b ·join inr d = inl (-A (d ·A (b *)))
-- --   inr b ·join push c d i = push (-A (d ·A (b *))) (c ·A b) (~ i)
-- --   push a b i ·join inl x = push (a ·A x) (x ·A b) i
-- --   push a b i ·join inr x = push (-A (x ·A (b *))) ((a *) ·A x) (~ i)
-- --   push a b i ·join push c d j = ·joinSquare a b c d i j i1

-- --   1J : SA*SA
-- --   1J = inl north

-- --   ·j-lUnit : (x : SA*SA) → (1J ·join x) ≡ x
-- --   ·j-lUnit (inl x) = cong inl (lUnitA x)
-- --   ·j-lUnit (inr x) = cong inr (lUnitA x)
-- --   ·j-lUnit (push a b i) j = push (lUnitA a j) (lUnitA b j) i

-- --   ·j-rUnit : (x : SA*SA) → (x ·join 1J) ≡ x
-- --   ·j-rUnit (inl x) = cong inl (rUnitA x)
-- --   ·j-rUnit (inr x) = cong inr (lUnitA x)
-- --   ·j-rUnit (push a b i) j = push (rUnitA a j) (lUnitA b j) i

-- --   malem : ∀ {ℓ} {A : Type ℓ} {x y z w : A} (s : y ≡ z) (q : x ≡ w) (r : w ≡ z) (p : x ≡ y)
-- --         → (e : PathP (λ i → q i ≡ s i) p r) → (λ i → e i i) ≡ q ∙∙ refl ∙∙ r
-- --   malem {x = x} {y = y} {z = z} {w = w} s q r p e k i =
-- --     hcomp (λ l → λ {(i = i0) → q (~ l)
-- --                    ; (i = i1) → r l
-- --                    ; (k = i0) → e (i ∨ ~ l) (i ∧ l)})
-- --           w

-- --   malem8 : {!∀ {ℓ} {A : Type ℓ} {x y z w : A} (s : y ≡ z) (q : x ≡ w) (r : w ≡ z) (p : x ≡ y)
-- --         → (e : PathP (λ i → q i ≡ s i) p r) → (λ i → e i i) ≡ (p ∙∙ refl ∙∙ s)!}
-- --   malem8 = {!!}

-- --   malem2 : ∀ {ℓ} {A : Type ℓ} {x y z w : A} (s : y ≡ z) (q : x ≡ w) (r : w ≡ z) (p : x ≡ y)
-- --         → (e : PathP (λ i → q i ≡ s i) p r) → (λ i → e i i) ≡ (p ∙∙ refl ∙∙ s)
-- --   malem2 s q r p e k i =
-- --     hcomp (λ l → λ {(i = i0) → p (~ l)
-- --                    ; (i = i1) → s l
-- --                    ; (k = i0) → e (i ∧ l) (i ∨ ~ l)})
-- --           (p i1)

-- --   idLem : (a₀ : A) (x : SA*SA) → x ·join x ≡ inl north
-- --   idLem a₀ (inl a) = push (a ·A a) north ∙ sym (push north north) 
-- --   idLem a₀ (inr a) = push (-A (a ·A (a *))) north ∙ sym (push north north)
-- --   idLem a₀ (push a b i) j =
-- --     hcomp (λ k → λ {(i = i0) → (push (a ·A a) north ∙ sym (push north north)) j
-- --                    ; (i = i1) → (push (-A (b ·A (b *))) north ∙ sym (push north north)) j
-- --                    ; (j = i0) → wacka (~ k) i
-- --                    ; (j = i1) → inl north})
-- --           (lam j i)
-- --     where
-- --     gz : PathP (λ j → (push (a ·A a) (a ·A b) j) ≡ push (-A (b ·A (b *))) ((a *) ·A b) (~ j))
-- --                (λ i → push (a ·A a) ((a *) ·A b) i)
-- --                λ i → push (-A (b ·A (b *))) (a ·A b) (~ i)
-- --     gz i j = push a b i ·join push a b j

-- --     pushDistr : {!!}
-- --     pushDistr = {!!}


-- --     lemm : north ≡ -A (b ·A (b *))
-- --     lemm = {!!}


-- --     wacka : cong₂ _·join_ (push a b) (push a b) ≡ (push (a ·A a) (a ·A b) ∙∙ refl ∙∙ sym (push (-A (b ·A (b *))) (a ·A b)))
-- --     wacka = malem _ _ _ _ gz

-- --     wacka2 : (push (a ·A a) (a ·A b) ∙∙ refl ∙∙ sym (push (-A (b ·A (b *))) (a ·A b)))
-- --             ≡ push (a ·A a) ((a *) ·A b) ∙∙ refl ∙∙ sym (push (-A (b ·A (b *))) ((a *) ·A b))
-- --     wacka2 = sym wacka ∙ malem2 _ _ _ _ gz

-- --     FF : Susp A → Susp A
-- --     FF a = {!!}

-- --     GG : Susp A → Susp A
-- --     GG a = {!diamondType a (a *) b a!}

-- --     di2 : diamondType (a ·A a) north north ((a *) ·A b)
-- --     di2 = {!mysquare FF GG a (a *) a b!}

-- --     di : diamondType (a ·A a) north north (a ·A b)
-- --     di = {!mysquare FF GG a (a *) (a *) b !}

-- --     M' : Square (push (a ·A a) (a ·A b)) (sym (push north north)) ((push (a ·A a) north)) (sym (push north (a ·A b)))
-- --     M' i j = di j i

-- --     M : push (a ·A a) (a ·A b)
-- --       ∙ sym (push north (a ·A b))
-- --       ∙ push north north
-- --       ∙ sym (push (a ·A a) north)
-- --       ≡ refl 
-- --     M = {!refl {x = (a · a)!}

-- --     lam : PathP (λ j → (push (a ·A a) north ∙ sym (push north north)) j ≡ (push (-A (b ·A (b *))) north ∙ sym (push north north)) j)
-- --                         (push (a ·A a) (a ·A b) ∙∙ refl ∙∙ sym (push (-A (b ·A (b *))) (a ·A b)))
-- --                         refl
-- --     lam = compPathR→PathP∙∙
-- --       (transport (λ w → (push (a ·A a) (a ·A b) ∙∙ refl ∙∙
-- --        sym (push (lemm w) (a ·A b)))
-- --       ≡
-- --       ((λ i₁ → (push (a ·A a) north ∙ sym (push north north)) i₁) ∙∙ refl
-- --        ∙∙
-- --        sym ((push (lemm w) north ∙ sym (push north north)))))
-- --        {!!})

-- --   HSpace : Σ[ n ∈ SA*SA ] Σ[ _·*_ ∈ (SA*SA → SA*SA → SA*SA) ]
-- --            (isHSpace SA*SA n _·*_)
-- --   fst HSpace = 1J
-- --   fst (snd HSpace) = _·join_
-- --   isHSpace.μₗ (snd (snd HSpace)) = ·j-lUnit
-- --   isHSpace.μᵣ (snd (snd HSpace)) = ·j-rUnit

-- -- open import Cubical.Data.Bool
-- -- open import Cubical.Algebra.Group.Instances.Bool renaming (Bool to BoolGroup)




-- -- joinIso : ∀ {ℓ ℓ' ℓ'' ℓ'''} → {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
-- --         → Iso A B → Iso C D → Iso (join A C) (join B D)
-- -- fun (joinIso isAB isCD) = joinFun (fun isAB) (fun isCD)
-- -- inv (joinIso isAB isCD) = joinFun (inv isAB) (inv isCD)
-- -- rightInv (joinIso isAB isCD) (inl x) = cong inl (rightInv isAB x)
-- -- rightInv (joinIso isAB isCD) (inr x) = cong inr (rightInv isCD x)
-- -- rightInv (joinIso isAB isCD) (push a b i) j = push (rightInv isAB a j) (rightInv isCD b j) i
-- -- leftInv (joinIso isAB isCD) (inl x) = cong inl (leftInv isAB x)
-- -- leftInv (joinIso isAB isCD) (inr x) = cong inr (leftInv isCD x)
-- -- leftInv (joinIso isAB isCD) (push a b i) j = push (leftInv isAB a j) (leftInv isCD b j) i

-- -- IsoJoinSuspBool-S³ : Iso (join (Susp Bool) (Susp Bool)) (S₊ 3)
-- -- IsoJoinSuspBool-S³ =
-- --   compIso
-- --     (compIso
-- --       (joinIso (invIso S¹IsoSuspBool) (invIso S¹IsoSuspBool))
-- --       ((iso JoinS¹S¹→TotalHopf
-- --                                     TotalHopf→JoinS¹S¹
-- --                                     TotalHopf→JoinS¹S¹→TotalHopf
-- --                                     JoinS¹S¹→TotalHopf→JoinS¹S¹)))
-- --     (invIso IsoS³TotalHopf)

-- -- S³' = join (Susp Bool) (Susp Bool)

-- -- open import Cubical.Data.Nat
-- -- ss : {ℓ : Level} {A : S³' → S³' → Type ℓ} →
-- --       ((x : S³') (y : S³') →
-- --        isOfHLevel 6 (A x y)) →
-- --       (f : (x : S³') → A (inl north) x)
-- --       (g : (x : S³') → A x (inl north)) →
-- --       g (inl north) ≡ f (inl north) →
-- --       (x : S³') (y : S³') → A x y
-- -- ss {ℓ = ℓ} {A = A} =
-- --   transport
-- --     (λ i → (A : l i → l i → Type ℓ) → ((x y : l i) →
-- --        isOfHLevel 6 (A x y)) →
-- --       (f : (x : l i) → A (transp (λ j → l (i ∧ j)) (~ i) north) x)
-- --       (g : (x : l i) → A x (transp (λ j → l (i ∧ j)) (~ i) north)) →
-- --       g (transp (λ j → l (i ∧ j)) (~ i) north) ≡ f (transp (λ j → l (i ∧ j)) (~ i) north) →
-- --       (x y : l i) → A x y)
-- --     (λ A → wedgeconFun 2 2) A
-- --   where
-- --   l = sym (isoToPath IsoJoinSuspBool-S³)

-- -- open import Cubical.Foundations.GroupoidLaws
-- -- fillSquare : ∀ {ℓ} {A : Type ℓ} {x : A} → (p : x ≡ x) → Square p p p p
-- -- fillSquare p = compPathR→PathP (rUnit p ∙ cong (p ∙_) (sym (rCancel p)))

-- -- open import Cubical.HITs.S1 renaming (_·_ to _*_)
-- -- _+SB_ : Susp Bool → Susp Bool → Susp Bool
-- -- x +SB y = S¹→SuspBool ((SuspBool→S¹ x) * SuspBool→S¹ y)

-- -- isGroupoidSuspBool : isGroupoid (Susp Bool)
-- -- isGroupoidSuspBool = isOfHLevelRetractFromIso 3 (invIso S¹IsoSuspBool) isGroupoidS¹

-- -- grejt : Susp Bool → S¹
-- -- grejt north = base
-- -- grejt south = base
-- -- grejt (merid false i) = loop i
-- -- grejt (merid true i) = loop (~ i)

-- -- SuspBoolWedge : ∀ {ℓ} {A : Susp Bool → Susp Bool → Type ℓ}
-- --              → ((x y : _) → isSet (A x y))
-- --              → (f : (x : _) → A x north)
-- --              → (g : (x : _) → A north x)
-- --              → f north ≡ g north
-- --              → (x y : _) → A x y
-- -- SuspBoolWedge {A = A} hlev g f p north y = f y
-- -- SuspBoolWedge {A = A} hlev g f p south y =
-- --   subst (λ x → A x y) (merid true) (f y)
-- -- SuspBoolWedge {A = A} hlev g f p (merid a i) y = help a y i
-- --   where
-- --   help-n : (a : Bool)
-- --     → PathP (λ i → A (merid a i) north) (f north) (subst (λ x → A x north) (merid true) (f north)) 
-- --   help-n a i =
-- --     hcomp (λ k → λ { (i = i0) → p k
-- --                     ; (i = i1) →
-- --                     ((λ i → transp (λ j → A (merid true (~ i ∨ j)) north) (~ i) (g (merid true (~ i))))
-- --                     ∙ cong (subst (λ x → A x north) (merid true)) p) k})
-- --         (g (merid a i))
-- --   help : (a : Bool) (y : Susp Bool) 
-- --     → PathP (λ i → A (merid a i) y) (f y) (subst (λ x → A x y) (merid true) (f y))
-- --   help a = suspToPropElim true (λ _ → isOfHLevelPathP' 1 (hlev _ _) _ _)
-- --            (help-n a)

-- -- rUnit* : (x : S¹) → x * base ≡ x
-- -- rUnit* base = refl
-- -- rUnit* (loop i) = refl

-- -- kalas : (x : Susp Bool) → x  ≡ susp- not x
-- -- kalas north = merid true
-- -- kalas south = sym (merid false)
-- -- kalas (merid false i) k = ll i k
-- --   where
-- --   ll : PathP (λ i → merid false i ≡ merid true (~ i)) (merid true) (sym (merid false))
-- --   ll = compPathR→PathP (sym (assoc _ _ _ ∙∙ cong (_∙ merid true) (rCancel (merid false)) ∙∙ sym (lUnit (merid true))))
-- -- kalas (merid true i) k = ll k i
-- --   where
-- --   ll : PathP (λ i → merid true i ≡ merid false (~ i)) (merid true) (sym (merid false))
-- --   ll = compPathR→PathP (rUnit (merid true) ∙ cong (merid true ∙_) (sym (lCancel (merid false))))

-- -- lemc : (x : Susp Bool) → SuspBool→S¹ (susp* not x) ≡ invLooper (SuspBool→S¹ x)
-- -- lemc north = loop
-- -- lemc south = refl
-- -- lemc (merid false i) j = loop (j ∧ ~ i)
-- -- lemc (merid true i) j = loop (j ∨ i)

-- -- multInvLooper : (x : S¹) → x * (invLooper x) ≡ base
-- -- multInvLooper base = refl
-- -- multInvLooper (loop i) k =
-- --   hcomp (λ r → λ {(i = i0) → base ; (i = i1) → base ; (k = i1) → base}) base

-- -- assoc* : (x y z : S¹) → x * (y * z) ≡ (x * y) * z
-- -- assoc* base y z = refl
-- -- assoc* (loop i) y z k = help y z k i
-- --   where
-- --   help : (y z : S¹) → rotLoop (y * z) ≡ cong (λ x → x * z) (rotLoop y)
-- --   help = wedgeconFun 0 0 (λ _ _ → isOfHLevelPath 2 (isGroupoidS¹ _ _) _ _)
-- --                          (λ { base → refl ; (loop i) → refl})
-- --                          (λ { base → refl ; (loop i) → refl})
-- --                          refl

-- -- assocImagBool : isAssocImaginaroid Bool
-- -- fst (fst assocImagBool) = not
-- -- fst (snd (fst assocImagBool)) = _+SB_
-- -- fst (snd (snd (fst assocImagBool))) =
-- --   SuspBoolWedge (λ _ _ → isGroupoidSuspBool _ _)
-- --     (λ x → cong S¹→SuspBool (rUnit* (SuspBool→S¹ x))
-- --     ∙∙ kalas (S¹→SuspBool (SuspBool→S¹ x))
-- --     ∙∙ cong (susp- not) (sym (cong S¹→SuspBool (rUnit* (SuspBool→S¹ x)))))
-- --     (λ x → SuspBool→S¹→SuspBool (susp- not x)
-- --           ∙ sym (cong (susp- not) (SuspBool→S¹→SuspBool x)))
-- --     refl
-- -- fst (snd (snd (snd (fst assocImagBool)))) x =
-- --   (λ i → S¹→SuspBool (SuspBool→S¹ x * lemc x i)) ∙ cong S¹→SuspBool (multInvLooper (SuspBool→S¹ x))
-- -- fst (snd (snd (snd (snd (fst assocImagBool))))) = lem
-- --   where
-- --   ss123 : (x : S¹) → susp* not (S¹→SuspBool x) ≡ S¹→SuspBool (invLooper x)
-- --   ss123 base = refl
-- --   ss123 (loop i) k = h k i
-- --     where
-- --     h : cong (susp* not) (merid false ∙ sym (merid true)) ≡ sym (merid false ∙ sym (merid true))
-- --     h = cong-∙ (susp* not) (merid false) (sym (merid true)) ∙ sym (symDistr (merid false) (sym (merid true)))

-- --   invLooperPullOut : (x :  _) → SuspBool→S¹ (susp* not x) ≡ invLooper (SuspBool→S¹ x)
-- --   invLooperPullOut x = cong SuspBool→S¹ (cong (susp* not) (sym (SuspBool→S¹→SuspBool x))
-- --                      ∙ ss123 (SuspBool→S¹ x))
-- --                      ∙ S¹→SuspBool→S¹ (invLooper (SuspBool→S¹ x))

-- --   invLooperDistr : (x y : S¹) → invLooper (x * y) ≡ invLooper x * invLooper y
-- --   invLooperDistr = wedgeconFun 0 0 (λ _ _ → isGroupoidS¹ _ _)
-- --                  (λ _ → refl)
-- --                  (λ x → cong invLooper (rUnit* x) ∙ sym (rUnit* (invLooper x)))
-- --                  (sym (rUnit refl))

-- --   comm* : (x y : S¹) → x * y ≡ y * x
-- --   comm* = wedgeconFun 0 0 (λ _ _ → isGroupoidS¹ _ _)
-- --           (λ x → sym (rUnit* x))
-- --           (λ x → rUnit* x)
-- --           refl

-- --   gl : (x y : _) → (invLooper (SuspBool→S¹ x * SuspBool→S¹ y)) ≡ (SuspBool→S¹ (susp* not y) * SuspBool→S¹ (susp* not x))
-- --   gl x y = cong invLooper (comm* (SuspBool→S¹ x) (SuspBool→S¹ y))
-- --         ∙∙ invLooperDistr (SuspBool→S¹ y) (SuspBool→S¹ x)
-- --         ∙∙ sym (cong₂ _*_ (invLooperPullOut y) (invLooperPullOut x))

-- --   lem : (x y : _) → susp* not (S¹→SuspBool (SuspBool→S¹ x * SuspBool→S¹ y))
-- --                    ≡ S¹→SuspBool (SuspBool→S¹ (susp* not y) * SuspBool→S¹ (susp* not x))
-- --   lem x y = ss123 (SuspBool→S¹ x * SuspBool→S¹ y)
-- --          ∙ cong S¹→SuspBool
-- --            (gl x y)
-- -- isHSpace.μₗ (snd (snd (snd (snd (snd (fst assocImagBool)))))) x = SuspBool→S¹→SuspBool x
-- -- isHSpace.μᵣ (snd (snd (snd (snd (snd (fst assocImagBool)))))) x =
-- --     cong S¹→SuspBool (rUnit* (SuspBool→S¹ x))
-- --   ∙ SuspBool→S¹→SuspBool x
-- -- snd assocImagBool x y z =
-- --      cong S¹→SuspBool (cong (SuspBool→S¹ x *_) (S¹→SuspBool→S¹ (SuspBool→S¹ y * SuspBool→S¹ z))
-- --                      ∙∙ assoc* (SuspBool→S¹ x) (SuspBool→S¹ y) (SuspBool→S¹ z)
-- --                      ∙∙ cong (_* SuspBool→S¹ z) (sym (S¹→SuspBool→S¹ (SuspBool→S¹ x * SuspBool→S¹ y))))

-- -- module joinBoolSusp = joinHSpace Bool assocImagBool (funExt notnot)
-- -- -SB = joinBoolSusp.-A
-- -- *SB = joinBoolSusp._*

-- -- t : (x : _) → SuspBool→S¹ (-SB (S¹→SuspBool x)) ≡ x
-- -- t base = refl
-- -- t (loop i) k = w k i
-- --   where
-- --   w : cong (SuspBool→S¹ ∘ -SB) (merid false ∙ sym (merid true)) ≡ loop
-- --   w = cong (cong (SuspBool→S¹)) (cong-∙ -SB (merid false) (sym (merid true)) ∙ sym (symDistr (sym (merid false)) ( (merid true))))
-- --            ∙∙ cong sym (cong-∙ SuspBool→S¹ (sym (merid false)) ((merid true)) ∙ sym (rUnit (sym loop)))
-- --            ∙∙ refl
-- --   l : cong (SuspBool→S¹ ∘ *SB) (merid false ∙ sym (merid true)) ≡ sym loop
-- --   l = cong (cong SuspBool→S¹) (cong-∙ *SB (merid false) (sym (merid true)))
-- --    ∙∙ cong-∙ SuspBool→S¹ (merid true) (sym (merid false))
-- --    ∙∙ (sym (lUnit (sym loop))
-- --    ∙ refl)

-- -- _+S³_ : S₊ 3 → S₊ 3 → S₊ 3
-- -- _+S³_ = {!joinBoolSusp.idLem true ?!}

-- -- -- checking : (x : S³') → x ≡ {!? +SB ? \!}
-- -- -- checking (inl x) = {!inl x joinBoolSusp.·join inl x!} -- inl (x *' y)  = 0
-- -- -- checking (inr x) = {!inr x joinBoolSusp.·join inr x!} -- inl (susp- not ?)
-- -- -- checking (push a b i) = {!push a b i joinBoolSusp.·join push a b i!}

-- -- -- -- module joinBoolSusp = joinHSpace Bool assocImagBool (funExt notnot)

-- -- -- --   -- Imaginaroid→HSpace : isImaginaroid A
-- -- -- --   --                    → isHSpace (join (Susp A) (Susp A))
-- -- -- --   -- isHSpace.0h (Imaginaroid→HSpace A (invol , _·A_ , -distr , *Unit , *distr)) = inl north
-- -- -- --   -- isHSpace.μ (Imaginaroid→HSpace A (invol , _·A_ , -distr , *Unit , *distr)) = {!!}
-- -- -- --   --   where
-- -- -- --   --   h : join (Susp A) (Susp A) → join (Susp A) (Susp A) → join (Susp A) (Susp A)
-- -- -- --   --   h (inl x) (inl y) = inl (x ·A y)
-- -- -- --   --   h (inl x) (inr y) = inr ({!!} ·A y)
-- -- -- --   --   h (inl x) (push a b i) = {!!}
-- -- -- --   --   h (inr x) y = {!!}
-- -- -- --   --   h (push a b i) y = {!!}
-- -- -- --   -- isHSpace.μₗ (Imaginaroid→HSpace A (invol , _·A_ , -distr , *Unit , *distr)) = {!!}
-- -- -- --   -- isHSpace.μᵣ (Imaginaroid→HSpace A (invol , _·A_ , -distr , *Unit , *distr)) = {!!}

-- -- module hspace-test (_+S_ : S³ → S³ → S³) (rUnitS : ((x : S³) → x +S base ≡ x)) (lUnitS : ((x : S³) → base +S x ≡ x)) (hlem : lUnitS base ≡ rUnitS base)  where
-- --   malem : ∀ {ℓ} {A : Type ℓ} {x y z w : A} (s : y ≡ z) (q : x ≡ w) (r : w ≡ z) (p : x ≡ y)
-- --         → (e : PathP (λ i → q i ≡ s i) p r) → (λ i → e i i) ≡ q ∙∙ refl ∙∙ r
-- --   malem {x = x} {y = y} {z = z} {w = w} s q r p e k i =
-- --     hcomp (λ l → λ {(i = i0) → q (~ l)
-- --                    ; (i = i1) → r l
-- --                    ; (k = i0) → e (i ∨ ~ l) (i ∧ l)})
-- --           w

-- --   open import Cubical.Homotopy.Loopspace

-- --   l1 : S³
-- --   l1 = base +S base

-- --   l2 : l1 ≡ l1
-- --   l2 = refl

-- --   l3 : l2 ≡ l2
-- --   l3 = refl

-- --   l4 : l3 ≡ l3
-- --   l4 j2 i2 k2 = base +S surf j2 i2 k2

-- --   l5 : l4 ≡ l4
-- --   l5 = refl

-- --   l6 : l5 ≡ l5
-- --   l6 = refl

-- --   extractPathP : {B : I → I → I → I → I → I → Type}
-- --                → (p : (i j k i2 j2 k2 : I) → B i j k i2 j2 k2)
-- --                → PathP (λ i →
-- --                        PathP (λ j →
-- --                          PathP (λ k →
-- --                            PathP (λ i2 →
-- --                              PathP (λ j2 →
-- --                                PathP (λ k2 → B i j k i2 j2 k2)
-- --                                  (p i j k i2 j2 i0) (p i j k i2 j2 i1))
-- --                        (λ k2 → p i j k i2 i0 k2) λ k2 → p i j k i2 i1 k2)
-- --                        (λ j2 k2 → p i j k i0 j2 k2) λ j2 k2 → p i j k i1 j2 k2)
-- --                        (λ i2 j2 k2 → p i j i0 i2 j2 k2) λ i2 j2 k2 → p i j i1 i2 j2 k2)
-- --                        (λ k i2 j2 k2 → p i i0 k i2 j2 k2) λ k i2 j2 k2 → p i i1 k i2 j2 k2)
-- --                        (λ j k i2 j2 k2 → p i0 j k i2 j2 k2) λ j k i2 j2 k2 → p i1 j k i2 j2 k2
-- --   extractPathP p i j k i2 j2 k2 = p i j k i2 j2 k2

-- --   the6path = (extractPathP {B = λ _ _ _ _ _ _ → S³} (λ j j2 i i2 k k2 → surf j i k +S surf j2 i2 k2))

-- --   lem2 : lUnitS base ≡ rUnitS base
-- --   lem2 = {!hlem!}

-- --   grr : PathP (λ i → {!!} ≡ {!sym hlem i!}) (sym hlem) (sym hlem)
-- --   grr = {!!}

-- --   lem7 : PathP (λ r → PathP (λ k → lUnitS base ≡ rUnitS base)
-- --                hlem hlem) refl refl
-- --   lem7 = {!!}

-- --   testi : (x : _) → x +S x ≡ base
-- --   testi base = lUnitS base
-- --   testi (surf j i k) w =
-- --     hcomp (λ r → λ {(j = i0) → lUnitS base w ; (j = i1) → hlem (~ r ∧ i ∧ k) w
-- --                    ; (i = i0) → lUnitS base w ; (i = i1) → hlem (~ r ∧ j ∧ k) w
-- --                    ; (k = i0) → lUnitS base w ; (k = i1) → hlem (~ r ∧ i ∧ j) w
-- --                    ; (w = i0) → surf j i k +S surf j i k
-- --                    ; (w = i1) → base})
-- --           (hcomp (λ r → λ {(j = i0) → lUnitS (surf (~ r) (i ∨ ~ r) (k ∨ ~ r)) w ; (j = i1) → hlem ((i ∧ k)) w
-- --                    ; (i = i0) → lUnitS (surf (j ∨ ~ r) (~ r) (k ∨ ~ r)) w ; (i = i1) → hlem ((j ∧ k)) w
-- --                    ; (k = i0) → lUnitS (surf (j ∨ ~ r) (i ∨ ~ r) (~ r)) w ; (k = i1) → hlem ((i ∧ j)) w
-- --                    ; (w = i0) → surf j i k +S surf (j ∨ ~ r) (i ∨ ~ r) (k ∨ ~ r)
-- --                    ; (w = i1) → {!(surf (j ∨ ~ r) (i ∨ ~ r) (~ r ∨ k))!}})
-- --                    {!!})
-- --   {-
-- --     hcomp (λ r → λ {(j = i0) → {!!} ; (j = i1) → {!!}
-- --                    ; (i = i0) → {!!} ; (i = i1) → {!!}
-- --                    ; (k = i0) → {!!} ; (k = i1) → {!!}
-- --                    ; (w = i0) → surf (j ∧ r) (i ∧ r) (k ∧ r) +S surf (j ∨ ~ r) (i ∨ ~ r) (k ∨ ~ r)
-- --                               ; (w = i1) → {!!}})
-- --           {!!} -}
-- --     where
-- --     k123 :
-- --       {!j = i0 ⊢ lUnitS base w
-- -- j = i1 ⊢ lUnitS base w
-- -- i = i0 ⊢ lUnitS base w
-- -- i = i1 ⊢ lUnitS base w
-- -- k = i0 ⊢ lUnitS base w
-- -- k = i1 ⊢ lUnitS base w
-- -- w = i0 ⊢ surf j i k +S surf j i k
-- -- w = i1 ⊢ base!}
-- --     k123 =
-- --       malem {A = {!!}}
-- --             (λ j i i2 k k2 → surf j i k +S base)
-- --             (λ j2 i i2 k k2 → base +S surf j2 i2 k2)
-- --             (λ j i i2 k k2 → surf j i k +S base)
-- --             (λ j2 i i2 k k2 → base +S surf j2 i2 k2)
-- --             (λ j j2 i i2 k k2 → surf j i k +S surf j2 i2 k2)
