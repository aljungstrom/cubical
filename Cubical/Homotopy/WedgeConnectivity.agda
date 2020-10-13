{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Homotopy.WedgeConnectivity where

open import Cubical.Foundations.Everything
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation.FromNegOne as Trunc
open import Cubical.Homotopy.Connected

{-
open import Cubical.HITs.Sn

S₊∙s : (n : ℕ) → Pointed₀
S₊∙s n = S₊ n , thePt n
  where
  thePt : (n : ℕ) → S₊ n
  thePt zero = true
  thePt (suc zero) = base
  thePt (suc (suc n)) = south

WedgeConSn : ∀ {ℓ} (n : ℕ)
  (A : S₊ (suc n) → S₊ (suc n) → TypeOfHLevel ℓ (suc n + suc n))
  (f : (a : S₊ (suc n)) → typ (A a (pt (S₊∙ (suc n)) )))
  (g : (b : S₊ (suc n)) → typ (A (pt (S₊∙ (suc n))) b))
  (p : f (pt (S₊∙ (suc n))) ≡ g (pt (S₊∙ (suc n)))) →
    Σ[ h ∈ ((x y : S₊ (suc n)) → typ (A x y)) ]
      ((a : S₊ (suc n)) → h a (pt (S₊∙ (suc n))) ≡ f a)
    × ((a : S₊ (suc n)) → h (pt (S₊∙ (suc n))) a ≡ g a)
WedgeConSn zero A f g p = {!!}
WedgeConSn (suc n) A f g p = h , {!!}
  where
  ptSn+1 : S₊ (1 + n)
  ptSn+1 = pt (S₊∙ (1 + n))
  transpId : (a : S₊ (1 + n)) →
             subst (λ x → typ (A x north)) (merid a) (g north) ≡ f south
  transpId a = (λ i → subst (λ x → typ (A x north)) (merid a) (p (~ i)))
           ∙ fromPathP λ i → f (merid a i)
  transpId2 : (a b : S₊ (1 + n)) → subst (λ x → typ (A x south)) (merid a) (g south)
                                  ≡ subst (λ x → typ (A x south)) (merid b) (g south)
  transpId2 a b = {!!} ∙∙ {!!} ∙∙ {!!}
    where
    helper : subst (λ x → typ (A x south)) (merid a) (g south) ≡ {!!}
    helper = {!!}


  h : (x y : S₊ (2 + n)) → typ (A x y)
  h north north = g north
  h north south = g south
  h north (merid a i) = g (merid a i)
  h south north = f south
  h south south = subst (λ x → typ (A x south)) (merid ptSn+1) (g south)
  h south (merid a i) = 
    hcomp (λ k → λ { (i = i0) → transpId ptSn+1 k
                    ; (i = i1) → h south south})
          (transport (λ j → typ (A (merid ptSn+1 j) (merid a i))) (g (merid a i)))

  h (merid a i) north =
    hcomp ((λ k → λ { (i = i0) → p k
                     ; (i = i1) → f south}))
          (f (merid a i))
  h (merid a i) south = {!!}
    where
    helper : subst (λ x → typ (A north x)) (merid a) (g north) ≡ g south
    helper = fromPathP (cong g (merid a))
  h (merid a i) (merid b j) = helper a b i j
    where
    helper : (a b : S₊ (1 + n)) → SquareP (λ i j → typ (A (merid a i) (merid b j)))
                (λ j → h north (merid b j)) (λ j → h south (merid b j))
                (λ i → h (merid a i) north) (λ i → h (merid a i) south)
    helper = WedgeConSn n (λ a b → _ , {!λ p q → ?!})
               (λ a → {!!})
               (λ b → {!!})
               {!!} .fst
  helper : {!!}
  helper = {!!}


WedgeConSn : ∀ {ℓ} (n : ℕ)
  (A : S₊ (suc n) → S₊ (suc n) → Type ℓ)
  (f : (a : S₊ (suc n)) → hLevelTrunc (suc n + suc n) (A a (pt (S₊∙ (suc n)) )))
  (g : (b : S₊ (suc n)) → hLevelTrunc (suc n + suc n) (A (pt (S₊∙ (suc n))) b))
  (p : f (pt (S₊∙ (suc n))) ≡ g (pt (S₊∙ (suc n)))) →
    Σ[ h ∈ ((x y : S₊ (suc n)) → hLevelTrunc (suc n + suc n) (A x y)) ]
      ((a : S₊ (suc n)) → h a (pt (S₊∙ (suc n))) ≡ f a)
    × ((a : S₊ (suc n)) → h (pt (S₊∙ (suc n))) a ≡ g a)
WedgeConSn zero A f g p =
  h , (λ { base → sym p
         ; (loop i) j → square i (~ j) })
     , λ _ → refl
  where
  square : (i : I) → I → hLevelTrunc 2 (A (loop i) base)
  square i j = hfill (λ k → λ { (i = i0) → p k
                               ; (i = i1) → p k})
                     (inS (f (loop i)))
                     j
  h : (x y : S₊ 1) → hLevelTrunc 2 (A x y)
  h base y = g y
  h (loop i) x = helper x i
    where
    helper : (x : S₊ 1) → PathP (λ i → hLevelTrunc 2 (A (loop i) x)) (g x) (g x)
    helper = toPropElim (λ s → isOfHLevelPathP' 1 (isOfHLevelTrunc 2) _ _)
                        λ i → square i i1
WedgeConSn (suc zero) A f g p = h , {!!}
  where
  h : (x y : S₊ 2) → hLevelTrunc 4 (A x y)
  h north north = g north
  h north south = subst (λ x → hLevelTrunc 4 (A north x))
                        (merid base)
                        (f north)
  h north (merid base i) =
    hcomp (λ k → λ { (i = i0) → p k
                    ; (i = i1) → h north south})
          (transp (λ j → hLevelTrunc 4 (A north (merid base (i ∧ j))))
                                        (~ i)
                                        (f north))
  h north (merid (loop j) i) = {!!}
  h south y = {!!}
  h (merid a i) y = {!!}
WedgeConSn (suc (suc n)) A f g p = h , {!!} , {!!}
  where
  m = (3 + n) + (3 + n)
  h : (x y : S₊ (3 + n)) → hLevelTrunc m (A x y)
  h north north = g north
  h north south = subst (λ x → hLevelTrunc m (A north x))
                        (merid north)
                        (f north)
  h north (merid north i) =
    hcomp (λ k → λ { (i = i0) → p k
                    ; (i = i1) → h north south})
          (transp (λ j → hLevelTrunc m (A north (merid north (i ∧ j))))
                                    (~ i)
                                    (f north))
  h north (merid south i) = {!!}
  h north (merid (merid a j) i) = {!a!}
    where
    helper : {!!}
    helper = {!!}
  h south north = f south
  h south south = 
    subst (λ x → hLevelTrunc m (A x south))
          (merid north)
          (g south)
  h south (merid a i) = {!a!}
  h (merid a i) y = {!!}


  h : (x y : S₊ (3 + n)) → hLevelTrunc ((3 + n) + (3 + n)) (A x y)
  h north y = g y
  h south y = subst (λ x → hLevelTrunc ((3 + n) + (3 + n)) (A x y))
                    (merid north)
                    (g y)
  h (merid north i) y = transp (λ j → hLevelTrunc ((3 + n) + (3 + n)) (A (merid north (i ∧ j)) y)) (~ i) (g y)
  h (merid south i) y =
    hcomp (λ k → λ { (i = i0) → g y ;
                      (i = i1) → transp (λ j → hLevelTrunc ((3 + n) + (3 + n))
                                         (A (merid (merid (pt (S₊∙ (suc n))) (~ k)) (i ∧ j)) y)) (~ i) (g y)})
          (transp (λ j → hLevelTrunc ((3 + n) + (3 + n)) (A (merid south (i ∧ j)) y)) (~ i) (g y))
  h (merid (merid a i₁) i) y = {!!}
    where
    helper : SquareP (λ i j → hLevelTrunc m (A (merid (merid a i) j) y))
                     (λ i → h (merid north i) y) (λ i → h (merid south i) y)
                     (λ _ → h north y) λ _ → h south y
    helper = transport⁻ (PathP≡Path _ _ _) {!transport⁻ ?!}

    where
    helper : PathP (λ i → hLevelTrunc m (A (merid a i) y)) (g y) (subst (λ x → hLevelTrunc m (A x y)) (merid north) (g y))
    helper = transport⁻ (PathP≡Path _ _ _) {!!}
-}

module WedgeConnectivity {ℓ ℓ' ℓ''} (n m : ℕ)
  (A : Pointed ℓ) (connA : isConnected (suc n) (typ A))
  (B : Pointed ℓ') (connB : isConnected (suc m) (typ B))
  (P : typ A → typ B → TypeOfHLevel ℓ'' (n + m))
  (f : (a : typ A) → P a (pt B) .fst)
  (g : (b : typ B) → P (pt A) b .fst)
  (p : f (pt A) ≡ g (pt B))
  where

  private
    Q : typ A → TypeOfHLevel _ n
    Q a =
      ( (Σ[ k ∈ ((b : typ B) → P a b .fst) ] k (pt B) ≡ f a)
      , isOfHLevelRetract n
          (λ {(h , q) → h , funExt λ _ → q})
          (λ {(h , q) → h , funExt⁻ q _})
          (λ _ → refl)
          (isOfHLevelPrecomposeConnected n m (P a) (λ _ → pt B)
            (isConnectedPoint m connB (pt B)) (λ _ → f a))
      )

    main : isContr (fiber (λ s _ → s (pt A)) (λ _ → g , p ⁻¹))
    main =
      elim.isEquivPrecompose (λ _ → pt A) n Q
        (isConnectedPoint n connA (pt A))
        .equiv-proof (λ _ → g , p ⁻¹)


  extension : ∀ a b → P a b .fst
  extension a b = main .fst .fst a .fst b

  left : ∀ a → extension a (pt B) ≡ f a
  left a = main .fst .fst a .snd

  right : ∀ b → extension (pt A) b ≡ g b
  right = funExt⁻ (cong fst (funExt⁻ (main .fst .snd) _))

    -- TODO: left (pt A) ⁻¹ ∙ right (pt B) ≡ p
