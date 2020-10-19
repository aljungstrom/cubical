{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Homotopy.WedgeConnectivity where

open import Cubical.Foundations.Everything
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as Trunc
open import Cubical.Homotopy.Connected

open import Cubical.HITs.Sn
open import Cubical.HITs.S1
{-
wedgeConAlt1 : ∀ {ℓ} (n m : ℕ) → (P : S₊ (1 + n) → S₊ (1 + m) → TypeOfHLevel ℓ (2 + n + m))
              → (f : ((a : S₊ (1 + n)) → P a (ptSn (suc m)) .fst))
              → (g : ((a : S₊ (1 + m)) → P (ptSn (suc n)) a .fst))
              → f (ptSn (suc n)) ≡ g (ptSn (suc m))
              → ∀ a b → P a b .fst
theIdRight : ∀ {ℓ} (n m : ℕ) → (P : S₊ (1 + n) → S₊ (1 + m) → TypeOfHLevel ℓ (2 + n + m))
              → (f : ((a : S₊ (1 + n)) → P a (ptSn (suc m)) .fst))
              → (g : ((a : S₊ (1 + m)) → P (ptSn (suc n)) a .fst))
              → (hom : f (ptSn (suc n)) ≡ g (ptSn (suc m)))
              → (a : S₊ (suc m)) → wedgeConAlt1 n m P f g hom (ptSn (suc n)) a ≡ g a
theIdLeft : ∀ {ℓ} (n m : ℕ) → (P : S₊ (1 + n) → S₊ (1 + m) → TypeOfHLevel ℓ (2 + n + m))
              → (f : ((a : S₊ (1 + n)) → P a (ptSn (suc m)) .fst))
              → (g : ((a : S₊ (1 + m)) → P (ptSn (suc n)) a .fst))
              → (hom : f (ptSn (suc n)) ≡ g (ptSn (suc m)))
              → (a : S₊ (suc n)) → wedgeConAlt1 n m P f g hom a (ptSn (suc m)) ≡ f a
wedgeConAlt1 zero zero P f g hom = {!!}
wedgeConAlt1 zero (suc n) P f g hom a north = f a
wedgeConAlt1 zero (suc n) P f g hom base south = g south
wedgeConAlt1 zero (suc n) P f g hom (loop i) south =
  hcomp (λ k → λ { (i = i0) → (cong (subst (λ x → P base x .fst) (merid (ptSn (suc n)))) hom
                                    ∙ λ i → transp (λ j → P base (merid (ptSn (suc n)) (i ∨ j)) .fst) i
                                                    (g (merid (ptSn (suc n)) i))) k
                  ; (i = i1) → (cong (subst (λ x → P base x .fst) (merid (ptSn (suc n)))) hom
                                    ∙ λ i → transp (λ j → P base (merid (ptSn (suc n)) (i ∨ j)) .fst) i
                                                    (g (merid (ptSn (suc n)) i))) k})
        (subst (λ x → P (loop i) x .fst) (merid (ptSn (suc n))) (f (loop i)))
wedgeConAlt1 zero (suc n) P f g hom a (merid b i) = {!!}
  where
  ind :  PathP (λ i → P a (merid b i) .fst) (f a) (wedgeConAlt1 zero (suc n) P f g hom a south)
  ind = wedgeConAlt1 zero n (λ a b → PathP (λ i → P a (merid b i) .fst) (f a)
                              (wedgeConAlt1 zero (suc n) P f g hom a south)
                            , isOfHLevelPathP' (2 + n) (P a south .snd) _ _)
                            (λ { base i → hcomp (λ k →  λ { (i = i0) → hom (~ k)
                                                            ; (i = i1) → g south })
                                                 (g (merid (ptSn (suc n)) i))
                              ; (loop i) j → {!f (loop i)!} {- hcomp (λ k →  λ { (j = i0) → {!!}
                                                               ; (j = i1) → {!!}})
                                                    {!!} -}})
                            (λ a i → hcomp (λ k →  λ { (i = i0) → hom (~ k)
                                                       ; (i = i1) → g south })
                                            (g (merid a i)))
                            refl a b
wedgeConAlt1 (suc n) zero P f g hom a b = {!!}
  {- wedgeConAlt1 zero (suc n)
       (λ a b → P b a .fst
              , subst (λ x → isOfHLevel x (P b a .fst)) (cong (λ x → 3  + x) (+-zero n))
                      (P b a .snd))
       g f (sym hom) b a -}
wedgeConAlt1 (suc n) (suc m) P f g hom a north = f a
wedgeConAlt1 (suc n) (suc m) P f g hom a south = subst (λ x → P a x .fst) (merid (ptSn (suc m))) (f a)
wedgeConAlt1 (suc n) (suc m) P f g hom a (merid b i) = {!!}
  where
  helper :  PathP (λ i → P a (merid b i) .fst) (f a) (subst (λ x → P a x .fst) (merid (ptSn (suc m))) (f a))
  helper = wedgeConAlt1 (suc n) m
           (λ a b → PathP (λ i → P a (merid b i) .fst) (f a)
                           (subst (λ x → P a x .fst) (merid (ptSn (suc m))) (f a)) , {!!})
           (λ x → {!!})
           (λ b → {!!})
           {!!}
           a b
theIdRight zero zero P f g hom a = {!!}
theIdRight zero (suc m) P f g hom north = hom
theIdRight zero (suc m) P f g hom south = refl
theIdRight zero (suc m) P f g hom (merid a i) = {!!}
theIdRight (suc n) m P f g hom a = {!!}
theIdLeft zero zero P f g hom a = {!!}
theIdLeft zero (suc m) P f g hom a = refl
theIdLeft (suc n) m P f g hom a = {!!}


wedgeConAlt1 : ∀ {ℓ} (n : ℕ) → (P : S₊ (1 + n) → S₊ (1 + n) → TypeOfHLevel ℓ (2 + n + n))
              → (f : ((a : S₊ (1 + n)) → P a (ptSn (suc n)) .fst))
              → (g : ((a : S₊ (1 + n)) → P (ptSn (suc n)) a .fst))
              → f (ptSn (suc n)) ≡ g (ptSn (suc n))
              → ∀ a b → P a b .fst
theIdRight : ∀ {ℓ} (n : ℕ) → (P : S₊ (1 + n) → S₊ (1 + n) → TypeOfHLevel ℓ (2 + n + n))
              → (f : ((a : S₊ (1 + n)) → P a (ptSn (suc n)) .fst))
              → (g : ((a : S₊ (1 + n)) → P (ptSn (suc n)) a .fst))
              → (hom : f (ptSn (suc n)) ≡ g (ptSn (suc n)))
              → (a : S₊ (suc n)) → wedgeConAlt1 n P f g hom (ptSn (suc n)) a ≡ g a
theIdLeft : ∀ {ℓ} (n : ℕ) → (P : S₊ (1 + n) → S₊ (1 + n) → TypeOfHLevel ℓ (2 + n + n))
              → (f : ((a : S₊ (1 + n)) → P a (ptSn (suc n)) .fst))
              → (g : ((a : S₊ (1 + n)) → P (ptSn (suc n)) a .fst))
              → (hom : f (ptSn (suc n)) ≡ g (ptSn (suc n)))
              → (a : S₊ (suc n)) → wedgeConAlt1 n P f g hom a (ptSn (suc n)) ≡ f a
wedgeConAlt1 zero P f g hom a b = {!!}
wedgeConAlt1 (suc n) P f g hom x north = f x
wedgeConAlt1 (suc n) P f g hom north south = g south
wedgeConAlt1 (suc n) P f g hom south south = {!!}
wedgeConAlt1 (suc n) P f g hom (merid a i) south = {!!}
wedgeConAlt1 (suc n) P f g hom north (merid a i) =
  hcomp (λ k → λ { (i = i0) → hom (~ k)
                  ; (i = i1) → g south})
        (g (merid a i))
wedgeConAlt1 (suc n) P f g hom south (merid a i) = {!!}
wedgeConAlt1 (suc n) P f g hom (merid a₁ i₁) (merid a i) = {!!}
theIdRight zero P f g hom a = {!!}
theIdRight (suc n) P f g hom north = hom
theIdRight (suc n) P f g hom south = refl
theIdRight (suc n) P f g hom (merid a i) j =
  hcomp (λ k → λ { (i = i0) → hom (j ∨ ~ k)
                  ; (i = i1) → g (merid a (i ∨ k))
                  ; (j = i1) → g (merid a i)})
        (g (merid a i))
theIdLeft zero P f g hom a = {!!}
theIdLeft (suc n) P f g hom x = refl

wedgeConAlt1 : ∀ {ℓ} (n : ℕ) → (P : S₊ (1 + n) → S₊ (1 + n) → TypeOfHLevel ℓ (2 + n + n))
              → (f : ((a : S₊ (1 + n)) → P a (ptSn (suc n)) .fst))
              → (g : ((a : S₊ (1 + n)) → P (ptSn (suc n)) a .fst))
              → f (ptSn (suc n)) ≡ g (ptSn (suc n))
              → ∀ a b → P a b .fst
wedgeConAlt1 zero P f g hom base b = g b
wedgeConAlt1 zero P f g hom (loop i) base = hcomp (λ k → λ {(i = i0) → hom k ; (i = i1) → hom k}) (f (loop i))
wedgeConAlt1 zero P f g hom (loop i) (loop j) = helper i j
  where
  helper : SquareP (λ i j → P (loop i) (loop j) .fst)
                   (λ j → g (loop j))
                   (λ j → g (loop j))
                   (λ i → hcomp (λ k → λ {(i = i0) → hom k ; (i = i1) → hom k}) (f (loop i)))
                   λ i → hcomp (λ k → λ {(i = i0) → hom k ; (i = i1) → hom k}) (f (loop i))
  helper = transport⁻ (PathP≡Path _ _ _)
                      (isOfHLevelPathP' 1 (λ x y → P base base .snd _ _)
                                          _ _ _ _)
wedgeConAlt1 (suc n) P f g hom north north = f north
wedgeConAlt1 (suc n) P f g hom north south = g south
wedgeConAlt1 (suc n) P f g hom north (merid a i) = hcomp (λ k → λ {(i = i0) → hom (~ k) ; (i = i1) → g south}) (g (merid a i))
wedgeConAlt1 (suc n) P f g hom south north = f south
wedgeConAlt1 (suc n) P f g hom south south = subst (λ x → P x south .fst) (merid (ptSn (suc n))) (g south)
wedgeConAlt1 (suc n) P f g hom south (merid a i) =
  hcomp (λ k → λ { (i = i0) → ((λ i → transp (λ j → P south (merid a (~ i ∧ ~ j)) .fst) i
                                          (transport (λ j → P (merid (ptSn (suc n)) j) (merid a (~ i)) .fst) (g (merid a (~ i)))))
                                      ∙∙ cong (transport (λ j → P (merid (ptSn (suc n)) j) (merid a i0) .fst))
                                              (sym hom)
                                      ∙∙ λ i → transp (λ j → P (merid (ptSn (suc n)) (i ∨ j)) north .fst) i
                                                       (f (merid (ptSn (suc n)) i))) k
                  ; (i = i1) → subst (λ x → P x south .fst) (merid (ptSn (suc n))) (g south)})
        (transp (λ j → P south (merid a (i ∨ (~ j))) .fst) i
                (subst (λ x → P x south .fst) (merid (ptSn (suc n)))
                       (g south)))
wedgeConAlt1 (suc n) P f g hom (merid a i) north = f (merid a i)
wedgeConAlt1 (suc n) P f g hom (merid a i) south =
  hcomp (λ k → λ { (i = i0) → (cong (subst (λ x → P north x .fst ) (merid (ptSn (suc n)))) hom
                               ∙ (λ i → transp (λ j → P north (merid (ptSn (suc n)) (i ∨ j)) .fst) i
                                                (g (merid (ptSn (suc n)) i)))) k
                  ; (i = i1) → ((λ i → subst (λ x → P south x .fst) (merid (ptSn (suc n)))
                                               (transp (λ j → P (merid (ptSn (suc n)) (j ∨ ~ i)) north .fst) (~ i)
                                                       (f (merid (ptSn (suc n)) (~ i)))))
                              ∙∙ (λ i → subst (λ x → P south x .fst) (merid (ptSn (suc n)))
                                           (subst (λ x → P x north .fst) (merid (ptSn (suc n)))
                                                  (hom i)))
                              ∙∙ (λ i → transp (λ j → P south (merid (ptSn (suc n)) (i ∨ j)) .fst) i
                                           (subst (λ x → P x (merid (ptSn (suc n)) i) .fst) (merid (ptSn (suc n)))
                                                  (g (merid (ptSn (suc n)) i) )))) k})
        (subst (λ x → P (merid a i) x .fst ) (merid (ptSn (suc n))) (f (merid a i)))
wedgeConAlt1 (suc n) P f g hom (merid a i) (merid b j) =
  helper a b i j
  where
  theType : (a b : S₊ (suc n))  → Type₀ _
  theType a b = SquareP (λ i j → P (merid a i) (merid b j) .fst)
                                        (λ i → wedgeConAlt1 (suc n) P f g hom north (merid b i))
                                        (λ i → wedgeConAlt1 (suc n) P f g hom south (merid b i))
                                        (cong f (merid a))
                                        λ i → wedgeConAlt1 (suc n) P f g hom (merid a i) south

  helper : (a b : S₊ (suc n)) → SquareP (λ i j → P (merid a i) (merid b j) .fst)
                                        (λ i → wedgeConAlt1 (suc n) P f g hom north (merid b i))
                                        (λ i → wedgeConAlt1 (suc n) P f g hom south (merid b i))
                                        (cong f (merid a))
                                        λ i → wedgeConAlt1 (suc n) P f g hom (merid a i) south
  helper = wedgeConAlt1 n (λ a b → theType a b , {!!})
                          {!!}
                          {!!}
                          {!!}
{-
wedgeConAlt1 (suc n) P f g hom south north = f south -- subst (λ x → P x n .fst) (merid (ptSn (suc n))) (g b)
wedgeConAlt1 (suc n) P f g hom south south = subst (λ x → P south x .fst) (merid (ptSn (suc n))) (f south)
wedgeConAlt1 (suc n) P f g hom south (merid a i) = {!!}
wedgeConAlt1 (suc n) P f g hom (merid a i) north =  hcomp (λ k → λ {(i = i0) → hom k ; (i = i1) → f south}) (f (merid a i))
wedgeConAlt1 (suc n) P f g hom (merid a i) south =
  hcomp (λ k → λ { (i = i0) → (cong (subst (λ x → P north x .fst) (merid (ptSn (suc n)))) hom
                              ∙ λ i → transp (λ j → P north (merid (ptSn (suc n)) (i ∨ j)) .fst) i
                                              (g (merid (ptSn (suc n)) i))) k
                  ; (i = i1) → subst (λ x → P south x .fst) (merid (ptSn (suc n))) (f south)})
        (subst (λ x → P (merid a i) x .fst) (merid (ptSn (suc n))) (f (merid a i)))
wedgeConAlt1 (suc n) P f g hom (merid a i) (merid b i₁) =
  {!!}
  where
  aSquare : (a b : S₊ (suc n))
         → SquareP (λ i j → P (merid a i) (merid b j) .fst)
                    {!!} {!!} {!!} {!!}
  aSquare = {!!}
-}

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
