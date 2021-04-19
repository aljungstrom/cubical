{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Algebra.Group.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

module GroupLemmas (G : Group {ℓ}) where
  open GroupStr (snd G)
  abstract
    simplL : (a : ⟨ G ⟩) {b c : ⟨ G ⟩} → a + b ≡ a + c → b ≡ c
    simplL a {b} {c} p =
       b
        ≡⟨ sym (lid b) ∙ cong (_+ b) (sym (invl a)) ∙ sym (assoc _ _ _) ⟩
      - a + (a + b)
        ≡⟨ cong (- a +_) p ⟩
      - a + (a + c)
        ≡⟨ assoc _ _ _ ∙ cong (_+ c) (invl a) ∙ lid c ⟩
      c ∎

    simplR : {a b : ⟨ G ⟩} (c : ⟨ G ⟩) → a + c ≡ b + c → a ≡ b
    simplR {a} {b} c p =
      a
        ≡⟨ sym (rid a) ∙ cong (a +_) (sym (invr c)) ∙ assoc _ _ _ ⟩
      (a + c) - c
        ≡⟨ cong (_- c) p ⟩
      (b + c) - c
        ≡⟨ sym (assoc _ _ _) ∙ cong (b +_) (invr c) ∙ rid b ⟩
      b ∎

    invInvo : (a : ⟨ G ⟩) → - (- a) ≡ a
    invInvo a = simplL (- a) (invr (- a) ∙ sym (invl a))

    invId : - 0g ≡ 0g
    invId = simplL 0g (invr 0g ∙ sym (lid 0g))

    idUniqueL : {e : ⟨ G ⟩} (x : ⟨ G ⟩) → e + x ≡ x → e ≡ 0g
    idUniqueL {e} x p = simplR x (p ∙ sym (lid _))

    idUniqueR : (x : ⟨ G ⟩) {e : ⟨ G ⟩} → x + e ≡ x → e ≡ 0g
    idUniqueR x {e} p = simplL x (p ∙ sym (rid _))

    invUniqueL : {g h : ⟨ G ⟩} → g + h ≡ 0g → g ≡ - h
    invUniqueL {g} {h} p = simplR h (p ∙ sym (invl h))

    invUniqueR : {g h : ⟨ G ⟩} → g + h ≡ 0g → h ≡ - g
    invUniqueR {g} {h} p = simplL g (p ∙ sym (invr g))

    invDistr : (a b : ⟨ G ⟩) → - (a + b) ≡ - b - a
    invDistr a b = sym (invUniqueR γ) where
      γ : (a + b) + (- b - a) ≡ 0g
      γ = (a + b) + (- b - a)
            ≡⟨ sym (assoc _ _ _) ⟩
          a + b + (- b) + (- a)
            ≡⟨ cong (a +_) (assoc _ _ _ ∙ cong (_+ (- a)) (invr b)) ⟩
          a + (0g - a)
            ≡⟨ cong (a +_) (lid (- a)) ∙ invr a ⟩
          0g ∎

isPropIsGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
             → isProp (IsGroup 0g _+_ -_)
IsGroup.isMonoid (isPropIsGroup 0g _+_ -_ g1 g2 i) = isPropIsMonoid _ _ (IsGroup.isMonoid g1) (IsGroup.isMonoid g2) i
IsGroup.inverse (isPropIsGroup 0g _+_ -_ g1 g2 i) = isPropInv (IsGroup.inverse g1) (IsGroup.inverse g2) i
  where
  isSetG : isSet _
  isSetG = IsSemigroup.is-set (IsMonoid.isSemigroup (IsGroup.isMonoid g1))

  isPropInv : isProp ((x : _) → ((x + (- x)) ≡ 0g) × (((- x) + x) ≡ 0g))
  isPropInv = isPropΠ λ _ → isProp× (isSetG _ _) (isSetG _ _)

{-
open import Cubical.HITs.Truncation
open import Cubical.HITs.Susp
data K1 {ℓ : Level} (G : Group {ℓ}) : Type ℓ where
  base : K1 G
  loop : ⟨ G ⟩ → base ≡ base
  loop-ident : loop (GroupStr.0g (snd G)) ≡ refl
  loop-comp : (x y : ⟨ G ⟩)
            → PathP (λ i → base ≡ loop y i)
                     (loop x)
                     (loop (GroupStr._+_ (snd G) x y))

isGroupoidK1 : ∀ {ℓ} {G : Group {ℓ}} → isGroupoid (K1 G)
isGroupoidK1 = {!!}

K1-elim : ∀ {ℓ ℓ'} {G : Group {ℓ}} {A : K1 G → Type ℓ'}
         → (pt : A base)
         → (loop' : (g : ⟨ G ⟩) → PathP (λ i → A (loop g i)) pt pt)
         → PathP (λ j → PathP (λ i → A (loop-ident j i)) pt pt)
                                (loop' (GroupStr.0g (snd G)))
                                (λ _ → pt)
         → ((x y : ⟨ G ⟩) → PathP (λ j → PathP (λ i → A (loop-comp x y j i)) pt (loop' y j))
                                   (loop' x)
                                   (loop' (GroupStr._+_ (snd G) x y)))
         → (x : _) → A x
K1-elim pt loop' ident comp base = pt
K1-elim pt loop' ident comp (loop x i) = loop' x i
K1-elim pt loop' ident comp (loop-ident i i₁) = ident i i₁
K1-elim pt loop' ident comp (loop-comp x y i i₁) = comp x y i i₁

K1→Set : ∀ {ℓ ℓ'} {G : Group {ℓ}} {A : K1 G → Type ℓ'}
         → ((x : _) → isSet (A x)) 
         → (pt : A base)
         → (loop' : (g : ⟨ G ⟩) → PathP (λ i → A (loop g i)) pt pt)
         → (x : _) → A x
K1→Set set pt loop' =
  K1-elim pt loop'
    (isProp→PathP (λ i → isOfHLevelPathP' 1 (set _) _ _) _ _)
    λ _ _ → (isProp→PathP (λ i → isOfHLevelPathP' 1 (set _) _ _) _ _)

K1→Prop : ∀ {ℓ ℓ'} {G : Group {ℓ}} {A : K1 G → Type ℓ'}
         → ((x : _) → isProp (A x)) 
         → (pt : A base)
         → (x : _) → A x
K1→Prop prop pt = K1→Set (λ x → isProp→isSet (prop _)) pt
                            λ _ → isProp→PathP (λ i → prop _) _ _

K1-rec : ∀ {ℓ ℓ'} {G : Group {ℓ}} {A : Type ℓ'}
         → (pt : A)
         → (loop' : ⟨ G ⟩ → pt ≡ pt)
         → (loop' (GroupStr.0g (snd G)) ≡ refl)
         → ((x y : ⟨ G ⟩) →  loop' x ∙ loop' y ≡ (loop' (GroupStr._+_ (snd G) x y)))
         → (x : K1 G) → A
K1-rec pt loop' ident comp base = pt
K1-rec pt loop' ident comp (loop x i) = loop' x i
K1-rec pt loop' ident comp (loop-ident i i₁) = ident i i₁
K1-rec {G = G} pt loop' ident comp (loop-comp x y i j) =
  hcomp (λ k → λ {(i = i0) → compPath-filler (loop' x) (loop' y) (~ k) j
                 ; (i = i1) → loop' ((snd G GroupStr.+ x) y) j
                 ; (j = i0) → pt
                 ; (j = i1) → loop' y (~ k ∨ i)})
        (comp x y i j)
open import Cubical.Data.Nat
K' : ∀ {ℓ} (G : Group {ℓ}) (n : ℕ) → Type ℓ
K' G zero = ⟨ G ⟩
K' G (suc zero) = K1 G
K' G (suc (suc n)) = Susp (K' G (suc n))

ptK' : ∀ {ℓ} {G : Group {ℓ}} (n : ℕ) → K' G n
ptK' {G = G} zero = GroupStr.0g (snd G)
ptK' {G = G} (suc zero) = base
ptK' {G = G} (suc (suc n)) = north

K1+ : ∀ {ℓ} {G : Group {ℓ}} → ((x y : ⟨ G ⟩) → GroupStr._+_ (snd G) x y ≡ GroupStr._+_ (snd G) y x) → K1 G → K1 G → K1 G
K1+ {G = G} comm =
  K1-rec
    (λ x → x)
    (λ g → funExt (K1→Set (λ _ → isGroupoidK1 _ _) (loop g)
                   (help g)))
    {!!} -- (λ i j x → test x i j) -- ( λ i j x → test x i j)
    λ x y → {!!}
  where
  help : (g h : _) → PathP (λ i → loop h i ≡ loop h i) (loop g) (loop g)
  help g h i j =
    hcomp (λ k → λ { (i = i0) → loop-comp g h (~ k) j
                    ; (i = i1) → loop g (~ k ∨ j)
                    ; (j = i0) → loop-comp h g (~ k) i -- loop h (i ∧ k)
                    ; (j = i1) → loop h (i ∨ ~ k)})
          (hcomp (λ k → λ { (i = i0) → loop (comm g h (~ k)) j
                    ; (i = i1) → base
                    ; (j = i0) → loop-comp h g i1 i
                    ; (j = i1) → base})
                 (loop (GroupStr._+_ (snd G) h g) (i ∨ j)))
  test : (x : K1 G) → (K1→Set (λ z → isGroupoidK1 z z) (loop (GroupStr.0g (snd G)))
       (help (GroupStr.0g (snd G)))) x ≡ refl
  test = K1→Prop (λ _ → isGroupoidK1 _ _ _ _) loop-ident

  test2 : (x y : ⟨ G ⟩) → (z : K1 G) → funExt⁻ (funExt (K1→Set (λ z → isGroupoidK1 z z) (loop x) (help x)) ∙
      funExt (K1→Set (λ z → isGroupoidK1 z z) (loop y) (help y))) z ≡ (K1→Set (λ z → isGroupoidK1 z z) (loop ((snd G GroupStr.+ x) y))
       (help ((snd G GroupStr.+ x) y))) z
  test2 x y = K1→Prop (λ _ → isGroupoidK1 _ _ _ _) {!!}


{-
i = i0 ⊢ loop g j
i = i1 ⊢ loop g j
j = i0 ⊢ loop h i
j = i1 ⊢ loop h i
K1+ {G = G} (loop x i) y = help x y i
  where
  help : (x : ⟨ G ⟩) → (y : K1 _) → y ≡ y
  help x = K1→Set (λ _ → isGroupoidK1 _ _)
                   (loop x)
                   λ g → {!!}
K1+ {G = G} (loop-ident i i₁) =
  {!!}
  where
  help : {!!}
  help = {!!}
K1+ {G = G , groupstr 0g _++_ -_ (isgroup isMonoid inverse)} (loop-comp x y₁ i i₁) y =
  {!!}
  -}

-- K'G-elim : ∀ {ℓ ℓ'} {G : Group {ℓ}} (n : ℕ) {A : K' G (suc (suc n)) → Type ℓ'}
--                   → ((x : _) → isOfHLevel (suc n) (A x))
--                   → A north
--                   → (x : _) → A x
-- K'G-elim zero hlev pt = suspToPropElim base hlev pt
-- K'G-elim (suc n) hlev pt north = pt
-- K'G-elim (suc n) {A = A} hlev pt south = subst A (merid (ptK' (2 + n))) pt
-- K'G-elim (suc n) {A = A} hlev pt (merid a i) = help a i
--   where
--   help : (a : K' _ (suc (suc n))) → PathP (λ i → A (merid a i)) pt (subst A (merid (ptK' (2 + n))) pt)
--   help = K'G-elim n (λ _ → isOfHLevelPathP' (suc n) (hlev _) _ _)
--                     λ i → transp (λ j → A (merid north (i ∧ j))) (~ i) pt

-- K''G-elim : ∀ {ℓ ℓ'} {G : Group {ℓ}} (n : ℕ) {A : K' G (suc n) → Type ℓ'}
--                   → ((x : _) → isOfHLevel (suc n) (A x))
--                   → A (ptK' (suc n))
--                   → (x : _) → A x
-- K''G-elim zero p s x = K1→Prop p s x
-- K''G-elim (suc n) p s north = s
-- K''G-elim {G = G} (suc n) {A = A} p s south =
--   subst A (merid (ptK' (suc n))) s
-- K''G-elim (suc n) {A = A} p s (merid a i) = {!!}
--   where
--   help : (a : _) → PathP (λ i → A (merid a i)) s (subst A (merid (ptK' (suc n))) s)
--   help = K''G-elim n (λ _ → isOfHLevelPathP' (suc n) (p _ ) _ _) λ i → transp (λ j → A (merid (ptK' (suc n)) (i ∧ j))) (~ i) s

-- wedgeConK : ∀ {ℓ ℓ'} (n m : ℕ) (G : Group {ℓ'}) {A : (K' G (suc n)) → (K' G (suc m)) → Type ℓ}
--           → ((x : K' G (suc n)) (y : K' G (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y))
--           → (f : (x : _) → A (ptK' (suc n)) x)
--           → (g : (x : _) → A x (ptK' (suc m)))
--           → (g (ptK' (suc n)) ≡ f (ptK' (suc m)))
--           → Σ[ F ∈ ((x : K' G (suc n)) (y : K' G (suc m)) → A x y) ]
--               ((x : K' G (suc m)) → F (ptK' (suc n)) x ≡ f x) × ((x : K' G (suc n)) → F x (ptK' (suc m)) ≡ g x)
-- wedgeConK zero zero G {A = A} hlev f g hom = F , (λ _ → refl) , testi
--   where
--   help2 : (x : ⟨ G ⟩) (y : K1 G) → PathP (λ i → A (loop x i) y)
--                                    (f y)
--                                    (f y)
--   help2 x = K1→Prop (λ _ → isOfHLevelPathP' 1 (hlev _ _) _ _)
--                      λ i → hcomp (λ k → λ {(i = i0) → hom k
--                                           ; (i = i1) → hom k})
--                                   (g (loop x i))

--   F : (x y : K1 G) → A x y
--   F =
--     K1→Set (λ x → isSetΠ λ _ → hlev _ _)
--             f
--             λ x i y → help2 x y i

--   testi : (x : K1 G) → F x base ≡ g x
--   testi = K1→Prop (λ _ → hlev _ _ _ _) (sym hom)

-- wedgeConK zero (suc m) G {A = A} hlev f g hom =
--     (λ x y → F y x)
--   , (λ x → {!λ x !})
--   , (λ x → refl)
--   where
--   Fn : (x : K1 G)  → A x north
--   Fn x = g x

--   Fs : (x : K1 G)  → A x south
--   Fs x = subst (A x) (merid (ptK' (suc m))) (g x)

--   fs≡fn : f south ≡ Fs base
--   fs≡fn = (λ i → transp (λ j → A base (merid (ptK' (suc m)) (~ i ∨ j))) (~ i) (f (merid (ptK' (suc m)) (~ i)))) ∙ cong (subst (A base) (merid (ptK' (suc m)))) (sym hom)

--   Lem : ((x : K1 G) (y : K' G (suc m)) → PathP (λ i → A x (merid y i)) (Fn x) (Fs x))
--   Lem base y i =
--       hcomp (λ k → λ { (i = i0) → sym hom k
--                       ; (i = i1) → fs≡fn k})
--             (f (merid y i))
--   Lem (loop x i) = {!help1 i!}
--     where
--     help1 : SquareP (λ i₁ j → A (loop x i₁) (merid (ptK' (suc m)) j))
--       (λ i₁ →
--          hcomp (λ { k (i₁ = i0) → hom (~ k) ; k (i₁ = i1) → fs≡fn k })
--          (f (merid (ptK' (suc m)) i₁)))
--       (λ i₁ →
--          hcomp (λ { k (i₁ = i0) → hom (~ k) ; k (i₁ = i1) → fs≡fn k })
--          (f (merid (ptK' (suc m)) i₁)))
--       (cong Fn (loop x)) (cong Fs (loop x))
-- {-
-- Goal: A (loop x i) (merid (ptK' (suc m)) j)
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ hcomp
--          (λ { i₂ (j = i0) → hom (~ i₂) ; i₂ (j = i1) → fs≡fn i₂ })
--          (f (merid (ptK' (suc m)) j))
-- i = i1 ⊢ hcomp
--          (λ { i₂ (j = i0) → hom (~ i₂) ; i₂ (j = i1) → fs≡fn i₂ })
--          (f (merid (ptK' (suc m)) j))
-- j = i0 ⊢ cong Fn (loop x) i
-- j = i1 ⊢ cong Fs (loop x) i
-- -}


--     help1 i j =
--       hcomp (λ k → λ {(i = i0) → {!!}
--                      ; (j = i1) → {!!}
--                      ; (j = i0) → {!cong Fn (loop x)!}})
--             {!cong Fs (loop x) i!}

--     help : (y : K' G (suc m)) → SquareP (λ i j → A (loop x i) (merid y j)) (Lem base y) (Lem base y) (cong Fn (loop x)) (cong Fs (loop x))
--     help = K''G-elim m (λ _ → isOfHLevelPathP' (suc m) (isOfHLevelPathP' (suc (suc m)) (hlev _ _) _ _) _ _) {!!}
--   Lem (loop-ident i i₁) = {!!}
--   Lem (loop-comp x y i i₁) = {!!}
--   -- K''G-elim m (λ _ → isOfHLevelPathP' (suc m) {!hlev x south!} _ _) {!!}
--   {- base y i =
--     hcomp (λ k → λ {(i = i0) → sym hom k
--                    ; (i = i1) → fs≡fn k})
--           (f (merid y i))
--   Lem (loop x i) y j = help y i j
--     where
--     help : (y : K' G (suc m)) → SquareP (λ i j → A (loop x i) (merid y j)) (Lem base y) (Lem base y) (cong Fn (loop x)) (cong Fs (loop x))
--     help = {!K'G-elim ? ? ?!}
--   Lem (loop-ident i i₁) y = {!!}
--   Lem (loop-comp x y₁ i i₁) y = {!!} -}

--   F : (y : Susp (K' G (suc m))) (x : K1 G)  → A x y
--   F north x = Fn x
--   F south x = Fs x
--   F (merid a i) x = {!Fs ?!} -- Lem x a i

-- wedgeConK (suc n) m G hlev f g hom = {!!}

-- open import Cubical.HITs.Sn.Properties
-- {-
-- wedgeConSn : ∀ {ℓ} (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
--           → ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y))
--           → (f : (x : _) → A (ptSn (suc n)) x)
--           → (g : (x : _) → A x (ptSn (suc m)))
--           → (g (ptSn (suc n)) ≡ f (ptSn (suc m)))
--           → Σ[ F ∈ ((x : S₊ (suc n)) (y : S₊ (suc m)) → A x y) ]
--               ((x : S₊ (suc m)) → F (ptSn (suc n)) x ≡ f x) × ((x : S₊ (suc n)) → F x (ptSn (suc m)) ≡ g x)
-- -}
-}
