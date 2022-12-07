module Cubical.TwoPlusTwo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using ( idfun )
open import Cubical.Foundations.Equiv.Properties using ( isEquivCong )
open import Cubical.Functions.Embedding using ( isEquiv→isEmbedding )

variable
  ℓ : Level
  A : Type ℓ

-- First we need "Local-global looping" (I've inlined this from a file
-- I guess I should submit to the cubical library, though it is rather
-- CCHM-specific...)

-- A lemma for squares in isEquiv
isEquivSquare : ∀ {ℓ} {A B : I → I → Type ℓ}
  (f : (i j : I) → A i j → B i j)
  {e₀₀ : isEquiv (f i0 i0)} {e₀₁ : isEquiv (f i0 i1)}
  {e₁₀ : isEquiv (f i1 i0)} {e₁₁ : isEquiv (f i1 i1)}
  (e₋₀ : PathP (λ i → isEquiv (f i i0)) e₀₀ e₁₀)
  (e₋₁ : PathP (λ i → isEquiv (f i i1)) e₀₁ e₁₁)
  (e₀₋ : PathP (λ j → isEquiv (f i0 j)) e₀₀ e₀₁)
  (e₁₋ : PathP (λ j → isEquiv (f i1 j)) e₁₀ e₁₁) →
  PathP (λ i → PathP (λ j → isEquiv (f i j)) (e₋₀ i) (e₋₁ i)) e₀₋ e₁₋
isEquivSquare f e₋₀ e₋₁ e₀₋ e₁₋ =
  isProp→PathP
    (λ i → isProp→isPropPathP (λ j → isPropIsEquiv (f i j)) (e₋₀ i) (e₋₁ i))
    e₀₋ e₁₋

-- The goal here is to construct the equivalence Kraus and Sattler
-- called the "local-global looping principle" and Licata and Brunerie
-- called the "key maneuver" for πₙSⁿ:
-- https://arxiv.org/abs/1311.4002
-- https://dlicata.wescreates.wesleyan.edu/pubs/lb13cpp/lb13cpp.pdf

-- For now I only implemented the lowest level, n=0:

-- ((x : A) → Ω (A , x)) ≃ Ω² (Type , A)

-- We could replay the "classical" argument using univalence, but the
-- resulting computational behavior will be overly
-- complicated. Instead, I want to find the "simplest" possible
-- construction using Glue and transp.

-- We have "global" 2-loops in Type, Global A = Ω² (Type , A)
Global : Type ℓ → Type (ℓ-suc ℓ)
Global A = Path (A ≡ A) refl refl

Global' : (A : Type ℓ) (p : A ≡ A) → Type (ℓ-suc ℓ)
Global' A p = PathP (λ i → p i ≡ p i) refl refl

-- and we have a "local" thing, Local A = (x : A) → Ω (A , x)
Local : Type ℓ → Type ℓ
Local A = (x : A) → x ≡ x

Local'' : (A : Type ℓ) (p : A ≡ A) → Type _
Local'' A p = PathP (λ i → p i → p i) (idfun A) (idfun A)

-- We want Global A ≃ Local A.

-- It is sometimes convenient to use "flipped" local things. (Perhaps
-- we should make this the main definition...)
Local' : Type ℓ → Type ℓ
Local' A = Path (A → A) (idfun A) (idfun A)

flip : Local A → Local' A
flip h i x = h x i

-- First, we will go from local to global, using Glue:

module _ {A : Type ℓ} (h : Local A) (i j : I) where
  globalSys : Partial (~ i ∨ i ∨ ~ j ∨ j) (Σ[ T ∈ Type ℓ ] T ≃ A)
  globalSys (i = i0) = A , idEquiv A
  globalSys (i = i1) = A , idEquiv A
  globalSys (j = i0) = A , equivEq {e = idEquiv A} {f = idEquiv A} (λ k x → h x k) i
  globalSys (j = i1) = A , idEquiv A

global : Local A → Global A
global {A = A} h i j = Glue A (globalSys h i j)

-- For the other direction, we can just transport, using the funny
-- (i ∨ ~ i) to do it in a single transp, with no hcomp:
local : Global A → Local A
local h x i = transp (λ j → h i j) (i ∨ ~ i) x

local' : Global A → Local' A
local' h i x = local h x i

SQ1 : ∀ {ℓ}
  {A : (a : I) → Type ℓ}
  (α : (a : I) → A a) →
  Type ℓ
SQ1 {A = A} α =
  PathP (λ a → A a) (α i0) (α i1)

sq1 : ∀ {ℓ}
  {A : (a : I) → Type ℓ}
  (α : (a : I) → A a) →
  SQ1 α
sq1 {A = A} α a = α a

local'' : (A : Type ℓ) (p : A ≡ A) → Global' A p → Local'' A p
local'' A p h i x = transp (λ j → h i j) (i ∨ ~ i) x

local* : (A B : Type ℓ) (p : A ≡ B)
  → PathP (λ i → p i ≡ p i) refl refl
  → PathP (λ i → p i → p i) (λ x → x) (λ x → x)
local* A B p h i x = transp (λ j → h i j) (i ∨ ~ i) x

-- Now, we can prove two lemmas which explain dependent squares over
-- "global" squares H : Global A.

-- First, using glue we can construct squares over global h from
-- squares in A with an h in the j=0 face:
globalLemma : (h : Local A)
  {x y z w : A}
  {p : x ≡ y} {q : z ≡ w} {r : x ≡ z} {s : y ≡ w} →
  PathP (λ i → h (r i) i ≡ s i) p q →
  PathP (λ i → PathP (λ j → global h i j) (r i) (s i)) p q
globalLemma h {p = p} {q = q} {r = r} {s = s} h₀ i j =
  glue (λ { (i = i0) → p j ; (i = i1) → q j ; (j = i0) → r i ; (j = i1) → s i })
       (h₀ i j)

-- Second, using another funny transp we can construct squares with an
-- extra local H in the j=0 face from squares over H:
localLemma : (H : Global A)
  {x y z w : A}
  {p : x ≡ y} {q : z ≡ w} {r : x ≡ z} {s : y ≡ w} →
  PathP (λ i → PathP (λ j → H i j) (r i) (s i)) p q →
  PathP (λ i → local H (r i) i ≡ s i) p q
localLemma H h₀ i j = transp (λ k → H i (k ∨ j)) (~ i ∨ i ∨ j) (h₀ i j)

-- Composing these two lemmas gives our first homotopy:

localGlobalLemma : (h : Local A) {x : A} (p : x ≡ x) → h x ≡ p → local (global h) x ≡ p
localGlobalLemma h p t i j =
  localLemma (global h) {p = refl} {refl} {refl} {p} (globalLemma h {p = refl} {refl} {refl} {p} (λ i j → t j i)) j i

localGlobal : (h : Local A) → local (global h) ≡ h
localGlobal h = funExt (λ x → localGlobalLemma h (h x) refl)

-- Now for the other homotopy...

-- local' H induces a path idEquiv A ≡ idEquiv A
localLine : (H : Global A) → Path (A ≃ A) (idEquiv A) (idEquiv A)
localLine H = equivEq (local' H)

-- We also get this square using the funny transp from localLemma
-- again
localSquare : (H : Global A) → PathP (λ i → PathP (λ j → H i j ≃ A) (localLine H i) (idEquiv A)) refl refl
fst (localSquare H i j) h = transp (λ l → H i (l ∨ j)) (~ i ∨ i ∨ j) h
snd (localSquare {A = A} H i j) = isEquivSquare (λ i j → fst (localSquare H i j)) (λ i → snd (localLine H i)) (λ _ → idIsEquiv A) (λ _ → idIsEquiv A) (λ _ → idIsEquiv A) i j

-- With this, we can directly prove an "extensionality principle" for
-- Global using Glue:
global≡ : (H₀ H₁ : Global A) → local H₀ ≡ local H₁ → H₀ ≡ H₁
global≡ {A = A} H₀ H₁ eq k i j =
  Glue A (λ { (i = i0) → A , idEquiv A
            ; (i = i1) → A , idEquiv A
            ; (j = i0) → A , bridge k i
            ; (j = i1) → A , idEquiv A
            ; (k = i0) → H₀ i j , localSquare H₀ i j
            ; (k = i1) → H₁ i j , localSquare H₁ i j
            })
  where
  eq' : Path (Local' A) (local' H₀) (local' H₁)
  eq' = cong flip eq

  bridge : Path (Path (A ≃ A) (idEquiv A) (idEquiv A)) (localLine H₀) (localLine H₁)
  fst (bridge k i) = eq' k i
  snd (bridge k i) = isEquivSquare (λ i k → eq' k i) (λ i → snd (localLine H₀ i)) (λ i → snd (localLine H₁ i)) refl refl i k

-- This is enough to derive the second homotopy using the first
-- homotopy. (We have not quite shown that isPathSplitEquiv local, but
-- the missing part is not actually needed to construct an
-- isomorphism.)
globalLocal : (H : Global A) → global (local H) ≡ H
globalLocal H = global≡ (global (local H)) H (localGlobal (local H))

-- So we're done!
localGlobalEquiv : Global A ≃ Local A
localGlobalEquiv = isoToEquiv (iso local global localGlobal globalLocal)

-- it will be useful to have an extensionality principle for Ω(Global A):
Ωglobal≡ : {H : Global A} (p₀ p₁ : H ≡ H) → cong local p₀ ≡ cong local p₁ → p₀ ≡ p₁
Ωglobal≡ {A = A} {H = H} p₀ p₁ = hmm
  where
  -- is this stupid?
  hmm : cong local p₀ ≡ cong local p₁ → p₀ ≡ p₁
  hmm = invIsEq (isEquiv→isEmbedding (isEquivCong localGlobalEquiv) p₀ p₁)



-- Now the "2+2=4" lemma attempt:

𝟚 : {x : A} (s : Path (Path A x x) refl refl) → s ≡ s
𝟚 s j a b =
  hcomp (λ i → λ { (j = i0) → s a b
                 ; (j = i1) → s a b
                 ; (a = i0) → s i j
                 ; (a = i1) → s i j
                 ; (b = i0) → s i j
                 ; (b = i1) → s i j
                 })
        (s a b)

𝟙-filler : {x : A} (s : Path (Path A x x) refl refl) → I → I → I → I → A
𝟙-filler {x = x} s i j a b =
  hfill (λ i → λ { (j = i0) → s (a ∧ i) b
                  ; (j = i1) → s (a ∧ i) b
                  ; (a = i0) → x
                  ; (a = i1) → s i b
                  ; (b = i0) → x
                  ; (b = i1) → x
                  })
         (inS x) i

𝟙 : {x : A} (s : Path (Path A x x) refl refl) → s ≡ s
𝟙 {x = x} s j a b =
  hcomp (λ i → λ { (j = i0) → s (a ∧ i) b
                  ; (j = i1) → s (a ∧ i) b
                  ; (a = i0) → x
                  ; (a = i1) → s i b
                  ; (b = i0) → x
                  ; (b = i1) → x
                  })
         x



𝟚fill : {x : A} (s : Path (Path A x x) refl refl) →
  PathP (λ i → PathP (λ j → PathP (λ a → PathP (λ b → A) (s i j) (s i j)) refl refl)
                     (λ a b → s a b)
                     (λ a b → s a b))
        refl
        (𝟚 s)
𝟚fill s i j a b =
  hfill (λ i → λ { (j = i0) → s a b
                 ; (j = i1) → s a b
                 ; (a = i0) → s i j
                 ; (a = i1) → s i j
                 ; (b = i0) → s i j
                 ; (b = i1) → s i j
                 })
        (inS (s a b))
        i


𝟙+𝟙=𝟚 : {x : A} (s : Path (Path A x x) refl refl) → 𝟙 s ∙ 𝟙 s ≡ 𝟚 s
𝟙+𝟙=𝟚 {x = x} s r j a b =
  hcomp (λ i → λ { (j = i0) → s a b
                  ; (j = i1) → s a b
                  ; (a = i0) → s i j
                  ; (a = i1) → s i j
                  ; (b = i0) → s i j
                  ; (b = i1) → s i j
                  ; (r = i0) → help i j a b
                  })
         (s a b)
  where -- r i a b
  pp : PathP (λ r → Cube s (𝟙 s r)
                      (λ i b → x) (λ i b → x)
                      (λ i b → x) λ i b → x)
             refl
             λ _ → s
  pp r i j k =
    hcomp (λ a → λ { (j = i0) → x
                    ; (j = i1) → s (a ∧ j) k
                    ; (i = i0) → s (j ∧ a) k
                    ; (i = i1) → 𝟙-filler s a r j k
                    ; (r = i0) → s (j ∧ a) k
                    ; (r = i1) → s (j ∧ a) k
                    ; (k = i0) → s (j ∧ a) k
                    ; (k = i1) → s (j ∧ a) k
                    })
           x

  help : PathP (λ i
    → Cube s s
            (λ j b → s i j) (λ j b → s i j)
            (λ j a → s i j) λ j a → s i j)
            refl
            (𝟙 s ∙ 𝟙 s)
  help i j a b =
    hcomp (λ r → λ { (j = i0) → s a b
                    ; (j = i1) → pp r i a b
                    ; (a = i0) → s i j
                    ; (a = i1) → s i j
                    ; (b = i0) → s i j
                    ; (b = i1) → s i j
                    ; (i = i0) → s a b
                    ; (i = i1) → compPath-filler (𝟙 s) (𝟙 s) r j a b
                    })
     (hcomp (λ r → λ { (j = i0) → s a b
                      ; (j = i1) → s a b
                      ; (a = i0) → s i j
                      ; (a = i1) → s i j
                      ; (b = i0) → s i j
                      ; (b = i1) → s i j
                      ; (i = i0) → s a b
                      ; (i = i1) →  pp j r a b
                      })
           (hcomp (λ r → λ { (j = i0) → s a b
                      ; (j = i1) → s a b
                      ; (a = i0) → s i j
                      ; (a = i1) → s i j
                      ; (b = i0) → s i j
                      ; (b = i1) → s i j
                      ; (i = i0) → s a b
                      ; (i = i1) → s a b
                      })
                   {!!}))

𝟚transp-lemma : {x : A} (s : Path (Path A x x) refl refl) →
  transport (λ i → PathP (λ j → PathP (λ a → PathP (λ b → A) (s i j) (s i j)) refl refl) (λ a b → s a b) (λ a b → s a b)) refl
  ≡ 𝟚 s
𝟚transp-lemma {A = A} {x = x} s i j a b =
  hcomp (λ k → λ { (i = i0) → lemma k j a b
                 ; (i = i1) → 𝟚fill s k j a b
                 ; (j = i0) → s a b
                 ; (j = i1) → s a b
                 ; (a = i0) → s k j
                 ; (a = i1) → s k j
                 ; (b = i0) → s k j
                 ; (b = i1) → s k j
                 })
        (s a b)
  where
  lemma : PathP (λ i → PathP (λ j → PathP (λ a → PathP (λ b → A) (s i j) (s i j)) refl refl) (λ a b → s a b) (λ a b → s a b))
                refl
                (transport (λ i → PathP (λ j → PathP (λ a → PathP (λ b → A) (s i j) (s i j)) refl refl) (λ a b → s a b) (λ a b → s a b)) refl)
  lemma = transpFill {A = A} i0 (λ i → inS (PathP (λ j → PathP (λ a → PathP (λ b → A) (s i j) (s i j)) refl refl) (λ a b → s a b) (λ a b → s a b))) refl



module Hope {ℓ}
  (C : Type ℓ)
  (D : Global C)
  (hyp : ((x : C) → Path (PathP (λ i → local D x i ≡ local D x i)
                          (local D x) (local D x))
                          (λ i j → local D (local D x i) j)
                          (λ i j → local D (local D x j) i)))
  where
  -- all of these steps seem more or less plausible to me, but I don't
  -- know how to actually do most of them yet
  goal₃ : Path (Path (Local C) (local D) (local D)) (cong local (𝟚 D)) refl
  goal₃ =
    cong local (𝟚 D)
      ≡⟨ refl ⟩
    (λ i x j → hcomp (λ k → λ { (i = i0) → transp (λ _ → C) k (transp (λ _ → C) k (transp (λ l → D j l) (~ j ∨ j) x))
                              ; (i = i1) → transp (λ _ → C) k (transp (λ _ → C) k (transp (λ l → D j l) (~ j ∨ j) x))
                              ; (j = i0) → transp (λ l → D (l ∨ k) i) k (transp (λ l → D (k ∨ ~ l) i) k x)
                              ; (j = i1) → transp (λ l → D (l ∨ k) i) k (transp (λ l → D (k ∨ ~ l) i) k x)
                              })
                 (transp (λ k → D k i) i0
                   (hcomp
                     (λ k → λ { (i = i0) → transp (λ l → D j (l ∨ k)) k (transp (λ _ → D j k) i0 (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x))
                              ; (i = i1) → transp (λ l → D j (l ∨ k)) k (transp (λ _ → D j k) i0 (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x))
                              ; (j = i0) → transp (λ _ → C) k (transp (λ l → D (~ l) i) i0 x)
                              ; (j = i1) → transp (λ _ → C) k (transp (λ l → D (~ l) i) i0 x)
                              })
                     (transp (λ k → D j k) i0 (transp (λ k → D (~ k) i) i0 x)))))
      -- applying the hypothesis (somehow??) to move the innermost
      -- `transp (λ k → D (~ k) i)` up past the `transp (λ k → D j k)`:
      ≡⟨ {!!} ⟩
      {!!} ≡⟨ {!cong local (𝟚 D)!} ⟩
    (λ i x j → hcomp (λ k → λ { (i = i0) → transp (λ _ → C) k (transp (λ _ → C) k (transp (λ l → D j l) (~ j ∨ j) x))
                              ; (i = i1) → transp (λ _ → C) k (transp (λ _ → C) k (transp (λ l → D j l) (~ j ∨ j) x))
                              ; (j = i0) → transp (λ l → D (l ∨ k) i) k (transp (λ l → D (k ∨ ~ l) i) k x)
                              ; (j = i1) → transp (λ l → D (l ∨ k) i) k (transp (λ l → D (k ∨ ~ l) i) k x)
                              })
                 (transp (λ k → D k i) i0
                   (hcomp
                     (λ k → λ { (i = i0) → transp (λ _ → C) i0 (transp (λ l → D j (l ∨ k)) k (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x))
                              ; (i = i1) → transp (λ _ → C) i0 (transp (λ l → D j (l ∨ k)) k (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x))
                              ; (j = i0) → transp (λ l → D (~ l) i) i0 (transp (λ _ → C) k x)
                              ; (j = i1) → transp (λ l → D (~ l) i) i0 (transp (λ _ → C) k x)
                              })
                     (transp (λ k → D (~ k) i) i0 (transp (λ k → D j k) i0 x)))))
      -- pulling (transp (λ k → D (~ k) i) i0) out of the comp -- this
      -- is just a "pres" I think?
      ≡⟨ {!!} ⟩
    (λ i x j → hcomp (λ k → λ { (i = i0) → transp (λ _ → C) k
                                              (transp (λ _ → C) k
                                               (transp (λ l → D j l) (~ j ∨ j) x))
                              ; (i = i1) → transp (λ _ → C) k
                                             (transp (λ _ → C) k
                                              (transp (λ l → D j l) (~ j ∨ j) x))
                              ; (j = i0) → transp (λ l → D (l ∨ k) i) k
                                             (transp (λ l → D (k ∨ ~ l) i) k x)
                              ; (j = i1) → transp (λ l → D (l ∨ k) i) k
                                             (transp (λ l → D (k ∨ ~ l) i) k x)
                              })
                 (transp (λ k → D k i) i0
                   (transp (λ k → D (~ k) i) i0
                     (hcomp
                       (λ k → λ { (i = i0) → transp (λ l → D j (l ∨ k)) k
                                               (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x)
                                ; (i = i1) → transp (λ l → D j (l ∨ k)) k
                                               (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x)
                                ; (j = i0) → transp (λ _ → C) k x
                                ; (j = i1) → transp (λ _ → C) k x
                                })
                       (transp (λ k → D j k) i0 x)))))
      -- cancelling `transp (λ k → D k i) i0 (transp (λ k → D (~ k) i) i0 ...)`
      ≡⟨ {!!} ⟩
    (λ i x j → hcomp (λ k → λ { (i = i0) → transp (λ l → D j l) (~ j ∨ j) x
                              ; (i = i1) → transp (λ l → D j l) (~ j ∨ j) x
                              ; (j = i0) → x
                              ; (j = i1) → x
                              })
                 (hcomp
                   (λ k → λ { (i = i0) → transp (λ l → D j (l ∨ k)) k
                                            (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x)
                            ; (i = i1) → transp (λ l → D j (l ∨ k)) k
                                            (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x)
                            ; (j = i0) → transp (λ _ → C) k x
                            ; (j = i1) → transp (λ _ → C) k x
                            })
                   (transp (λ k → D j k) i0 x)))
      -- cancelling the trivial hcomp:
      ≡⟨ {!!} ⟩
    (λ i x j → hcomp
                 (λ k → λ { (i = i0) → transp (λ l → D j (l ∨ k)) k
                                          (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x)
                          ; (i = i1) → transp (λ l → D j (l ∨ k)) k
                                          (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x)
                          ; (j = i0) → transp (λ _ → C) k x
                          ; (j = i1) → transp (λ _ → C) k x
                          })
                 (transp (λ k → D j k) i0 x))
      -- this is the most mysterious step to me, it looks vaguely
      -- plausible at least...?
      ≡⟨ (λ r i x j → hcomp
                 (λ k → λ { (i = i0) → transp (λ l → D j (l ∨ k)) k
                                         (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x)
                          ; (i = i1) → transp (λ l → D j (l ∨ k)) k
                                         (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x)
                          ; (j = i0) → transp (λ _ → C) k x
                          ; (j = i1) → transp (λ _ → C) k x
                          ; (r = i1) → transp (λ l → D j (l ∨ k)) k
                                         (transp (λ l → D j (k ∧ l)) (~ j ∨ j ∨ ~ k) x)
                          })
                 (transport (λ l → D j l) x)) ⟩
    (λ _ x j → transp (λ k → D j k) (~ j ∨ j) x)
      ≡⟨ refl ⟩
    refl
      ∎

  goal₂ : Path (Path (Global C) D D) (𝟚 D) refl
  goal₂ = Ωglobal≡ (𝟚 D) refl goal₃

  goal₁ : Path (Path (Global C) (λ a b → D a b) (λ a b → D a b))
               (transport (λ i → PathP (λ j → PathP (λ a → PathP (λ b → Type ℓ) (D i j) (D i j)) refl refl) (λ a b → D a b) (λ a b → D a b)) refl)
               refl
  goal₁ = Ωglobal≡ _ _ (cong (cong local) (𝟚transp-lemma D ∙ goal₂))

  goal : PathP (λ i → PathP (λ j → PathP (λ a → PathP (λ b → Type ℓ) (D i j) (D i j)) refl refl) (λ a b → D a b) (λ a b → D a b)) refl refl
  goal = toPathP goal₁

Csq : {x y z : A} → x ≡ y → y ≡ z → Type _
Csq p q = PathP (λ i → p i ≡ q i) p q

2+2=4 : (h : (x : A) → x ≡ x) →
  ((x : A) → Path (Csq (h x) (h x)) (λ i j → h (h x i) j) (λ i j → h (h x j) i)) →
  PathP (λ i → PathP (λ j → PathP (λ a → PathP (λ b → (Type ℓ)) (global h i j) (global h i j)) refl refl) (λ a b → global h a b) (λ a b → global h a b)) refl refl
2+2=4 {A = A} h comm = Hope.goal _ (global h) fun
  where
  fun : (x : A) → Path (Csq (local (global h) x) (local (global h) x)) (λ i j → local (global h) (local (global h) x i) j) (λ i j → local (global h) (local (global h) x j) i)
  fun x =
    transp
      (λ k → Path (Csq (localGlobal h (~ k) x) (localGlobal h (~ k) x)) (λ i j → localGlobal h (~ k) (localGlobal h (~ k) x i) j) (λ i j → localGlobal h (~ k) (localGlobal h (~ k) x j) i))
      i0
      (comm x)


conglocaltwo : ∀ {ℓ} {A : Type ℓ}
  (h : (x : A) → x ≡ x)
  → ((x : A) → Path (Csq (h x) (h x)) (λ i j → h (h x i) j) (λ i j → h (h x j) i))
  → Path (local (global h) ≡ local (global h))
       (cong local (𝟚 (global h)))
       refl
conglocaltwo {ℓ = ℓ} {A = A} h hyp i j =
  comp (λ k → (x : global h k j) → x ≡ x)
    (λ k → λ {(i = i0) → λ s i → local'' (global h k j) _ (𝟚fill (global h) k j) i s
                 ; (i = i1) → λ x i → {!transp (λ j → (global h) i j) (i ∨ ~ i) ?!}
                 ; (j = i0) → local (global h)
                 ; (j = i1) → local (global h)})
        {!local''!}
  where
  s : 𝟚 (global h) ≡ {!cong global ...!} ∙ {!cong global ...!}
  s = {!
i = i0 ⊢ local (𝟚 (global h) j) x
i = i1 ⊢ refl j x
j = i0 ⊢ local (global h) x
j = i1 ⊢ local (global h) x!}
