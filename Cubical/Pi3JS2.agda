module Cubical.Pi3JS2 where

-- Things below:

-- 2+2=4 -- conjecture I have postulated here :(
-- J₃S¹, J₂S² -- "Reduced" versions of word length filtrations of James constructions
-- L₂J₂S² -- word-length filtration of a model for ΩJ₂S² (?)
-- compute-π₂JS¹ -- π₂JS¹ (≃ π₃S²) → ℤ    (on types only so far, not groups)
-- compute-π₃JS² -- π₃JS² (≃ π₄S³) → Bool (ditto)
-- 𝟚 -- should be a "Brunerie" element, generator of kernel of π₃S² → π₄S³
-- 𝟙 -- should be a generator of π₃S²
-- nontriv-π₄S³ -- nontrivial element of π₄S³ induced by 𝟙

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using ( isProp→isPropPathP )
open import Cubical.Homotopy.Connected
open import Cubical.Data.Nat.Base hiding ( elim )
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.HITs.S1 hiding ( elim ; rec )
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.Data.Int

Ω Ω² Ω³ Ω⁴ : ∀ {ℓ} (A : Type ℓ) (a : A) → Type ℓ
Ω A a = a ≡ a
Ω² A a = Ω (Ω A a) refl
Ω³ A a = Ω (Ω² A a) refl
Ω⁴ A a = Ω (Ω³ A a) refl

-- Defining my own truncations (see comment at j₃s¹-loops' below)

-- 1-truncation (HoTT Book indexing)
data ∥_∥₁ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∥ A ∥₁
  trunc : isOfHLevel 3 ∥ A ∥₁

-- 2-truncation
data ∥_∥₂ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∥ A ∥₂
  trunc : isOfHLevel 4 ∥ A ∥₂

data ∥_∥₃ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∥ A ∥₃
  trunc : isOfHLevel 5 ∥ A ∥₃

-- 4-truncation
data ∥_∥₄ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∥ A ∥₄
  trunc : isOfHLevel 6 ∥ A ∥₄

module Trunc₁ {ℓ} {A : Type ℓ}
  where
  module _  {ℓ'}
    {P : ∥ A ∥₁ → Type ℓ'}
    (lev : ∀ x → isOfHLevel 3 (P x))
    (fun : ∀ x → P ∣ x ∣)
    where
    elim : ∀ x → P x
    elim ∣ x ∣ = fun x
    elim (trunc a b c d e f g h i) = fst triv g h i
      where
      triv : isContr (PathP (λ g → PathP (λ h → PathP (λ i → P (trunc a b c d e f g h i)) (elim a) (elim b)) (λ i → elim (c i)) (λ i → elim (d i))) (λ h i → elim (e h i)) (λ h i → elim (f h i)))
      triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (lev _) _ _) _ _) _ _

  module _ {ℓ'}
    {B : Type ℓ'}
    (lev : isOfHLevel 3 B)
    (fun : A → B)
    where
    rec : ∥ A ∥₁ → B
    rec = elim (λ _ → lev) fun

  module _ {ℓ'}
    {B : Type ℓ'}
    (fun : A → B)
    where
    map : ∥ A ∥₁ → ∥ B ∥₁
    map = rec trunc (λ x → ∣ fun x ∣)

module Trunc₂ {ℓ} {A : Type ℓ}
  where
  module _  {ℓ'}
    {P : ∥ A ∥₂ → Type ℓ'}
    (lev : ∀ x → isOfHLevel 4 (P x))
    (fun : ∀ x → P ∣ x ∣)
    where
    elim : ∀ x → P x
    elim ∣ x ∣ = fun x
    elim (trunc a b c d e f g h i j k l) = fst triv i j k l
      where
      triv : isContr (PathP (λ i → PathP (λ j → PathP (λ k → PathP (λ l → P (trunc a b c d e f g h i j k l)) (elim a) (elim b)) (λ l → elim (c l)) (λ l → elim (d l))) (λ k l → elim (e k l)) (λ k l → elim (f k l))) (λ j k l → elim (g j k l)) (λ j k l → elim (h j k l)))
      triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (lev _) _ _) _ _) _ _) _ _

  module _ {ℓ'}
    {B : Type ℓ'}
    (lev : isOfHLevel 4 B)
    (fun : A → B)
    where
    rec : ∥ A ∥₂ → B
    rec = elim (λ _ → lev) fun

  module _ {ℓ'}
    {B : Type ℓ'}
    (fun : A → B)
    where
    map : ∥ A ∥₂ → ∥ B ∥₂
    map = rec trunc (λ x → ∣ fun x ∣)

module Trunc₃ {ℓ} {A : Type ℓ}
  where
  module _  {ℓ'}
    {P : ∥ A ∥₃ → Type ℓ'}
    (lev : ∀ x → isOfHLevel 5 (P x))
    (fun : ∀ x → P ∣ x ∣)
    where
    elim : ∀ x → P x
    elim ∣ x ∣ = fun x
    elim (trunc a b c d e f g h i j k l m n o) = fst triv k l m n o
      where
      triv : isContr (PathP (λ k → PathP (λ l → PathP (λ m → PathP (λ n → PathP (λ o → P (trunc a b c d e f g h i j k l m n o)) (elim a) (elim b)) (λ o → elim (c o)) (λ o → elim (d o))) (λ n o → elim (e n o)) (λ n o → elim (f n o))) (λ m n o → elim (g m n o)) (λ m n o → elim (h m n o))) (λ l m n o → elim (i l m n o)) (λ l m n o → elim (j l m n o)))
      triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (isOfHLevelPathP' 4 (lev _) _ _) _ _) _ _) _ _) _ _

  module _ {ℓ'}
    {B : Type ℓ'}
    (lev : isOfHLevel 5 B)
    (fun : A → B)
    where
    rec : ∥ A ∥₃ → B
    rec = elim (λ _ → lev) fun

  module _ {ℓ'}
    {B : Type ℓ'}
    (fun : A → B)
    where
    map : ∥ A ∥₃ → ∥ B ∥₃
    map = rec trunc (λ x → ∣ fun x ∣)

module Trunc₄ {ℓ} {A : Type ℓ}
  where
  module _  {ℓ'}
    {P : ∥ A ∥₄ → Type ℓ'}
    (lev : ∀ x → isOfHLevel 6 (P x))
    (fun : ∀ x → P ∣ x ∣)
    where
    elim : ∀ x → P x
    elim ∣ x ∣ = fun x
    elim (trunc a b c d e f g h i j k l m n o p q r) = fst triv m n o p q r
      where
      triv : isContr (PathP (λ m → PathP (λ n → PathP (λ o → PathP (λ p → PathP (λ q → PathP (λ r → P (trunc a b c d e f g h i j k l m n o p q r)) (elim a) (elim b)) (λ r → elim (c r)) (λ r → elim (d r))) (λ q r → elim (e q r)) (λ q r → elim (f q r))) (λ p q r → elim (g p q r)) (λ p q r → elim (h p q r))) (λ o p q r → elim (i o p q r)) (λ o p q r → elim (j o p q r))) (λ n o p q r → elim (k n o p q r)) (λ n o p q r → elim (l n o p q r)))
      triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (isOfHLevelPathP' 4 (isOfHLevelPathP' 5 (lev _) _ _) _ _) _ _) _ _) _ _) _ _

  module _ {ℓ'}
    {B : Type ℓ'}
    (lev : isOfHLevel 6 B)
    (fun : A → B)
    where
    rec : ∥ A ∥₄ → B
    rec = elim (λ _ → lev) fun

  module _ {ℓ'}
    {B : Type ℓ'}
    (fun : A → B)
    where
    map : ∥ A ∥₄ → ∥ B ∥₄
    map = rec trunc (λ x → ∣ fun x ∣)

  Code : A → ∥ A ∥₄ → TypeOfHLevel ℓ 5
  Code x = rec (isOfHLevelTypeOfHLevel 5) λ y → (∥ x ≡ y ∥₃ , trunc) 

  encode₁ : (x : A) (y : ∥ A ∥₄) → ∣ x ∣ ≡ y → fst (Code x y)
  encode₁ x y p = transp (λ i → fst (Code x (p i))) i0 ∣ refl ∣

  encode₀ : {x : A} → Path ∥ A ∥₄ ∣ x ∣ ∣ x ∣ → ∥ x ≡ x ∥₃
  encode₀ {x} = encode₁ x ∣ x ∣



-- "constant" squares (as in constcubes.ctt, also like rotLoop in
-- Cubical.HITs.S1.) Should come up with a better name. Diamonds?
Csq : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → Type ℓ
Csq p q = PathP (λ i → p i ≡ q i) p q

-- the canonical constant square
csq : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → Ω² A y → Csq p q
csq p q r i j = hcomp (λ k → λ { (i = i0) → p (~ k ∨ j)
                               ; (i = i1) → q (k ∧ j)
                               ; (j = i0) → p (~ k ∨ i)
                               ; (j = i1) → q (k ∧ i)
                               })
                      (r i j)

csq⁻¹ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → Csq p q → Ω² A y
csq⁻¹ p q r i j = hcomp (λ k → λ { (i = i0) → p (k ∨ j)
                                 ; (i = i1) → q (~ k ∧ j)
                                 ; (j = i0) → p (k ∨ i)
                                 ; (j = i1) → q (~ k ∧ i)
                                 })
                        (r i j)

-- "csq" and "csq⁻¹" are slight simplifications of transport over this
-- path in the universe:
csqPath : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → Ω² A y ≡ Csq p q
csqPath {A = A} p q k = PathP (λ i → PathP (λ j → A) (p (~ k ∨ i)) (q (k ∧ i))) (λ j → p (~ k ∨ j)) (λ j → q (k ∧ j))

-- Side note: if we draw a picture of the homotopy
-- Path (Ω² A y) (csq⁻¹ (csq refl)) refl, by tracing the midpoint of
-- the paths p/q, the picture seems to say "two circles are equal to
-- nothing"...

-- Using csqPath we can build a "constant cube" with all sides the
-- same 2-loop:
ccube : ∀ {ℓ} {A : Type ℓ} {x : A} (p : Ω² A x) →
  PathP (λ i → PathP (λ j → p i j ≡ p i j) (λ k → p i k) (λ k → p i k)) (λ j k → p j k) (λ j k → p j k)
ccube p i = transp (λ k → csqPath (p i) (p i) k) (i ∨ ~ i) p



-- We will need the first level of "local-global looping" (as Kraus
-- and Sattler called it.) This is also what Licata and Brunerie
-- called the "key maneuver" for πₙSⁿ (this one's for π₂S²).

module _ {ℓ} {A : Type ℓ} (h : (x : A) → x ≡ x) (i j : I) where
  globalSys : Partial (~ i ∨ i ∨ ~ j ∨ j) (Σ[ T ∈ Type ℓ ] T ≃ A)
  globalSys (i = i0) = A , idEquiv A
  globalSys (i = i1) = A , idEquiv A
  globalSys (j = i0) = A , equivEq {e = idEquiv A} {f = idEquiv A} (λ k x → h x k) i
  globalSys (j = i1) = A , idEquiv A

global : ∀ {ℓ} {A : Type ℓ} → ((x : A) → x ≡ x) → Ω² (Type _) A
global {A = A} h i j = Glue A (globalSys h i j)



-- The following "2+2=4" lemma is the crux of the π₄S³ computer
-- below. I don't know how to construct it yet. I am not even certain
-- it is possible... but I have some evidence for it: I can define
-- part of a map in the easy direction, and this map "looks like it
-- should be an equivalence"... Unfortunately, what we need below is a
-- map in the hard direction.

-- The 2+2=4 lemma should construct 4-cells in the universe, attached
-- to some 2-cell in the manner indicated by the lovely redtt syntax:

--     [i j a b] type [∂[i j] → H a b, ∂[a b] → H i j]

-- We can assume the 2-cell is given by local-global looping. This
-- suggests thinking of local-global looping above as a special case
-- of the "1+1=2" lemma...

-- I conjecture that it goes like this:

postulate
  2+2=4 : ∀ {ℓ} {A : Type ℓ} (h : (x : A) → x ≡ x) →
    -- given 3-cells at every point, identifying the 2-cells from h
    -- with their transpose
    ((x : A) → Path (Csq (h x) (h x)) (λ i j → h (h x i) j) (λ i j → h (h x j) i)) →
    -- we get the 4-cell in the universe
    PathP (λ i → PathP (λ j → PathP (λ a → PathP (λ b → (Type ℓ)) (global h i j) (global h i j)) refl refl) (λ a b → global h a b) (λ a b → global h a b)) refl refl


2+2=4' : {!∀ {ℓ} {A : Type ℓ} (h : (x : A) → x ≡ x) →
    -- given 3-cells at every point, identifying the 2-cells from h
    -- with their transpose
    ((x : A) → Path (Csq (h x) (h x)) (λ i j → h (h x i) j) (λ i j → h (h x j) i)) →
    -- we get the 4-cell in the universe
    PathP (λ i → PathP (λ j → PathP (λ a → PathP (λ b → (Type ℓ)) (global h i j) (global h i j)) refl refl) (λ a b → global h a b) (λ a b → global h a b)) refl refl!}
2+2=4' = {!local!}

-- I will also need a lemma which helps constructing paths in
-- Ω²Type. It requires a few things:

isEquivLine : ∀ {ℓ} {A B : I → Type ℓ}
  (f : (i : I) → A i → B i)
  (e₀ : isEquiv (f i0)) (e₁ : isEquiv (f i1)) →
  PathP (λ i → isEquiv (f i)) e₀ e₁
isEquivLine f e₀ e₁ =
  isProp→PathP
    (λ i → isPropIsEquiv (f i))
    e₀ e₁

isEquivSquare : ∀ {ℓ} {A B : I → I → Type ℓ}
  (f : (i j : I) → A i j → B i j)
  {e₀₀ : isEquiv (f i0 i0)}
  {e₀₁ : isEquiv (f i0 i1)}
  {e₁₀ : isEquiv (f i1 i0)}
  {e₁₁ : isEquiv (f i1 i1)}
  (e₋₀ : PathP (λ i → isEquiv (f i i0)) e₀₀ e₁₀)
  (e₋₁ : PathP (λ i → isEquiv (f i i1)) e₀₁ e₁₁)
  (e₀₋ : PathP (λ j → isEquiv (f i0 j)) e₀₀ e₀₁)
  (e₁₋ : PathP (λ j → isEquiv (f i1 j)) e₁₀ e₁₁) →
  PathP (λ i → PathP (λ j → isEquiv (f i j)) (e₋₀ i) (e₋₁ i)) e₀₋ e₁₋
isEquivSquare f e₋₀ e₋₁ e₀₋ e₁₋ =
  isProp→PathP
    (λ i → isProp→isPropPathP (λ j → isPropIsEquiv (f i j)) (e₋₀ i) (e₋₁ i))
    e₀₋ e₁₋

-- the "local" direction of "local-global looping" (only needed here
-- for global-eq-lemma, for now)
local :  ∀ {ℓ} {A : Type ℓ} → Ω² (Type ℓ) A → (x : A) → x ≡ x
local h x i = transp (λ j → h i j) (i ∨ ~ i) x

local' : ∀ {ℓ} {A : Type ℓ} → Ω² (Type _) A → Path (A → A) (λ x → x) (λ x → x)
local' h i x = local h x i

-- (this lemma is one half of a proof that local and global are inverses)
global-eq-lemma : ∀ {ℓ} {A : Type ℓ} (H₀ H₁ : Ω² (Type ℓ) A) → local H₀ ≡ local H₁ → H₀ ≡ H₁
global-eq-lemma {A = A} H₀ H₁ eq k i j =
  Glue A (λ { (i = i0) → A , idEquiv A
            ; (i = i1) → A , idEquiv A
            ; (j = i0) → A , bridge k i
            ; (j = i1) → A , idEquiv A
            ; (k = i0) → H₀ i j , localThingy H₀ i j
            ; (k = i1) → H₁ i j , localThingy H₁ i j
            })
  where
  isEquivLocal : (H : Ω² (Type _) A) → PathP (λ i → isEquiv (local' H i)) (idIsEquiv A) (idIsEquiv A)
  isEquivLocal H = isEquivLine (λ i → local' H i) (idIsEquiv A) (idIsEquiv A)

  localEquiv : (H : Ω² (Type _) A) → Path (A ≃ A) (idEquiv A) (idEquiv A)
  localEquiv H i = (local' H i , isEquivLocal H i)

  localThingy : (H : Ω² (Type _) A) → PathP (λ i → PathP (λ j → H i j ≃ A) (localEquiv H i) (idEquiv A)) refl refl
  fst (localThingy H i j) h = transp (λ l → H i (l ∨ j)) (~ i ∨ i ∨ j) h -- the funny transp from local-lemma again
  snd (localThingy H i j) = isEquivSquare (λ i j → fst (localThingy H i j)) (isEquivLocal H) (λ _ → idIsEquiv A) (λ _ → idIsEquiv A) (λ _ → idIsEquiv A) i j

  eq' : Path (Path (A → A) (λ x → x) (λ x → x)) (local' H₀) (local' H₁)
  eq' = cong (λ h x i → h i x) eq

  bridge : Path (Path (A ≃ A) (idEquiv A) (idEquiv A)) (localEquiv H₀) (localEquiv H₁)
  bridge k i = (eq' k i , isEquivSquare (λ i k → eq' k i) (isEquivLocal H₀) (isEquivLocal H₁) refl refl i k)



-- I will use these two "reduced" versions of Brunerie's James
-- construction:

-- JS¹ ≃ ΩS²
data JS¹ : Type where
  base : JS¹
  loops : (x : JS¹) → Ω JS¹ x

-- JS² ≃ ΩS³
data JS² : Type where
  base : JS²
  surfs : (x : JS²) → Ω² JS² x

-- TODO construct ΩS² ≃ JS¹ and ΩS³ ≃ JS²...

-- But the main types of interest here are these "reduced" versions of
-- the word-length filtrations:

data J₃S¹ : Type where
  base : J₃S¹
  loop : PathP (λ i → J₃S¹) base base
  loop₂ : PathP (λ i → PathP (λ j → J₃S¹) (loop i) (loop i)) (λ j → loop j) (λ j → loop j)
  loop₃ : PathP (λ i → PathP (λ j → PathP (λ k → J₃S¹) (loop₂ i j) (loop₂ i j)) (λ k → loop₂ i k) (λ k → loop₂ i k)) (λ j k → loop₂ j k) (λ j k → loop₂ j k)

data J₂S² : Type where
  base : J₂S²
  surf : PathP (λ i → PathP (λ j → J₂S²) base base) refl refl
  surf₂ : PathP (λ i → PathP (λ j → PathP (λ a → PathP (λ b → J₂S²) (surf i j) (surf i j)) refl refl) (λ a b → surf a b) (λ a b → surf a b)) refl refl

-- TODO try relating these to Cubical.HITs.James?

-- Now, there are obvious nice maps:

j₃s¹→js¹ : J₃S¹ → JS¹
j₃s¹→js¹ base = base
j₃s¹→js¹ (loop i) = loops base i
j₃s¹→js¹ (loop₂ i j) = loops (loops base i) j
j₃s¹→js¹ (loop₃ i j k) = loops (loops (loops base i) j) k

j₂s²→js² : J₂S² → JS²
j₂s²→js² base = base
j₂s²→js² (surf i j) = surfs base i j
j₂s²→js² (surf₂ i j a b) = surfs (surfs base i j) a b

-- We should be able to prove that these maps are as connected as
-- Brunerie's versions: 2- and 4-connected respectively. I tried and
-- failed to prove this so far...

-- But we can at least prove directly that the maps induce
-- equivalences on 2- and 4-truncations, and that should be enough for
-- me for now.

-- Unfortunately, when I tried to do this using the Cubical library's
-- truncations, typechecking was very slow for the J₃S¹ case, and
-- seemed to run forever for the J₂S² case. Defining my own
-- special-case truncation types seemed to solve the problem.

j₃s¹-loops' : (x : J₃S¹) → Ω (∥ J₃S¹ ∥₂) ∣ x ∣
j₃s¹-loops' base l = ∣ loop l ∣
j₃s¹-loops' (loop i) l = ∣ loop₂ i l ∣
j₃s¹-loops' (loop₂ i j) l = ∣ loop₃ i j l ∣
j₃s¹-loops' (loop₃ i j k) l = fst triv i j k l
  where
  -- the 2-truncation of J₃S¹ is just enough for this:
  triv : isContr (PathP (λ i → PathP (λ j → PathP (λ k → PathP (λ l → ∥ J₃S¹ ∥₂) ∣ loop₃ i j k ∣ ∣ loop₃ i j k ∣) (λ l → ∣ loop₃ i j l ∣) (λ l → ∣ loop₃ i j l ∣)) (λ k l → ∣ loop₃ i k l ∣) (λ k l → ∣ loop₃ i k l ∣)) (λ j k l → ∣ loop₃ j k l ∣) (λ j k l → ∣ loop₃ j k l ∣))
  triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 trunc _ _) _ _) _ _) _ _

j₃s¹-loops : (x : ∥ J₃S¹ ∥₂) → Ω (∥ J₃S¹ ∥₂) x
j₃s¹-loops =
  Trunc₂.elim
    (λ x → isOfHLevelPathP 4 trunc x x)
    j₃s¹-loops'

js¹→j₃s¹ : JS¹ → ∥ J₃S¹ ∥₂
js¹→j₃s¹ base = ∣ base ∣
js¹→j₃s¹ (loops x i) = j₃s¹-loops (js¹→j₃s¹ x) i

j₃s¹-homotopy₁ : ∀ x → js¹→j₃s¹ (j₃s¹→js¹ x) ≡ ∣ x ∣
j₃s¹-homotopy₁ base = refl
j₃s¹-homotopy₁ (loop i) = refl
j₃s¹-homotopy₁ (loop₂ i j) = refl
j₃s¹-homotopy₁ (loop₃ i j k) = refl

js¹-loops-trunc : (x : ∥ JS¹ ∥₂) → x ≡ x
js¹-loops-trunc =
  Trunc₂.elim
    (λ x → isOfHLevelPathP 4 trunc x x)
    (λ x → cong {B = λ _ → ∥ JS¹ ∥₂} ∣_∣ (loops x))

j₃s¹-lemma' : (x : J₃S¹) → Path (Path (∥ JS¹ ∥₂) ∣ j₃s¹→js¹ x ∣ ∣ j₃s¹→js¹ x ∣)
                               (λ i → Trunc₂.map j₃s¹→js¹ (j₃s¹-loops' x i))
                               (λ i → ∣ loops (j₃s¹→js¹ x) i ∣)
j₃s¹-lemma' base = refl
j₃s¹-lemma' (loop i) = refl
-- after this, trivial by hlevel
j₃s¹-lemma' (loop₂ i j) = refl
j₃s¹-lemma' (loop₃ i j k) = fst triv i j k
  where
  triv : isContr (PathP (λ i → PathP (λ j → PathP (λ k → Path (Path (∥ JS¹ ∥₂) ∣ j₃s¹→js¹ (loop₃ i j k) ∣ ∣ j₃s¹→js¹ (loop₃ i j k) ∣) (λ a → Trunc₂.map j₃s¹→js¹ (j₃s¹-loops' (loop₃ i j k) a)) (λ a → ∣ loops (j₃s¹→js¹ (loop₃ i j k)) a ∣)) refl refl) (λ _ → refl) (λ _ → refl)) (λ _ _ → refl) (λ _ _ → refl))
  triv = isOfHLevelPathP 0 (isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 trunc _ _) _ _) _ _) _ _) _ _

j₃s¹-lemma : (x : ∥ J₃S¹ ∥₂) → Path (Path (∥ JS¹ ∥₂) (Trunc₂.map j₃s¹→js¹ x) (Trunc₂.map j₃s¹→js¹ x))
                                    (λ i → Trunc₂.map j₃s¹→js¹ (j₃s¹-loops x i))
                                    (js¹-loops-trunc (Trunc₂.map j₃s¹→js¹ x))
j₃s¹-lemma =
  Trunc₂.elim
    (λ x → isOfHLevelPathP 4 (isOfHLevelPathP 4 trunc _ _) _ _)
    j₃s¹-lemma'

j₃s¹-homotopy₂ : ∀ x → Trunc₂.map j₃s¹→js¹ (js¹→j₃s¹ x) ≡ ∣ x ∣
j₃s¹-homotopy₂ base = refl
j₃s¹-homotopy₂ (loops x i) = step₄ x (j₃s¹-homotopy₂ x) i
  where
  step₂ : (x : JS¹) (y : Trunc₂.map j₃s¹→js¹ (js¹→j₃s¹ x) ≡ ∣ x ∣) → PathP (λ j → y j ≡ y j) (js¹-loops-trunc (Trunc₂.map j₃s¹→js¹ (js¹→j₃s¹ x))) (λ i → ∣ loops x i ∣)
  step₂ x y j i = js¹-loops-trunc (y j) i

  step₃ : (x : JS¹) (y : Trunc₂.map j₃s¹→js¹ (js¹→j₃s¹ x) ≡ ∣ x ∣) → PathP (λ j → y j ≡ y j) (λ i → Trunc₂.map j₃s¹→js¹ (j₃s¹-loops (js¹→j₃s¹ x) i)) (λ i → ∣ loops x i ∣)
  step₃ x y =
    transp (λ k → PathP (λ j → y j ≡ y j) (λ i → j₃s¹-lemma (js¹→j₃s¹ x) (~ k) i) (λ i → ∣ loops x i ∣))
           i0
           (step₂ x y)

  step₄ : (x : JS¹) (y : Trunc₂.map j₃s¹→js¹ (js¹→j₃s¹ x) ≡ ∣ x ∣) → PathP (λ i → Trunc₂.map j₃s¹→js¹ (j₃s¹-loops (js¹→j₃s¹ x) i) ≡ ∣ loops x i ∣) y y
  step₄ x y i j = step₃ x y j i

-- so the map J₃S¹ → JS¹ induces an equivalence on 2-truncations:

trunc-j₃s¹→js¹-isEquiv : isEquiv (Trunc₂.map j₃s¹→js¹)
trunc-j₃s¹→js¹-isEquiv =
  isoToIsEquiv (iso (Trunc₂.map j₃s¹→js¹)
                    (Trunc₂.rec trunc js¹→j₃s¹)
                    (Trunc₂.elim (λ x → isOfHLevelPathP 4 trunc _ _) j₃s¹-homotopy₂)
                    (Trunc₂.elim (λ x → isOfHLevelPathP 4 trunc _ _) j₃s¹-homotopy₁))

-- so that tells us that π₃S² ≃ π₂J₃S¹.

-- now we must do the same for J₂S²... :(

j₂s²-surfs' : (x : J₂S²) → Ω² (∥ J₂S² ∥₄) ∣ x ∣
j₂s²-surfs' base m n = ∣ surf m n ∣
j₂s²-surfs' (surf i j) m n = ∣ surf₂ i j m n ∣
j₂s²-surfs' (surf₂ i j a b) m n = fst triv i j a b m n
  where
  -- again, the 4-truncation is just enough for this
  triv : isContr (PathP (λ i → PathP (λ j → PathP (λ a → PathP (λ b → PathP (λ m → PathP (λ n → ∥ J₂S² ∥₄) ∣ surf₂ i j a b ∣ ∣ surf₂ i j a b ∣) refl refl) (λ m n → ∣ surf₂ i j m n ∣) (λ m n → ∣ surf₂ i j m n ∣)) refl refl) (λ a b m n → ∣ surf₂ a b m n ∣) (λ a b m n → ∣ surf₂ a b m n ∣)) refl refl)
  triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (isOfHLevelPathP' 4 (isOfHLevelPathP' 5 trunc _ _) _ _) _ _) _ _) _ _) _ _

j₂s²-surfs : (x : ∥ J₂S² ∥₄) → Ω² (∥ J₂S² ∥₄) x
j₂s²-surfs = Trunc₄.elim (λ x → isOfHLevelPathP 6 (isOfHLevelPathP 6 trunc _ _) _ _) j₂s²-surfs'

js²→j₂s² : JS² → ∥ J₂S² ∥₄
js²→j₂s² base = ∣ base ∣
js²→j₂s² (surfs x i j) = j₂s²-surfs (js²→j₂s² x) i j

j₂s²-homotopy₁ : ∀ x → js²→j₂s² (j₂s²→js² x) ≡ ∣ x ∣
j₂s²-homotopy₁ base = refl
j₂s²-homotopy₁ (surf i j) = refl
j₂s²-homotopy₁ (surf₂ i j a b) = refl

js²-surfs-trunc : (x : ∥ JS² ∥₄) → Ω² (∥ JS² ∥₄) x
js²-surfs-trunc =
  Trunc₄.elim
    (λ x → isOfHLevelPathP 6 (isOfHLevelPathP 6 trunc _ _) _ _)
    (λ x → cong (cong {B = λ _ → ∥ JS² ∥₄} ∣_∣) (surfs x))

j₂s²-lemma' : (x : J₂S²) → Path (PathP (λ i → PathP (λ j → ∥ JS² ∥₄) ∣ j₂s²→js² x ∣ ∣ j₂s²→js² x ∣) refl refl)
                               (λ i j → Trunc₄.map j₂s²→js² (j₂s²-surfs' x i j))
                               (λ i j → ∣ surfs (j₂s²→js² x) i j ∣)
j₂s²-lemma' base = refl
j₂s²-lemma' (surf a b) = refl
j₂s²-lemma' (surf₂ a b m n) = fst triv a b m n
  where
  triv : isContr (PathP (λ a → PathP (λ b → PathP (λ m → PathP (λ n → Path (PathP (λ i → PathP (λ j → ∥ JS² ∥₄) ∣ j₂s²→js² (surf₂ a b m n) ∣ ∣ j₂s²→js² (surf₂ a b m n) ∣) refl refl) (λ i j → Trunc₄.map j₂s²→js² (j₂s²-surfs' (surf₂ a b m n) i j)) (λ i j → ∣ surfs (j₂s²→js² (surf₂ a b m n)) i j ∣)) refl refl) refl refl) (λ _ _ → refl) (λ _ _ → refl)) (λ _ _ _ → refl) (λ _ _ _ → refl))
  triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (isOfHLevelPathP' 4 (isOfHLevelPathP' 5 (isOfHLevelPathP 6 trunc _ _) _ _) _ _) _ _) _ _) _ _) _ _

j₂s²-lemma : (x : ∥ J₂S² ∥₄) → Path (PathP (λ i → PathP (λ j → ∥ JS² ∥₄) (Trunc₄.map j₂s²→js² x) (Trunc₄.map j₂s²→js² x)) refl refl)
                                   (λ i j → Trunc₄.map j₂s²→js² (j₂s²-surfs x i j))
                                   (js²-surfs-trunc (Trunc₄.map j₂s²→js² x))
j₂s²-lemma =
  Trunc₄.elim
    (λ x → isOfHLevelPathP 6 (isOfHLevelPathP 6 (isOfHLevelPathP 6 trunc _ _) _ _) _ _)
    j₂s²-lemma'

j₂s²-homotopy₂ : ∀ x → Trunc₄.map j₂s²→js² (js²→j₂s² x) ≡ ∣ x ∣
j₂s²-homotopy₂ base = refl
j₂s²-homotopy₂ (surfs x i j) = step₄ x (j₂s²-homotopy₂ x) i j
  where
  step₃ : (x : JS²) (y : Trunc₄.map j₂s²→js² (js²→j₂s² x) ≡ ∣ x ∣) → PathP (λ k → PathP (λ i → y k ≡ y k) refl refl) (λ i j → Trunc₄.map j₂s²→js² (j₂s²-surfs (js²→j₂s² x) i j)) (λ i j → ∣ surfs x i j ∣)
  step₃ x y =
    transp (λ l → PathP (λ k → PathP (λ i → y k ≡ y k) refl refl) (j₂s²-lemma (js²→j₂s² x) (~ l)) (λ i j → ∣ surfs x i j ∣))
           i0
           (λ k i j → js²-surfs-trunc (y k) i j)

  step₄ : (x : JS²) (y : Trunc₄.map j₂s²→js² (js²→j₂s² x) ≡ ∣ x ∣) → PathP (λ i → PathP (λ j → Trunc₄.map j₂s²→js² (j₂s²-surfs (js²→j₂s² x) i j) ≡ ∣ surfs x i j ∣) y y) refl refl
  step₄ x y i j k = step₃ x y k i j

-- So the map J₂S² → JS² induces an equivalence on 4-truncations:
trunc-j₂s²→js²-isEquiv : isEquiv (Trunc₄.map j₂s²→js²)
trunc-j₂s²→js²-isEquiv =
  isoToIsEquiv (iso (Trunc₄.map j₂s²→js²)
                    (Trunc₄.rec trunc js²→j₂s²)
                    (Trunc₄.elim (λ x → isOfHLevelPathP 6 trunc _ _) j₂s²-homotopy₂)
                    (Trunc₄.elim (λ x → isOfHLevelPathP 6 trunc _ _) j₂s²-homotopy₁))

-- OK, so we have confirmed that the maps π₂JS¹ → π₂J₃S¹ and
-- π₃JS² → π₃J₂S² are equivalences. I won't use this fact yet in this
-- example, but I wanted to make sure I could prove it.

-- Ljungström and Mörtberg's Theorem 3 in "The 4th Homotopy Group of
-- the 3-Sphere in Cubical Agda" suggests that we can just skip JS¹
-- and JS² entirely. But for now I am still using them... I think
-- these types are pedagogically useful at least.



-- Now let's define a π₂JS¹ (π₃S²) computer. First we need a π₂S²
-- computer. It will be convenient later to define it on ∥S₂∥₂,
-- i.e. K(ℤ,2). I guess the below is just like Licata and Brunerie?

-- type of 1-types
Groupoid = TypeOfHLevel ℓ-zero 3

Hopf : S² → Type
Hopf base = S¹
Hopf (surf i j) = global rotLoop i j

isGroupoidHopf : (x : S²) → isGroupoid (Hopf x)
isGroupoidHopf base = isGroupoidS¹
isGroupoidHopf (surf i j) = fst triv i j
  where
  triv : isContr (PathP (λ i → PathP (λ j → isGroupoid (Hopf (surf i j))) isGroupoidS¹ isGroupoidS¹) refl refl)
  triv = isOfHLevelPathP 0 (isOfHLevelPathP' 0 isPropIsGroupoid _ _) _ _

HopfGpd : S² → Groupoid
HopfGpd x = (Hopf x , isGroupoidHopf x)

TruncHopf : ∥ S² ∥₂ → Groupoid
TruncHopf = Trunc₂.rec (isOfHLevelTypeOfHLevel 3) HopfGpd

compute-π₂S² : Ω² ∥ S² ∥₂ ∣ base ∣ → ℤ
compute-π₂S² p = winding (λ i → transp (λ j → fst (TruncHopf (p i j))) (~ i ∨ i) base)

-- Now, we can also define a funny map J₃S¹ → S², using the ccube
-- lemma.

j₃s¹→s² : J₃S¹ → S²
j₃s¹→s² base = base
j₃s¹→s² (loop i) = base
j₃s¹→s² (loop₂ i j) = surf i j
j₃s¹→s² (loop₃ i j k) = ccube surf i j k

-- This is enough to define a π₂JS¹ (≃ π₃S²) computer:

compute-π₂JS¹ : Ω² JS¹ base → ℤ
compute-π₂JS¹ p = done
  where
  -- first we go to J₃S¹ as above (and so we need to 2-truncate):
  p₁ : Ω² ∥ J₃S¹ ∥₂ ∣ base ∣
  p₁ = cong (cong js¹→j₃s¹) p

  -- now we apply the funny map
  p₂ : Ω² ∥ S² ∥₂ ∣ base ∣
  p₂ = cong (cong (Trunc₂.map j₃s¹→s²)) p₁

  -- and then the π₂S² computer
  done : ℤ
  done = compute-π₂S² p₂

-- Empirically, testing on small examples in cubicaltt, this seems to
-- be a group isomorphism...

-- TODO prove it



-- Now, consider π₃J₂S² (π₄S³).

-- First, observe that J₂S² is S² with a 4-cell attached. This was
-- part of Brunerie's third chapter. But looking at the 4-path
-- constructor surf₂, it seems we can directly "read off" the
-- attaching map, in some sense.

-- One way to see it is to apply fromPathP to surf₂. The fromPathP
-- equivalence tells us that the type of surf₂ is equivalent to a type
-- like this:

-- Path (surf ≡ surf) (transport ... refl) refl

-- The transport will be propositionally equal to the composition of
-- the open box consisting of 7 of 8 of the faces of the 4-cube.

𝟚 : Path (Ω² S² base) surf surf
𝟚 j a b =
  hcomp (λ i → λ { (j = i0) → surf a b
                 ; (j = i1) → surf a b
                 ; (a = i0) → surf i j
                 ; (a = i1) → surf i j
                 ; (b = i0) → surf i j
                 ; (b = i1) → surf i j
                 })
        (surf a b)

-- The type (surf ≡ surf) is easily equivalent to Ω³S². This
-- equivalence takes the 8th face (refl {x = surf}) to refl.

-- So, naively, surf₂ seems to say that π₃J₂S² is like π₃S², but a
-- certain 3-cell (𝟚 with the "two ends tied off") is trivialized.

-- If we apply the π₃S² computer to this in cubicaltt (TODO actually
-- define it here) then we get 2. So it seems we learn that "2 = 0" in
-- π₃JS².

-- I believe this intuition corresponds to some version of Brunerie's
-- section 3.4, specializing everything for the types above. I have
-- not worked out the whole proof of this yet, though.

-- If we draw a picture of the hcomp 𝟚, e.g. by tracing out the
-- "antipode of the basepoint" of S², we see that it is basically a
-- Hopf link. The weird type (surf ≡ surf) means that one of the
-- circles is a circle "at infinity" and appears as a horizontal
-- line. The other circle is linked around it.

-- So, the 4-cell surf₂ is in some sense a "trivialization of the Hopf
-- link induced by surf."

-- Now, J₂S² is a nice type, we have a mapping out property: pointed
-- maps J₂S² →∙ X are equivalent to 2-loops in X, together with
-- 4-cells like surf₂, "trivializing the Hopf link" induced by the
-- 2-loop.

-- So... in the same handwavy sense that ΩS² is "generated by a 2-loop
-- in the universe," the loop space ΩJ₂S² should be "generated by a
-- 2-loop in the universe _and_ a trivialization of its Hopf link."
-- But if the 2+2=4 lemma holds, that should mean that ΩJ₂S² is like
-- this:

data LJ₂S² : Type where
  base : LJ₂S²
  loops : (x : LJ₂S²) → x ≡ x
  loopsComm : (x : LJ₂S²) → Path (Csq (loops x) (loops x))
                                 (λ i j → loops (loops x i) j)
                                 (λ i j → loops (loops x j) i)

-- This time, I will skip LJ₂S² and go straight to a word-length
-- filtration. The number of cells of LJ₂S² in each dimension seems to
-- follow the "Narayana's Cows" sequence (https://oeis.org/A000930),
-- i.e. the "number of compositions of n into parts 1 and 3."

-- Since we only care about π₄S³ for now, we can 2-truncate at
-- 1,1,1,2,... and the result is reasonably nice: ∥ΩJ₂S²∥₂ should be
-- like J₃S¹ with an extra 3-cell, corresponding to (loopsComm base).

-- (TODO try to go up to π₅S³... I think we'll have to consider J₄S¹
-- with an extra 3-cell and two extra 4-cells: 1+3=3+1=4?)

-- I call this "L₂J₂S²" because it is supposed to be a model of the
-- loop space of J₂S² up to 2-truncation. (Maybe it would be good to
-- rename J₂S² to L₄S³, etc?)

data L₂J₂S² : Type where
  base : L₂J₂S²
  loop : PathP (λ i → L₂J₂S²) base base
  loop₂ : PathP (λ i → PathP (λ j → L₂J₂S²) (loop i) (loop i)) (λ j → loop j) (λ j → loop j)
  loop₃ : PathP (λ i → PathP (λ j → PathP (λ k → L₂J₂S²) (loop₂ i j) (loop₂ i j)) (λ k → loop₂ i k) (λ k → loop₂ i k)) (λ j k → loop₂ j k) (λ j k → loop₂ j k)
  -- extra 3-cell:
  loop₂Inv : Path (Csq loop loop) (λ i j → loop₂ i j) (λ i j → loop₂ j i)

-- If you picture loop₂ as a "positive crossing," then loop₂Inv seems
-- to say that you can change positive crossings to negative
-- crossings...

-- Perhaps we should actually define L₂J₂S² in terms of J₃S¹? But for
-- now I will just redefine the 2-loop in the universe at L₂J₂S², in
-- the same way as for J₃S¹:

l₂j₂s²-loops' : (x : L₂J₂S²) → Ω (∥ L₂J₂S² ∥₂) ∣ x ∣
l₂j₂s²-loops' base l = ∣ loop l ∣
l₂j₂s²-loops' (loop i) l = ∣ loop₂ i l ∣
l₂j₂s²-loops' (loop₂ i j) l = ∣ loop₃ i j l ∣
l₂j₂s²-loops' (loop₃ i j k) l = fst triv i j k l
  where
  -- as before, 2-truncation is just enough:
  triv : isContr (PathP (λ i → PathP (λ j → PathP (λ k → PathP (λ l → ∥ L₂J₂S² ∥₂) ∣ loop₃ i j k ∣ ∣ loop₃ i j k ∣) (λ l → ∣ loop₃ i j l ∣) (λ l → ∣ loop₃ i j l ∣)) (λ k l → ∣ loop₃ i k l ∣) (λ k l → ∣ loop₃ i k l ∣)) (λ j k l → ∣ loop₃ j k l ∣) (λ j k l → ∣ loop₃ j k l ∣))
  triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 trunc _ _) _ _) _ _) _ _
l₂j₂s²-loops' (loop₂Inv k i j) l = fst triv k i j l
  where
  -- also just enough here:
  triv : isContr (PathP (λ k → PathP (λ i → PathP (λ j → PathP (λ l → ∥ L₂J₂S² ∥₂) ∣ loop₂Inv k i j ∣ ∣ loop₂Inv k i j ∣) (λ l → ∣ loop₂ i l ∣) (λ l → ∣ loop₂ i l ∣)) (λ j l → ∣ loop₂ j l ∣) (λ j l → ∣ loop₂ j l ∣)) (λ i j l → ∣ loop₃ i j l ∣) (λ i j l → ∣ loop₃ j i l ∣))
  triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 trunc _ _) _ _) _ _) _ _

l₂j₂s²-loops : (x : ∥ L₂J₂S² ∥₂) → Ω ∥ L₂J₂S² ∥₂ x
l₂j₂s²-loops = Trunc₂.elim (λ x → isOfHLevelPathP 4 trunc x x) l₂j₂s²-loops'

-- Now we need to define loopsComm on ∥ L₂J₂S² ∥₂... Almost all of
-- this is trivial by hlevel. Unfortunately, we must write out the
-- boundaries, and in order to write out the boundaries in a somewhat
-- "sane" way without tripping up the termination checker, it seems we
-- must give names to these trivialities. :(

triv-l₂j₂s²-loopsComm'-loop : isContr (PathP (λ i → PathP (λ l → PathP (λ m → PathP (λ n → ∥ L₂J₂S² ∥₂) ∣ loop₂ i m ∣ ∣ loop₂ i m ∣) (λ n → ∣ loop₂ i n ∣) (λ n → ∣ loop₂ i n ∣)) (λ m n → ∣ loop₃ i m n ∣) (λ m n → ∣ loop₃ i n m ∣)) (λ l m n → ∣ loop₂Inv l m n ∣) (λ l m n → ∣ loop₂Inv l m n ∣))
triv-l₂j₂s²-loopsComm'-loop = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 trunc _ _) _ _) _ _) _ _

triv-l₂j₂s²-loopsComm'-loop₂ : isContr (PathP (λ i → PathP (λ j → Path (Csq (l₂j₂s²-loops' (loop₂ i j)) (l₂j₂s²-loops' (loop₂ i j))) (λ m n → l₂j₂s²-loops (l₂j₂s²-loops' (loop₂ i j) m) n) (λ m n → l₂j₂s²-loops (l₂j₂s²-loops' (loop₂ i j) n) m)) (fst triv-l₂j₂s²-loopsComm'-loop i) (fst triv-l₂j₂s²-loopsComm'-loop i)) (λ j → fst triv-l₂j₂s²-loopsComm'-loop j) (λ j → fst triv-l₂j₂s²-loopsComm'-loop j))
triv-l₂j₂s²-loopsComm'-loop₂ = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (isOfHLevelPathP 4 trunc _ _) _ _) _ _) _ _) _ _

triv-l₂j₂s²-loopsComm'-loop₃ : isContr (PathP (λ i → PathP (λ j → PathP (λ k → Path (Csq (l₂j₂s²-loops' (loop₃ i j k)) (l₂j₂s²-loops' (loop₃ i j k))) (λ m n → l₂j₂s²-loops (l₂j₂s²-loops' (loop₃ i j k) m) n) (λ m n → l₂j₂s²-loops (l₂j₂s²-loops' (loop₃ i j k) n) m)) (fst triv-l₂j₂s²-loopsComm'-loop₂ i j) (fst triv-l₂j₂s²-loopsComm'-loop₂ i j)) (λ k → fst triv-l₂j₂s²-loopsComm'-loop₂ i k) (λ k → fst triv-l₂j₂s²-loopsComm'-loop₂ i k)) (λ j k → fst triv-l₂j₂s²-loopsComm'-loop₂ j k) (λ j k → fst triv-l₂j₂s²-loopsComm'-loop₂ j k))
triv-l₂j₂s²-loopsComm'-loop₃ = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (isOfHLevelPathP 4 (isOfHLevelPathP 4 trunc _ _) _ _) _ _) _ _) _ _) _ _

triv-l₂j₂s²-loopsComm'-loop₂Inv : isContr (PathP (λ k → PathP (λ i → PathP (λ j → Path (Csq (l₂j₂s²-loops' (loop₂Inv k i j)) (l₂j₂s²-loops' (loop₂Inv k i j))) (λ m n → l₂j₂s²-loops (l₂j₂s²-loops' (loop₂Inv k i j) m) n) (λ m n → l₂j₂s²-loops (l₂j₂s²-loops' (loop₂Inv k i j) n) m)) (fst triv-l₂j₂s²-loopsComm'-loop i) (fst triv-l₂j₂s²-loopsComm'-loop i)) (λ j → fst triv-l₂j₂s²-loopsComm'-loop j) (λ j → fst triv-l₂j₂s²-loopsComm'-loop j)) (λ i j → fst triv-l₂j₂s²-loopsComm'-loop₂ i j) (λ i j → fst triv-l₂j₂s²-loopsComm'-loop₂ j i))
triv-l₂j₂s²-loopsComm'-loop₂Inv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (isOfHLevelPathP 4 (isOfHLevelPathP 4 trunc _ _) _ _) _ _) _ _) _ _) _ _

l₂j₂s²-loopsComm' : (x : L₂J₂S²) → Path (Csq (l₂j₂s²-loops' x) (l₂j₂s²-loops' x)) (λ i j → l₂j₂s²-loops (l₂j₂s²-loops' x i) j) (λ i j → l₂j₂s²-loops (l₂j₂s²-loops' x j) i)
l₂j₂s²-loopsComm' base k i j = ∣ loop₂Inv k i j ∣
-- trivial by hlevel :(
l₂j₂s²-loopsComm' (loop i) = fst triv-l₂j₂s²-loopsComm'-loop i
l₂j₂s²-loopsComm' (loop₂ i j) = fst triv-l₂j₂s²-loopsComm'-loop₂ i j
l₂j₂s²-loopsComm' (loop₃ i j k) = fst triv-l₂j₂s²-loopsComm'-loop₃ i j k
l₂j₂s²-loopsComm' (loop₂Inv k i j) = fst triv-l₂j₂s²-loopsComm'-loop₂Inv k i j

l₂j₂s²-loopsComm : (x : ∥ L₂J₂S² ∥₂) → Path (Csq (l₂j₂s²-loops x) (l₂j₂s²-loops x)) (λ i j → l₂j₂s²-loops (l₂j₂s²-loops x i) j) (λ i j → l₂j₂s²-loops (l₂j₂s²-loops x j) i)
l₂j₂s²-loopsComm =
  Trunc₂.elim
    (λ x → isOfHLevelPathP 4 (isOfHLevelPathP 4 (isOfHLevelPathP 4 trunc _ _) _ _) _ _)
    l₂j₂s²-loopsComm'

-- This gives us a fibration over J₂S², using the 2+2=4 lemma with
-- loopsComm:

P : J₂S² → Type
P base = ∥ L₂J₂S² ∥₂
P (surf i j) = global l₂j₂s²-loops i j
P (surf₂ i j a b) = 2+2=4 l₂j₂s²-loops l₂j₂s²-loopsComm i j a b

-- So we can map ΩJ₂S² to L₂J₂S²:

Ωj₂s²→l₂j₂s² : Ω J₂S² base → ∥ L₂J₂S² ∥₂
Ωj₂s²→l₂j₂s² p = transp (λ i → P (p i)) i0 ∣ base ∣

-- We need a slightly truncated version in the π₄S³ computer. Really
-- we should use Ω∥J₂S²∥₃ on the left to make this an equivalence (?),
-- but we can just skip past that for now. (The reason for this slack
-- is that J₂S² is good up to π₅S³, but we're only going to π₄S³.)

Ω∥j₂s²∥→l₂j₂s² : Ω ∥ J₂S² ∥₄ ∣ base ∣ → ∥ L₂J₂S² ∥₂
Ω∥j₂s²∥→l₂j₂s² p =
  Trunc₃.rec
    (isOfHLevelSuc 4 trunc)
    Ωj₂s²→l₂j₂s²
    (Trunc₄.encode₀ p)

-- Now we basically need one more map, to K(ℤ/2ℤ, 2). This is similar
-- to the funny map from J₃S¹ to S², but we map the new 3-cell loop₂Inv
-- to a new 3-cell surfInv:

data S²/2 : Type where
  base : S²/2
  surf : Ω² S²/2 base
  surfInv : Path (Ω² S²/2 base) (λ i j → surf i j) (λ i j → surf j i)

l₂j₂s²→s²/2 : L₂J₂S² → S²/2
l₂j₂s²→s²/2 base = base
l₂j₂s²→s²/2 (loop i) = base
l₂j₂s²→s²/2 (loop₂ i j) = surf i j
l₂j₂s²→s²/2 (loop₃ i j k) = ccube surf i j k
l₂j₂s²→s²/2 (loop₂Inv k i j) = surfInv k i j

-- Now we need Ω²K(ℤ/2ℤ, 2) → ℤ/2ℤ, which is standard. First we need
-- K(ℤ/2ℤ, 1). I'm going to define the untruncated "S¹/2" and then
-- truncate later. (Really, this is RP² I guess??)

data S¹/2 : Type where
  base : S¹/2
  loop : PathP (λ i → S¹/2) base base
  loopInv : PathP (λ i → PathP (λ j → S¹/2) base base) (λ j → loop j) (λ j → loop (~ j))

Helix/2 : S¹/2 → Type
Helix/2 base = Bool
Helix/2 (loop i) = notEq i
Helix/2 (loopInv i j) = hmm i j
  where
  -- uh.. not computationally relevant so whatever
  hmm : notEq ≡ sym notEq
  hmm = sym (ua-pathToEquiv notEq) ∙∙ cong ua (equivEq refl) ∙∙ ua-pathToEquiv (sym notEq)

-- pulled this out to satisfy termination checker
silly : isContr (PathP (λ i → isSet (Helix/2 (loop i))) isSetBool isSetBool)
silly = isOfHLevelPathP' 0 isPropIsSet _ _

isSetHelix/2 : ∀ x → isSet (Helix/2 x)
isSetHelix/2 base = isSetBool
isSetHelix/2 (loop i) = fst silly i
isSetHelix/2 (loopInv i j) = fst triv i j
  where
  triv : isContr (PathP (λ i → PathP (λ j → isSet (Helix/2 (loopInv i j))) (isSetHelix/2 base) (isSetHelix/2 base)) (fst silly) (λ j → fst silly (~ j)))
  triv = isOfHLevelPathP 0 (isOfHLevelPathP' 0 isPropIsSet _ _) _ _

∥Helix/2∥ : ∥ S¹/2 ∥₁ → TypeOfHLevel ℓ-zero 2
∥Helix/2∥ = Trunc₁.rec (isOfHLevelTypeOfHLevel 2) (λ x → Helix/2 x , isSetHelix/2 x)

compute-π₁S¹/2 : Path ∥ S¹/2 ∥₁ ∣ base ∣ ∣ base ∣ → Bool
compute-π₁S¹/2 p = transp (λ i → fst (∥Helix/2∥ (p i))) i0 false

-- Now we can use K(ℤ/2ℤ, 1) for Ω²K(ℤ/2ℤ, 2) → ℤ/2ℤ. For this we need
-- the obvious Ω²(Type, K(ℤ/2ℤ, 1)):

rot/2' : (x : S¹/2) → Path ∥ S¹/2 ∥₁ ∣ x ∣ ∣ x ∣
rot/2' base k = ∣ loop k ∣
rot/2' (loop i) k = csq (λ i → ∣ loop i ∣) (λ i → ∣ loop i ∣) refl i k
rot/2' (loopInv i j) k = fst triv i j k
  where
  -- question: do we really need the 1-truncation for this? we will
  -- have to truncate soon anyway I think
  triv : isContr (PathP (λ i → PathP (λ j → PathP (λ k → ∥ S¹/2 ∥₁) ∣ loopInv i j ∣ ∣ loopInv i j ∣) (λ k → ∣ loop k ∣) (λ k → ∣ loop k ∣)) (csq (λ i → ∣ loop i ∣) (λ i → ∣ loop i ∣) refl) (λ j k → csq (λ i → ∣ loop i ∣) (λ i → ∣ loop i ∣) refl (~ j) k))
  triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 trunc _ _) _ _) _ _

rot/2 : (x : ∥ S¹/2 ∥₁) → Path ∥ S¹/2 ∥₁ x x
rot/2 = Trunc₁.elim (λ x → isOfHLevelPathP 3 trunc x x) rot/2'

-- Due to loopInv, this Ω²(Type, K(ℤ/2ℤ, 1)) is equal to its own
-- transpose. this will allow us to define a fibration over
-- S²/2. "locally" this is expressed by rot/2Sym:

rot/2Sym' : (x : S¹/2) → Path (Path ∥ S¹/2 ∥₁ ∣ x ∣ ∣ x ∣) (rot/2' x) (sym (rot/2' x))
rot/2Sym' base i j = ∣ loopInv i j ∣
rot/2Sym' (loop i) = fst triv i
  where
  triv : isContr (PathP (λ i → Path (Path ∥ S¹/2 ∥₁ ∣ loop i ∣ ∣ loop i ∣) (rot/2' (loop i)) (sym (rot/2' (loop i)))) (λ i j → ∣ loopInv i j ∣) (λ i j → ∣ loopInv i j ∣))
  triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 trunc _ _) _ _) _ _
rot/2Sym' (loopInv i j) = fst triv i j
  where
  triv : isContr (PathP (λ i → PathP (λ j → Path (Path ∥ S¹/2 ∥₁ ∣ loopInv i j ∣ ∣ loopInv i j ∣) (rot/2' (loopInv i j)) (sym (rot/2' (loopInv i j)))) (rot/2Sym' base) (rot/2Sym' base)) (λ j → rot/2Sym' (loop j)) (λ j → rot/2Sym' (loop (~ j))))
  triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP 3 trunc _ _) _ _) _ _) _ _

rot/2Sym : (x : ∥ S¹/2 ∥₁) → Path (Path ∥ S¹/2 ∥₁ x x) (rot/2 x) (sym (rot/2 x))
rot/2Sym = Trunc₁.elim (λ x → isOfHLevelPathP 3 (isOfHLevelPathP 3 trunc _ _) _ _) rot/2Sym'

-- We'll have to clean up some irregularities...

-- The extra `transp (λ _ → A)` come from using ∥_∥₁ :(

hcompNudge : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → x ≡ y
hcompNudge {A = A} {x = x} {y} p i = hcomp (λ j → λ { (i = i0) → transp (λ _ → A) j x ; (i = i1) → transp (λ _ → A) j y }) (transp (λ _ → A) i0 (p i))

hfillNudge : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ hcompNudge p
hfillNudge {A = A} {x = x} {y = y} p = s3
  where
  -- hmm, is there an easier way?
  s1 : PathP (λ f → transp (λ _ → A) f x ≡ transp (λ _ → A) f y) (λ i → transp (λ _ → A) i0 (p i)) (hcompNudge p)
  s1 f i = hfill (λ j → λ { (i = i0) → transp (λ _ → A) (j ∧ f) x ; (i = i1) → transp (λ _ → A) (j ∧ f) y }) (inS (transp (λ _ → A) i0 (p i))) f

  s2 : PathP (λ f → transp (λ _ → A) f x ≡ transp (λ _ → A) f y) (λ i → transp (λ _ → A) i0 (p i)) p
  s2 f i = transp (λ _ → A) f (p i)

  s3 : p ≡ hcompNudge p
  s3 i j = hcomp (λ k → λ { (i = i0) → s2 k j 
                          ; (i = i1) → s1 k j
                          ; (j = i0) → transp (λ _ → A) k x
                          ; (j = i1) → transp (λ _ → A) k y
                          })
                 (transp (λ _ → A) i0 (p j))

hcompInv : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
hcompInv {A = A} {x = x} p i = hcomp (λ j → λ { (i = i0) → transp (λ _ → A) j (p j) ; (i = i1) → transp (λ _ → A) j x }) (transp (λ _ → A) i0 x)

hfillInv : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → sym p ≡ hcompInv p
hfillInv {A = A} {x = x} {y = y} p = s3
  where
  -- ditto?
  s1 : PathP (λ f → transp (λ _ → A) f (p f) ≡ transp (λ _ → A) f x) (λ _ → transport refl x) (hcompInv p)
  s1 f i = hfill (λ j → λ { (i = i0) → transp (λ _ → A) j (p j) ; (i = i1) → transp (λ _ → A) j x }) (inS (transp (λ _ → A) i0 x)) f

  s2 : PathP (λ f → transp (λ _ → A) f (p f) ≡ transp (λ _ → A) f x) (λ _ → transport refl x) (sym p)
  s2 f i = transp (λ _ → A) f (p (f ∧ ~ i))

  s3 : sym p ≡ hcompInv p
  s3 i j = hcomp (λ k → λ { (i = i0) → s2 k j 
                          ; (i = i1) → s1 k j
                          ; (j = i0) → transp (λ _ → A) k (p k)
                          ; (j = i1) → transp (λ _ → A) k x
                          })
                 (transport refl x)

-- with rot/2Sym and the irregularity cleanup we can define a
-- fibration over S²/2:

Hopf/2 : S²/2 → Type
Hopf/2 base = ∥ S¹/2 ∥₁
Hopf/2 (surf i j) = global rot/2 i j
Hopf/2 (surfInv k i j) = need k i j
  where
  enough : PathP (λ i → PathP (λ j → ∥ S¹/2 ∥₁ → ∥ S¹/2 ∥₁) (λ x → x) (λ x → x))
               (λ j x → rot/2 x j)
               (λ j x → rot/2 x (~ j))
  enough i j x = rot/2Sym x i j

  junk : PathP (λ i → PathP (λ j → ∥ S¹/2 ∥₁ → ∥ S¹/2 ∥₁) (λ x → x) (λ x → x))
               (λ j x → hcompNudge (hcompNudge (rot/2 x)) j)
               (λ j x → hcompNudge (hcompInv (rot/2 x)) j)
  junk = (λ k j x → hfillNudge (hcompNudge (rot/2 x)) (~ k) j)
      ∙∙ (λ k j x → hfillNudge (rot/2 x) (~ k) j)
      ∙∙ enough
      ∙∙ (λ k j x → hfillInv (rot/2 x) k j)
      ∙∙ (λ k j x → hfillNudge (hcompInv (rot/2 x)) k j)

  need : Path (Ω² Type ∥ S¹/2 ∥₁) (λ i j → global rot/2 i j) (λ i j → global rot/2 j i)
  need = global-eq-lemma _ _ {!λ i x j → junk i j x!}

isGroupoidHopf/2 : (x : S²/2) → isGroupoid (Hopf/2 x)
isGroupoidHopf/2 base = trunc
isGroupoidHopf/2 (surf i j) = fst triv i j
  where
  triv : isContr (PathP (λ i → PathP (λ j → isGroupoid (Hopf/2 (surf i j))) trunc trunc) refl refl)
  triv = isOfHLevelPathP 0 (isOfHLevelPathP' 0 isPropIsGroupoid _ _) _ _
isGroupoidHopf/2 (surfInv k i j) = fst triv k i j
  where
  triv : isContr (PathP (λ k → PathP (λ i → PathP (λ j → isGroupoid (Hopf/2 (surfInv k i j))) trunc trunc) refl refl) (λ i j → isGroupoidHopf/2 (surf i j)) (λ i j → isGroupoidHopf/2 (surf j i)))
  triv = isOfHLevelPathP' 0 (isOfHLevelPathP 1 (isOfHLevelPathP 1 isPropIsGroupoid _ _) _ _) _ _

Hopf/2Gpd : S²/2 → Groupoid
Hopf/2Gpd x = (Hopf/2 x , isGroupoidHopf/2 x)

TruncHopf/2 : ∥ S²/2 ∥₂ → Groupoid
TruncHopf/2 = Trunc₂.rec (isOfHLevelTypeOfHLevel 3) Hopf/2Gpd

-- So we can compute π₂K(ℤ/2ℤ, 2):
compute-π₂S²/2 : Ω² ∥ S²/2 ∥₂ ∣ base ∣ → Bool
compute-π₂S²/2 p = compute-π₁S¹/2 (λ i → transp (λ j → fst (TruncHopf/2 (p i j))) (~ i ∨ i) ∣ base ∣)


-- Finally we can build the π₃JS² computer:
compute-π₃JS² : Ω³ JS² base → Bool
compute-π₃JS² p = p₄
  where
  -- JS² → ∥J₂S²∥₄
  p₁ : Ω³ ∥ J₂S² ∥₄ ∣ base ∣
  p₁ = cong (cong (cong js²→j₂s²)) p

  -- Ω∥J₂S²∥₄ → ∥L₂J₂S²∥₂
  p₂ : Ω² ∥ L₂J₂S² ∥₂ ∣ base ∣
  p₂ = cong (cong Ω∥j₂s²∥→l₂j₂s²) p₁

  -- ∥L₂J₂S²∥₂ → K(ℤ/2ℤ, 2) and we're basically done
  p₃ : Ω² ∥ S²/2 ∥₂ ∣ base ∣
  p₃ = cong (cong (Trunc₂.map l₂j₂s²→s²/2)) p₂

  -- Ω²K(ℤ/2ℤ, 2) → Bool
  p₄ : Bool
  p₄ = compute-π₂S²/2 p₃

-- Zero works :D
_ : compute-π₃JS² refl ≡ false
_ = refl

-- Now we need a generator of π₃S². It seems convenient to just define
-- it in terms of any 2-loop:

𝟙' : ∀ {ℓ} {A : Type ℓ} {x : A} (p : Ω² A x) → Csq {A = Ω A x} p p
𝟙' {x = x} p i j k =
  hcomp (λ f → λ { (i = i0) → p j (k ∧ f)
                 ; (i = i1) → p j (k ∧ f)
                 ; (j = i0) → p i k
                 ; (j = i1) → p i k
                 ; (k = i0) → x
                 ; (k = i1) → p j f
                 })
        (p i k)

𝟙 : ∀ {ℓ} {A : Type ℓ} {x : A} → Ω² A x → Ω³ A x
𝟙 {x = x} p = csq⁻¹ p p (𝟙' p)

-- If you draw a picture of (𝟙' surf) by tracing the antipode of the
-- basepoint (like "surf 1/2 1/2"), it looks like a "positive
-- crossing." There are horizontal and vertical flows. One of them
-- goes straight through the middle of the cube, and the other bends
-- around it using the connections.

-- Then, 𝟙 looks like 𝟙' with two pairs of corners tied off. So it is
-- something like a figure eight with the one crossing, or like a
-- "circle with a twist in the framing."

-- This gives us 1 in π₃JS² too:

nontriv : Ω³ JS² base
nontriv = 𝟙 (surfs base)

-- But... it doesn't seem to compute in Agda. I have not tried waiting
-- for a WHNF yet.

-- _ : compute-π₃JS² nontriv ≡ true
-- _ = refl

-- According to computations in cubicaltt, 𝟙 also directly gives us a
-- nontrivial element of π₄S³:

nontriv-π₄S³ : Ω⁴ S³ base
nontriv-π₄S³ = 𝟙 surf
