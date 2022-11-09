
module Cubical.Experiments.DoubleFunky where

open import Cubical.Foundations.Prelude
  using ( Type
        ; ℓ-zero
        ; _≡_ ; I ; i0 ; i1 ; ~_ ; _∨_ ; _∧_ ; Partial
        ; Path ; PathP ; refl
        ; transp ; hcomp
        ; isContr
        ; Σ ; _,_ ; fst ; snd
        )
open import Cubical.Core.Glue
  using ( Glue )
open import Cubical.Foundations.Equiv
  using ( _≃_ ; idEquiv ; equivEq )
open import Cubical.Foundations.HLevels
  using ( isOfHLevel ; isOfHLevelPathP' ; isOfHLevelPathP
        ; isPropIsOfHLevel ; TypeOfHLevel ; isOfHLevelTypeOfHLevel
        )
open import Cubical.Data.Nat
  using ( ℕ )
open import Cubical.Data.Int
  using ( ℤ ; pos )
open import Cubical.HITs.S1
  using ( S¹ ; base ; rotLoop ; winding ; isGroupoidS¹ )
open import Cubical.HITs.S2
  using ( S² ; base ; surf )

globalSys : {A : Type ℓ-zero} (h : (x : A) → x ≡ x) (i j : I) → Partial (~ i ∨ i ∨ ~ j ∨ j) (Σ (Type ℓ-zero) (λ T → T ≃ A))
globalSys {A} h i j (i = i0) = A , idEquiv A
globalSys {A} h i j (i = i1) = A , idEquiv A
globalSys {A} h i j (j = i0) = A , equivEq {e = idEquiv A} {f = idEquiv A} (λ k x → h x k) i
globalSys {A} h i j (j = i1) = A , idEquiv A

global : ∀ {A : Type ℓ-zero} → ((x : A) → x ≡ x) → Path (A ≡ A) refl refl
global {A = A} h i j = Glue A (globalSys h i j)

Ω : ∀ {ℓ} (A : Type ℓ) → A → Type ℓ
Ω A a = a ≡ a

Ω² : ∀ {ℓ} (A : Type ℓ) → A → Type ℓ
Ω² A a = Path (Ω A a) refl refl

Ω³ : ∀ {ℓ} (A : Type ℓ) → A → Type ℓ
Ω³ A a = Path (Ω² A a) refl refl

data JS¹ : Type where
  base : JS¹
  loops : (x : JS¹) → Ω JS¹ x

data JS² : Type where
  base : JS²
  surfs : (x : JS²) → Ω² JS² x

data ∥S²∥₂ : Type ℓ-zero where
  base : ∥S²∥₂
  surf : Path (Path ∥S²∥₂ base base) refl refl
  trunc : isOfHLevel 4 ∥S²∥₂

data J₃S¹ : Type where
  base : J₃S¹
  loop : base ≡ base
  funk : PathP (λ i → PathP (λ j → J₃S¹) (loop i) (loop i)) (λ j →  loop j ) (λ j → loop j)
  whoa : PathP (λ i → PathP (λ j → PathP (λ k → J₃S¹) (funk i j) (funk i j)) (λ k → funk i k) (λ k → funk i k)) (λ j k → funk j k) (λ j k → funk j k)

data ∥J₃S¹∥₂ : Type where
  base : ∥J₃S¹∥₂
  loop : base ≡ base
  funk : PathP (λ i → PathP (λ j → ∥J₃S¹∥₂) (loop i) (loop i)) (λ j →  loop j ) (λ j → loop j)
  whoa : PathP (λ i → PathP (λ j → PathP (λ k → ∥J₃S¹∥₂) (funk i j) (funk i j)) (λ k → funk i k) (λ k → funk i k)) (λ j k → funk j k) (λ j k → funk j k)
  trunc : isOfHLevel 4 ∥J₃S¹∥₂

trJ₃S¹ : J₃S¹ → ∥J₃S¹∥₂
trJ₃S¹ base = base
trJ₃S¹ (loop i) = loop i
trJ₃S¹ (funk i j) = funk i j
trJ₃S¹ (whoa i j k) = whoa i j k

funky-loops : (x : ∥J₃S¹∥₂) → Ω (∥J₃S¹∥₂) x
funky-loops base i = loop i
funky-loops (loop i) j = funk i j
funky-loops (funk i j) k = whoa i j k
funky-loops (whoa i j k) l = fst triv i j k l
  where
  triv : isContr (PathP (λ i → PathP (λ j → PathP (λ k → PathP (λ l → ∥J₃S¹∥₂) (whoa i j k) (whoa i j k)) (λ l →  whoa i j l ) (λ l →  whoa i j l )) (λ k l →  whoa i k l ) (λ k l →  whoa i k l )) (λ j k l →  whoa j k l ) (λ j k l →  whoa j k l ))
  triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 trunc _ _) _ _) _ _) _ _
funky-loops (trunc a b c d e f g h i j k l) m = fst triv i j k l m
  where
  triv : isContr (PathP (λ i → PathP (λ j → PathP (λ k → PathP (λ l → PathP (λ m → ∥J₃S¹∥₂) (trunc a b c d e f g h i j k l) (trunc a b c d e f g h i j k l)) (λ m → funky-loops a m) (λ m → funky-loops b m)) (λ l m → funky-loops (c l) m) (λ l m → funky-loops (d l) m)) (λ k l m → funky-loops (e k l) m) (λ k l m → funky-loops (f k l) m)) (λ j k l m → funky-loops (g j k l) m) (λ j k l m → funky-loops (h j k l) m))
  triv = isOfHLevelPathP 0 (isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 trunc _ _) _ _) _ _) _ _) _ _

JS¹→J₃S¹ : JS¹ → ∥J₃S¹∥₂
JS¹→J₃S¹ base = base
JS¹→J₃S¹ (loops x i) = funky-loops (JS¹→J₃S¹ x) i

csqPath : ∀ {A : Type ℓ-zero} {x y z : A} (p : x ≡ y) (q : y ≡ z) → Ω² A y ≡ PathP (λ i → p i ≡ q i) p q
csqPath p q k = PathP (λ i → p (i ∨ ~ k) ≡ q (i ∧ k)) (λ j → p (j ∨ ~ k)) (λ j → q (j ∧ k))

ccube : ∀ {A : Type ℓ-zero} {x : A} (p q r : Ω² A x) →
  PathP (λ i → PathP (λ j → p i j ≡ q i j) (λ k → p i k) (λ k → q i k)) (λ j k → r j k) (λ j k → r j k)
ccube p q r i = transp (λ k → csqPath (p i) (q i) k) (i ∨ ~ i) r

∥J₃S¹→S²∥₂ : ∥J₃S¹∥₂ → ∥S²∥₂
∥J₃S¹→S²∥₂ base = base
∥J₃S¹→S²∥₂ (loop i) = base
∥J₃S¹→S²∥₂ (funk i j) = surf i j
∥J₃S¹→S²∥₂ (whoa i j k) = ccube surf surf surf i j k
∥J₃S¹→S²∥₂ (trunc a b c d e f g h i j k l) = fst triv i j k l
  where
  triv : isContr (PathP (λ i → PathP (λ j → PathP (λ k → PathP (λ l → ∥S²∥₂) (∥J₃S¹→S²∥₂ a) (∥J₃S¹→S²∥₂ b)) (λ l → ∥J₃S¹→S²∥₂ (c l)) (λ l → ∥J₃S¹→S²∥₂ (d l))) (λ k l → ∥J₃S¹→S²∥₂ (e k l)) (λ k l → ∥J₃S¹→S²∥₂ (f k l))) (λ j k l → ∥J₃S¹→S²∥₂ (g j k l)) (λ j k l → ∥J₃S¹→S²∥₂ (h j k l)))
  triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 trunc _ _) _ _) _ _) _ _

recS² : ∀ {ℓ} {A : Type ℓ} (x : A) → Path (x ≡ x) refl refl → S² → A
recS² x p base = x
recS² x p (surf i j) = p i j

module RecΩS²
  (C : Type ℓ-zero)
  (D : Path (C ≡ C) refl refl)
  (c : C)
  where
  DD : S² → Type ℓ-zero
  DD = recS² C D

  rec' : (y : S²) → base ≡ y → DD y
  rec' y p = transp (λ k → DD (p k)) i0 c

  rec : base ≡ base → C
  rec = rec' base

ΩS²→JS¹ : Ω S² base → JS¹
ΩS²→JS¹ = RecΩS².rec JS¹ (global loops) base

annoying : Path ∥S²∥₂ base base
annoying i = ∥J₃S¹→S²∥₂ (JS¹→J₃S¹ (ΩS²→JS¹ (surf i)))

_ : annoying ≡ (λ i → hcomp (λ _ → λ { (i = i0) → base ; (i = i1) → base }) (hcomp (λ _ → λ { (i = i0) → base ; (i = i1) → base }) base))
_ = refl

map : Ω (Ω² S² base) surf → Ω (Ω ∥S²∥₂ base) annoying
map p i j = ∥J₃S¹→S²∥₂ (JS¹→J₃S¹ (ΩS²→JS¹ (p i j)))

μ : ∥S²∥₂ → TypeOfHLevel ℓ-zero 3
μ base = S¹ , isGroupoidS¹
μ (surf i j) = (global rotLoop i j , fst triv i j)
  where
  triv : isContr (PathP (λ i → PathP (λ j → isOfHLevel 3 (global rotLoop i j)) isGroupoidS¹ isGroupoidS¹) refl refl)
  triv = isOfHLevelPathP 0 (isOfHLevelPathP' 0 (isPropIsOfHLevel 3) _ _) _ _
μ (trunc a b c d e f g h i j k l) = fst triv i j k l
  where
  triv : isContr (PathP (λ i → PathP (λ j → PathP (λ k → PathP (λ l → TypeOfHLevel ℓ-zero 3) (μ a) (μ b)) (λ l → μ (c l)) (λ l → μ (d l))) (λ k l → μ (e k l)) (λ k l → μ (f k l))) (λ j k l → μ (g j k l)) (λ j k l → μ (h j k l)))
  triv = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (isOfHLevelTypeOfHLevel 3) _ _) _ _) _ _) _ _

annoying-winding : annoying ≡ annoying → ℤ
annoying-winding p = winding (λ i → transp (λ j → fst (μ (p i j))) i0 base)

thingSys : (q : Ω² S² base) (j a b : I) → I → Partial (~ j ∨ j ∨ ~ a ∨ a ∨ ~ b ∨ b) S²
thingSys q j a b i (j = i0) = q a b
thingSys q j a b i (j = i1) = q a b
thingSys q j a b i (a = i0) = q i j
thingSys q j a b i (a = i1) = q i j
thingSys q j a b i (b = i0) = q i j
thingSys q j a b i (b = i1) = q i j

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Homotopy.Loopspace hiding (Ω)

annoying* : annoying ≡ annoying
annoying* = (λ i → rUnit (rUnit refl (~ i)) (~ i)) ∙∙ (surf ∙ surf) ∙∙ (λ i → rUnit (rUnit refl i) i)

thing : (q : Ω² S² base) → Path (Ω² S² base) surf surf
thing q j a b = hcomp (thingSys surf j a b) (surf a b)

-- n : ℤ
-- n = annoying-winding (map thing)

asd : {!map !}
asd = {!!}

-- _ : n ≡ pos 2
-- _ = {!annoying-winding (map thing)!}
open Cubical.Foundations.HLevels
data S²* : Type where
  b : S²*
  sq : (x : S²*) → Path (Path S²* x x) refl refl

sq→Set : ∀ {ℓ} {A : S²* → Type ℓ} → ((x : _) → isSet (A x))
  → (pt : A b)
  → (x : _) → A x
sq→Set set p b = p
sq→Set {A = A} set p (sq z i j) = isOfHLevel→isOfHLevelDep 2 set (sq→Set set p z) (sq→Set set p z) refl refl (sq z) i j

open import Cubical.HITs.Truncation as TR
abra : hLevelTrunc 5 S² → hLevelTrunc 5 S²*
abra = TR.map λ { base → b ; (surf i i₁) → sq b i i₁}

S²*-elim : ∀ {ℓ} {A : S²* → Type ℓ} → (pt : A b) → ((f : (x : S²*) → A x) → ((x : S²*)
  → PathP (λ i → PathP (λ j → A (sq x i j)) (f x) (f x)) (λ _ → f x) λ _ → f x))
  → (x : _) → A x
S²*-elim pt f b = pt
S²*-elim pt f (sq pp i j) = {!!}

gen : ∀ {ℓ} {A : Type ℓ} (x : A) (p : x ≡ x) (r : refl ≡ p)
  → PathP (λ k → Cube (λ i j → r i j) (λ i j → r i j) (λ l j → r k l) {!λ l j → r k l!} {!!} {!!}) {!!} {!!} 
gen = {!!}

abra' : hLevelTrunc 5 S²* → hLevelTrunc 5 S²
abra' = TR.rec (isOfHLevelTrunc 5) help -- λ { b → base ; (sq x i j) → {!!}}
  where
  help : S²* → hLevelTrunc 5 S²
  help b = ∣ base ∣
  help (sq b i j) = ∣ surf i j ∣
  help (sq (sq b k l) i j) =
    hcomp (λ r → λ {(i = i0) → ∣ compPath-filler {ℓ-zero} {(Path S² base base)} surf surf (~ r) k l ∣ₕ
                   ; (i = i1) → ∣ compPath-filler {ℓ-zero} {(Path S² base base)} surf surf (~ r ∧ j) k l ∣ₕ
                   ; (j = i0) → ∣ compPath-filler {ℓ-zero} {(Path S² base base)} surf surf (~ r ∧ ~ i) k l ∣ₕ
                   ; (j = i1) → ∣ compPath-filler {ℓ-zero} {(Path S² base base)} surf surf (~ r) k l ∣ₕ
                   ; (k = i0) → {!!}
                   ; (k = i1) → {!!}
                   ; (l = i0) → {!∣ compPath-filler {ℓ-zero} {(Path S² base base)} surf surf (~ r ∧ ~ i) k l ∣ₕ!}
                   ; (l = i1) → {!∣ compPath-filler {ℓ-zero} {(Path S² base base)} surf surf (~ r ∧ ~ i) k l ∣ₕ!}})
          {!!}
  help (sq (sq (sq x m n) k l) i j) =
    {!
k = i0 ⊢ ∣ surf i j ∣
k = i1 ⊢ ∣ surf i j ∣
l = i0 ⊢ ∣ surf i j ∣
l = i1 ⊢ ∣ surf i j ∣
i = i0 ⊢ ∣ surf k l ∣
i = i1 ⊢ ∣ surf k l ∣
j = i0 ⊢ ∣ surf k l ∣
j = i1 ⊢ ∣ surf k l ∣!}
    where
    asd' : (x : S²*) → PathP (λ k → Cube (λ i j → help (sq x i j)) (λ i j → help (sq x i j)) -- l i j
                              (λ l j → help (sq x k l))
                              (λ l j → help (sq x k l))
                              (λ l i → help (sq x k l))
                              λ l i → help (sq x k l))
                              (λ l i j → help (sq x i j)) -- 
                              (λ l i j → help (sq x i j)) -- λ l i j → help (sq x i j)
    asd' x = {!!}



J₂' : {!!}
J₂' = {!!}



open import Cubical.HITs.S3
data S³* : Type where
  b : S³*
  re : (x : S³*) → Cube {A = S³*} (λ _ _ → x) (λ _ _ → x) (λ _ _ → x) (λ _ _ → x) (λ _ _ → x) (λ _ _ → x)

data S²a : Type where
  b : S²a
  surf : refl {x = b} ≡ refl
  high : PathP (λ i → Cube {A = S²a} (λ k l → surf k l) (λ k l → surf k l) (λ j l → surf i j) (λ j l → surf i j) (λ j k → surf i j) λ j k → surf i j) (λ k i j → surf i j) λ k i j → surf i j
  

open import Cubical.HITs.Wedge 
S4→ : S³ → Type
S4→ base = S²a
S4→ (surf j i k) = Glue S²a λ {(i = i0) → S²a , idEquiv S²a ; (i = i1) → S²a , abr j k ; (j = i0) → S²a , idEquiv S²a ; (j = i1) → S²a , idEquiv S²a ; (k = i0) → S²a , idEquiv S²a ; (k = i1) → S²a , idEquiv S²a}
  where
  abr : Square (λ _ → idEquiv S²a) (λ _ → idEquiv S²a) (λ _ → idEquiv S²a) (λ _ → idEquiv S²a) 
  fst (abr i j) b = surf i j
  fst (abr i j) (surf k l) = high k l i j
  fst (abr i j) (high a m c d) = {!!}
  snd (abr i j) = {!!}

enc1 : (x : S³) → (base ≡ x) → S4→ x
enc1 = J> b

del1 : Path S³ base base → hLevelTrunc 5 S²a
del1 x = ∣ enc1 base x ∣

open import Cubical.Foundations.Path
S²a→ : S²a → Type
S²a→ b = S²a
S²a→ (surf i j) = S²a
S²a→ (high i j k l) = Glue S²a λ {(i = i0) → S²a , (idEquiv S²a)
                                 ; (i = i1) → S²a , (idEquiv S²a)
                                 ; (j = i1) → S²a , (idEquiv S²a)
                                 ; (j = i0) → S²a , (idEquiv S²a)
                                 ; (k = i0) → S²a , (idEquiv S²a)
                                 ; (k = i1) → S²a , (idEquiv S²a)
                                 ; (l = i0) → S²a , h i j k
                                 ; (l = i1) → S²a , (idEquiv S²a)}
  where
  h : Cube (λ _ _ → idEquiv S²a) (λ _ _ → idEquiv S²a) (λ _ _ → idEquiv S²a) (λ _ _ → idEquiv S²a) (λ _ _ → idEquiv S²a) (λ _ _ → idEquiv S²a)
  fst (h i j k) b = hcomp (λ r → λ {(i = i0) → surf (~ r) j
                                   ; (i = i1) → surf j r
                                   ; (j = i0) → b
                                   ; (j = i1) → b
                                   ; (k = i0) → sym≡flipSquare surf i r j
                                   ; (k = i1) → sym≡flipSquare surf i r j})
                          b
  fst (h i j k) (surf c d) = {!!}
  fst (h i j k) (high i₁ i₂ i₃ i₄) = {!!}
  snd (h i j k) = {!!}

data S²' : Type where
  base : S²'
  surf' : refl {x = base} ≡ refl
  high : surf' ≡ surf'

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
selfer : S² → Type
selfer base = hLevelTrunc 4 S²'
selfer (surf i i₁) = Glue (hLevelTrunc 4 S²') λ {(i = i0) → hLevelTrunc 4 S²' , idEquiv _ ; (i = i1) → hLevelTrunc 4 S²' , h i₁ ; (i₁ = i0) → hLevelTrunc 4 S²' , idEquiv _ ; (i₁ = i1) → hLevelTrunc 4 S²' , idEquiv _}
  where
  h : idEquiv (hLevelTrunc 4 S²') ≡ idEquiv (hLevelTrunc 4 S²')
  h = Σ≡Prop isPropIsEquiv
       (funExt (TR.elim {!!}
        λ { base → refl
         ; (surf' i j) k → ∣ high k i j ∣
         ; (high i j k) l → {!!}}))

enc' : (x : S²) → (base ≡ x) → selfer x
enc' = J> ∣ base ∣

del0 : Path S² base base → hLevelTrunc 4 S²'
del0 = enc' base

del0^ : Path (Path (Path S² base base) refl refl) refl refl
     → Path (Path (hLevelTrunc 4 S²') ∣ base ∣ ∣ base ∣) refl refl
del0^ p i j = del0 (p i j)

open import Cubical.HITs.Susp
open import Cubical.Data.Bool
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Order2

open import Cubical.Data.Fin

S²'' = hLevelTrunc 4 S²'

data glS1 : Type where
  base : glS1
  loop' : base ≡ base
  surf* : loop' ≡ loop'
  surf'' : Cube {A = glS1}
              (λ _ _ → base) (λ i j → surf* i j )
              (λ r j → loop' (j ∨ ~ r)) (λ r j → loop' (j ∨ ~ r))
              (λ r i → loop' (~ r)) λ r i → base
  surf''' : Cube {A = glS1}
              (λ _ _ → base) (λ i j → surf* i j )
              (λ r j → loop' (j ∧ r)) (λ r j → loop' (j ∧ r))
              (λ r i → base) λ r i → loop' r

glS1* = hLevelTrunc 4 glS1

open import Cubical.HITs.S1 renaming (_·_ to _*_)
på : S¹ → Ω S² base
på base = refl
på (loop i) j = surf i j



haj : Ω³ S² base
haj i j k =
  hcomp (λ r → λ {(i = i0) → surf j r
                 ; (i = i1) → surf j r
                 ; (j = i0) → surf i r
                 ; (j = i1) → surf i r
                 ; (k = i0) → på (loop i * loop j) r
                 ; (k = i1) → på (loop i * loop j) r})
    base
{- 
  hcomp (λ r → λ {(i = i0) → surf (j ∨ r) k
                 ; (i = i1) → surf (j ∧ ~ r) k
                 ; (j = i0) → surf (i ∨ r) k
                 ; (j = i1) → surf (i ∧ ~ r) k
                 ; (k = i0) → base
                 ; (k = i1) → base})
    (på (loop i * loop j) k)
-}

data S₂ : Type where
  base : S₂
  surf : refl {x = base} ≡ refl
  surf* : PathP (λ i → Cube surf surf (λ j l → surf i j) (λ j l → surf i j)
                             (λ j k → surf i j) λ j k → surf i j)
                             (λ _ → surf) λ _ → surf
y→' : ∀ {ℓ} {A : S₂ → Type ℓ} → ((x : S₂) → isSet (A x))
  → (pt : A base)
  → ((x : _) → A x)
y→' {A = A} gr pt base = pt
y→' {A = A} gr pt (surf i j) = H i j
  where
  H : SquareP (λ i j → A (surf i j)) (λ _ → pt) (λ _ → pt) (λ _ → pt) λ _ → pt
  H = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (gr base) _ _) _ _ .fst
y→' {A = A} gr pt (surf* i j k l) = HA i j k l
  where
  H : SquareP (λ i j → A (surf i j)) (λ _ → pt) (λ _ → pt) (λ _ → pt) λ _ → pt
  H = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (gr base) _ _) _ _ .fst

  HA : PathP (λ i
    → PathP (λ j
    → PathP (λ k
    → PathP (λ l → A (surf* i j k l)) (H i j) (H i j)) (λ _ → H i j) λ _ → H i j)
      (λ m n → H m n) H) (λ a d c → H d c) λ i j k → H j k
  HA = isOfHLevelPathP' 0
        (isOfHLevelPathP' 1
        (isOfHLevelPathP' 2
        (isOfHLevelPathP' 3 (isOfHLevelSuc 3 (isOfHLevelSuc 2 (gr base))) _ _) _ _ ) _ _) _ _ .fst



y→ : ∀ {ℓ} {A : S₂ → Type ℓ} → ((x : S₂) → is2Groupoid (A x))
  → (pt : A base)
  → SquareP (λ i j → A (surf i j))
            (λ _ → pt) (λ _ → pt)
            (λ _ → pt) (λ _ → pt)
  → ((x : _) → A x)
y→ {A = A} gr pt sp base = pt
y→ {A = A} gr pt sp (surf i j) = sp i j
y→ {A = A} gr pt sp (surf* i j k l) = HA i j k l
  where
  HA : PathP (λ i
    → PathP (λ j
    → PathP (λ k
    → PathP (λ l → A (surf* i j k l)) (sp i j) (sp i j)) (λ _ → sp i j) λ _ → sp i j)
      (λ m n → sp m n) sp) (λ a d c → sp d c) λ i j k → sp j k
  HA = isOfHLevelPathP' 0
        (isOfHLevelPathP' 1
        (isOfHLevelPathP' 2
        (isOfHLevelPathP' 3 (gr base) _ _) _ _ ) _ _) _ _ .fst

baba : (y : S₂)
  → Square {A = hLevelTrunc 5 S₂} (λ _ → ∣ y ∣) (λ _ → ∣ y ∣) (λ _ → ∣ y ∣) (λ _ → ∣ y ∣)
baba = y→ (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 5 _ _) _ _)
           (λ i j → ∣ surf i j ∣)
           λ i j k l → ∣ surf* i j k l ∣

_+H_ : S₂ → S₂ → hLevelTrunc 5 S₂
base +H y = ∣ y ∣
surf i i₁ +H y = baba y i i₁
surf* i j k l +H y = H y i j k l
  where
  H : (y : S₂) → PathP (λ i → Cube (baba y) (baba y) (λ j l → (baba y) i j)
                        (λ j l → (baba y) i j)
                             (λ j k → (baba y) i j) λ j k → (baba y) i j)
                             (λ _ → (baba y)) λ _ → (baba y)
  H = y→' (λ _ → isOfHLevelPathP 2 (isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (isOfHLevelPath' 4 (isOfHLevelTrunc 5) _ _) _ _) _ _) _ _) λ i j k l → ∣ surf* i j k l ∣

2S = hLevelTrunc 5 S₂

_++_ : 2S → 2S → 2S
_++_ = TR.rec2 (isOfHLevelTrunc 5) _+H_

brasd* : S² → Type
brasd* base = 2S
brasd* (surf i j) = Glue 2S λ {(i = i0) → 2S , {!!}
           ; (i = i1) → 2S , idEquiv 2S
           ; (j = i0) → 2S , idEquiv 2S
           ; (j = i1) → 2S , idEquiv 2S}
  where
  haa : idEquiv 2S ≡ idEquiv 2S
  haa =
      Σ≡Prop isPropIsEquiv
      (funExt (TR.elim {!!} (y→ (λ _ → isOfHLevelTrunc 5 _ _)
          refl
          {!!})))

-- brasd : S² → Type
-- brasd base = S²
-- brasd (surf i j) =
--   Glue S² λ {(i = i0) → S² , back j
--            ; (i = i1) → S² , idEquiv S²
--            ; (j = i0) → S² , idEquiv S²
--            ; (j = i1) → S² , idEquiv S²}
--   where
--   gg : (x : S²) → x ≡ x
--   gg base = refl
--   gg (surf i j) k =
--     hcomp (λ r → λ { (i = i0) → base
--                     ; (i = i1) → surf r (j ∨ ~ r)
--                     ; (j = i0) → surf (i ∧ r) (~ r)
--                     ; (j = i1) → base
--                     ; (k = i0) → surf (i ∧ r) (j ∨ ~ r)
--                     ; (k = i1) → surf (i ∧ r) (j ∨ ~ r)})
--            base
--   {-
--     hcomp (λ r → λ { (i = i0) → base
--                     ; (i = i1) → surf r j
--                     ; (j = i0) → base
--                     ; (j = i1) → haj i j r
--                     ; (k = i0) → surf (i ∧ r) j
--                     ; (k = i1) → surf (i ∧ r) j})
--            base -}

--   back : idEquiv S² ≡ idEquiv S²
--   back = Σ≡Prop isPropIsEquiv (funExt gg)

-- sd : (x : S²) → base ≡ x → brasd x
-- sd = J> base

-- haha : Ω³ S² base → Ω² S² base
-- haha p i j = sd base (p i j)


-- S²-fib : S² → Type
-- S²-fib base = S¹
-- S²-fib (surf i j) =
--   Glue S¹ λ {(i = i0) → S¹ , gg j
--            ; (i = i1) → S¹ , idEquiv S¹
--            ; (j = i0) → S¹ , idEquiv S¹
--            ; (j = i1) → S¹ , idEquiv S¹}
--   where
--   gg : idEquiv S¹ ≡ idEquiv S¹
--   gg = Σ≡Prop isPropIsEquiv (funExt λ { base → S¹.loop ; (S¹.loop i) j → S¹.loop i * S¹.loop j})

-- enc-S² : (x : S²) → base ≡ x → S²-fib x
-- enc-S² = J> base

-- dd : Ω³ S² base
-- dd = sym (rCancel surf) ∙∙ EH 0 surf (sym surf) ∙∙ lCancel surf

-- maf : Path (Ω² S² base) (surf ∙ sym surf) (sym surf ∙ surf) → Ω² S² base
-- maf p i j = {!sd base (p i0 j)!}



-- ϕ : Ω³ S² base → ℤ
-- ϕ p = winding (cong (enc-S² base) (haha p))

-- nn = ϕ haj
-- open import Cubical.Data.Int
-- kk : nn + 1 ≡ 2
-- kk = refl
-- -- br : S² → Type
-- -- br base = glS1*
-- -- br (surf i j) = Glue glS1* λ {(i = i0) → glS1* , bra j
-- --                             ; (i = i1) → glS1* , idEquiv glS1*
-- --                             ; (j = i0) → glS1* , idEquiv glS1*
-- --                             ; (j = i1) → glS1* , idEquiv glS1*}
-- --   where
-- --   lb : I → I → I → glS1*
-- --   lb i j k = hfill (λ k → λ {(i = i0) → ∣ loop' (j ∨ ~ k) ∣
-- --                           ; (i = i1) → ∣ loop' (j ∧ k) ∣
-- --                           ; (j = i0) → ∣ loop' (i ∨ ~ k) ∣
-- --                           ; (j = i1) → ∣ loop' (i ∧ k) ∣})
-- --                  (inS (∣ base ∣)) k

-- --   l' : I → I → I → glS1*
-- --   l' i j k = hfill (λ k → λ {(i = i0) → ∣ surf* k j ∣
-- --                           ; (i = i1) → ∣ loop' j ∣
-- --                           ; (j = i0) → ∣ loop' i ∣
-- --                           ; (j = i1) → ∣ loop' i ∣})
-- --                  (inS (lb i j i1)) k  

-- --   gala : Cube {A = glS1}
-- --               (λ _ _ → base) (λ i j → surf* i j )
-- --               (λ r j → loop' (j ∨ ~ r)) (λ r j → loop' (j ∨ ~ r))
-- --               (λ r i → loop' (~ r)) λ r i → base -- r i j
-- --   gala = surf''

-- --   c3 : Cube {A = glS1*}
-- --     (λ j k → l' j k i1) (λ j k → l' j k i1)
-- --     (λ i k → ∣ loop' k ∣) (λ i k → ∣ loop' k ∣)
-- --     (λ i j → ∣ surf* i j ∣) (λ i j → ∣ surf* i j ∣)
-- --   c3 i j k =
-- --     hcomp (λ r → λ {(i = i0) → l' j k r
-- --                    ; (i = i1) → l' j k r
-- --                    ; (j = i0) → l' j k r
-- --                    ; (j = i1) → l' j k r
-- --                    ; (k = i0) → ∣ surf* i j ∣
-- --                    ; (k = i1) → ∣ surf* i j ∣})
-- --      (hcomp (λ r → λ { (i = i0) → lb j k r
-- --                       ; (i = i1) → lb j k r
-- --                       ; (j = i0) → lb j k r
-- --                       ; (j = i1) → lb j k r
-- --                       ; (k = i0) → ∣ surf'' r i j ∣
-- --                       ; (k = i1) → ∣ surf''' r i j ∣})
-- --                ∣ base ∣)

-- --   m : (a : glS1) → Path (glS1*) ∣ a ∣ ∣ a ∣
-- --   m base = cong ∣_∣ₕ loop'
-- --   m (loop' i) j = l' i j i1
-- --   m (surf* i j) k = c3 i j k
-- --   m (surf'' i j k) l = {!!}
-- --     where
-- --     Sq1 : {!!}
-- --     Sq1 = {!!}
-- --   m (surf''' i j k) l = {!!}

-- --   bra : idEquiv glS1* ≡ idEquiv glS1*
-- --   bra = Σ≡Prop isPropIsEquiv
-- --                (funExt
-- --                (TR.elim (λ _ → isOfHLevelPath 4
-- --                  (isOfHLevelTrunc 4) _ _) m))

-- -- bacardi : (x : _) → base ≡ x → br x
-- -- bacardi = J> ∣ base ∣

-- -- Ω³→ : Ω³ S² base → Ω² glS1* ∣ base ∣
-- -- Ω³→ p i j = bacardi base (p i j)

-- -- gala : Ω³ S² base
-- -- gala = sym (rCancel surf) ∙∙ EH 0 surf (sym surf) ∙∙ lCancel surf

-- -- gh : S² → Type
-- -- gh base = Ω S³ base
-- -- gh (surf i j) =
-- --   Glue (Ω S³ base) λ {(i = i0) → Ω S³ base , c j
-- --                ; (i = i1) → Ω S³ base , idEquiv (Ω S³ base)
-- --                ; (j = i0) → Ω S³ base , idEquiv (Ω S³ base)
-- --                ; (j = i1) → Ω S³ base , idEquiv (Ω S³ base)}
-- --   where
-- --   gada : {!!}
-- --   gada = {!!}

-- --   brabra : (x : S³) (p : base ≡ x) → p ≡ p
-- --   brabra base p l k = {!p!}
-- --   brabra (surf i j k) p l q = {!!}

-- --   c : idEquiv (Ω S³ base) ≡ idEquiv (Ω S³ base)
-- --   c = Σ≡Prop isPropIsEquiv (funExt λ p → rUnit p ∙∙ cong (p ∙_) {!!} ∙∙ sym (rUnit p))

-- -- fib2 : glS1 → S²
-- -- fib2 base = base
-- -- fib2 (loop' i) = {!!}
-- -- fib2 (surf* i i₁) = surf i i₁
-- -- fib2 (surf'' i i₁ i₂) = {!gala i i₁ i₂!}
-- -- fib2 (surf''' i i₁ i₂) = {!!}

-- -- theMega : (x : S²) → (x ≡ x) → Type
-- -- theMega x = {!!}

-- -- brec : (x : S²) → base ≡ x → S²''
-- -- brec = J> ∣ base ∣



-- -- ΩS²→ : (Ω^ 3) (S² , base) .fst → Ω² S²'' ∣ base ∣
-- -- ΩS²→ p i j = brec base (p i j)

-- -- data S¹* : Type where
-- --   base : S¹*
-- --   l : base ≡ base
-- --   surf* : l ≡ l


-- -- S1* = hLevelTrunc 3 S¹*

-- -- Sq3 : Square {A = S1*} (cong ∣_∣ₕ l) (cong ∣_∣ₕ l) (cong ∣_∣ₕ l) (cong ∣_∣ₕ l)
-- -- Sq3 i j = hcomp (λ k → λ {(i = i0) → ∣ l (~ k ∨ j) ∣ ; (i = i1) → ∣ l (k ∧ j) ∣ ; (j = i0) → ∣ l (~ k ∨  i) ∣ ; (j = i1) → ∣ l (k ∧ i) ∣})
-- --                         ∣ base ∣

-- -- ma : (a : S¹*) → Path S1* ∣ a ∣ ∣ a ∣
-- -- ma base i = ∣ l i ∣
-- -- ma (l i) j = Sq3 i j
-- -- ma (surf* i j) k = help i j k
-- --   where
-- --   help : Cube Sq3 Sq3 (λ i k → ∣ l k ∣) (λ i k → ∣ l k ∣) (λ i j → ∣ surf* i j ∣) (λ i j → ∣ surf* i j ∣)
-- --   help = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelTrunc 3) _ _) _ _) _ _ .fst


-- -- help : idEquiv S1* ≡ idEquiv S1*
-- -- help = Σ≡Prop isPropIsEquiv (funExt (TR.elim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3)  _ _ )
-- --               ma))

-- -- sndFib : S²' → Type
-- -- sndFib base = hLevelTrunc 3 S¹*
-- -- sndFib (surf' i j) = Glue S1* λ {(i = i0) → S1* , idEquiv S1*
-- --                                ; (i = i1) → S1* , help j
-- --                                ; (j = i0) → S1* , idEquiv S1*
-- --                                ; (j = i1) → S1* , idEquiv S1*}
-- -- sndFib (high k i j) = Glue S1*
-- --          (λ { (i = i0) → S1* , idEquiv S1*
-- --             ; (i = i1) → S1* , help j
-- --             ; (j = i0) → S1* , idEquiv S1*
-- --             ; (j = i1) → S1* , idEquiv S1*
-- --             })

-- -- sndFib' : S²'' → Type
-- -- sndFib' ∣ x ∣ = sndFib x
-- -- sndFib' (hub f) = {!!}
-- -- sndFib' (spoke f x i) = {!!}

-- -- enc52 : (x : S²'') → ∣ base ∣ ≡ x → sndFib' x
-- -- enc52 = J> ∣ base ∣

-- -- m2 : Ω² S²'' ∣ base ∣ → Ω S1* ∣ base ∣
-- -- m2 p i = enc52 ∣ base ∣ (p i)


-- -- open import Cubical.Data.Fin.Arithmetic
-- -- open import Cubical.Foundations.Isomorphism
-- -- open import Cubical.Data.Int
-- -- S¹*→ : S¹* → Type
-- -- S¹*→ base = ℤ
-- -- S¹*→ (l i) = sucPathℤ i
-- -- S¹*→ (surf* i i₁) = sucPathℤ i₁

-- -- cool : (x : S1*) → Type
-- -- cool ∣ x ∣ = S¹*→ x
-- -- cool (hub f) = {!!}
-- -- cool (spoke f x i) = {!!}

-- -- enc4 : (x : S1*) → ∣ base ∣ ≡ x → ℤ
-- -- enc4 = J> 0

-- -- m4 : Ω S1* ∣ base ∣ → ℤ
-- -- m4 = enc4 ∣ base ∣

-- -- gl : Ω³ S² base
-- -- gl = sym (rCancel surf) ∙∙ EH 0 surf (sym surf) ∙∙ lCancel surf

-- -- mains : Ω³ S² base → ℤ
-- -- mains p = m4 (m2 (ΩS²→ p))

-- -- hLev-snd : (x : _) → isOfHLevel 3 (sndFib x)
-- -- hLev-snd = {!mains gl!}



-- -- sndmap : S²' → EM ℤ/2 2
-- -- sndmap base = ∣ north ∣
-- -- sndmap (surf' i i₁) = (sym (EM→ΩEM+1-0ₖ {G = ℤ/2} 1) ∙∙ cong (EM→ΩEM+1 {G = ℤ/2}  1) (EM→ΩEM+1 {G = ℤ/2} 0 (1 , 0 , refl)) ∙∙ EM→ΩEM+1-0ₖ {G = ℤ/2} 1) i i₁
-- -- sndmap (high i k m) = hcomp (λ r → λ{(i = i0) → p (k ∧ r) m
-- --                 ; (i = i1) → p (k ∧ r) m
-- --                 ; (k = i0) → p (k ∧ r) m
-- --                 ; (k = i1) → p (k ∧ r) m
-- --                 ; (m = i0) → p (k ∧ r) m
-- --                 ; (m = i1) → p (k ∧ r) m})
-- --         ∣ north ∣
-- --   where
-- --   p : _
-- --   p = (sym (EM→ΩEM+1-0ₖ {G = ℤ/2} 1) ∙∙ cong (EM→ΩEM+1 {G = ℤ/2}  1) (EM→ΩEM+1 {G = ℤ/2} 0 (1 , 0 , refl)) ∙∙ EM→ΩEM+1-0ₖ {G = ℤ/2} 1)



-- -- -- asd' : Path (Path (Path S² base base) refl refl) refl refl
-- -- -- asd' = sym (rCancel surf) ∙∙ EH 0 surf (sym surf) ∙∙ lCancel surf

-- -- -- pst : (Path (Path (hLevelTrunc 4 S²') ∣ base ∣ ∣ base ∣) refl refl)
-- -- --    → Path (Path (EM ℤ/2 2) ∣ north ∣ ∣ north ∣) refl refl
-- -- -- pst p i j = TR.rec (isOfHLevelTrunc 4) sndmap (p i j)

-- -- -- pst2 : Path (Path (EM ℤ/2 2) ∣ north ∣ ∣ north ∣) refl refl → ℕ
-- -- -- pst2 p = ΩEM+1→EM {G = ℤ/2} 0 (cong (ΩEM+1→EM {G = ℤ/2} 1) p) .fst

-- -- -- main : Path (Path (Path S² base base) refl refl) refl refl → ℕ
-- -- -- main p = pst2 (pst (del0^ p))




-- -- -- -- S³→S³* : S³ → S³*
-- -- -- -- S³→S³* x = {!!}

-- -- -- -- S³*→ : hLevelTrunc 6 S³ → hLevelTrunc 6 S³*
-- -- -- -- S³*→ = TR.map λ {base → b ; (surf i j k) → re b i j k}

-- -- -- -- S³*→Type : ∀ {ℓ} {A : S³* → Type ℓ} → ((x : _) → isOfHLevel {!!} (A x)) → {!!} 
-- -- -- -- S³*→Type = {!!}

-- -- -- -- open import Cubical.Foundations.Equiv
-- -- -- -- open import Cubical.Foundations.Function
-- -- -- -- open import Cubical.Foundations.Equiv

-- -- -- -- oth : S³ → Type
-- -- -- -- oth base = hLevelTrunc 5 S²*
-- -- -- -- oth (surf j i k) = Glue A λ {(i = i0) → A , idEquiv A
-- -- -- --                            ; (i = i1) → A , idEquiv A
-- -- -- --                            ; (j = i0) → A , l i k
-- -- -- --                            ; (j = i1) → A , idEquiv A
-- -- -- --                            ; (k = i0) → A , idEquiv A
-- -- -- --                            ; (k = i1) → A , idEquiv A}
-- -- -- --   where
-- -- -- --   A = hLevelTrunc 5 S²*

-- -- -- --   pst : (x : A) → Square (λ _ → x) (λ _ → x) (λ _ → x) (λ _ → x)
-- -- -- --   pst = TR.elim (λ _ → isOfHLevelPathP 5 (isOfHLevelPath 5 (isOfHLevelTrunc 5) _ _) _ _)
-- -- -- --         λ x i j → ∣ sq x i j ∣

-- -- -- --   l : Square {A = A ≃ A} (λ _ → idEquiv A) (λ _ → idEquiv A) (λ _ → idEquiv A) λ _ → idEquiv A
-- -- -- --   fst (l i j) x = pst x i j
-- -- -- --   snd (l i j) = S i j
-- -- -- --     where
-- -- -- --     S : SquareP (λ i j → isEquiv (λ x → pst x i j)) (λ _ → idIsEquiv A) (λ _ → idIsEquiv A) (λ _ → idIsEquiv A) (λ _ → idIsEquiv A)
-- -- -- --     S = isProp→PathP (λ _ → isOfHLevelPathP 1 (isPropIsEquiv _) _ _)  _ _

-- -- -- -- data S¹* : Type where
-- -- -- --   base : S¹*
-- -- -- --   l : (x : S¹*) → x ≡ x

-- -- -- -- A* = hLevelTrunc 4 S¹*

-- -- -- -- Sq1 : Square (λ _ → idEquiv A*) (λ _ → idEquiv A*) (λ _ → idEquiv A*)(λ _ → idEquiv A*)
-- -- -- -- Sq1 = {!!}

-- -- -- -- sq2' : (x : S²*) → (p : Square (λ _ → x) (λ _ → x) refl refl) → {!!}
-- -- -- -- sq2' = {!!}

-- -- -- -- open import Cubical.Data.Sigma
-- -- -- -- S¹↓ : (x : S²*) → Type
-- -- -- -- S¹↓ b = hLevelTrunc 4 S¹*
-- -- -- -- S¹↓ (sq b i j) = Glue A* λ {(i = i0) → A* , idEquiv A*
-- -- -- --                           ; (i = i1) → A* , idEquiv A*
-- -- -- --                           ; (j = i0) → A* , idEquiv A*
-- -- -- --                           ; (j = i1) → A* , asdd i}
-- -- -- --   where
-- -- -- --   sq1 : Square (l base) (l base) (l base) (l base)
-- -- -- --   sq1 i j = hcomp (λ k → λ {(i = i0) → l base (j ∨ ~ k)
-- -- -- --                            ; (i = i1) → l base (j ∧ k)
-- -- -- --                            ; (j = i0) → l base (i ∨ ~ k) -- l base (i ∧ k)
-- -- -- --                            ; (j = i1) → l base (i ∧ k)})
-- -- -- --                   base
-- -- -- --   asdd : idEquiv A* ≡ idEquiv A*
-- -- -- --   asdd = Σ≡Prop isPropIsEquiv (funExt (TR.elim {!!}
-- -- -- --     λ { base → cong ∣_∣ₕ (l base)
-- -- -- --       ; (l base i) j → ∣ sq1 i j ∣
-- -- -- --       ; (l (l base k) i) j → {!!}
-- -- -- --       ; (l (l (l base i₂) i₁) i) → {!!}
-- -- -- --       ; (l (l (l (l a i₃) i₂) i₁) i) → {!!}}))


-- -- -- -- S¹↓ (sq (sq b i j) k r) = {!!}
-- -- -- --   where
-- -- -- --   h : Cube (λ _ _ → idEquiv A*) (λ _ _ → idEquiv A*) (λ _ _ → idEquiv A*) (λ _ _ → idEquiv A*) (λ _ _ → idEquiv A*) λ _ _ → idEquiv A*
-- -- -- --   fst (h i j k) x = {!!}
-- -- -- --   snd (h i j k) = {!!}

-- -- -- --   h≡ : h ≡ refl
-- -- -- --   h≡ = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (isOfHLevelPath' 3 (isOfHLevelΣ 4 (isOfHLevelΠ 4 (λ _ → isOfHLevelTrunc 4)) {!!}) _ _ ) _ _) _ _) _ _ .fst
-- -- -- -- S¹↓ (sq (sq (sq x x₁ x₂) i j) k r) = {!!}

-- -- -- -- S²*→Bool : {!!}
-- -- -- -- S²*→Bool = {!!}
