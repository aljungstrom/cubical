{-# OPTIONS --safe --experimental-lossy-unification #-}

{-
This file contains
1. The Thom isomorphism (various related forms of it)
2. The Gysin sequence
-}
open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct

open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.GradedCommTensor
  hiding (⌣ₖ-comm)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import Cubical.Functions.Morphism
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.EilenbergMacLane1.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.S1

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order hiding (eq)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_≤_)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.HITs.RPn
open import Cubical.Homotopy.EilenbergMacLane.Order2

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.SmashProduct

open import Cubical.Foundations.Univalence


module Cubical.Cohomology.EilenbergMacLane.Steenrod where

RP∞ = 2-EltType₀

2-Elt≃ : (X Y : RP∞) → fst X ≃ fst Y → X ≡ Y
2-Elt≃ X Y p = Σ≡Prop (λ _ → squash₁) (ua p)

RP∞pt→Prop : ∀ {ℓ} {B : RP∞ → Type ℓ}
  → ((x : _) → isProp (B x))
  → B Bool*
  → (x : _) → B x
RP∞pt→Prop {B = B} p b =
  uncurry λ X → PT.elim (λ _ → p _)
    λ x → subst B (2-Elt≃ Bool* (X , ∣ x ∣₁) (invEquiv x)) b

DiscreteBool : Discrete Bool
DiscreteBool false false = yes refl
DiscreteBool false true = no (true≢false ∘ sym)
DiscreteBool true false = no true≢false
DiscreteBool true true = yes refl

decPt : (X : RP∞) → Discrete (fst X)
decPt = RP∞pt→Prop (λ _ → isPropDiscrete) DiscreteBool

Bool≃Charac : Iso (Bool ≃ Bool) Bool
Bool≃Charac = iso F G (λ { false → refl ; true → refl}) λ e → Σ≡Prop isPropIsEquiv (funExt (F→G→F e))
  where
  F : Bool ≃ Bool → Bool
  F e = fst e true

  G : Bool → Bool ≃ Bool
  G false = notEquiv
  G true = idEquiv Bool

  F→G→F : (e : Bool ≃ Bool) (x : Bool) → G (F e) .fst x ≡ e .fst x
  F→G→F e with (dichotomyBool (fst e true)) | (dichotomyBool (fst e false))
  ... | inl p | inl q = ⊥.rec
    (true≢false (sym (retEq e true) ∙∙ cong (invEq e) (p ∙ sym q) ∙∙ retEq e false))
  ... | inl p | inr q = λ { false → (λ i → G (p i) .fst false) ∙ sym q
                          ; true → (λ i → G (p i) .fst true) ∙ sym p}
  ... | inr p | inl q = λ { false → (λ i → G (p i) .fst false) ∙ sym q
                          ; true → (λ i → G (p i) .fst true) ∙ sym p}
  ... | inr p | inr q =
    ⊥.rec (true≢false  (sym (retEq e true) ∙∙ cong (invEq e) (p ∙ sym q) ∙∙ retEq e false))

BoolAutoElim : ∀ {ℓ} {A : Bool ≃ Bool → Type ℓ}
  → A (idEquiv Bool)
  → A notEquiv
  → (x : _) → A x
BoolAutoElim {A = A} p q e with (dichotomyBool (fst e true))
... | inl z = subst A (cong (Iso.inv Bool≃Charac) (sym z)
                     ∙ Iso.leftInv Bool≃Charac e ) p
... | inr z = subst A (cong (Iso.inv Bool≃Charac) (sym z)
                     ∙ Iso.leftInv Bool≃Charac e) q

pst : {x y : Bool} → isProp (Bool , x ≃∙ Bool , y)
pst {x} {y} =
  subst2 (λ x y → isProp (x ≃∙ y)) (help x) (help y)
    (isContr→isProp lem)
  where
  lem : isContr (Bool , true ≃∙ Bool , true)
  fst lem = idEquiv Bool , refl
  snd lem e = Σ≡Prop (λ _ → isSetBool _ _)
    (cong (Iso.inv Bool≃Charac) (sym (snd e)) ∙ Iso.leftInv Bool≃Charac (fst e))

  help : isHomogeneous (Bool , true)
  help false = ΣPathP ((ua notEquiv) , toPathP refl)
  help true = refl

isPropNegBool : isProp (Σ[ e ∈ (Bool ≃ Bool) ] ¬ e ≡ idEquiv Bool)
isPropNegBool = isContr→isProp help
  where
  help : isContr (Σ[ e ∈ (Bool ≃ Bool) ] ¬ e ≡ idEquiv Bool)
  fst help = notEquiv , (λ p → true≢false (funExt⁻ (cong fst p) false))
  snd help (e , g) =
    Σ≡Prop (λ _ → isProp¬ _)
      (⊎.rec (λ p → ⊥.rec (g (sym (Iso.leftInv Bool≃Charac e)
                    ∙ cong (Iso.inv Bool≃Charac) p)))
              (λ p → sym (cong (Iso.inv Bool≃Charac) p)
                        ∙ (Iso.leftInv Bool≃Charac e))
              (dichotomyBool (fst e true)))

isPropNegRP∞ : (X : RP∞) → isProp (Σ[ e ∈ (fst X ≃ fst X) ] ¬ e ≡ idEquiv (fst X))
isPropNegRP∞ = RP∞pt→Prop (λ _ → isPropIsProp) isPropNegBool

notEquiv* : (X : RP∞) → Σ[ e ∈ (fst X ≃ fst X) ] ¬ e ≡ idEquiv (fst X)
notEquiv* =
  RP∞pt→Prop isPropNegRP∞
    (notEquiv , (λ p → true≢false (funExt⁻ (cong fst p) false)))

isSetRPpt : (X : RP∞) → isSet (fst X)
isSetRPpt = RP∞pt→Prop (λ _ → isPropIsSet) isSetBool

not* : (X : RP∞) → fst X → fst X
not* X = fst (fst (notEquiv* X))

not*not* : (X : RP∞) (x : fst X) → not* X (not* X x) ≡ x
not*not* = RP∞pt→Prop (λ X → isPropΠ λ _ → isSetRPpt X _ _)
  λ { false → refl ; true → refl}

not-charac : (X : RP∞) (x y : fst X) → ¬ x ≡ y → x ≡ not* X y
not-charac = RP∞pt→Prop (λ X → isPropΠ3 λ _ _ _ → isSetRPpt X _ _)
  λ { false false q → ⊥.rec (q refl)
    ; false true _ → refl
    ; true false _ → refl
    ; true true q → ⊥.rec (q refl)}

¬not≡id : (X : RP∞) (x : fst X) → ¬ x ≡ not* X x
¬not≡id =
  RP∞pt→Prop (λ _ → isPropΠ λ _ → isProp¬ _)
    λ { false → true≢false ∘ sym ; true → true≢false}


preCasesRP : ∀ {ℓ} (X : RP∞) {A : fst X → Type ℓ} (x₀ : fst X)
  → A x₀
  → A (not* X x₀)
  → (x : _) → Dec (x₀ ≡ x)
  → A x
preCasesRP X {A = A} x₀ l r x (yes p) = subst A p l
preCasesRP X {A = A} x₀ l r x (no ¬p) = subst A (sym (not-charac X x x₀ (¬p ∘ sym))) r

CasesRP : ∀ {ℓ} (X : RP∞) {A : fst X → Type ℓ} (x₀ : fst X)
  → A x₀ → A (not* X x₀) → (x : _) → A x
CasesRP X {A = A} x₀ l r x = preCasesRP X x₀ l r x (decPt X x₀ x)

CasesRPβ : ∀ {ℓ} (X : RP∞) {A : fst X → Type ℓ} (x₀ : fst X)
  → (l : A x₀) (r : A (not* X x₀))
  → (CasesRP X {A = A} x₀ l r x₀ ≡ l)
   × (CasesRP X {A = A} x₀ l r (not* X x₀) ≡ r)
fst (CasesRPβ X x₀ l r) =
  cong (preCasesRP X x₀ l r x₀)
    (isPropDec (isSetRPpt X _ _) (decPt X x₀ x₀) (yes refl))
    ∙ transportRefl l
snd (CasesRPβ X {A = A} x₀ l r) =
    cong (preCasesRP X x₀ l r (not* X x₀))
    (isPropDec (isSetRPpt X _ _) (decPt X x₀ (not* X x₀))
      (no (¬not≡id X x₀)))
  ∙ (λ i → subst A (isSetRPpt X _ _ (sym (not-charac X (not* X x₀) x₀
                     (λ x → ¬not≡id X x₀ (λ i₁ → x (~ i₁))))) refl i) r)
  ∙ transportRefl r

∑RP : (X : RP∞) (n : fst X → ℕ) → ℕ
∑RP = uncurry λ X → rec→Set (isSetΠ (λ _ → isSetℕ))
  (λ e n → n (invEq e true) + n (invEq e false))
  (EquivJ (λ X e → (y : X ≃ Bool) →
      (λ (n : X → ℕ) → n (invEq e true) + n (invEq e false)) ≡
      (λ n → n (invEq y true) + n (invEq y false)))
    (BoolAutoElim refl
      (funExt λ n → +-comm _ _)))


∑∑RP : (X Y : RP∞) (n : fst X → fst Y → ℕ) → ℕ
∑∑RP = uncurry λ X
  → rec→Set
       (isSetΠ2 (λ _ _ → isSetℕ))
       (λ e → λ Y n → ∑RP Y (n (invEq e false)) + ∑RP Y (n (invEq e true)))
       (EquivJ (λ X e → (y : X ≃ Bool) →
      (λ (Y : RP∞) (n : X → fst Y → ℕ)
        → ∑RP Y (n (invEq e false)) + ∑RP Y (n (invEq e true))) ≡
      (λ Y n → ∑RP Y (n (invEq y false)) + ∑RP Y (n (invEq y true))))
      (BoolAutoElim refl
        (funExt λ Y → funExt λ n
          → +-comm _ _)))



module genSmash {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ)
                (f : (x : fst X) (a : fst (A x)) → (x : fst X) → A x .fst ) where
  data ⋀∞gen  : Type ℓ where
    proj : ((x : fst X) → A x .fst) → ⋀∞gen
    base : fst X → ⋀∞gen
    gl : (x : fst X) (a : fst (A x)) → proj (f x a) ≡ base x

  proj* : ((x : fst X) → A x .fst) → ⋀∞gen
  proj* = proj


gen* : {!(X Y : RP∞) → ?!}
gen* = {!!}

2CaseBool : {ℓ : Level} (A : Bool → Pointed ℓ)
  → (x : Bool) → fst (A x) → (x₁ : Bool) → A x₁ .fst
2CaseBool A false p false = p
2CaseBool A false p true = A true .snd
2CaseBool A true p false = A false .snd
2CaseBool A true p true = p

module _ {ℓ : Level} (A : Bool → Pointed ℓ) where
  open genSmash renaming (⋀∞gen to ⋀∞)
  ⋀∞→Smash : ⋀∞ Bool* A (2CaseBool A)
           → Smash (A true) (A false)
  ⋀∞→Smash (proj f) = proj (f true) (f false)
  ⋀∞→Smash (base false) = baser
  ⋀∞→Smash (base true) = basel
  ⋀∞→Smash (gl false a i) = gluer a i
  ⋀∞→Smash (gl true a i) = gluel a i

  toBool→ : (x : A true .fst) (y : A false .fst) → (x : Bool) → A x .fst
  toBool→ x y false = y
  toBool→ x y true = x

  toBool→≡₁ : (x : A true .fst) → toBool→ x (pt (A false)) ≡ 2CaseBool A true x
  toBool→≡₁ x = funExt λ { false → refl ; true → refl}

  toBool→≡₂ : (x : A false .fst) → toBool→ (pt (A true)) x ≡ 2CaseBool A false x
  toBool→≡₂ x = funExt λ { false → refl ; true → refl}

  Smash→⋀∞ : Smash (A true) (A false)
    → ⋀∞ Bool* A (2CaseBool A)
  Smash→⋀∞ basel = base true
  Smash→⋀∞ baser = base false
  Smash→⋀∞ (proj x y) = proj (toBool→ x y)
  Smash→⋀∞ (gluel a i) = ((λ i → proj (toBool→≡₁ a i)) ∙ gl true a) i
  Smash→⋀∞ (gluer b i) = ((λ i → proj (toBool→≡₂ b i)) ∙ gl false b) i

  Smash→⋀∞→Smash : (x : Smash (A true) (A false)) → ⋀∞→Smash (Smash→⋀∞ x) ≡ x
  Smash→⋀∞→Smash basel = refl
  Smash→⋀∞→Smash baser = refl
  Smash→⋀∞→Smash (proj x y) = refl
  Smash→⋀∞→Smash (gluel a i) j = help j i
    where
    help : cong (⋀∞→Smash) ((λ i → proj (toBool→≡₁ a i)) ∙ gl true a)
         ≡ gluel a
    help = cong-∙ ⋀∞→Smash (λ i → proj (toBool→≡₁ a i)) (gl true a)
         ∙ sym (lUnit _)
  Smash→⋀∞→Smash (gluer b i) j = help j i
    where
    help : cong (⋀∞→Smash) ((λ i → proj (toBool→≡₂ b i)) ∙ gl false b)
         ≡ gluer b
    help = cong-∙ ⋀∞→Smash (λ i → proj (toBool→≡₂ b i)) (gl false b)
         ∙ sym (lUnit _)

  toBool→diag : (f : ((x : Bool) → A x .fst))
    →  (toBool→ (f true) (f false)) ≡ f
  toBool→diag f = funExt λ { false → refl ; true → refl}

  ⋀∞→Smash→⋀∞ : (x : ⋀∞ Bool* A (2CaseBool A))
    → (Smash→⋀∞ (⋀∞→Smash x)) ≡ x
  ⋀∞→Smash→⋀∞ (proj x) i = proj (toBool→diag x i)
  ⋀∞→Smash→⋀∞ (base false) = refl
  ⋀∞→Smash→⋀∞ (base true) = refl
  ⋀∞→Smash→⋀∞ (gl false a i) j = lem j i
    where
    help' : toBool→diag (2CaseBool A false a) ≡ toBool→≡₂ a
    help' = cong funExt (funExt λ { false → refl ; true → refl})


    lem : PathP (λ j → Path (⋀∞ Bool* A (2CaseBool A))
                             (proj (toBool→diag (2CaseBool A false a) j))
                             (base false))
                (((λ i₁ → proj (toBool→≡₂ a i₁)) ∙ gl false a)) (gl false a)
    lem = cong (_∙ gl false a) (λ i j → proj (help' (~ i) j))
        ◁ λ i j → compPath-filler'
          (λ i → proj (toBool→diag (2CaseBool A false a) i))
          (gl false a) (~ i) j

  ⋀∞→Smash→⋀∞ (gl true a i) j = lem j i
    where
    help' : toBool→diag (2CaseBool A true a) ≡ toBool→≡₁ a
    help' = cong funExt (funExt λ { false → refl ; true → refl})


    lem : PathP (λ j → Path (⋀∞ Bool* A (2CaseBool A))
                             (proj (toBool→diag (2CaseBool A true a) j))
                             (base true))
                (((λ i₁ → proj (toBool→≡₁ a i₁)) ∙ gl true a)) (gl true a)
    lem = cong (_∙ gl true a) (λ i j → proj (help' (~ i) j))
        ◁ λ i j → compPath-filler'
          (λ i → proj (toBool→diag (2CaseBool A true a) i))
          (gl true a) (~ i) j

  ⋀∞≃Smash : Iso (⋀∞ Bool* A (2CaseBool A)) (Smash (A true) (A false))
  Iso.fun ⋀∞≃Smash = ⋀∞→Smash
  Iso.inv ⋀∞≃Smash = Smash→⋀∞
  Iso.rightInv ⋀∞≃Smash = Smash→⋀∞→Smash
  Iso.leftInv ⋀∞≃Smash = ⋀∞→Smash→⋀∞


myInd : {!∀ {ℓ} {A : Type ℓ} → ?!}
myInd = {!!}


module _ {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ) where
  module M = genSmash X A (λ x a → CasesRP X {fst ∘ A} x a ((snd ∘ A) (not* X x)))
  open M public renaming (⋀∞gen to ⋀∞)

  ⋀∞∙ : Pointed _
  fst ⋀∞∙ = ⋀∞
  snd ⋀∞∙ = proj λ x → A x .snd

anId : {ℓ : Level} (A : Bool → Pointed ℓ)
  → Path ((x : Bool) (a : fst (A x)) → (x : Bool) → A x .fst)
          (λ x a → CasesRP Bool* {fst ∘ A} x a ((snd ∘ A) (not* Bool* x)))
          (2CaseBool A)
anId A =
  funExt λ { false → funExt λ a
    → funExt λ { false → transportRefl a
                ; true → transportRefl (A true .snd)}
                ; true → funExt λ a
         → funExt λ { false → transportRefl (A false .snd)
                     ; true → transportRefl a}}

Iso-⋀∞Bool : ∀ {ℓ} (A : Bool → Pointed ℓ)
  → Iso (⋀∞ Bool* A) (Smash (A true) (A false))
Iso-⋀∞Bool A =
  compIso (pathToIso (cong (genSmash.⋀∞gen Bool* A) (anId A))) (⋀∞≃Smash A)

Iso-⋀∞Bool-funId : ∀ {ℓ} (A : Bool → Pointed ℓ)
  (e : (x : fst Bool*) → A x .fst)
  → Iso.fun (Iso-⋀∞Bool A) (proj e) ≡ proj (e true) (e false)
Iso-⋀∞Bool-funId A e i = proj (transportRefl (e true) i) (transportRefl (e false) i)

Kgen : (X : RP∞) (n : fst X → ℕ) → Pointed₀
Kgen X n = EM∙ ℤ/2 (∑RP X n)

K∙ = EM∙ ℤ/2
K = EM ℤ/2

module _ (⌣gen : (X : RP∞) (n : fst X → ℕ)
       → ⋀∞∙ X (λ x → K∙ (n x))
       →∙ K∙ (∑RP X n)) where
  module _ (X : RP∞) (n : fst X → ℕ) where
    Πpt :  (((x : fst X) → K (n x)) , λ x → 0ₖ (n x)) →∙ K∙ (∑RP X n)
    fst Πpt f = ⌣gen X n .fst (proj f)
    snd Πpt = ⌣gen X n .snd

  lem' : (n : ℕ) (X : RP∞) → ∑RP X (λ _ → n) ≡ n + n
  lem' n = RP∞pt→Prop (λ _ → isSetℕ _ _) refl

  Sq : (n : ℕ) → K n × RP∞ → K (n + n)
  Sq n (x , t) = subst K (lem' n t) (Πpt t (λ _ → n) .fst λ _ → x)

  genconst : (t : RP∞) (n : fst t → ℕ)
    → ((x : fst t) → K (n x)) → K (∑RP t n)
  genconst t n s = Πpt t n .fst s

  doubler : (t s : RP∞) (n : fst t → fst s → ℕ)
       (a : (x : fst t) (y : fst s) → K (n x y))
    → K (∑RP t (λ z → ∑RP s (n z)))
  doubler t s n a =
    genconst t (λ z → ∑RP s (n z))
       λ x → genconst s (n x) (a x)

  S'S' : (X Y : RP∞) (n : fst X → fst Y → ℕ) → (x : fst X) (y : fst Y)
    → (K∙ (n x y) ⋀∙ K∙ (n x (not* Y y))) ⋀ (K∙ (n (not* X x) y) ⋀∙ K∙ (n (not* X x) (not* Y y))) → K (∑RP X (λ x → ∑RP Y (n x))) 
  S'S' X Y n x y (inl x₁) = {!!}
  S'S' X Y n x y (inr (inl x₁ , b)) = {!!}
  S'S' X Y n x y (inr (inr x₁ , inl x₂)) = {!!}
  S'S' X Y n x y (inr (inr x₁ , inr x₂)) = Πpt X (λ x → ∑RP Y (n x)) .fst λ x' → Πpt Y (n x') .fst λ y → {!⌣gen X ? .fst ? .fst ?!} --  ⌣gen X (λ x → {!n x y!}) .fst (proj {!!})
  S'S' X Y n x y (inr (inr x₁ , push a i)) = {!!}
  S'S' X Y n x y (inr (push a i , b)) = {!!}
  S'S' X Y n x y (push a i) = {!!}

{-
  SS : (X Y : RP∞) (n : fst X → fst Y → ℕ) → Pointed₀ 
  SS X Y n = ⋀∞∙ X λ x → ⋀∞∙ Y λ y → K∙ (n x y)

  SS' : (X Y : RP∞) (n : fst X → fst Y → ℕ) → Pointed₀ 
  SS' X Y n = ⋀∞∙ Y λ y → ⋀∞∙ X λ x → K∙ (n x y)

  test123 : (X : RP∞) (A : fst X → Pointed₀) → Susp (Susp (⋀∞ X A)) → ⋀∞ X (λ x → Susp∙ (fst (A x)))
  test123 X A north = proj λ _ → north
  test123 X A south = proj λ _ → south
  test123 X A (merid north i) = {!!}
  test123 X A (merid south i) = {!!}
  test123 X A (merid (merid a i₁) i) = {!!}

  SS→ : (X Y : RP∞) (n : fst X → fst Y → ℕ)
    → SS X Y n .fst
    → K (∑RP X (λ x → ∑RP Y (n x)))
  SS→ X Y n (genSmash.proj f) =
    genconst X (λ x → ∑RP Y (n x))
      λ x → ⌣gen Y (n x) .fst (f x)
  SS→ X Y n (genSmash.base x) = 0ₖ (∑RP X (λ x₁ → ∑RP Y (n x₁)))
  SS→ X Y n (genSmash.gl x (genSmash.proj x₁) i) = {!!}
  SS→ X Y n (genSmash.gl x (genSmash.base x₁) i) = {!!}
  SS→ X Y n (genSmash.gl x (genSmash.gl x₁ a i) j) = {!!}

  SS→* : (X Y : RP∞) (n : fst X → fst Y → ℕ)
    → SS X Y n .fst
    → K (∑RP Y (λ y → ∑RP X (λ x → n x y)))
  SS→* X Y n (genSmash.proj x) =
    ⌣gen Y (λ y → ∑RP X (λ x₁ → n x₁ y)) .fst
      (proj λ y → {!x ?!})
  SS→* X Y n (genSmash.base x) = {!!}
  SS→* X Y n (genSmash.gl x a i) = {!!}

hPropFib : ∀ {ℓ} (X : RP∞) (A : fst X → fst X → Pointed ℓ)
  → ((x y : _) → isProp (typ (A x y)))
  → hProp ℓ
hPropFib = uncurry (λ X
  → rec→Set {!!}
    (λ e A pr → A (invEq e true) (invEq e false) .fst , {!!})
    λ e g → funExt λ A → funExt λ z → Σ≡Prop {!!} {!!})
-}

module _ (⌣gen : (X : RP∞) (n : fst X → ℕ)
       → ⋀∞∙ X (λ x → K∙ (n x))
       →∙ K∙ (∑RP X n)) where
  h : (m : ℕ) (x : K m) (y y' : RP∞)
    → Sq ⌣gen (m + m) ((Sq ⌣gen m (x , y')) , y)
     ≡ Sq ⌣gen (m + m) ((Sq ⌣gen m (x , y)) , y')
  h m x y y' = {!Πpt ⌣gen y (λ _ → m + m) .fst (λ _ → Sq ⌣gen m (x , y'))!}

{-
SqA : (n : ℕ) → K n × RP∞ → K (n + n)
Sq n (x , t) = subst K (lem' n t) (Πpt t (λ _ → n) .fst λ _ → x)
-}

-- flipBool : {X : Type₀} → X ≃ Bool → X ≃ Bool
-- flipBool e = compEquiv e notEquiv

-- notComm : (X : RP∞) (e : fst X ≃ Bool)
--   → not* X (invEq e true) ≡ invEq e false
-- notComm =
--   RP∞pt→Prop (λ X → isPropΠ λ _ → isSetRPpt X _ _)
--     λ e → {!funExt⁻ (cong fst (Iso.leftInv Bool≃Charac (invEquiv e))) x!} ∙∙ {!!} ∙∙ funExt⁻ (cong invEq (Iso.leftInv Bool≃Charac e)) false

-- liftHom : (X : RP∞) (A : fst X → Pointed₀) (C : Type)
--   → (e : fst X ≃ Bool)
--   → (((x : fst X) → A x .fst) → C)
--   → A (invEq e true) .fst → A (invEq e false) .fst → C
-- liftHom X A C e f x y =
--   f (CasesRP X (invEq e true) x (subst (fst ∘ A) (sym (notComm X e)) y))

-- test123 : (A B C : Pointed₀)
--   → Iso (A →∙ (B →∙ C ∙))
--       (Σ[ f ∈ (fst A → fst B → fst C) ]
--         Σ[ l ∈ ((x : fst A) → f x (pt B) ≡ pt C) ]
--           Σ[ r ∈ ((y : fst B) → f (pt A) y ≡ pt C) ]
--               PathP (λ i → r (pt B) i ≡ snd C)
--                (l (pt A)) (λ _ → pt C) )
-- Iso.fun (test123 A B C) f = (λ x y → f .fst x .fst y)
--                           , ((λ x → f .fst x .snd)
--                           , (λ y i → f .snd i .fst y)
--                           , cong snd (snd f))
-- Iso.inv (test123 A B C) = {!!}
-- Iso.rightInv (test123 A B C) = {!!}
-- Iso.leftInv (test123 A B C) = {!!}

-- ind* : (X : RP∞) → fst X → fst X ≃ Bool
-- ind* X x = isoToEquiv (iso (F⁻ X x) (F X x) (F-F X x .snd) (F-F X x .fst))
--   where
--   F : (X : RP∞) → fst X → Bool → fst X
--   F X x false = not* X x
--   F X x true = x

--   F⁻ : (X : RP∞) → fst X → fst X → Bool
--   F⁻ X x = CasesRP X x true false

--   F-F : (X : RP∞) (x : fst X) → ((y : fst X) → F X x (F⁻ X x y) ≡ y) × ((y : Bool) → F⁻ X x (F X x y) ≡ y)
--   F-F =
--     uncurry λ X → PT.elim (λ p
--       → isPropΠ λ _ → isProp× (isPropΠ (λ _ → isSetRPpt (X , p) _ _))
--          (isPropΠ (λ _ → isSetBool _ _)))
--       (EquivJ (λ X x₁ → (x₂ : X) → ((y : X) → F (X , ∣ x₁ ∣₁) x₂ (F⁻ (X , ∣ x₁ ∣₁) x₂ y) ≡ y) ×
--       ((y : Bool) → F⁻ (X , ∣ x₁ ∣₁) x₂ (F (X , ∣ x₁ ∣₁) x₂ y) ≡ y))
--         λ { false → (λ { false → refl ; true → refl}) , λ { false → refl ; true → refl}
--           ; true → (λ { false → refl ; true → refl}) , λ { false → refl ; true → refl}})

-- ind** : ∀ {ℓ} (A : (X : RP∞) → fst X → Type ℓ)
--   → Σ[ F ∈ (A Bool* true → (x : _) (y : _) → A x y) ] ((p : A Bool* true) → F p Bool* true ≡ p)
-- ind** A = (λ p x y → subst A' (sym (Path1 x y)) p)
--         , λ p → cong (λ x → subst A' (sym x) p) Path1≡refl ∙ transportRefl p
--   where
--   help : (x : RP∞) (y : fst x) → x ≡ Bool*
--   help x y = Σ≡Prop (λ _ → squash₁) (ua (ind* x y))

--   ind*-lem : ind* Bool* true ≡ idEquiv _
--   ind*-lem = Σ≡Prop isPropIsEquiv (funExt λ { false → refl ; true → refl})

--   abstract
--     help-base : help Bool* true ≡ refl 
--     help-base = (λ i → Σ≡Prop (λ _ → squash₁) (ua (ind*-lem i)))
--       ∙ ΣSquareSet (λ _ → isProp→isSet squash₁) uaIdEquiv

--   p2 : (x : RP∞) (y : fst x) → PathP (λ i → help x y i .fst) y true
--   p2 = uncurry λ X → PT.elim (λ _ → isPropΠ λ _ → isOfHLevelPathP' 1 isSetBool _ _)
--     (EquivJ (λ X x → (y : X) →
--       PathP (λ i → help (X , ∣ x ∣₁) y i .fst) y true)
--         λ { false → toPathP refl ; true → toPathP refl})

--   p2-pp : PathP (λ i → PathP (λ X → help-base i X .fst) true true) (p2 Bool* true) refl
--   p2-pp = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 isSetBool _ _) _ _ .fst

--   A' : Σ RP∞ fst → Type _
--   A' (x , p) = A x p

--   Path1 : (x : RP∞) (y : fst x) → Path (Σ RP∞ fst) (x , y) (Bool* , true)
--   Path1 x y = ΣPathP ((help x y ) , (p2 x y))

--   Path1≡refl : Path1 Bool* true ≡ refl
--   Path1≡refl = ΣSquareSet (λ X → isSetRPpt X) help-base

--   pst' : (x : RP∞) (y : fst x) → A x y ≡ A Bool* true
--   pst' x y i = A (help x y i) (p2 x y i)

-- bakam : (A B C : Pointed₀)
--   → isHomogeneous C
--   → isSet (A →∙ (B →∙ C ∙))
--   → isSet
--         (Σ[ f ∈ (fst A → (fst B → fst C)) ]
--          (Σ[ l ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
--            Σ[ r ∈ ((a : fst A) → f a (pt B) ≡ pt C) ]
--              ∥ PathP (λ i → l (pt B) i ≡ pt C) (r (pt A)) refl ∥₂))
-- bakam A B C hom c =
--   uncurry λ f1 → uncurry λ l1 → uncurry
--     λ r1 → ST.elim (λ _ → isSetΠ λ _ → isProp→isSet isPropIsProp)
--       λ q1
--       → uncurry λ f2 → uncurry λ l2 → uncurry
--     λ r2 → ST.elim (λ _ → isProp→isSet isPropIsProp)
--       λ q2 → {!!}
--   where
--   T' : Type _
--   T' = Σ[ q ∈ Σ[ f ∈ (fst A → (fst B → fst C)) ]
--                (Σ[ l ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
--                 ((a : fst A) → f a (pt B) ≡ pt C)) ]
--         ∥ PathP (λ i → q .snd .fst (pt B) i ≡ pt C) (q .snd .snd (pt A)) refl ∥₂

--   T = (Σ[ f ∈ (fst A → (fst B → fst C)) ]
--          (Σ[ l ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
--            Σ[ r ∈ ((a : fst A) → f a (pt B) ≡ pt C) ]
--              ∥ PathP (λ i → l (pt B) i ≡ pt C) (r (pt A)) refl ∥₂))


--   to : (A →∙ (B →∙ C ∙)) → T
--   to f = (λ x y → fst f x .fst y)
--        , ((λ b → λ i → snd f i .fst b)
--        , ((λ a → fst f a .snd) , ∣ cong snd (snd f) ∣₂)) -- (f , l , r , ∣ p ∣₂)

--   back : T → A →∙ (B →∙ C ∙)
--   back = uncurry λ f → uncurry λ l → uncurry λ r → ST.rec c λ q → (λ x → f x , r x) , (λ i → (λ b → l b i) , (q i))



--   ptsd : isSet T'
--   ptsd = λ {((f , l , r) , p) → J> λ y → {!!}}
--   {- uncurry λ {(f , l  , r)
--     → ST.elim (λ _ → isSetΠ λ _ → isProp→isSet isPropIsProp)
--          λ q1 → uncurry λ {(f2 , l2  , r2)
--     → ST.elim (λ _ → isProp→isSet isPropIsProp)
--       λ q2 → λ p q → ΣSquareSet (λ _ → squash₂)
--         {!c (back (f , (l , (r , ∣ q1 ∣₂)))) ((back (f , (l , (r , ∣ q1 ∣₂))))) !}}}
-- -}

--   open import Cubical.Functions.Embedding



--   back-emb : isEmbedding back
--   back-emb x y = isoToIsEquiv (iso _ (h x y)
--     (λ q → {!!})
--      λ q → {!!})
--     where
--     h : (x y : _) → back x ≡ back y → x ≡ y
--     h x y p = {!!} --  ΣPathP ((λ i a b → {!p i .fst a .fst b!}) , {!!}) -- →∙Homogeneous≡ (isHomogeneous→∙ hom) (funExt λ a → →∙Homogeneous≡ hom (λ i b → fst (q i) a b))

--     h⁻ : {!!}
--     h⁻ = {!!}


-- foo : ∀ {ℓ} (A : (X : RP∞) → fst X → Type ℓ) → Iso ((x : _) (y : _) → A x y) (A Bool* true)
-- Iso.fun (foo A) F = F Bool* true
-- Iso.inv (foo A) = ind** A .fst
-- Iso.rightInv (foo A) p = ind** A .snd p
-- Iso.leftInv (foo A) F = funExt λ X → funExt (help X)
--   where
--   help : (X : RP∞) (y : fst X) → ind** A .fst (F Bool* true) X y ≡ F X y
--   help = ind** (λ X y → ind** A .fst (F Bool* true) X y ≡ F X y) .fst (ind** A .snd (F Bool* true))


-- majp : {!(A : (X : RP∞) (x : fst X) → Pointed₀) (B : (X : RP∞) (x : fst X) → Pointed₀) → ?!}
-- majp = {!!}

-- ind**a : (A : (X : RP∞) (x : fst X) → Pointed₀) (B : (X : RP∞) (x : fst X) → Pointed₀)
--   → (((X : RP∞) (x : fst X) → A X x .fst) → (X : RP∞) (x : fst X) → B X x .fst)
--   → Σ[ X ∈ RP∞ ] (⋀∞ X (A X)) → Σ[ X ∈ RP∞ ] ((x : fst X) → B X x .fst)
-- ind**a A B ind (X , genSmash.proj x) = {!x!} , (ind (λ X q → {!!}) X )
-- ind**a A B ind (X , genSmash.base x) = {!!}
-- ind**a A B ind (X , genSmash.gl x a i) = {!!}

-- module _ (A : (X : RP∞) → (x : fst X) → (Y : RP∞) → (y : fst Y) → (fst X → fst Y → ℕ) → Pointed₀)
--   where
--   l' : (X : RP∞) (Y : RP∞) (n : fst X → fst Y → ℕ) → Type _
--   l' X Y n = ⋀∞ X λ x → ⋀∞ Y (λ y → A X x Y y n) , proj (λ y → A X x Y y n .snd)

--   r' : (X : RP∞) (Y : RP∞) (n : fst X → fst Y → ℕ) → Type _
--   r' X Y n = ⋀∞ Y λ y → ⋀∞ X (λ x → A X x Y y n) , proj (λ x → A X x Y y n .snd)

--   IS1 : (Y : RP∞) → Iso ((X : RP∞) (x₁ : fst X) → (n : fst X → fst Y → ℕ) → ⋀∞ Y (λ Y₁ → A X x₁ Y Y₁ n)) ((n : Bool → fst Y → ℕ) → ⋀∞ Y (λ Y₁ → A Bool* true Y Y₁ n))
--   IS1 Y = foo _

--   blahem : (X : RP∞) (Y : RP∞) (n : fst X → fst Y → ℕ) →
--       l' X Y n → r' X Y n
--   blahem X Y n (genSmash.proj x) = proj λ y → {!!}
--   blahem X Y n (genSmash.base x) = {!!}
--   blahem X Y n (genSmash.gl x a i) = {!!}

-- BiHom' : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- BiHom' X A C =
--   Σ[ f ∈ (((x : fst X) → A x .fst) → C .fst) ]
--     Σ[ g ∈ ((e : fst X ≃ Bool)
--       → A (invEq e true) →∙ (A (invEq e false) →∙ C ∙)) ]
--       {!!}

-- RPfun-gen : (X : RP∞) (A : fst X → Pointed₀) (x : fst X)
--   → A x .fst
--   → (x' : fst X) → Dec (x ≡ x') → A x' .fst
-- RPfun-gen X A x a x' (yes p) = subst (fst ∘ A) p a
-- RPfun-gen X A x a x' (no ¬p) = A x' .snd

-- RPfun : (X : RP∞) (A : fst X → Pointed₀) (x : fst X)
--   → A x .fst
--   → (x : fst X) → A x .fst
-- RPfun X A x p y = RPfun-gen X A x p y (decPt X x y)

-- RPfun-const : (X : RP∞) (A : fst X → Pointed₀) (x₀ : fst X)
--   → (x : fst X)
--   → (p : Dec (x₀ ≡ x))
--   → RPfun-gen X A x₀ (A x₀ .snd) x p
--    ≡ A x .snd
-- RPfun-const X A x₀ x (yes p) i =
--   transp (λ j → fst (A (p (i ∨ j)))) i (A (p i) .snd)
-- RPfun-const X A x₀ x (no ¬p) = refl

-- {-
-- BiHom* : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- BiHom* X A C =
--   Σ[ c ∈ (fst X → fst C) ]
--   Σ[ f ∈ ((((x : fst X) → A x .fst) , λ x → A x .snd) →∙ C) ]
--     ((x : fst X) (a : A x .fst) → fst f (RPfun X A x a) ≡ c x)
-- -}

-- isBihom : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀)
--   → (((x : fst X) → A x .fst) , λ x → A x .snd) →∙ C → Type
-- isBihom X A C f =
--   Σ[ c ∈ (fst X → fst C) ]
--     ((x : fst X) (a : A x .fst) → fst f (RPfun X A x a) ≡ c x)

-- BiHom* : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- BiHom* X A C = Σ[ f ∈ ((((x : fst X) → A x .fst) , λ x → A x .snd) →∙ C) ]
--     isBihom X A C f

-- BiHom's : (X Y : RP∞) (A : fst X → fst Y → Pointed₀) (C : Pointed₀)
--   → BiHom* X (λ x → ((y : fst Y) → A x y .fst) , (λ y → A x y .snd)) C
--   → Type
-- BiHom's X Y A C (F , c) =
--   Σ[ l ∈ ((x : fst X) (f : (y : _) → A x y .fst) → {!F .fst !}) ] {!is!}
--   where
--   c' : {!!}
--   c' = {!!}

-- QHom** : (X Y : RP∞) (A : fst X → fst Y → Pointed₀) (C : Pointed₀) → Type
-- QHom** X Y A C = Σ[ F ∈ BiHom* X (λ x → BiHom* Y (λ y → A x y) C , {!!}) C ] {!!}

-- -- BiHom** : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- -- BiHom** X A C =
-- --   Σ[ f ∈ ((((x : fst X) → A x .fst) , snd ∘ A) →∙ C) ]
-- --    Σ[ f-coh ∈ ((x : fst X) (z : A x .fst) → fst f (RPfun X A x z) ≡ pt C) ]
-- --      ((x : fst X)
-- --        → PathP (λ i → fst f (λ x' → RPfun-const X A x x' (decPt X x x') (~ i)) ≡ pt C)
-- --                 (f .snd) (f-coh x (A x .snd)))

-- -- 4-elt : Type₁
-- -- 4-elt = Σ[ X ∈ Type ] ∥ X ≃ Bool × Bool ∥₁

-- -- isSet-4 : (x : 4-elt) → isSet (fst x)
-- -- isSet-4 = uncurry λ X → PT.elim (λ _ → isPropIsOfHLevel 2)
-- --   λ p → subst isSet (sym (ua p))
-- --     (isSet× isSetBool isSetBool)

-- -- perm : (X : 4-elt) → hSet ℓ-zero
-- -- perm = uncurry λ X → {!PT.rec ? ?!}

-- -- Z ONE TWO THREE : Bool × Bool
-- -- Z = false , false
-- -- ONE = true , false
-- -- TWO = false , true
-- -- THREE = true , true

-- -- suc' : Bool × Bool → Bool × Bool
-- -- suc' (false , false) = ONE
-- -- suc' (false , true) = THREE
-- -- suc' (true , false) = TWO
-- -- suc' (true , true) = Z

-- -- data sub2 (X : 4-elt) : Type where
-- --   [_,_] : (x y : fst X) → ¬ (x ≡ y) → sub2 X
-- --   pz : (x y : fst X) (p : ¬ (x ≡ y))
-- --     → [ x , y ] p ≡ [ y , x ] (p ∘ sym)

-- -- isCyclic : (X : 4-elt)
-- --   → (fst X ≃ Bool × Bool)
-- --   → hProp ℓ-zero
-- -- isCyclic =
-- --   uncurry λ X
-- --    → rec→Set
-- --        {!X!}
-- --        {!X!}
-- --        {!X!}
-- --   where
-- --   F : (X : Type) → X ≃ Bool × Bool → X ≃ Bool × Bool → hProp ℓ-zero
-- --   fst (F X e p) = {!!}
-- --   snd (F X e p) = {!p!}

-- -- sub2-4 : (X : 4-elt) → sub2 X
-- --   → {!1,2,3,4!}
-- -- sub2-4 = {!!}

-- -- sub2* : (X : 4-elt) → isSet (sub2 X)
-- -- sub2* =
-- --   uncurry (λ X → PT.elim (λ p → isPropIsOfHLevel 2)
-- --    (EquivJ (λ X x → isSet (sub2 (X , ∣ x ∣₁)))
-- --     {!!}))

-- -- bram : (X : 4-elt) → fst X → fst X
-- -- bram = {!!}

-- -- BiHom^ : (x : 4-elt) → fst x → fst x
-- -- BiHom^ = uncurry λ X
-- --   → elim→Set (λ p → isSetΠ λ _ → isSet-4 (X , p))
-- --       (λ e x → invEq e (suc' (fst e x)))
-- --       λ e e' → funExt λ x → {!e .fst x ≡ ?!}

-- -- QuadHomIso* : (X : 4-elt) {A : fst X → Pointed₀}  (C : Pointed₀) → Type₁ 
-- -- QuadHomIso* X {A = A} C =
-- --   Σ[ F ∈ (((x : fst X) → A x .fst) → typ C) ]
-- --   Σ[ Fl ∈ {!!} ]
-- --   {!!}

-- -- Q* : (X Y : RP∞) (A : fst X → fst Y → Pointed₀) (B : Pointed₀)
-- --   → Type 
-- -- Q* X Y A B =
-- --   Σ[ F ∈ (((x : fst X) (y : fst Y) → A x y .fst) → B .fst) ]
-- --     Σ[ e ∈ ((y : fst Y)
-- --             (f : (x : fst X) → A x y .fst)
-- --          → {!!}) ]
-- --       {!!}

-- -- -- QuadHomIso : {A B C D E : Pointed₀}
-- -- --   → Iso (A →∙ (B →∙ C →∙ D →∙ E ∙ ∙ ∙))
-- -- --          (Σ[ f ∈ (fst A → fst B → fst C → fst D → fst E) ]
-- -- --           Σ[ f-a ∈ ((b : fst B) (c : fst C) (d : fst D) → f (pt A) b c d ≡ pt E) ]
-- -- --           Σ[ f-b ∈ ((a : fst A) (c : fst C) (d : fst D) → f a (pt B) c d ≡ pt E) ]
-- -- --           Σ[ f-c ∈ ((a : fst A) (b : fst B) (d : fst D) → f a b (pt C) d ≡ pt E) ]
-- -- --           Σ[ f-d ∈ ((a : fst A) (b : fst B) (c : fst C) → f a b c (pt D) ≡ pt E) ]
-- -- --           Σ[ f-ab ∈ ((c : fst C) (d : fst D)
-- -- --             → PathP (λ i → f-a (pt B) c d i ≡ pt E) (f-b (pt A) c d) refl) ]
-- -- --           Σ[ f-bc ∈ ((a : fst A) (d : fst D)
-- -- --             → PathP (λ i → f-b a (pt C) d i ≡ pt E) (f-c a (pt B) d) refl) ]
-- -- --           Σ[ f-cd ∈ ((a : fst A) (b : fst B)
-- -- --             → PathP (λ i → f-c a b (pt D) i ≡ pt E) (f-d a b (pt C)) refl) ]
-- -- --           Σ[ f-ac ∈ ((b : fst B) (d : fst D)
-- -- --             → PathP (λ i → f-a b (pt C) d i ≡ pt E) (f-c (pt A) b d) refl) ]
-- -- --           Σ[ f-ad ∈ ((b : fst B) (c : fst C)
-- -- --             → PathP (λ i → f-a b c (pt D) i ≡ pt E) (f-d (pt A) b c) refl) ]
-- -- --           Σ[ f-bd ∈ ((a : fst A) (c : fst C)
-- -- --             → PathP (λ i → f-b a c (pt D) i ≡ pt E) (f-d a (pt B) c) refl) ]
-- -- --           Σ[ f-bcd ∈ ((a : typ A)
-- -- --             → Cube (f-cd a (pt B)) (λ _ _ → pt E)
-- -- --                     (f-bd a (pt C)) (λ _ _ → pt E)
-- -- --                     (f-bc a (pt D)) (λ _ _ → pt E)) ]
-- -- --           Σ[ f-acd ∈ ((b : typ B)
-- -- --             → Cube (f-cd (pt A) b) (λ _ _ → pt E)
-- -- --                     (f-ad b (pt C)) (λ _ _ → pt E)
-- -- --                     (f-ac b (pt D)) (λ _ _ → pt E)) ]
-- -- --           Σ[ f-abd ∈ ((c : typ C)
-- -- --             → Cube (f-bd (pt A) c) (λ _ _ → pt E)
-- -- --                     (f-ad (pt B) c) (λ _ _ → pt E)
-- -- --                     (f-ab c (pt D)) (λ _ _ → pt E)) ]
-- -- --           Σ[ f-abc ∈ ((d : typ D)
-- -- --             → Cube (f-bc (pt A) d) (λ _ _ → pt E)
-- -- --                     (f-ac (pt B) d) (λ _ _ → pt E)
-- -- --                     (f-ab (pt C) d) (λ _ _ → pt E)) ]
-- -- --           PathP (λ i
-- -- --            → Cube (f-acd (pt B) i) (λ _ _ → pt E)
-- -- --                    (f-abd (pt C) i) (λ _ _ → pt E)
-- -- --                    (f-abc (pt D) i) λ _ _ → pt E)
-- -- --             (f-bcd (pt A))
-- -- --             refl)
-- -- -- Iso.fun (QuadHomIso {A} {B} {C} {D} {E}) f =
-- -- --   (λ x y z w → f .fst x .fst y .fst z .fst w)
-- -- --   , ((λ b c d i → f .snd i .fst b .fst c .fst d)
-- -- --   , (λ a c d i → f .fst a .snd i .fst c .fst d)
-- -- --   , ((λ a b d i → f .fst a .fst b .snd i .fst d)
-- -- --   , ((λ a b c → f .fst a .fst b .fst c .snd)
-- -- --   , ((λ c d i j → f .snd i .snd j .fst c .fst d)
-- -- --   , (λ a d i j → f .fst a .snd i .snd j .fst d)
-- -- --   , (λ a b i j → f .fst a .fst b .snd i .snd j)
-- -- --   , ((λ b d i j → f .snd i .fst b .snd j .fst d)
-- -- --   , (λ b c i → f .snd i .fst b .fst c .snd)
-- -- --   , (λ a c i → f .fst a .snd i .fst c .snd)
-- -- --   , ((λ a i j k → f .fst a .snd i .snd j .snd k)
-- -- --   , (λ b i j k  → f .snd i .fst b .snd j .snd k)
-- -- --   , (λ c i j k → f .snd i .snd j .fst c .snd k)
-- -- --   , (λ d i j k → f .snd i .snd j .snd k .fst d)
-- -- --   , λ i j k w → f .snd i .snd j .snd k .snd w))))))
-- -- -- Iso.inv (QuadHomIso {A} {B} {C} {D} {E})
-- -- --   (f , f-a , f-b , f-c , f-d , f-ab , f-bc , f-cd , f-ac , f-ad , f-bd
-- -- --      , f-bcd , f-acd , f-abd , f-abc , co) =
-- -- --        (λ a → (λ b → (λ c → (λ d → f a b c d)
-- -- --          , f-d a b c)
-- -- --            , λ i → (λ d → f-c a b d i)
-- -- --                   , (f-cd a b i))
-- -- --           , λ i → (λ c → (λ d → f-b a c d i)
-- -- --                  , f-bd a c i)
-- -- --                  , (λ j → (λ d → f-bc a d i j)
-- -- --                  , (f-bcd a i j)))
-- -- --      , λ i → (λ b → (λ c → (λ d → f-a b c d i)
-- -- --             , f-ad b c i)
-- -- --             , λ j → (λ d → f-ac b d i j)
-- -- --                    , f-acd b i j)
-- -- --             , (λ j → (λ c → (λ d → f-ab c d i j)
-- -- --                     , (f-abd c i j))
-- -- --                     , (λ k → (λ d → f-abc d i j k)
-- -- --                     , (co i j k)))
-- -- -- Iso.rightInv (QuadHomIso {A} {B} {C} {D} {E}) _ = refl
-- -- -- Iso.leftInv (QuadHomIso {A} {B} {C} {D} {E}) _ = refl

-- -- -- TriHom* : {!!}
-- -- -- TriHom* = {!!}


-- -- -- Bool→ : ∀ {ℓ} → (A : (x : Bool) → Type ℓ)
-- -- --   → Iso ((x : Bool) → A x) (A true × A false)
-- -- -- Iso.fun (Bool→ A) f = f true , f false
-- -- -- Iso.inv (Bool→ A) (a , b) false = b
-- -- -- Iso.inv (Bool→ A) (a , b) true = a
-- -- -- Iso.rightInv (Bool→ A) _ = refl
-- -- -- Iso.leftInv (Bool→ A) f = funExt λ { false → refl ; true → refl}


-- -- -- Iso-BiHom** : (A : Bool → Pointed₀) (C : Pointed₀)
-- -- --   → Iso (BiHom** Bool* A C)
-- -- --          ((Σ[ f ∈ (A true .fst × A false .fst → fst C) ]
-- -- --            Σ[ l ∈ ((x : A true .fst) → f (x , A false .snd) ≡ pt C) ]
-- -- --              Σ[ r ∈ ((b : A false .fst) → f (A true .snd , b) ≡ pt C) ]
-- -- --                PathP (λ i → r (A false .snd) i ≡ pt C) (l (A true .snd)) refl)) 
-- -- -- Iso-BiHom** A C =
-- -- --   compIso
-- -- --     (compIso
-- -- --       (invIso (Σ-cong-iso-fst (Σ-cong-iso-fst (invIso (domIso (Bool→ (fst ∘ A)))))))
-- -- --       (Σ-cong-iso-snd λ f → invIso
-- -- --         (Σ-cong-iso-fst (invIso (Bool→ (λ x → (z : A x .fst) →
-- -- --           f .fst (RPfun Bool* A x z true , RPfun Bool* A x z false) ≡ pt C))))))
-- -- --     (compIso
-- -- --       Σ-assoc-Iso
-- -- --       (Σ-cong-iso-snd
-- -- --         λ f → {!!}))

-- -- -- →∙→∙Iso : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
-- -- --   → Iso (A →∙ (B →∙ C ∙))
-- -- --          (Σ[ f ∈ (fst A → fst B → fst C) ]
-- -- --            Σ[ l ∈ ((x : fst A) → f x (pt B) ≡ pt C) ]
-- -- --              Σ[ r ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
-- -- --                PathP (λ i → r (pt B) i ≡ pt C) (l (pt A)) refl)
-- -- -- Iso.fun →∙→∙Iso f =
-- -- --      (λ x y → f .fst x .fst y)
-- -- --    , ((λ x → f .fst x .snd)
-- -- --    , ((λ y i → f .snd i .fst y)
-- -- --    , cong snd (snd f)))
-- -- -- Iso.inv →∙→∙Iso = {!!}
-- -- -- Iso.rightInv →∙→∙Iso = {!!}
-- -- -- Iso.leftInv →∙→∙Iso = {!!}

-- -- -- BiHom**-bool : {!BiHom**!}
-- -- -- BiHom**-bool = {!!}

-- -- -- -- BiBiHom : (X Y : RP∞) (A : fst X → fst Y → Pointed₀)
-- -- -- --   (C : Pointed₀) → Type
-- -- -- -- BiBiHom X Y A C =
-- -- -- --   Σ[ F ∈ (((x : fst X) (y : fst Y) → A x y .fst)
-- -- -- --               , λ x y → A x y .snd)
-- -- -- --           →∙ C ]
-- -- -- --   Σ[ pts ∈ (fst Y → fst C × fst C)  ]
-- -- -- --   Σ[ l∧ ∈ ((x : fst X) → BiHom* Y (A x) C) ] 
-- -- -- --   Σ[ r ∈ ((y : fst Y) → ((x : fst X) → A x y .fst) → fst C) ]
-- -- -- --   Σ[ F-lr ∈ ((y : fst Y) (f : ((x : fst X) → A x y .fst))
-- -- -- --            → F .fst (λ x → RPfun Y (A x) y (f x)) ≡ r y f) ]
-- -- -- --   Σ[ l∧-r ∈ ((x : fst X) (y : fst Y) (z : A x y .fst) 
-- -- -- --              → r y (RPfun X (λ x → A x y) x z) ≡ l∧ x .fst y) ]
-- -- -- --   Σ[ F-coh ∈ ((x : fst X) (f : (y : fst Y) → A x y .fst)
-- -- -- --                → F .fst
-- -- -- --                  (RPfun X (λ x → (((y : fst Y) → A x y .fst) , λ y → A x y .snd))
-- -- -- --                         x f)
-- -- -- --                 ≡ l∧ x .snd .fst .fst f) ]
-- -- -- --   Σ[ high ∈ ((x : fst X) (y : fst Y) (z : A x y .fst)
-- -- -- --       → PathP (λ i → F-coh x (RPfun Y (A x) y z) i ≡ l∧-r x y z i)
-- -- -- --                (cong (F .fst) (funExt
-- -- -- --                  (λ x' → funExt λ y'
-- -- -- --                    → cool x y z x' y' (decPt X x x') (decPt Y y y')))
-- -- -- --                ∙ F-lr y (RPfun X (λ x₁ → A x₁ y) x z))
-- -- -- --                (l∧ x .snd .snd y z)) ]
-- -- -- --   Σ[ l∧-pt ∈ ((x : fst X) → l∧ x .snd .fst .fst (λ y → A x y .snd) ≡ pts .fst) ]
-- -- -- --   Σ[ F-2r ∈ ((y : fst Y) (f : ((x : fst X) → A x y .fst))
-- -- -- --     → F .fst (λ x → RPfun Y (A x) y (f x)) ≡ pts .fst) ]
-- -- -- --     {!!}
-- -- -- --   where
-- -- -- --   cool : (x : fst X) (y : fst Y) (z : A x y .fst) (x' : fst X) (y' : fst Y)
-- -- -- --     → (p : Dec (x ≡ x')) (q : Dec (y ≡ y'))
-- -- -- --     → Path (A x' y' .fst)
-- -- -- --               ((RPfun-gen X
-- -- -- --        (λ x₁ → ((y₁ : fst Y) → A x₁ y₁ .fst) , (λ y₁ → A x₁ y₁ .snd)) x
-- -- -- --        (λ y' → RPfun-gen Y (A x) y z y' (decPt Y y y'))) x' p y')
-- -- -- --               (RPfun-gen Y (A x') y (RPfun-gen X (λ x → A x y) x z x' p) y' q)
-- -- -- --   cool x y z x' y' (yes p) (yes q) =
-- -- -- --       (λ j → subst2 (λ x₁ y' → A x₁ y' .fst) p
-- -- -- --                (λ i → transportRefl y' (i ∨ j))
-- -- -- --                      (RPfun-gen Y (A x) y z (transportRefl y' j)
-- -- -- --                        (decPt Y y (transportRefl y' j))))
-- -- -- --       ∙ cong (subst (λ x₁ → A x₁ y' .fst) p)
-- -- -- --            (cong (RPfun-gen Y (A x) y z y')
-- -- -- --              (isPropDec (isSetRPpt Y y y') (decPt Y y y') (yes q)))
-- -- -- --       ∙ {!!}
-- -- -- --       ∙ {!!}
-- -- -- --   cool x y z x' y' (yes p) (no ¬q) = {!(λ y'' → RPfun-gen Y (A x) y z y'' (decPt Y y y'')) y'!}
-- -- -- --   cool x y z x' y' (no ¬p) q = {!!}

-- -- -- -- module _ (A B C D E : Pointed₀) (ptl ptr : fst E)
-- -- -- --          (l∧ r∧ : typ (Smash⋆ C D) → fst E) -- ok
-- -- -- --          (l r : typ A → typ B → typ E) -- ok
-- -- -- --          (F : typ A → typ B → typ C → typ D → typ E) -- ok
-- -- -- --          (F-l : (x : typ A) (y : fst B) (c : fst C)
-- -- -- --            → F x y c (pt D)
-- -- -- --            ≡ l x y)
-- -- -- --          (F-r : (x : typ A) (y : fst B) (d : fst D)
-- -- -- --            → F x y (pt C) d
-- -- -- --            ≡ r x y)
-- -- -- --          (l∧-l : (a : typ A) → l a (pt B) ≡ l∧ basel)
-- -- -- --          (r∧-r : (a : typ A) → r a (pt B) ≡ l∧ baser)
-- -- -- --          (Fg : (a : typ A) (x : fst C) (y : fst D) → F a (pt B) x y ≡ l∧ (proj x y))
-- -- -- --          (Gg : (b : typ B) (x : fst C) (y : fst D) → F (pt A) b x y ≡ r∧ (proj x y))
-- -- -- --          (Fg-high-l : (a : typ A) (c : fst C)
-- -- -- --            → PathP (λ i → Fg a c (pt D) i ≡ l∧-l a i)
-- -- -- --                 (F-l a (pt B) c)
-- -- -- --                 (cong l∧ (gluel c)))
-- -- -- --          (Fg-high-r : (a : typ A) (d : fst D)
-- -- -- --            → PathP (λ i → Fg a (pt C) d i ≡ r∧-r a i)
-- -- -- --                 (F-r a (pt B) d) -- ()
-- -- -- --                 (cong l∧ (gluer d)))
-- -- -- --          (l-r∧ : (b : typ B) → l (pt A) b ≡ r∧ basel)
-- -- -- --          (r-r∧ : (b : typ B) → r (pt A) b ≡ r∧ baser)
-- -- -- --          (l∧-pt : l∧ (proj (pt C) (pt D)) ≡ ptl)
-- -- -- --          (r∧-pt : r∧ (proj (pt C) (pt D)) ≡ ptl)
-- -- -- --          (F-2r : (x : typ A) (y : typ B) → F x y (pt C) (pt D) ≡ ptl)
-- -- -- --          where
-- -- -- --   test : Smash⋆ (Smash⋆ A B) (Smash⋆ C D) →∙ E
-- -- -- --   fst test basel = ptl -- ∙l
-- -- -- --   fst test baser = ptr -- ∙r
-- -- -- --   fst test (proj basel y) = l∧ y
-- -- -- --   fst test (proj baser y) = r∧ y
-- -- -- --   fst test (proj (proj x y) basel) = l x y
-- -- -- --   fst test (proj (proj x y) baser) = r x y
-- -- -- --   fst test (proj (proj x y) (proj z w)) = F x y z w
-- -- -- --   fst test (proj (proj x y) (gluel a i)) = F-l x y a i
-- -- -- --   fst test (proj (proj x y) (gluer b i)) = F-r x y b i
-- -- -- --   fst test (proj (gluel a i) basel) = l∧-l a i
-- -- -- --   fst test (proj (gluel a i) baser) = r∧-r a i
-- -- -- --   fst test (proj (gluel a i) (proj x y)) = Fg a x y i
-- -- -- --   fst test (proj (gluel a i) (gluel b j)) = Fg-high-l a b i j
-- -- -- --   fst test (proj (gluel a i) (gluer b j)) = Fg-high-r a b i j
-- -- -- --   fst test (proj (gluer b i) basel) = l-r∧ b i
-- -- -- --   fst test (proj (gluer b i) baser) = r-r∧ b i
-- -- -- --   fst test (proj (gluer b i) (proj x y)) = Gg b x y i
-- -- -- --   fst test (proj (gluer b i) (gluel c j)) = {!!}
-- -- -- --   fst test (proj (gluer b i) (gluer d j)) = {!!}
-- -- -- --   fst test (gluel basel i) = l∧-pt i
-- -- -- --   fst test (gluel baser i) = r∧-pt i
-- -- -- --   fst test (gluel (proj x y) i) = F-2r x y i
-- -- -- --   fst test (gluel (gluel a j) i) = {!!}
-- -- -- --   fst test (gluel (gluer b j) i) = {!!}
-- -- -- --   fst test (gluer basel i) = {!!}
-- -- -- --   fst test (gluer baser i) = {!!}
-- -- -- --   fst test (gluer (proj x y) i) = {!F-2r!}
-- -- -- --   fst test (gluer (gluel a i₁) i) = {!!}
-- -- -- --   fst test (gluer (gluer b i₁) i) = {!!}
-- -- -- --   snd test = {!!}


-- -- -- -- -- BiHomBool : (A : Bool → Pointed₀) (C : Pointed₀)
-- -- -- -- --   → Iso (BiHom* Bool* A C) (Smash⋆ (A true) (A false) →∙ C)
-- -- -- -- -- BiHomBool A C =
-- -- -- -- --   compIso
-- -- -- -- --    (invIso (Σ-cong-iso-fst (invIso (Bool→ (λ _ → fst C)))))
-- -- -- -- --    (compIso
-- -- -- -- --      (Σ-cong-iso-snd
-- -- -- -- --       (λ c → invIso (Σ-cong-iso-fst
-- -- -- -- --         (compIso idIso
-- -- -- -- --           (Σ-cong-iso-fst (invIso (domIso (Bool→ (fst ∘ A)))))))))
-- -- -- -- --      (compIso
-- -- -- -- --        (Σ-cong-iso-snd (λ p
-- -- -- -- --          → Σ-cong-iso-snd λ r
-- -- -- -- --            → compIso
-- -- -- -- --              (Bool→ (λ x → (a : A x .fst) →
-- -- -- -- --               r .fst (Iso.fun (Bool→ (λ x → A x .fst)) (RPfun Bool* A x a))
-- -- -- -- --               ≡ Iso.inv (Bool→ (λ _ → fst C)) p x))
-- -- -- -- --              (pathToIso
-- -- -- -- --               (cong₂ _×_
-- -- -- -- --                 (λ i → (a : A true .fst)
-- -- -- -- --                   → r .fst ((transportRefl a i) , (A false .snd))
-- -- -- -- --                    ≡ fst p)
-- -- -- -- --                 λ i → (a : A false .fst)
-- -- -- -- --                   → r .fst (A true .snd , transportRefl a i)
-- -- -- -- --                    ≡ snd p))))
-- -- -- -- --        AS))
-- -- -- -- --   where
-- -- -- -- --   AS : Iso
-- -- -- -- --     (Σ[ p ∈ fst C × fst C ]
-- -- -- -- --       Σ[ f ∈ (A true ×∙ A false) →∙ C ]
-- -- -- -- --         ((a : A true .fst) → fst f (a , A false .snd) ≡ fst p)
-- -- -- -- --       × (((a : A false .fst) → fst f (A true .snd , a) ≡ snd p)))
-- -- -- -- --     (Smash⋆ (A true) (A false) →∙ C)
-- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) basel = c1
-- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) baser = c2
-- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) (proj x y) = f (x , y)
-- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) (gluel a i) = l a i
-- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) (gluer b i) = r b i
-- -- -- -- --   snd (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) = p
-- -- -- -- --   Iso.inv AS (f , p) = (f basel , f baser)
-- -- -- -- --     , ((λ x → f (proj (x .fst) (x .snd)))
-- -- -- -- --     , p)
-- -- -- -- --     , (λ a → cong f (gluel a))
-- -- -- -- --     , (λ a → cong f (gluer a))
-- -- -- -- --   Iso.rightInv AS (f , p) =
-- -- -- -- --     ΣPathP ((funExt (λ { basel → refl
-- -- -- -- --       ; baser → refl
-- -- -- -- --       ; (proj x y) → refl
-- -- -- -- --       ; (gluel a i) → refl
-- -- -- -- --       ; (gluer b i) → refl})) , refl)
-- -- -- -- --   Iso.leftInv AS _ = refl


-- -- -- -- -- -- BiHom : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- BiHom X A C =
-- -- -- -- -- --   Σ[ f ∈ (((x : fst X) → A x .fst) → C .fst) ]
-- -- -- -- -- --     Σ[ r ∈ ((e : fst X ≃ Bool) (x : {!!}) (y : _)
-- -- -- -- -- --       → liftHom X A (fst C) e f {!!} {!!} ≡ {!!}) ]
-- -- -- -- -- --       ((e : fst X ≃ Bool)
-- -- -- -- -- --       → {!!} ≡ {!funExt⁻ (r (compEquiv e notEquiv) (A (invEq (compEquiv e notEquiv) true) .snd)) !})

-- -- -- -- -- -- BiHomK : (X : RP∞) (n : fst X → ℕ) → hProp ℓ-zero
-- -- -- -- -- -- BiHomK = uncurry λ X → rec→Set (isSetΠ (λ _ → isSetHProp))
-- -- -- -- -- --   (λ f n → (Σ[ g ∈ ((K∙ (n (invEq f true))) ⋀∙ (K∙ (n (invEq f false))))
-- -- -- -- -- --                 →∙ K∙ (n (invEq f true)
-- -- -- -- -- --                       + n (invEq f false)) ]
-- -- -- -- -- --               {!!})
-- -- -- -- -- --             , {!!})
-- -- -- -- -- --   {!!}

-- -- -- -- -- -- PushT : (A B C : Pointed₀) → Type
-- -- -- -- -- -- PushT A B C = {!Pushout ? ?!}

-- -- -- -- -- -- -- data ASD (X Y : RP∞) (A : fst X → fst Y → Pointed₀) : Type where
-- -- -- -- -- -- --   marp : ((x : _) (y : _) → A x y .fst) → ASD X Y A
-- -- -- -- -- -- --   marp' : (y : fst Y) (z : (x : fst X) → A x y .fst)
-- -- -- -- -- -- --     → marp (λ x → CasesRP Y y (z x) (A x (not* Y y) .snd))
-- -- -- -- -- -- --     ≡ marp λ x y → A x y .snd

-- -- -- -- -- -- -- mapInto : (X Y : RP∞) (A : fst X → fst Y → Pointed₀)
-- -- -- -- -- -- --   → ASD X Y A  → ((y : fst Y) → ⋀∞ X (λ x → A x y)) 
-- -- -- -- -- -- -- mapInto X Y A (marp x) = λ y → proj λ z → x z y
-- -- -- -- -- -- -- mapInto X Y A (marp' y z i) p = {!!}
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --   lem : (λ (z₁ : fst X) → CasesRP Y {A = λ y → A z₁ y .fst} y (z z₁) (A z₁ (not* Y y) .snd) p)
-- -- -- -- -- -- --       ≡ CasesRP X {!p !} {!!} {!!}
-- -- -- -- -- -- --   lem = {!!}
-- -- -- -- -- -- -- {-
-- -- -- -- -- -- --   (({!!} ∙ gl {X = X} {!z x!} {!!}) ∙ {!!}) i
-- -- -- -- -- -- --   -}
-- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- i = i0 ⊢ proj (λ z₁ → CasesRP Y y (z z₁) (A z₁ (not* Y y) .snd) p)
-- -- -- -- -- -- -- i = i1 ⊢ proj (λ z₁ → A z₁ p .snd)
-- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- mapInto X Y A (marp x) y = proj (λ s → x s y)

-- -- -- -- -- -- -- --   SS→' : (X Y : RP∞) (n : fst X → fst Y → ℕ)
-- -- -- -- -- -- -- --     → SS' X Y n .fst
-- -- -- -- -- -- -- --     → K (∑RP Y (λ y → ∑RP X (λ x → n x y)))
-- -- -- -- -- -- -- --   SS→' X Y n (genSmash.proj x) =
-- -- -- -- -- -- -- --     ⌣gen Y (λ y → ∑RP X (λ x₁ → n x₁ y)) .fst
-- -- -- -- -- -- -- --       (proj λ y → {!⌣gen Y ?!})
-- -- -- -- -- -- -- --   SS→' X Y n (genSmash.base x) = {!!}
-- -- -- -- -- -- -- --   SS→' X Y n (genSmash.gl x a i) = {!!}

-- -- -- -- -- -- -- --   {-
-- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- --     help : ⌣gen X (λ x₁ → ∑RP Y (n x₁)) .fst (proj (λ x₂ →
-- -- -- -- -- -- -- --             ⌣gen Y (n x₂) .fst
-- -- -- -- -- -- -- --             (CasesRP X x a (proj (λ x₃ → K∙ (n (not* X x) x₃) .snd)) x₂)))
-- -- -- -- -- -- -- --          ≡ 0ₖ (∑RP X (λ x₁ → ∑RP Y (n x₁)))
-- -- -- -- -- -- -- --     help = cong (⌣gen X (λ x₁ → ∑RP Y (n x₁)) .fst)
-- -- -- -- -- -- -- --               {!genSmash.gl x a !}
-- -- -- -- -- -- -- --           ∙ {!a!}
-- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- --       lem : (z : _) → CasesRP X {A = λ x → ⋀∞ Y (λ X₁ → K∙ (n x X₁))}
-- -- -- -- -- -- -- --                x a (proj (λ x₃ → K∙ (n (not* X x) x₃) .snd)) z
-- -- -- -- -- -- -- --             ≡ proj (CasesRP Y {!!} {!!} {!!})
-- -- -- -- -- -- -- --       lem z = {!!}
-- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- --   doublerMash : {!!}
-- -- -- -- -- -- -- --   doublerMash = {!!}

-- -- -- -- -- -- -- -- ⌣gen : {!!}
-- -- -- -- -- -- -- -- ⌣gen = {!!}


-- -- -- -- -- -- -- -- -- myP : {!{ℓ : Level} (A : Bool → Pointed ℓ) → Iso (genSmash.⋀∞ !}
-- -- -- -- -- -- -- -- -- myP = {!!}


-- -- -- -- -- -- -- -- --   ⋀∞Bool : Iso (⋀∞ Bool* A) (Smash (A true) (A false))
-- -- -- -- -- -- -- -- --   Iso.fun ⋀∞Bool = {!!}
-- -- -- -- -- -- -- -- --   Iso.inv ⋀∞Bool = {!!}
-- -- -- -- -- -- -- -- --   Iso.rightInv ⋀∞Bool = {!!}
-- -- -- -- -- -- -- -- --   Iso.leftInv ⋀∞Bool = {!!}
