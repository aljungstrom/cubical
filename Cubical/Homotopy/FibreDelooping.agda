{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Homotopy.FibreDelooping where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation hiding (elim2) renaming (rec to trRec)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Morphism
open import Cubical.Data.Sigma
open Iso

module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} where
  F : {a x : A} {b y : B} (h : x ≡ a → y ≡ b)
    → (e : x ≡ a)
    → Ω (A , a) →∙ Ω (B , b)
  fst (F h e) p = sym (h e) ∙ h (e ∙ p)
  snd (F h e) = cong (sym (h e) ∙_) (cong h (sym (rUnit e)))
              ∙ lCancel (h e)

  C : {a : A} {b : B} (x : A) (y : B) (g : Ω (A , a) →∙ Ω (B , b))
    → Type _
  C {a = a} {b = b} x y g = Σ[ h ∈ (x ≡ a → y ≡ b) ] ((e : x ≡ a) → F h e ≡ g)

  LT : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) → Type _
  LT g = (x : A) → Σ[ y ∈ B ] C x y g

  RT : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) → Type _
  RT {a = a} {b = b} g =
    Σ[ f ∈ (A → B) ]
      Σ[ f₀ ∈ (f a ≡ b) ] Ω→ (f , f₀) ≡ g

  LT-prelim : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
  LT-prelim {a = a} {b = b} g f = (x : A) → C x (f x) g

  RT-prelim : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
  RT-prelim {a = a} {b = b} g f =
    Σ[ h ∈ ((x : A) → x ≡ a → f x ≡ b) ]
      ((x : A) → (e : x ≡ a) → F (h x) e ≡ g)

  RT→LT1 : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
       → RT-prelim g f → LT-prelim g f
  fst (RT→LT1 g f (h , p) x) = h x
  snd (RT→LT1 g f (h , p) x) e = p x e

  LT1→RT : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
       → LT-prelim g f → RT-prelim g f
  fst (LT1→RT g f F) x e = F x .fst e
  snd (LT1→RT g f F) x e = F x .snd e

  F2 : {x : A} {b y : B} (h : x ≡ x → y ≡ b)
    → Ω (A , x) →∙ Ω (B , b)
  fst (F2 h) p = sym (h refl) ∙ h p
  snd (F2 h) = lCancel (h refl)

  Iso₁ : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
      →  Iso (LT-prelim g f)
              (RT-prelim g f)
  fun (Iso₁ {a = a} {b = b} g f) = LT1→RT g f
  inv (Iso₁ {a = a} {b = b} g f) =  RT→LT1 g f
  rightInv (Iso₁ {a = a} {b = b} g f) p = refl
  leftInv (Iso₁ {a = a} {b = b} g f) p = refl

  Fib2 : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
  Fib2 {a = a} {b = b} g f =
    Σ[ h ∈ ((x : A) → (x ≡ a) → f x ≡ b) ]
      F (h a) refl ≡ g

  IsContrIso : ∀ {ℓ ℓ'} {A : Type ℓ} {a : A} (B : (x : A) (e : x ≡ a) → Type ℓ')
    → Iso ((x : A) (e : x ≡ a) → B x e) (B a refl)
  fun (IsContrIso B) F = F _ refl
  inv (IsContrIso {a = a} B) r x e =
    J (λ x e → B x (sym e)) r (sym e)
  rightInv (IsContrIso B) r = transportRefl r
  leftInv (IsContrIso {a = a} B) F =
    funExt λ x → funExt λ p
      → J (λ x p → PathP (λ _ → B x (sym p))
      (inv (IsContrIso B) (fun (IsContrIso B) F) x (sym p)) (F x (sym p)))
        (transportRefl (F a refl))
        (sym p)

  Iso₂ : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
      →  Iso (RT-prelim g f) (Fib2 g f)
  Iso₂ g f =
    Σ-cong-iso-snd
      λ h → IsContrIso _

  lem : {x : A} {b y : B} (h : x ≡ x → y ≡ b)
    → F h refl ≡ F2 h
  lem h = →∙Homogeneous≡ (isHomogeneousPath _ _)
     (funExt λ p → cong (sym (h refl) ∙_) (cong h (sym (lUnit p))))


  Fib3 : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
  Fib3 {a = a} {b = b} g f =
    Σ[ h ∈ ((x : A) → (x ≡ a) → f x ≡ b) ]
      F2 (h a) ≡ g

  Iso₃ : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
       → Iso (Fib2 g f) (Fib3 g f)
  Iso₃ {a = a} {b = b} g f =
    pathToIso (cong (Σ ((x : A) → (x ≡ a) → f x ≡ b))
      (funExt λ h → cong (_≡ g) (lem (h a))))

  Fib3' : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
  Fib3' {a = a} {b = b} g f =
    Σ[ f₀ ∈ f a ≡ b ]
      F2 (λ p → cong f p ∙ f₀) ≡ g



  Iso₄ : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
       → Iso (Fib3 g f) (Fib3' g f)
  Iso₄ {a = a} {b = b} g f =
     (Σ-cong-iso {A = ((x : A) → (x ≡ a) → f x ≡ b)}
                        {A' = f a ≡ b}
                        {B = λ h → F2 (h a) ≡ g}
                        {B' = λ h → F2 (λ p → cong f p ∙ h) ≡ g}
      (IsContrIso _)
        λ h → pathToIso (cong (_≡ g) (s h)))
    where
    s : (h : (x : A) → x ≡ a → f x ≡ b) → (F2 (h a)) ≡ F2 (λ p → cong f p ∙ h a refl)
    s h = →∙Homogeneous≡ (isHomogeneousPath _ _)
           (funExt λ p → cong₂ _∙_ (cong sym (lUnit (h a refl))) (sym (l p)))
      where
      l : (p : a ≡ a) → cong f p ∙ h a refl ≡ h a p
      l p = (λ i → (λ j → f (p (j ∧ ~ i))) ∙ h (p (~ i)) λ j → (p (~ i ∨ j)))
          ∙ sym (lUnit (h a p))

  Iso₅ : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
       → Iso (Fib3' g f) (Σ[ f₀ ∈ f a ≡ b ] Ω→ (f , f₀) ≡ g)
  Iso₅ {a = a} {b = b} g f =
    pathToIso (cong (Σ (f a ≡ b))
      (funExt λ q → cong (_≡ g)
        (→∙Homogeneous≡ (isHomogeneousPath _ _)
          (funExt
            λ p → cong (_∙ cong f p ∙ q) (cong sym (sym (lUnit q)))
          ∙ sym (doubleCompPath≡compPath (sym q) (cong f p) q)))))

  AllT : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
       → Iso (LT-prelim g f)
              (Σ[ f₀ ∈ f a ≡ b ] Ω→ (f , f₀) ≡ g)
  AllT g f =
    compIso
      (Iso₁ g f)
      (compIso (Iso₂ g f)
        (compIso
          (Iso₃ g f)
          (compIso
            (Iso₄ g f)
            (Iso₅ g f))))

  AllL : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b))
       → Iso (LT g) (RT g)
  fst (fun (AllL g) F) = fst ∘ F
  snd (fun (AllL {a = a} g) F) = Iso.fun (AllT g (fst ∘ F)) (snd ∘ F)
  fst (inv (AllL g) (f , f₀ , p) x) = f x
  snd (inv (AllL g) (f , f₀ , p) x) = Iso.inv (AllT g f) (f₀ , p) x
  fst (rightInv (AllL g) (f , f₀ , p) i) = f
  snd (rightInv (AllL g) (f , f₀ , p) i) = Iso.rightInv (AllT g f) (f₀ , p) i
  leftInv (AllL g) F = funExt λ x
    → ΣPathP (refl , λ i → (Iso.leftInv (AllT g (fst ∘ F)) (λ x → snd (F x))) i x)

  Ω→-fib : {a : A} {b : B}
       (g : Ω (A , a) →∙ Ω (B , b))
       → Iso (LT g) (fiber Ω→ g)
  Ω→-fib {a = a} {b = b} g =
    compIso (AllL g)
      (invIso Σ-assoc-Iso)

  C'-base : {a : A} {b : B} (g : Ω (A , a) →∙ Ω (B , b)) →
    Iso (Σ[ y ∈ B ] C a y g)
        (Σ[ h ∈ Ω (A , a) →∙ Ω (B , b) ] ((e : a ≡ a) → F (fst h) e ≡ g))
  C'-base {a = a} {b = b} g =
    compIso
      (Σ-cong-iso-snd (λ y → compIso (Σ-cong-iso-snd λ h
        → compIso (invIso (addSinglIso
                     {A' = ((e : a ≡ a) → F h e ≡ g)} (h refl)))
                   (compIso Σ-swap-Iso
                     Σ-assoc-Iso))
            (compIso (invIso Σ-assoc-Iso)
              (compIso (Σ-cong-iso-fst Σ-swap-Iso)
                Σ-assoc-Iso))))
      (compIso
        (compIso (invIso Σ-assoc-Iso)
          (Σ-cong-iso-fst {B = λ s → Σ[ h ∈ (a ≡ a → fst s ≡ b) ]
                          (h refl ≡ sym (snd s)) × ((e : a ≡ a) → F h e ≡ g)}
                          (invIso singl≅signl')))
        (compIso
          singlΣIso
          (invIso Σ-assoc-Iso)))

  G : {a : A} {b : B} (h : Ω (A , a) →∙ Ω (B , b)) → F (fst h) refl ≡ h
  G h = →∙Homogeneous≡ (isHomogeneousPath _ _)
          (funExt λ x → cong₂ _∙_ (cong sym (snd h)) (cong (fst h) (sym (lUnit x)))
          ∙ sym (lUnit (fst h x)))

  R2 : {a : A} {b : B} (g : Ω (A , a) →∙ Ω (B , b)) →
    Iso (Σ[ h ∈ Ω (A , a) →∙ Ω (B , b) ] ((e : a ≡ a) → F (fst h) e ≡ g))
        (Σ[ w ∈ ((e : a ≡ a) → F (fst g) e ≡ g) ] w refl ≡ G g)
  R2 {a = a} {b = b} g =
    compIso (Σ-cong-iso-snd
      (λ h → compIso (compIso (addSignlIsoDep λ w → G h ⁻¹ ∙ w refl)
               idIso)
              (invIso Σ-assoc-Iso)))
      (compIso
        (invIso Σ-assoc-Iso)
        (compIso
          (Σ-cong-iso-fst
            (compIso (Σ-cong-iso-snd (λ h → Σ-swap-Iso))
              ((invIso Σ-assoc-Iso))))
          (compIso
            Σ-assoc-Iso
            (compIso
              (Σ-cong-iso-fst
                {B = λ h → Σ[ z ∈ ((e : (a ≡ a))
                           → F (fst (fst h)) e ≡ g) ] G (fst h) ⁻¹ ∙ z (λ _ → a)
                            ≡ sym (snd h)} (invIso singl≅signl'))
              (compIso
                singlΣIso
                (Σ-cong-iso-snd
                  λ h → compIso (congIso (equivToIso (compPathlEquiv (G g))))
                                 (equivToIso
                                    (compEquiv
                                      (compPathrEquiv
                                        (sym (rUnit (G g))))
                                      (compPathlEquiv
                                      (lUnit (h refl)
                                    ∙ cong (_∙ h refl)
                                        (sym (rCancel (G g)))
                                    ∙ sym (assoc _ _ _)))))))))))


  C₀ : {a : A} {b : B} (g : Ω (A , a) →∙ Ω (B , b)) →
    Iso  (Σ[ y ∈ B ] C a y g)
        (Σ[ w ∈ ((e : a ≡ a) → F (fst g) e ≡ g) ] w refl ≡ G g)
  C₀ g = compIso (C'-base g) (R2 g)
  
  pre-main : (n k : ℕ) {a : A} {b : B} (g : Ω (A , a) →∙ Ω (B , b))
    → isConnected (suc (suc n)) A
       → isOfHLevel (suc (suc (n + n + k))) B
       → isOfHLevel k ((Σ[ w ∈ ((e : a ≡ a) → F (fst g) e ≡ g) ] w refl ≡ G g))
  pre-main n k {a = a} {b = b} g conA hLevB =
    isOfHLevelPointedFib n k r
      λ q → subst (λ m → isOfHLevel m (F (fst g) q ≡ g))
                   (+-comm n k)
                   (isOfHLevelPath' (n + k) l _ _)
    where
    r : isConnected (suc n) (fst (Ω (A , a)))
    r = isConnectedPath (suc n) conA _ _

    l : isOfHLevel (suc (n + k)) (Ω (A , a) →∙ Ω (B , b))
    l = isOfHLevelPointedFib n (suc (n + k)) r {B = λ _ → b ≡ b}
          λ _ → subst (λ m → isOfHLevel m (b ≡ b))
                   (cong suc
                             (sym (+-assoc n n k)
                             ∙ cong (n +_) (+-comm n k)
                             ∙ +-assoc n k n))
                   (isOfHLevelPath' (suc (n + n + k)) hLevB _ _)

  main' : (n k : ℕ) {a : A} {b : B} (g : Ω (A , a) →∙ Ω (B , b))
    → isConnected (suc (suc n)) A
    → isOfHLevel (suc (suc (n + n + k))) B
    → (x : _) → isOfHLevel k (Σ[ y ∈ B ] C x y g)
  main' n k {a = a} {b = b} g conA hLevB =
    (invEq (_ , L)
          λ _ →
            isOfHLevelRetractFromIso k
              (C₀ g)
              (pre-main n k g conA hLevB))
    where
    L = elim.isEquivPrecompose (λ (x : Unit) → a) 1
         (λ x → isOfHLevel k (Σ-syntax B (λ y → C x y g))
              , isPropIsOfHLevel k)
         λ p → isConnectedSubtr 1 n
           (subst (λ m → isConnected m (fiber (λ (x : Unit) → a) p))
                  (+-comm 1 n)
                  (isConnectedPoint (suc n) conA a p))

  main : (n k : ℕ) {a : A} {b : B} (g : Ω (A , a) →∙ Ω (B , b))
    → isConnected (suc (suc n)) A
    → isOfHLevel (suc (suc (n + n + k))) B
    → isOfHLevel k (fiber Ω→ g)
  main n k {a = a} {b = b} g conA hLevB =
    isOfHLevelRetractFromIso k
      (invIso (Ω→-fib g))
      (isOfHLevelΠ k (
        (invEq (_ , L)
          λ _ →
            isOfHLevelRetractFromIso k
              (C₀ g)
              (pre-main n k g conA hLevB))))
    where
    L = elim.isEquivPrecompose (λ (x : Unit) → a) 1
         (λ x → isOfHLevel k (Σ-syntax B (λ y → C x y g))
              , isPropIsOfHLevel k)
         λ p → isConnectedSubtr 1 n
           (subst (λ m → isConnected m (fiber (λ (x : Unit) → a) p))
                  (+-comm 1 n)
                  (isConnectedPoint (suc n) conA a p))

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.Order2

open import Cubical.Cohomology.EilenbergMacLane.Base


open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.CommRing.Instances.IntMod

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic

open CommRingStr renaming (_+_ to _+R_)
open IsCommRing
open IsMonoid
open IsSemigroup
open IsRing
open AbGroupStr renaming (_+_ to _+G_)

open import Cubical.Data.Nat.Order

-- ℤ/2 lemmas

K : (n : ℕ) → Type
K n = EM (Ring→AbGroup ℤ/2Ring) n

K∙ : (n : ℕ) → Pointed₀
K∙ n = EM∙ ℤ/2 n
open PlusBis
cup : (n m : ℕ) → K n → K m → K (n +' m) 
cup n m = _⌣ₖ_

open import Cubical.Data.Sum as ⊎
dic : (n m : ℕ) → (n ≤ m) ⊎ (n > m)
dic n m = l (n ≟ m)
  where
  l : Trichotomy n m → (n ≤ m) ⊎ (n > m)
  l (lt x) = inl (suc (fst x) , sym (+-suc (fst x) n) ∙ snd x)
  l (eq x) = inl (0 , x)
  l (gt x) = inr x

¬<-&-≡ : {n m : ℕ} → n < m → n ≡ m → ⊥
¬<-&-≡ {n} {m} (x , p) q = ¬m<m {m = n} (x , p ∙ sym q)

¬<-&-> : {n m : ℕ} → n < m → n > m → ⊥
¬<-&-> {n} {m} p q = ¬m<m (<-trans p q)

isPropTrichotomy : {n m : ℕ} → isProp (Trichotomy n m)
isPropTrichotomy (lt x) (lt y) = cong lt (isProp≤ x y)
isPropTrichotomy (lt x) (eq y) = ⊥.rec (¬<-&-≡ x y)
isPropTrichotomy (lt x) (gt y) = ⊥.rec (¬m<m (<-trans x y))
isPropTrichotomy (eq x) (lt y) = ⊥.rec (¬<-&-≡ y x)
isPropTrichotomy (eq x) (eq y) = cong eq (isSetℕ _ _ _ _)
isPropTrichotomy (eq x) (gt y) = ⊥.rec (¬<-&-≡ y (sym x))
isPropTrichotomy (gt x) (lt y) = ⊥.rec (¬m<m (<-trans x y))
isPropTrichotomy (gt x) (eq y) = ⊥.rec (¬<-&-≡ x (sym y))
isPropTrichotomy (gt x) (gt y) = cong gt (isProp≤ x y)

substℕ-lem : ∀ {ℓ} {B : ℕ → Type ℓ}
  → {n m : ℕ} (p q : n ≡ m)
  → (bn : B n)
  → subst B p bn ≡ subst B q bn
substℕ-lem {B = B} p q bn i = subst B (isSetℕ _ _ p q i) bn

lemiSubst : {x y : ℕ} (p : x ≡ y) → subst K p (0ₖ x) ≡ 0ₖ y
lemiSubst {x = x} = J (λ y p → subst K p (0ₖ x) ≡ 0ₖ y) (transportRefl _)

lemiSubst-refl : {x : ℕ} → lemiSubst {x = x} refl ≡ transportRefl (0ₖ x)
lemiSubst-refl = transportRefl _

lemiSubst' : {x y : ℕ} (p : x ≡ y) → subst (λ x → fst (Ω (K∙ x))) p refl ≡ refl
lemiSubst' {x = x} = J (λ y p → subst (λ x → fst (Ω (K∙ x))) p refl ≡ refl) (transportRefl _)

asd : (n : ℕ) (g : (Ω (K∙ (suc n)) →∙ Ω (K∙ (n +' (suc n)))))
  → (isProp (fiber Ω→ g))
  × ((x : _) → isProp (Σ[ y ∈ _ ] (C x y g)))
asd n g = main n 1 g (isConnectedEM (suc n))
         (subst (λ m → isOfHLevel m (K (n +' suc n)))
           lem'
           (hLevelEM (Ring→AbGroup ℤ/2Ring) (n +' suc n)))
       , main' n 1 g (isConnectedEM (suc n))
         (subst (λ m → isOfHLevel m (K (n +' suc n)))
           lem'
           (hLevelEM (Ring→AbGroup ℤ/2Ring) (n +' suc n)))
  where
  lem' : (2 + (n +' suc n)) ≡ suc (suc (n + n + 1))
  lem' = cong (suc ∘ suc) (+'≡+ n (suc n)
                        ∙ +-suc n n
                        ∙ +-comm 1 (n + n))
  H : (y : Ω (K∙ (suc n)) →∙ Ω (K∙ (n +' suc n)))
      → isProp (fiber Ω→ y)
  H y = main n 1 y (isConnectedEM (suc n))
         (subst (λ m → isOfHLevel m (K (n +' suc n)))
           lem'
           (hLevelEM (Ring→AbGroup ℤ/2Ring) (n +' suc n)))

+'-suc' : (n m : ℕ) → suc (n +' m) ≡ (n +' suc m)
+'-suc' n m = cong suc (+'-comm n m)
           ∙ +'-suc m n
           ∙ +'-comm (suc m) n

⌣-deloop : (n : ℕ)
  → (Ω (K∙ (suc n)) →∙ Ω (K∙ (n +' (suc n))))
fst (⌣-deloop n) x =
  subst (λ m → fst (Ω (K∙ m))) (+'-suc' n n)
       (EM→ΩEM+1 (n +' n) (cup n n (ΩEM+1→EM n x) (ΩEM+1→EM n x)))
snd (⌣-deloop n) =
  cong (subst (λ m → fst (Ω (K∙ m))) (+'-suc' n n))
       (cong (EM→ΩEM+1 (n +' n))
         (cong (λ x → cup n n x x) (ΩEM+1→EM-refl n) ∙ ⌣ₖ-0ₖ n n (0ₖ n))
         ∙ EM→ΩEM+1-0ₖ (n +' n))
     ∙ lemiSubst' (+'-suc' n n)

fib-deloop : (n : ℕ) → fiber Ω→ (⌣-deloop n)
fib-deloop n = fib-deloop'
{-
  Iso.fun (Ω→-fib (⌣-deloop n))
    (EM→Prop _ n (λ _ → asd n (⌣-deloop n) .snd _)
      (0ₖ (n +' suc n)
    , (⌣-deloop n .fst)
    , λ p → →∙Homogeneous≡ (isHomogeneousPath _ _)
             (funExt λ q →
               sym (substResp· _ (+'-suc' n n) _ _)
             ∙ cong (subst (λ m → fst (Ω (K∙ m))) (+'-suc' n n))
                    (cong₂ _∙_ (sym (EM→ΩEM+1-sym (n +' n) _)
                             ∙ cong (EM→ΩEM+1 (n +' n))
                                (-ₖConst-ℤ/2-gen (n +' n)
                                  (cup n n (ΩEM+1→EM n p) (ΩEM+1→EM n p))))
                             (cong (EM→ΩEM+1 (n +' n))
                               (cong₂ (cup n n)
                                 (ΩEM+1→EM-hom n p q)
                                 (ΩEM+1→EM-hom n p q)))
                   ∙ sym (EM→ΩEM+1-hom (n +' n) _ _)
                   ∙ cong (EM→ΩEM+1 (n +' n))
                      (mainLem _ _))))) -}
  where
  substResp· : {n : ℕ} (m : ℕ) (t : n ≡ m) (p q : _)
    → subst (λ m → fst (Ω (K∙ m))) t (p ∙ q)
     ≡ subst (λ m → fst (Ω (K∙ m))) t p
     ∙ subst (λ m → fst (Ω (K∙ m))) t q
  substResp· =
    J> λ p q → transportRefl _
              ∙ sym (cong₂ _∙_ (transportRefl p)
                               (transportRefl q))

  open PlusBis
  mainLem : (p q : EM ℤ/2 n)
    → cup n n p p +ₖ cup n n (p +ₖ q) (p +ₖ q)
     ≡ cup n n q q
  mainLem p q =
      cong (+ₖ-syntax (n +' n) (cup n n p p))
           lem1
     ∙ assocₖ (n +' n) _ _ _
     ∙ cong (_+ₖ cup n n q q) (+ₖ≡id-ℤ/2 (n +' n) _)
     ∙ lUnitₖ (n +' n) (cup n n q q)
    where
    lem1 : cup n n (p +ₖ q) (p +ₖ q) ≡ cup n n p p +ₖ cup n n q q
    lem1 = distrR⌣ₖ n n p q (p +ₖ q)
         ∙ cong₂ _+ₖ_ (distrL⌣ₖ n n p p q) (distrL⌣ₖ n n q p q)
         ∙ sym (assocₖ (n +' n) _ _ _)
         ∙ cong (+ₖ-syntax (n +' n) (cup n n p p))
                (assocₖ (n +' n) _ _ _
               ∙ cong (λ z → z +ₖ cup n n q q)
                      (cong (+ₖ-syntax (n +' n) (p ⌣ₖ q))
                        (⌣ₖ-commℤ/2 n n q p
                      ∙ (λ i → subst (EM ℤ/2)
                           (isSetℕ _ _ (+'-comm n n) refl i)
                           (cup n n p q))
                      ∙ transportRefl (cup n n p q))
                    ∙ +ₖ≡id-ℤ/2 (n +' n) _)
               ∙ lUnitₖ (n +' n) (cup n n q q))
  abstract
    P : (e : 0ₖ (suc n) ≡ 0ₖ (suc n)) →
        F (⌣-deloop n .fst) e ≡ ⌣-deloop n
    P p = →∙Homogeneous≡ (isHomogeneousPath _ _)
                 (funExt λ q →
                   sym (substResp· _ (+'-suc' n n) _ _)
                 ∙ cong (subst (λ m → fst (Ω (K∙ m))) (+'-suc' n n))
                        (cong₂ _∙_ (sym (EM→ΩEM+1-sym (n +' n) _)
                                 ∙ cong (EM→ΩEM+1 (n +' n))
                                    (-ₖConst-ℤ/2-gen (n +' n)
                                      (cup n n (ΩEM+1→EM n p) (ΩEM+1→EM n p))))
                                 (cong (EM→ΩEM+1 (n +' n))
                                   (cong₂ (cup n n)
                                     (ΩEM+1→EM-hom n p q)
                                     (ΩEM+1→EM-hom n p q)))
                       ∙ sym (EM→ΩEM+1-hom (n +' n) _ _)
                       ∙ cong (EM→ΩEM+1 (n +' n))
                          (mainLem _ _)))

  fib-deloop'' : fiber Ω→ (⌣-deloop n)
  fib-deloop'' =
    Iso.fun (Ω→-fib (⌣-deloop n))
     (EM→Prop _ n (λ _ → asd n (⌣-deloop n) .snd _) ((0ₖ (n +' suc n)) ,
       (⌣-deloop n .fst , P)))
  abstract
    fib-deloop' : fiber Ω→ (⌣-deloop n)
    fib-deloop' = Iso.fun (Ω→-fib (⌣-deloop n))
        (EM→Prop _ n (λ _ → asd n (⌣-deloop n) .snd _)
          (0ₖ (n +' suc n)
        , (⌣-deloop n .fst)
        , λ p → →∙Homogeneous≡ (isHomogeneousPath _ _)
                 (funExt λ q →
                   sym (substResp· _ (+'-suc' n n) _ _)
                 ∙ cong (subst (λ m → fst (Ω (K∙ m))) (+'-suc' n n))
                        (cong₂ _∙_ (sym (EM→ΩEM+1-sym (n +' n) _)
                                 ∙ cong (EM→ΩEM+1 (n +' n))
                                    (-ₖConst-ℤ/2-gen (n +' n)
                                      (cup n n (ΩEM+1→EM n p) (ΩEM+1→EM n p))))
                                 (cong (EM→ΩEM+1 (n +' n))
                                   (cong₂ (cup n n)
                                     (ΩEM+1→EM-hom n p q)
                                     (ΩEM+1→EM-hom n p q)))
                       ∙ sym (EM→ΩEM+1-hom (n +' n) _ _)
                       ∙ cong (EM→ΩEM+1 (n +' n))
                          (mainLem _ _)))))

eq' : (n i : ℕ) → (i < n)
  → (K∙ (suc n) →∙ K∙ (i +' (suc n)))
  ≃ ((Ω (K∙ (suc n)) →∙ Ω (K∙ (i +' (suc n)))))
fst (eq' n i p) = Ω→
snd (eq' zero i p) = ⊥.rec (snotz (+-comm (suc i) (fst p) ∙ snd p))
snd (eq' (suc n) i (x , p)) = record { equiv-proof = gr }
  where
  ℕPath : 2 + (i +' suc (x + suc i)) + x ≡ suc (suc (suc n + suc n + 0))
  ℕPath =
    (cong suc
        (cong suc
           (cong (_+ x) (+'≡+ i (suc (x + suc i)))
          ∙ (sym (+-assoc i (suc (x + suc i)) x)
          ∙ cong (λ z → i + suc z)
                 (sym (+-assoc x (suc i) x)
               ∙ cong (x +_) (cong suc (+-comm i x) ∙ sym (+-suc x i)))
          ∙ +-suc i (x + (x + suc i))
          ∙ +-assoc (suc i) x (x + suc i)
          ∙ cong (_+ (x + suc i))
               (+-comm (suc i) x))
          ∙ sym (+'≡+ (x + suc i) (x + suc i)))
         ∙ (+'-suc (x + suc i) (x + suc i))
         ∙ +'-comm (suc (x + suc i)) (x + suc i))
     ∙ cong suc (cong₂ _+'_ p (cong suc p))
     ∙ cong (suc ∘ suc ∘ suc) (+-comm 0 (n + suc n)))

  abstract
    gr : (g : Ω (K∙ (suc (suc n))) →∙ Ω (K∙ (i +' suc (suc n))))
      → isContr (fiber Ω→ g)
    gr g = main (suc n) 0 g (isConnectedEM (suc (suc n)))
                (subst2 (λ m n → isOfHLevel m (K (i +' suc n)))
                        ℕPath
                        p
                        (isOfHLevelPlus' {n = x} (2 + (i +' suc (x + suc i)))
                          (hLevelEM (Ring→AbGroup ℤ/2Ring) (i +' suc (x + suc i)))))

substIso : ∀ {ℓ ℓ'} {A : Type ℓ} {a a' : A} (P : A → Type ℓ') (p : a ≡ a') → Iso (P a) (P a')
fun (substIso P p) = subst P p
inv (substIso P p) = subst P (sym p)
rightInv (substIso P p) = substSubst⁻ P p
leftInv (substIso P p) = subst⁻Subst P p

substEquiv' : ∀ {ℓ ℓ'} {A : Type ℓ} {a a' : A} (P : A → Type ℓ') (p : a ≡ a') → P a ≃ P a'
substEquiv' P p = isoToEquiv (substIso P p)

eq2 : (n i : ℕ)
  → ((Ω (K∙ (suc n)) →∙ Ω (K∙ (i +' (suc n)))))
   ≃ (K∙ n →∙ K∙ (i +' n))
eq2 n i =
  isoToEquiv
   (compIso
    (post∘∙equiv ((isoToEquiv (invIso (Iso-EM-ΩEM+1 n))) , ΩEM+1→EM-refl n))
      (pre∘∙equiv
        (compEquiv∙ ((substEquiv' (λ x → fst (Ω (K∙ x)))
          ((+'-comm i (suc n) ∙ sym (+'-suc n i)) ∙ cong suc (+'-comm n i)))
          , lemiSubst' ((+'-comm i (suc n) ∙ sym (+'-suc n i))
                       ∙ cong suc (+'-comm n i)))
      ((isoToEquiv (invIso (Iso-EM-ΩEM+1 (i +' n))))
      , ΩEM+1→EM-refl (i +' n)))))

eq3 : (n i : ℕ) → (i < n)
  → (K∙ (suc n) →∙ K∙ (i +' (suc n)))
   ≃ (K∙ n →∙ K∙ (i +' n))
eq3 n i p = compEquiv (eq' n i p) (eq2 n i)

dec≤ℕ : (n i : ℕ) → (i ≤ n) ⊎ (i > n)
dec≤ℕ n i with (i ≟ n)
dec≤ℕ n i | lt x = inl (suc (fst x) , sym (+-suc (fst x) i) ∙ snd x)
dec≤ℕ n i | eq x = inl (0 , x)
dec≤ℕ n i | gt x = inr x

private
  propHelp : (n i : ℕ) → (i ≤ n) × (i > n) → ⊥
  propHelp n i ((x , p) , (y , q)) =
    ¬m<m {m = i} ((y + x)
      , (sym (+-assoc y x (suc i))
       ∙ cong (y +_) (+-suc x i))
       ∙ cong ((y +_) ∘ suc) p ∙ q)

isPropdec≤ℕ : (n i : ℕ) → isProp ((i ≤ n) ⊎ (i > n))
isPropdec≤ℕ n i (inl x) (inl y) = cong inl (isProp≤ x y)
isPropdec≤ℕ n i (inl x) (inr y) = ⊥.rec (propHelp n i (x , y))
isPropdec≤ℕ n i (inr x) (inl y) = ⊥.rec (propHelp n i (y , x))
isPropdec≤ℕ n i (inr x) (inr y) = cong inr (isProp≤ x y)

Sqₖ∙-gen' : (n i : ℕ) → Trichotomy i n → K∙ n →∙ K∙ (i +' n)
Sqₖ∙-gen' zero zero p = id∙ _
Sqₖ∙-gen' zero (suc i) p = (λ _ → 0ₖ (suc i)) , refl
Sqₖ∙-gen' (suc n) zero p = id∙ _
fst (Sqₖ∙-gen' (suc n) (suc i) (lt (zero , p))) x =
  subst (λ m → K (m +' (suc n))) (sym (cong predℕ p)) (fib-deloop n .fst .fst x)
snd (Sqₖ∙-gen' (suc n) (suc i) (lt (zero , p))) =
    cong (subst (λ m → K (m +' (suc n))) (sym (cong predℕ p))) (fib-deloop n .fst .snd)
  ∙ lemiSubst _
Sqₖ∙-gen' (suc n) (suc i) (lt (suc x , p)) =
  invEq (eq3 n (suc i) (x , cong predℕ p))
    (Sqₖ∙-gen' n (suc i) (lt (x , cong predℕ p)))
fst (Sqₖ∙-gen' (suc n) (suc i) (eq q)) x =
  subst (λ m → K (m +' suc n)) (sym q) (cup (suc n) (suc n) x x)
snd (Sqₖ∙-gen' (suc n) (suc i) (eq q)) =
    cong (subst (λ m → K (m +' suc n)) (sym q)) (0ₖ-⌣ₖ (suc n) (suc n) (0ₖ (suc n)))
  ∙ lemiSubst _
Sqₖ∙-gen' (suc n) (suc i) (gt q) = (λ _ → 0ₖ (suc (suc (i + n)))) , refl

Sqₖ∙' : {n : ℕ} (i : ℕ) → K∙ n →∙ K∙ (i +' n)
Sqₖ∙' {n = n} i = Sqₖ∙-gen' _ i (i ≟ n)

Sqₖ' : {n : ℕ} (i : ℕ) → K n → K (i +' n)
Sqₖ' i = Sqₖ∙' i .fst

SubstK : {n m : ℕ} (p : n ≡ m) → K∙ n →∙ K∙ m
fst (SubstK p) = subst K p
snd (SubstK p) = lemiSubst _

substΩK : {n m : ℕ} (p : n ≡ m) → Ω (K∙ n) →∙ Ω (K∙ m)
fst (substΩK p) = subst (fst ∘ Ω ∘ K∙) p
snd (substΩK p) = J (λ m p → subst (fst ∘ Ω ∘ K∙) p refl ≡ refl) (transportRefl refl) p

substΩ≡ : {n m : ℕ} (p : n ≡ m) → substΩK p ≡ Ω→ (SubstK p)
substΩ≡ {n = n} = J (λ m p → substΩK p
        ≡ Ω→ (SubstK p))
        (→∙Homogeneous≡ (isHomogeneousPath _ _)
        (funExt (λ p → transportRefl p
             ∙ (λ j i → hcomp (λ k → λ {(i = i0) → transportRefl (p i0) k
                                        ; (i = i1) → transportRefl (p i0) k
                                        ; (j = i0) → transportRefl (p i) k})
                               (transport refl (p i)))
             ∙ cong₂ (λ x y → sym x ∙∙ y ∙∙ x)
                     (sym lemiSubst-refl)
                     refl )))

-- axioms
Sqₖ0 : {n : ℕ} (x : K n) → Sqₖ' 0 x ≡ x
Sqₖ0 {n = zero} x = refl
Sqₖ0 {n = suc n} x = refl

Sqₖ⌣ₖ : {n : ℕ} (x : K n) → Sqₖ' n x ≡ cup n n x x
Sqₖ⌣ₖ {n = zero} = ℤ/2-elim refl refl
Sqₖ⌣ₖ {n = suc n} x =
     (λ i → Sqₖ∙-gen' (suc n) (suc n)
              (isPropTrichotomy (suc n ≟ suc n)
              (eq refl) i) .fst x) -- (inl (0 , refl)) i) .fst x)
  ∙ transportRefl _

Sqₖ> : {n : ℕ} (i : ℕ) → i > n → (x : K n) → Sqₖ' i x ≡ 0ₖ (i +' n)
Sqₖ> {n = zero} zero p x = ⊥.rec (¬m<m p)
Sqₖ> {n = zero} (suc i) p x = refl
Sqₖ> {n = suc n} zero p x = ⊥.rec (snotz (sym (+-suc _ _) ∙ snd p))
Sqₖ> {n = suc n} (suc i) p x j =
  Sqₖ∙-gen' (suc n) (suc i)
   (isPropTrichotomy (suc i ≟ suc n) (gt p) j) .fst x

Sq : ∀ {ℓ} {A : Type ℓ} {n : ℕ} (i : ℕ)
  → coHom n ℤ/2 A → coHom (i +' n) ℤ/2 A
Sq i = ST.map λ f x → Sqₖ' i (f x)

Sq-nat : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) {n : ℕ} (i : ℕ)
  → (x : coHom n ℤ/2 B)
  → (f *H) (Sq i x) ≡ Sq i ((f *H) x)
Sq-nat f i = ST.elim (λ _ → isSetPathImplicit) λ f → refl

ΩEM+1→EM∙ : {ℓ : Level} {G = G₁ : AbGroup ℓ} (n₁ : ℕ) →
      (Ω (EM∙ G₁ (suc n₁))) →∙ EM∙ G₁ n₁
fst (ΩEM+1→EM∙ {G = G₁} n) = ΩEM+1→EM n
snd (ΩEM+1→EM∙ {G = G₁} n) = ΩEM+1→EM-refl n


Sq↓' : (n i : ℕ) → Ω (EM∙ ℤ/2 (suc n)) →∙ Ω (EM∙ ℤ/2 (i +' suc n))
fst (Sq↓' n i) x = subst (λ n → fst (Ω (EM∙ ℤ/2 n)))
                        (+'-suc' i n)
                        (EM→ΩEM+1 (i +' n) (Sqₖ' {n = n} i (ΩEM+1→EM n x)))
snd (Sq↓' n i) =
      cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' i n))
         (cong (EM→ΩEM+1 (i +' n))
           (cong (Sqₖ' i)
             (ΩEM+1→EM-refl n)
          ∙ Sqₖ∙' i .snd)
        ∙ EM→ΩEM+1-0ₖ (i +' n))
  ∙ λ j → transp (λ k → fst (Ω (EM∙ ℤ/2 (+'-suc' i n (j ∨ k))))) j refl


wrap-id : (n : ℕ) {x : K n} (r q1 q2 : x ≡ x)
  → q1 ≡ q2 → q1 ≡ sym r ∙∙ q2 ∙∙ r
wrap-id zero {x = x} r _ _ _ = hLevelEM _ 0 _ _ _ _
wrap-id (suc n) {x = x} r q1 =
  J> (lUnit q1
  ∙ cong (_∙ q1) (sym (lCancel r))
  ∙ sym (assoc _ _ _)
  ∙ (cong (sym r ∙_) (isCommΩEM-base n x r q1)))
  ∙ sym (doubleCompPath≡compPath _ _ _)

cong₂-cup : (n : ℕ) (q : 0ₖ n ≡ 0ₖ n) → cong₂ (cup n n) q q ≡ refl  
cong₂-cup n q = cong₂Funct (cup n n) q q
              ∙ cong₂ _∙_ l1 l2
              ∙ sym (rUnit refl)
  where
  l1 : cong (λ x → cup n n x (0ₖ n)) q ≡ refl
  l1 i j = hcomp (λ k → λ {(i = i0) → ⌣ₖ-0ₖ n n (q j) (~ k)
                          ; (i = i1) → ⌣ₖ-0ₖ n n (0ₖ n) (~ k)
                          ; (j = i0) → ⌣ₖ-0ₖ n n (q j) (~ k)
                          ; (j = i1) → ⌣ₖ-0ₖ n n (q j) (~ k)})
                  (0ₖ (n +' n))
  l2 : cong (cup n n (0ₖ n)) q ≡ refl

  l2 i j = hcomp (λ k → λ {(i = i0) → 0ₖ-⌣ₖ n n (q j) (~ k)
                          ; (i = i1) → 0ₖ-⌣ₖ n n (0ₖ n) (~ k)
                          ; (j = i0) → 0ₖ-⌣ₖ n n (q j) (~ k)
                          ; (j = i1) → 0ₖ-⌣ₖ n n (q j) (~ k)})
                  (0ₖ (n +' n))

substRefl-lem : {n : ℕ} (m : ℕ) (p : n ≡ m) →
  subst (λ n₁ → fst (Ω (EM∙ ℤ/2 n₁))) p refl ≡ refl
substRefl-lem = J> (transportRefl refl)

Ω-Sq' : (n i : ℕ) → Trichotomy i n
  → Sq↓' n i
   ≡ Ω→ (Sqₖ∙' {n = suc n} i)
Ω-Sq' zero zero p =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt λ x → cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' zero zero))
      (Iso.rightInv (Iso-EM-ΩEM+1 zero) x)
    ∙ transportRefl x
    ∙ wrap-id 1 refl x _ refl)
Ω-Sq' zero (suc i) (lt x) = ⊥.rec (snotz (sym (+-suc _ _) ∙ x .snd))
Ω-Sq' zero (suc i) (eq p) = ⊥.rec (snotz p)
Ω-Sq' zero (suc i) (gt (zero , p)) =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q →   cong (substΩK (+'-suc' (suc i) zero) .fst)
                       (cong (EM→ΩEM+1 (suc i))
                         (λ j → Sqₖ∙-gen' 0 (suc i)
                         (isPropTrichotomy (suc i ≟ 0) (gt (i , +-comm i 1)) j) .fst (ΩEM+1→EM zero q))
                      ∙ EM→ΩEM+1-0ₖ (suc i))
                    ∙ substΩK (+'-suc' (suc i) zero) .snd
                    ∙ sym (funExt⁻ (cong fst h) q)))
  ∙ cong Ω→ (cong (Sqₖ∙-gen' 1 (suc i)) (isPropTrichotomy (eq (sym p)) (suc i ≟ 1)))
  where
  pr : (q : snd (K∙ 1) ≡ snd (K∙ 1))
     → cong (subst (λ m → K (m +' 1)) p)
           (cong₂ (cup 1 1) q q)
     ≡ refl
  pr q = cong (cong (subst (λ m → K (m +' 1)) p)) (cong₂-cup 1 q)

  h : Ω→ (Sqₖ∙-gen' 1 (suc i) (eq (sym p))) ≡ ((λ _ → refl) , refl)
  h = →∙Homogeneous≡ (isHomogeneousPath _ _)
       (funExt λ q → cong₂ (λ x y → sym x ∙∙ y ∙∙ x) refl (pr q)
                    ∙ ∙∙lCancel _)

Ω-Sq' zero (suc i) (gt (suc x , p)) =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt (λ q → cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' (suc i) zero))
                         (cong (EM→ΩEM+1 (suc i))
                           ((λ j → Sqₖ∙-gen' zero (suc i) (isPropTrichotomy (suc i ≟ zero)
                             (gt (i , +-comm i 1)) j) .fst (ΩEM+1→EM zero q))))
                  ∙ cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' (suc i) zero)) (EM→ΩEM+1-0ₖ _)
                  ∙ substΩK (+'-suc' (suc i) zero) .snd))
  ∙ sym (Ω^→const 1)
  ∙ cong Ω→ (cong (Sqₖ∙-gen' 1 (suc i)) (isPropTrichotomy (gt (x , +-suc x 1 ∙ p)) (suc i ≟ 1)))
Ω-Sq' (suc n) zero p =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q → substℕ-lem {B = fst ∘ Ω ∘ K∙} (+'-suc' zero (suc n)) refl _
                    ∙ transportRefl _
                    ∙ cong (EM→ΩEM+1 (suc n))
                         ((λ j → Sqₖ∙-gen' (suc n) zero
                           (isPropTrichotomy (lt (n , +-comm n 1)) (zero ≟ suc n) j)
                            .fst (ΩEM+1→EM (suc n) q)))
                    ∙ Iso.rightInv (Iso-EM-ΩEM+1 (suc n)) q))
  ∙ sym Ω→id
  ∙ cong (Ω→ ∘ Sqₖ∙-gen' (suc (suc n)) zero)
      (isPropTrichotomy
        (lt (suc n , +-comm (suc n) 1))
        (zero ≟ (suc (suc n))))
Ω-Sq' (suc n) (suc i) (lt (zero , p)) =
     →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q → substℕ-lem {B = λ n → Ω (K∙ n) .fst} (+'-suc' (suc i) (suc n)) (sym (cong (2 +_) (+-suc i n)))
                         (EM→ΩEM+1 (suc (suc (i + n))) (Sqₖ' (suc i) (ΩEM+1→EM (suc n) q)))
            ∙ substCommSlice K (λ n → fst (Ω (K∙ (suc n)))) EM→ΩEM+1 (cong suc (sym (+-suc i n)))
                         (Sqₖ' (suc i) (ΩEM+1→EM (suc n) q))
           ∙ cong (EM→ΩEM+1 (suc (i + suc n)))
               (cong (subst K (cong suc (sym (+-suc i n))))
                 λ k → Sqₖ∙-gen' (suc n) (suc i)
                           (isPropTrichotomy (suc i ≟ suc n) (lt (0 , p)) k) .fst (ΩEM+1→EM (suc n) q))))
  ∙ (sym (secEq (eq' (suc n) (suc i) (0 , p)) _)
  ∙ cong Ω→ (sym help))
  ∙ cong Ω→ λ j → Sqₖ∙-gen' (suc (suc n)) (suc i)
            (isPropTrichotomy (lt (1 , cong suc p)) (suc i ≟ suc (suc n)) j)
  where
  ℕP = (+'-comm (suc i) (suc (suc n)) ∙
      (λ i₂ → +'-suc (suc n) (suc i) (~ i₂)))
     ∙ (λ i₂ → suc (+'-comm (suc n) (suc i) i₂))

  helplem : (x : _) → substΩK (sym ℕP) .fst (EM→ΩEM+1 (suc (suc (i + n))) x)
                     ≡ EM→ΩEM+1 (suc (i + suc n)) (SubstK (cong suc (sym (+-suc i n))) .fst x)
  helplem x = substℕ-lem {B = λ n → Ω (K∙ n) .fst} (sym ℕP) (sym (cong (2 +_) (+-suc i n)))
                         (EM→ΩEM+1 (suc (suc (i + n))) x)
            ∙ substCommSlice K (λ n → fst (Ω (K∙ (suc n)))) EM→ΩEM+1 (cong suc (sym (+-suc i n))) x

  help : Sqₖ∙-gen' (suc (suc n)) (suc i) (lt (1 , cong suc p))
       ≡ invEq (eq' (suc n) (suc i) (0 , p))
               ((EM→ΩEM+1 ((suc (i + suc n))) , EM→ΩEM+1-0ₖ (suc (i + suc n)))
               ∘∙ ((SubstK (cong suc (sym (+-suc i n)))
                ∘∙ Sqₖ∙-gen' (suc n) (suc i) (lt (0 , p)))
                ∘∙ (ΩEM+1→EM∙ (suc n))))
  help = cong (invEq (eq' (suc n) (suc i) (0 , p)))
         (→∙Homogeneous≡ (isHomogeneousPath _ _)
           (funExt (λ q →
              helplem (subst (λ m → K (m +' suc n)) (λ i₁ → predℕ (p (~ i₁)))
              (fib-deloop n .fst .fst (ΩEM+1→EM (suc n) q))))))
Ω-Sq' (suc n) (suc i) (lt (suc x , p)) =
   →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q → substℕ-lem {B = λ n → Ω (K∙ n) .fst}
                         (+'-suc' (suc i) (suc n))  (sym (cong (suc ∘ suc) (+-suc i n)))
                         (EM→ΩEM+1 (suc (suc (i + n))) (Sqₖ' (suc i) (ΩEM+1→EM (suc n) q)))
                   ∙∙ substCommSlice K (λ n → fst (Ω (K∙ (suc n))))
                         EM→ΩEM+1 (cong suc (sym (+-suc i n)))
                          (Sqₖ' (suc i) (ΩEM+1→EM (suc n) q))
                   ∙∙ cong (EM→ΩEM+1 (suc (i + suc n)))
                       (cong (fst HH)
                         λ k → Sqₖ∙-gen' (suc n) (suc i)
                           (isPropTrichotomy (suc i ≟ suc n) (lt (suc x , p)) k)
                           .fst (ΩEM+1→EM (suc n) q))))
  ∙ sym (secEq (eq' (suc n) (suc i) (suc x , p))
      ((EM→ΩEM+1 ((suc (i + suc n))) , EM→ΩEM+1-0ₖ (suc (i + suc n)))
               ∘∙ ((HH
                ∘∙ Sqₖ∙-gen' (suc n) (suc i) (lt ((suc x) , p)))
                ∘∙ (ΩEM+1→EM∙ (suc n)))))
  ∙ cong Ω→ (sym help)
  ∙ cong Ω→ λ j → Sqₖ∙-gen' (suc (suc n)) (suc i)
            (isPropTrichotomy (lt (suc (suc x) ,  cong suc p))
            (suc i ≟ suc (suc n)) j)
  where
  HH : K∙ (suc (suc (i + n))) →∙ K∙ (suc (i + (suc n))) 
  HH = SubstK (cong suc (sym (+-suc i n)))

  ℕP = (+'-comm (suc i) (suc (suc n)) ∙
        (λ i₂ → +'-suc (suc n) (suc i) (~ i₂)))
       ∙ (λ i₂ → suc (+'-comm (suc n) (suc i) i₂))
  ℕP≡ : ℕP ≡ cong (2 +_) (+-suc i n)
  ℕP≡ = isSetℕ _ _ _ _

  helplem : (x : _) → substΩK (sym ℕP) .fst (EM→ΩEM+1 (suc (suc (i + n))) x)
                     ≡ EM→ΩEM+1 (suc (i + suc n)) (SubstK (cong suc (sym (+-suc i n))) .fst x)
  helplem x = substℕ-lem {B = λ n → Ω (K∙ n) .fst} (sym ℕP) (sym (cong (2 +_) (+-suc i n)))
                         (EM→ΩEM+1 (suc (suc (i + n))) x)
            ∙ substCommSlice K (λ n → fst (Ω (K∙ (suc n)))) EM→ΩEM+1 (cong suc (sym (+-suc i n))) x

  help : Sqₖ∙-gen' (suc (suc n)) (suc i) (lt (2 + x , cong suc p))
      ≡ invEq (eq' (suc n) (suc i) (suc x , p))
               ((EM→ΩEM+1 ((suc (i + suc n))) , EM→ΩEM+1-0ₖ (suc (i + suc n)))
               ∘∙ ((HH
                ∘∙ Sqₖ∙-gen' (suc n) (suc i) (lt (((suc x)) , p)))
                ∘∙ (ΩEM+1→EM∙ (suc n))))
  help = cong (invEq (eq' (suc n) (suc i) (suc x , p)))
              (→∙Homogeneous≡ (isHomogeneousPath _ _)
                (funExt λ q → cong (substΩK (sym ℕP) .fst)
                                    (λ _ → EM→ΩEM+1 (suc (suc (i + n)))
                                      (Sqₖ∙-gen' (suc n) (suc i)
                                         (lt (suc x , p)) .fst (ΩEM+1→EM (suc n) q)))
                             ∙ helplem (Sqₖ∙-gen' (suc n) (suc i)
                                  (lt (suc x , p)) .fst (ΩEM+1→EM (suc n) q))))

Ω-Sq' (suc n) (suc i) (eq p) =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q → cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' (suc i) (suc n)))
                          (cong (EM→ΩEM+1 (suc (suc (i + n))))
                            (λ j → Sqₖ∙-gen' (suc n) (suc i)
                                     (isPropTrichotomy
                                     (suc i ≟ suc n) (eq p) j) .fst
                                     (ΩEM+1→EM (suc n) q))
                        ∙ sym (substCommSlice K (fst ∘ Ω ∘ K∙ ∘ suc) EM→ΩEM+1
                            (cong (_+' suc n) (sym p))
                            (cup (suc n) (suc n) (ΩEM+1→EM (suc n) q) (ΩEM+1→EM (suc n) q))))
                    ∙ sym (substComposite (fst ∘ Ω ∘ K∙)
                       (λ i₁ → suc (p (~ i₁) +' suc n)) (+'-suc' (suc i) (suc n)) _)
                    ∙ substℕ-lem _ _ _
                    ∙ substComposite (fst ∘ Ω ∘ K∙)
                       (+'-suc' (suc n) (suc n)) (λ i₁ → sym p i₁ +' suc (suc n)) _
                    ∙ sym (Ω→H≡ (⌣-deloop (suc n) .fst q))))
  ∙ (refl
  ∙ (λ i → Ω→ H ∘∙ (fib-deloop (suc n) .snd (~ i))))
  ∙ sym (Ω→∘∙ H (fib-deloop (suc n) .fst))
  ∙ cong Ω→ (sym help)
  ∙ cong Ω→ λ j → Sqₖ∙-gen' (suc (suc n)) (suc i)
     (isPropTrichotomy (lt (zero , cong suc p)) (suc i ≟ suc (suc n)) j)
  where
  H : K∙ (suc (suc (n + suc n))) →∙ K∙ (suc (suc (i + suc n)))
  fst H = subst (λ m → K (m +' suc (suc n))) (sym p)
  snd H = lemiSubst _

  Ω→H≡  : (x : _) → Ω→ H .fst x ≡ subst (fst ∘ Ω ∘ K∙) (λ i → ((sym p i) +' suc (suc n))) x
  Ω→H≡ x = funExt⁻ (cong fst (sym (substΩ≡ (λ i → ((sym p i) +' suc (suc n)))))) x


  help : Sqₖ∙-gen' (suc (suc n)) (suc i) (lt (0 , cong suc p))
       ≡ (H
       ∘∙ fib-deloop (suc n) .fst)
  help = →∙Homogeneous≡ (isHomogeneousEM (suc (suc (i + suc n)))) refl
Ω-Sq' (suc n) (suc i) (gt (zero , p)) =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt (λ q → cong (substΩK (+'-suc' (suc i) (suc n)) .fst)
                       (cong (EM→ΩEM+1 (suc (suc (i + n))))
                         (λ j → Sqₖ∙-gen' (suc n) (suc i)
                                 (isPropTrichotomy (suc i ≟ suc n)
                                   (gt (0 , p)) j) .fst (ΩEM+1→EM (suc n) q))
                      ∙ EM→ΩEM+1-0ₖ (suc (suc (i + n))))
        ∙∙ (substRefl-lem _ (+'-suc' (suc i) (suc n))
                     ∙ sym (∙∙lCancel _))
        ∙∙ cong₂ (λ x y → sym x ∙∙ y ∙∙ x) refl
             (sym (cong (cong (subst (λ m → K m) (cong (_+' suc (suc n)) p)))
               (cong₂-cup (suc (suc n)) q)))))
  ∙ cong (Ω→ ∘ Sqₖ∙-gen' (suc (suc n)) (suc i))
      (isPropTrichotomy
        (eq (sym p))
        (suc i ≟ suc (suc n)))
Ω-Sq' (suc n) (suc i) (gt (suc x , p)) =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt (λ q → cong (substΩK (+'-suc' (suc i) (suc n)) .fst)
                     (cong (EM→ΩEM+1 (suc (suc (i + n))))
                       (λ j → Sqₖ∙-gen' (suc n) (suc i)
                          (isPropTrichotomy (suc i ≟ suc n) (gt (suc x , p)) j) .fst
                            (ΩEM+1→EM (suc n) q))
                     ∙ EM→ΩEM+1-0ₖ (suc (suc (i + n))))
                  ∙ substΩK (+'-suc' (suc i) (suc n)) .snd))
  ∙ sym Ω→const
  ∙ cong Ω→ (cong (Sqₖ∙-gen' (suc (suc n)) (suc i))
     (isPropTrichotomy (gt (x , +-suc x (2 + n) ∙ p)) (suc i ≟ suc (suc n))))

-- Ω-Sq : (n i : ℕ) → (i ≤ n) ⊎ (i > n)
--   → Sq↓ n i
--    ≡ Ω→ (Sqₖ∙ {n = suc n} i)
-- Ω-Sq zero zero p =
--   →∙Homogeneous≡ (isHomogeneousPath _ _)
--     (funExt λ x → cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' zero zero))
--       (Iso.rightInv (Iso-EM-ΩEM+1 zero) x)
--     ∙ transportRefl x
--     ∙ wrap-id 1 refl x _ refl)
-- Ω-Sq zero (suc i) (inl x) = ⊥.rec (snotz (sym (+-suc _ _) ∙ x .snd))
-- Ω-Sq zero (suc i) (inr (zero , p)) =
--     →∙Homogeneous≡ (isHomogeneousPath _ _)
--        (funExt (λ q → cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n)))
--                                    (+'-suc' (suc i) zero))
--                             (cong (EM→ΩEM+1 (suc i))
--                              (λ j → Sqₖ∙-gen zero (suc i)
--                               (isPropdec≤ℕ _ _ (dec≤ℕ _ _) (inr (0 , p)) j)
--                                 .fst (ΩEM+1→EM zero q))
--                            ∙ EM→ΩEM+1-0ₖ (suc i))
--                     ∙∙ ((λ j → transp (λ k → fst (Ω (EM∙ ℤ/2 (+'-suc' (suc i) zero (k ∨ j))))) j refl))
--                     ∙∙ sym (funExt⁻ (cong fst h) q)))
--    ∙ (cong Ω→ λ j → Sqₖ∙-gen (suc zero) (suc i)
--       (isPropdec≤ℕ 1 (suc i) (inl (0 , sym p)) (dec≤ℕ _ _) j))

--   where
--   pr : (q : snd (K∙ 1) ≡ snd (K∙ 1))
--      → cong (subst (λ m → K (m +' 1)) (λ i₂ → sym p (~ i₂)))
--            (cong₂ (cup 1 1) q q)
--      ≡ refl
--   pr q = cong (cong (subst (λ m → K (m +' 1)) p)) (cong₂-cup 1 q)

--   h : Ω→ (Sqₖ∙-gen 1 (suc i) (inl (0 , sym p))) ≡ ((λ _ → refl) , refl)
--   h = →∙Homogeneous≡ (isHomogeneousPath _ _)
--        (funExt λ q → cong₂ (λ x y → sym x ∙∙ y ∙∙ x) refl (pr q)
--                     ∙ ∙∙lCancel _)

-- Ω-Sq zero (suc i) (inr (suc x , p)) =
--    →∙Homogeneous≡ (isHomogeneousPath _ _)
--       (funExt (λ q → cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' (suc i) zero))
--            (EM→ΩEM+1-0ₖ (suc i))
--         ∙∙ (λ j → transp (λ k → fst (Ω (EM∙ ℤ/2 (+'-suc' (suc i) zero (k ∨ j))))) j refl)
--         ∙∙ sym (∙∙lCancel (snd (Sqₖ∙-gen 1 (suc i) (inr (x , +-suc x 1 ∙ p)))))))
--   ∙ cong Ω→ λ j → Sqₖ∙-gen (suc zero) (suc i)
--      (isPropdec≤ℕ 1 (suc i)
--       (inr (x , +-suc x 1 ∙ p)) (dec≤ℕ _ _) j)
-- Ω-Sq (suc n) zero p =
--   →∙Homogeneous≡ (isHomogeneousPath _ _)
--     (funExt λ x → cong (subst (λ n₁ → fst (Ω (EM∙ ℤ/2 n₁))) (+'-suc' zero (suc n)))
--                         (Iso.rightInv (Iso-EM-ΩEM+1 (suc n)) x)
--                  ∙ substℕ-lem (+'-suc' zero (suc n)) refl x
--                  ∙ transportRefl x
--                  ∙ wrap-id _ _ _ _ refl)
-- Ω-Sq (suc n) (suc i) (inl (zero , p)) =
--     →∙Homogeneous≡ (isHomogeneousPath _ _)
--       (funExt (λ q → cong (subst (λ n → fst (Ω (EM∙ ℤ/2 n))) (+'-suc' (suc i) (suc n)))
--                           (cong (EM→ΩEM+1 (suc (suc (i + n))))
--                             (λ j → Sqₖ∙-gen (suc n) (suc i)
--                                      (isPropdec≤ℕ _ _
--                                      (dec≤ℕ _ _) (inl (0 , p)) j) .fst
--                                      (ΩEM+1→EM (suc n) q))
--                         ∙ sym (substCommSlice K (fst ∘ Ω ∘ K∙ ∘ suc) EM→ΩEM+1
--                             (cong (_+' suc n) (sym p))
--                             (cup (suc n) (suc n) (ΩEM+1→EM (suc n) q) (ΩEM+1→EM (suc n) q))))
--                     ∙ sym (substComposite (fst ∘ Ω ∘ K∙)
--                        (λ i₁ → suc (p (~ i₁) +' suc n)) (+'-suc' (suc i) (suc n)) _)
--                     ∙ substℕ-lem _ _ _
--                     ∙ substComposite (fst ∘ Ω ∘ K∙)
--                        (+'-suc' (suc n) (suc n)) (λ i₁ → sym p i₁ +' suc (suc n)) _
--                     ∙ sym (Ω→H≡ (⌣-deloop (suc n) .fst q))))
--   ∙ (refl
--   ∙ (λ i → Ω→ H ∘∙ (fib-deloop (suc n) .snd (~ i))))
--   ∙ sym (Ω→∘∙ H (fib-deloop (suc n) .fst))
--   ∙ cong Ω→ (sym help)
--   ∙ cong Ω→ λ j → Sqₖ∙-gen (suc (suc n)) (suc i)
--      (isPropdec≤ℕ _ _ (inl (1 , cong suc p)) (dec≤ℕ _ _) j)
--   where
--   H : K∙ (suc (suc (n + suc n))) →∙ K∙ (suc (suc (i + suc n)))
--   fst H = subst (λ m → K (m +' suc (suc n))) (sym p)
--   snd H = lemiSubst _

--   Ω→H≡  : (x : _) → Ω→ H .fst x ≡ subst (fst ∘ Ω ∘ K∙) (λ i → ((sym p i) +' suc (suc n))) x
--   Ω→H≡ x = funExt⁻ (cong fst (sym (substΩ≡ (λ i → ((sym p i) +' suc (suc n)))))) x


--   help : Sqₖ∙-gen (suc (suc n)) (suc i) (inl (1 , cong suc p))
--        ≡ (H
--        ∘∙ fib-deloop (suc n) .fst)
--   help = →∙Homogeneous≡ (isHomogeneousEM (suc (suc (i + suc n)))) refl
-- Ω-Sq (suc n) (suc i) (inl (suc zero , p)) =
--    →∙Homogeneous≡ (isHomogeneousPath _ _)
--       (funExt (λ q → substℕ-lem {B = λ n → Ω (K∙ n) .fst} (+'-suc' (suc i) (suc n)) (sym (cong (2 +_) (+-suc i n)))
--                          (EM→ΩEM+1 (suc (suc (i + n))) (Sqₖ (suc i) (ΩEM+1→EM (suc n) q)))
--             ∙ substCommSlice K (λ n → fst (Ω (K∙ (suc n)))) EM→ΩEM+1 (cong suc (sym (+-suc i n)))
--                          (Sqₖ (suc i) (ΩEM+1→EM (suc n) q))
--            ∙ cong (EM→ΩEM+1 (suc (i + suc n)))
--                (cong (subst K (cong suc (sym (+-suc i n))))
--                  λ k → Sqₖ∙-gen (suc n) (suc i)
--                            (isPropdec≤ℕ _ _ (dec≤ℕ _ _) (inl (suc zero , p)) k) .fst (ΩEM+1→EM (suc n) q))))
--   ∙ (sym (secEq (eq' (suc n) (suc i) (0 , p)) _)
--   ∙ cong Ω→ (sym help))
--   ∙ cong Ω→ λ j → Sqₖ∙-gen (suc (suc n)) (suc i)
--             (isPropdec≤ℕ _ _ (inl (suc (suc zero) , cong suc p)) (dec≤ℕ _ _) j)
--   where
--   ℕP = (+'-comm (suc i) (suc (suc n)) ∙
--       (λ i₂ → +'-suc (suc n) (suc i) (~ i₂)))
--      ∙ (λ i₂ → suc (+'-comm (suc n) (suc i) i₂))

--   helplem : (x : _) → substΩK (sym ℕP) .fst (EM→ΩEM+1 (suc (suc (i + n))) x)
--                      ≡ EM→ΩEM+1 (suc (i + suc n)) (SubstK (cong suc (sym (+-suc i n))) .fst x)
--   helplem x = substℕ-lem {B = λ n → Ω (K∙ n) .fst} (sym ℕP) (sym (cong (2 +_) (+-suc i n)))
--                          (EM→ΩEM+1 (suc (suc (i + n))) x)
--             ∙ substCommSlice K (λ n → fst (Ω (K∙ (suc n)))) EM→ΩEM+1 (cong suc (sym (+-suc i n))) x

--   help : Sqₖ∙-gen (suc (suc n)) (suc i) (inl (2 , cong suc p))
--        ≡ invEq (eq' (suc n) (suc i) (0 , p))
--                ((EM→ΩEM+1 ((suc (i + suc n))) , EM→ΩEM+1-0ₖ (suc (i + suc n)))
--                ∘∙ ((SubstK (cong suc (sym (+-suc i n)))
--                 ∘∙ Sqₖ∙-gen (suc n) (suc i) (inl (1 , p)))
--                 ∘∙ (ΩEM+1→EM∙ (suc n))))
--   help = cong (invEq (eq' (suc n) (suc i) (0 , refl ∙ p)))
--          (→∙Homogeneous≡ (isHomogeneousPath _ _)
--            (funExt (λ q →
--               helplem (subst (λ m → K (m +' suc n)) (λ i₁ → predℕ (p (~ i₁)))
--               (fib-deloop n .fst .fst (ΩEM+1→EM (suc n) q))))))
--      ∙ λ k → invEq (eq' (suc n) (suc i) (0 , lUnit p (~ k)))
--                ((EM→ΩEM+1 ((suc (i + suc n))) , EM→ΩEM+1-0ₖ (suc (i + suc n)))
--                ∘∙ ((SubstK (cong suc (sym (+-suc i n)))
--                 ∘∙ Sqₖ∙-gen (suc n) (suc i) (inl (1 , p)))
--                 ∘∙ (ΩEM+1→EM∙ (suc n))))
-- Ω-Sq (suc n) (suc i) (inl (suc (suc x) , p)) =
--     →∙Homogeneous≡ (isHomogeneousPath _ _)
--        (funExt (λ q → (substℕ-lem {B = λ n → Ω (K∙ n) .fst}
--                          (+'-suc' (suc i) (suc n))  (sym (cong (suc ∘ suc) (+-suc i n)))
--                          (EM→ΩEM+1 (suc (suc (i + n))) (Sqₖ (suc i) (ΩEM+1→EM (suc n) q)))
--                      ∙ substCommSlice K (λ n → fst (Ω (K∙ (suc n))))
--                          EM→ΩEM+1 (cong suc (sym (+-suc i n))) (Sqₖ (suc i) (ΩEM+1→EM (suc n) q)))
--                      ∙ cong (EM→ΩEM+1 (suc (i + suc n)))
--                        (cong (fst HH)
--                          λ k → Sqₖ∙-gen (suc n) (suc i)
--                            (isPropdec≤ℕ _ _ (dec≤ℕ _ _) (inl (suc (suc x) , p)) k) .fst (ΩEM+1→EM (suc n) q))))
--   ∙ sym (secEq (eq' (suc n) (suc i) (suc x , cong suc (+-suc x (suc i)) ∙ p))
--       ((EM→ΩEM+1 ((suc (i + suc n))) , EM→ΩEM+1-0ₖ (suc (i + suc n)))
--                ∘∙ ((HH
--                 ∘∙ Sqₖ∙-gen (suc n) (suc i) (inl ((suc (suc x)) , p)))
--                 ∘∙ (ΩEM+1→EM∙ (suc n)))))
--   ∙ cong Ω→ (sym help)
--   ∙ cong Ω→ λ j → Sqₖ∙-gen (suc (suc n)) (suc i)
--             (isPropdec≤ℕ _ _ (inl (suc (suc (suc x)) ,  cong suc p)) (dec≤ℕ _ _) j)
--   where
--   HH : K∙ (suc (suc (i + n))) →∙ K∙ (suc (i + (suc n))) 
--   HH = SubstK (cong suc (sym (+-suc i n)))

--   ℕP = (+'-comm (suc i) (suc (suc n)) ∙
--         (λ i₂ → +'-suc (suc n) (suc i) (~ i₂)))
--        ∙ (λ i₂ → suc (+'-comm (suc n) (suc i) i₂))
--   ℕP≡ : ℕP ≡ cong (2 +_) (+-suc i n)
--   ℕP≡ = isSetℕ _ _ _ _

--   helplem : (x : _) → substΩK (sym ℕP) .fst (EM→ΩEM+1 (suc (suc (i + n))) x)
--                      ≡ EM→ΩEM+1 (suc (i + suc n)) (SubstK (cong suc (sym (+-suc i n))) .fst x)
--   helplem x = substℕ-lem {B = λ n → Ω (K∙ n) .fst} (sym ℕP) (sym (cong (2 +_) (+-suc i n)))
--                          (EM→ΩEM+1 (suc (suc (i + n))) x)
--             ∙ substCommSlice K (λ n → fst (Ω (K∙ (suc n)))) EM→ΩEM+1 (cong suc (sym (+-suc i n))) x

--   help : Sqₖ∙-gen (suc (suc n)) (suc i) (inl (3 + x , cong suc p))
--       ≡ invEq (eq' (suc n) (suc i) (suc x , (cong suc (+-suc x (suc i)) ∙ p)))
--                ((EM→ΩEM+1 ((suc (i + suc n))) , EM→ΩEM+1-0ₖ (suc (i + suc n)))
--                ∘∙ ((HH
--                 ∘∙ Sqₖ∙-gen (suc n) (suc i) (inl ((suc (suc x)) , p)))
--                 ∘∙ (ΩEM+1→EM∙ (suc n))))
--   help = cong (invEq (eq' (suc n) (suc i) (suc x , cong suc (+-suc x (suc i)) ∙ p)))
--               (→∙Homogeneous≡ (isHomogeneousPath _ _)
--                 (funExt λ q → cong (substΩK (sym ℕP) .fst)
--                                     (λ _ → EM→ΩEM+1 (suc (suc (i + n))) (Sqₖ∙-gen (suc n) (suc i)
--                                          (inl (suc (suc x) , (λ i₂ → predℕ (cong suc p i₂)))) .fst (ΩEM+1→EM (suc n) q)))
--                              ∙ helplem (Sqₖ∙-gen (suc n) (suc i)
--                                   (inl (suc (suc x) , (λ i₂ → predℕ (cong suc p i₂)))) .fst (ΩEM+1→EM (suc n) q))))
-- Ω-Sq (suc n) (suc i) (inr (zero , p)) =
--     →∙Homogeneous≡ (isHomogeneousPath _ _)
--       (funExt (λ q → cong (subst (λ n₁ → fst (Ω (EM∙ ℤ/2 n₁))) (+'-suc' (suc i) (suc n)))
--                           (((λ j → EM→ΩEM+1 (suc (suc (i + n)))
--                             (Sqₖ∙-gen (suc n) (suc i)
--                              (isPropdec≤ℕ _ _ (dec≤ℕ _ _)
--                              (inr (0 , p)) j) .fst (ΩEM+1→EM (suc n) q))))
--                          ∙ EM→ΩEM+1-0ₖ _)
--                     ∙ (substRefl-lem _ (+'-suc' (suc i) (suc n))
--                      ∙ sym (∙∙lCancel _))
--                     ∙ cong₂ (λ x y → sym x ∙∙ y ∙∙ x) refl
--                        (sym (cong (cong (subst (λ m → K m) (cong (_+' suc (suc n)) p)))
--                          (cong₂-cup (suc (suc n)) q)))))
--   ∙ cong Ω→ λ j → Sqₖ∙-gen (suc (suc n)) (suc i)
--             (isPropdec≤ℕ _ _ (inl (0 , sym p)) (dec≤ℕ _ _)
--              j)
-- Ω-Sq (suc n) (suc i) (inr (suc x , p)) =
--   →∙Homogeneous≡ (isHomogeneousPath _ _)
--     (funExt λ q →
--         (cong (subst (λ n₁ → fst (Ω (EM∙ ℤ/2 n₁)))
--                      (+'-suc' (suc i) (suc n)))
--               (cong (EM→ΩEM+1 (suc (suc (i + n))))
--                 (λ j → Sqₖ∙-gen (suc n) (suc i)
--                          (isPropdec≤ℕ _ _ (dec≤ℕ _ _)
--                          (inr (suc x , p)) j) .fst (ΩEM+1→EM (suc n) q))
--              ∙ EM→ΩEM+1-0ₖ (suc (suc (i + n))))
--        ∙ λ j → transp (λ k → fst (Ω (EM∙ ℤ/2 (+'-suc' (suc i) (suc n) (j ∨ k)))))
--                        j refl)
--       ∙ rUnit refl)
--   ∙ cong Ω→ (sym lem2)
--   where
--   lem2 : Sqₖ∙ {n = suc (suc n)} (suc i) ≡ ((λ _ → 0ₖ (suc (suc (i + suc n)))) , refl)
--   lem2 j = Sqₖ∙-gen (suc (suc n)) (suc i)
--             (isPropdec≤ℕ _ _ (dec≤ℕ _ _)
--             (inr (x , +-suc x (2 + n) ∙ p)) j)
