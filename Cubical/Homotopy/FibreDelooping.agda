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
  toΩ→ :  {a x : A} {b y : B} (h : x ≡ a → y ≡ b)
    → (e : x ≡ a)
    → Ω (A , a) →∙ Ω (B , b)
  fst (toΩ→ h e) p = sym (h e) ∙ h (e ∙ p)
  snd (toΩ→ h e) = cong (sym (h e) ∙_) (cong h (sym (rUnit e)))
              ∙ lCancel (h e)

  toΩ→-refl : {x : A} {b y : B} (h : x ≡ x → y ≡ b)
    → Ω (A , x) →∙ Ω (B , b)
  fst (toΩ→-refl h) p = sym (h refl) ∙ h p
  snd (toΩ→-refl h) = lCancel (h refl)

  toΩ→restr : {x : A} {y b : B} (h : x ≡ x → y ≡ b)
    → toΩ→ h refl ≡ toΩ→-refl {b = b} h
  toΩ→restr h = →∙Homogeneous≡ (isHomogeneousPath _ _)
     (funExt λ p → cong (sym (h refl) ∙_) (cong h (sym (lUnit p))))

  currySinglIso : ∀ {ℓ ℓ'} {A : Type ℓ} {a : A}
       (B : (x : A) (e : x ≡ a) → Type ℓ')
    → Iso ((x : A) (e : x ≡ a) → B x e) (B a refl)
  fun (currySinglIso B) toΩ→ = toΩ→ _ refl
  inv (currySinglIso {a = a} B) r x e =
    J (λ x e → B x (sym e)) r (sym e)
  rightInv (currySinglIso B) r = transportRefl r
  leftInv (currySinglIso {a = a} B) toΩ→ =
    funExt λ x → funExt λ p
      → J (λ x p → PathP (λ _ → B x (sym p))
      (inv (currySinglIso B) (fun (currySinglIso B) toΩ→) x (sym p))
        (toΩ→ x (sym p)))
        (transportRefl (toΩ→ a refl))
        (sym p)

  module _ {a : A} {b : B} where

    -- fibre of Ω→ (shuffled a bit for convenience)
    fibΩ : (g : Ω (A , a) →∙ Ω (B , b)) → Type _
    fibΩ g =
      Σ[ f ∈ (A → B) ]
        Σ[ f₀ ∈ (f a ≡ b) ] Ω→ (f , f₀) ≡ g

    -- we give an alternative construction and prove it equivalent
    -- this one is often easier to reason about
    pre-alt-fibΩ : (x : A) (y : B) (g : Ω (A , a) →∙ Ω (B , b))
      → Type _
    pre-alt-fibΩ x y g = Σ[ h ∈ (x ≡ a → y ≡ b) ] ((e : x ≡ a) → toΩ→ h e ≡ g)

    alt-fibΩ : (g : Ω (A , a) →∙ Ω (B , b)) → Type _
    alt-fibΩ g = (x : A) → Σ[ y ∈ B ] pre-alt-fibΩ x y g

    -- to show the equivalence, we start by showing that the following
    -- two types are equivalent
    ∘pre-alt-fibΩ : (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
    ∘pre-alt-fibΩ g f = (x : A) → pre-alt-fibΩ x (f x) g

    pre-fibΩ₁ : (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
    pre-fibΩ₁ g f =
      Σ[ h ∈ ((x : A) → x ≡ a → f x ≡ b) ]
        ((x : A) → (e : x ≡ a) → toΩ→ (h x) e ≡ g)

    Iso/∘pre-alt-fibΩ/pre-fibΩ₁ : (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
        →  Iso (∘pre-alt-fibΩ g f)
                (pre-fibΩ₁ g f)
    fst (fun (Iso/∘pre-alt-fibΩ/pre-fibΩ₁ g f) F) x = F x .fst
    snd (fun (Iso/∘pre-alt-fibΩ/pre-fibΩ₁ g f) F) x = F x .snd
    fst (inv (Iso/∘pre-alt-fibΩ/pre-fibΩ₁ g f) (h , p) x) = h x
    snd (inv (Iso/∘pre-alt-fibΩ/pre-fibΩ₁ g f) (h , p) x) = p x
    rightInv (Iso/∘pre-alt-fibΩ/pre-fibΩ₁ g f) p = refl
    leftInv (Iso/∘pre-alt-fibΩ/pre-fibΩ₁ g f) p = refl

    -- rewrite futher
    pre-fibΩ₂ : (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
    pre-fibΩ₂ g f =
      Σ[ h ∈ ((x : A) → (x ≡ a) → f x ≡ b) ]
        toΩ→ (h a) refl ≡ g

    Iso/pre-fibΩ₁/pre-fibΩ₂ : (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
        → Iso (pre-fibΩ₁ g f) (pre-fibΩ₂ g f)
    Iso/pre-fibΩ₁/pre-fibΩ₂ g f =
      Σ-cong-iso-snd
        λ h → currySinglIso _

    -- and further
    pre-fibΩ₃ : (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
    pre-fibΩ₃ g f =
      Σ[ h ∈ ((x : A) → (x ≡ a) → f x ≡ b) ]
        toΩ→-refl (h a) ≡ g

    Iso/pre-fibΩ₂/pre-fibΩ₃ : (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
         → Iso (pre-fibΩ₂ g f) (pre-fibΩ₃ g f)
    Iso/pre-fibΩ₂/pre-fibΩ₃ g f =
      pathToIso (cong (Σ ((x : A) → (x ≡ a) → f x ≡ b))
        (funExt λ h → cong (_≡ g) (toΩ→restr (h a))))

    -- and futher...
    pre-fibΩ₄ : (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B) → Type _
    pre-fibΩ₄ g f =
      Σ[ f₀ ∈ f a ≡ b ]
        toΩ→-refl (λ p → cong f p ∙ f₀) ≡ g

    Iso/pre-fibΩ₃/pre-fibΩ₄ : (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
         → Iso (pre-fibΩ₃ g f) (pre-fibΩ₄ g f)
    Iso/pre-fibΩ₃/pre-fibΩ₄ g f =
       (Σ-cong-iso {A = ((x : A) → (x ≡ a) → f x ≡ b)}
                          {A' = f a ≡ b}
                          {B = λ h → toΩ→-refl (h a) ≡ g}
                          {B' = λ h → toΩ→-refl (λ p → cong f p ∙ h) ≡ g}
        (currySinglIso _)
          λ h → pathToIso (cong (_≡ g) (lem h)))
      where
      lem : (h : (x : A) → x ≡ a → f x ≡ b)
       → (toΩ→-refl (h a))
         ≡ toΩ→-refl (λ p → cong f p ∙ h a refl)
      lem h = →∙Homogeneous≡ (isHomogeneousPath _ _)
             (funExt λ p → cong₂ _∙_ (cong sym (lUnit (h a refl))) (sym (help p)))
        where
        help : (p : a ≡ a) → cong f p ∙ h a refl ≡ h a p
        help p = (λ i → (λ j → f (p (j ∧ ~ i))) ∙ h (p (~ i)) λ j → (p (~ i ∨ j)))
               ∙ sym (lUnit (h a p))

    -- almost there...
    Iso/pre-fibΩ₄/half-fibΩ : (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
         → Iso (pre-fibΩ₄ g f) (Σ[ f₀ ∈ f a ≡ b ] Ω→ (f , f₀) ≡ g)
    Iso/pre-fibΩ₄/half-fibΩ g f =
      pathToIso (cong (Σ (f a ≡ b))
        (funExt λ q → cong (_≡ g)
          (→∙Homogeneous≡ (isHomogeneousPath _ _)
            (funExt
              λ p → cong (_∙ cong f p ∙ q) (cong sym (sym (lUnit q)))
            ∙ sym (doubleCompPath≡compPath (sym q) (cong f p) q)))))

    Iso/∘pre-alt-fibΩ/half-fibΩ : (g : Ω (A , a) →∙ Ω (B , b)) (f : A → B)
         → Iso (∘pre-alt-fibΩ g f)
                (Σ[ f₀ ∈ f a ≡ b ] Ω→ (f , f₀) ≡ g)
    Iso/∘pre-alt-fibΩ/half-fibΩ g f =
      compIso
        (Iso/∘pre-alt-fibΩ/pre-fibΩ₁ g f)
        (compIso (Iso/pre-fibΩ₁/pre-fibΩ₂ g f)
          (compIso
            (Iso/pre-fibΩ₂/pre-fibΩ₃ g f)
            (compIso
              (Iso/pre-fibΩ₃/pre-fibΩ₄ g f)
              (Iso/pre-fibΩ₄/half-fibΩ g f))))

    -- the first main result (useful for constructing points of fiber Ω→ g)
    Iso/alt-fibΩ/fibΩ→ : (g : Ω (A , a) →∙ Ω (B , b))
         → Iso (alt-fibΩ g) (fiber Ω→ g)
    Iso/alt-fibΩ/fibΩ→ g =
      compIso main
        (invIso Σ-assoc-Iso)
      where
      main : Iso (alt-fibΩ g) (fibΩ g)
      fst (fun main F) = fst ∘ F
      snd (fun main F) =
        Iso.fun (Iso/∘pre-alt-fibΩ/half-fibΩ g (fst ∘ F)) (snd ∘ F)
      fst (inv main (f , f₀ , p) x) = f x
      snd (inv main (f , f₀ , p) x) =
        Iso.inv (Iso/∘pre-alt-fibΩ/half-fibΩ g f) (f₀ , p) x
      fst (rightInv main (f , f₀ , p) i) = f
      snd (rightInv main (f , f₀ , p) i) =
        Iso.rightInv (Iso/∘pre-alt-fibΩ/half-fibΩ g f) (f₀ , p) i
      fst (leftInv main F i x) = fst (F x)
      snd (leftInv main F i x) =
        Iso.leftInv (Iso/∘pre-alt-fibΩ/half-fibΩ g
                      (fst ∘ F)) (λ x → snd (F x)) i x

    -- for reasoning about e.g. the hLevel of fiber Ω→ g, we
    -- rewrite every further

    rewrite-pre-alt-fibΩ₁ : (g : Ω (A , a) →∙ Ω (B , b)) →
      Iso (Σ[ y ∈ B ] pre-alt-fibΩ a y g)
          (Σ[ h ∈ Ω (A , a) →∙ Ω (B , b) ]
            ((e : a ≡ a) → toΩ→ (fst h) e ≡ g))
    rewrite-pre-alt-fibΩ₁ g =
      compIso
        (Σ-cong-iso-snd
          (λ y → compIso (Σ-cong-iso-snd λ h
          → compIso (invIso (addSinglIso
                       {A' = ((e : a ≡ a) → toΩ→ h e ≡ g)}
                       (h refl)))
                     (compIso Σ-swap-Iso
                       Σ-assoc-Iso))
              (compIso (invIso Σ-assoc-Iso)
                (compIso (Σ-cong-iso-fst Σ-swap-Iso)
                  Σ-assoc-Iso))))
        (compIso
          (compIso (invIso Σ-assoc-Iso)
            (Σ-cong-iso-fst
             {B = λ s → Σ[ h ∈ (a ≡ a → fst s ≡ b) ]
             (h refl ≡ sym (snd s)) × ((e : a ≡ a) → toΩ→ h e ≡ g)}
             (invIso singl≅signl')))
          (compIso
            singlΣIso
            (invIso Σ-assoc-Iso)))

    toΩ→-homotopy : (h : Ω (A , a) →∙ Ω (B , b)) → toΩ→ (fst h) refl ≡ h
    toΩ→-homotopy h = →∙Homogeneous≡ (isHomogeneousPath _ _)
            (funExt λ x → cong₂ _∙_ (cong sym (snd h))
                           (cong (fst h) (sym (lUnit x)))
            ∙ sym (lUnit (fst h x)))

    -- This one is just a big rearrangement of Σ-types
    -- (don't worry about it...)
    rewrite-pre-alt-fibΩ₂ : (g : Ω (A , a) →∙ Ω (B , b)) →
      Iso (Σ[ h ∈ Ω (A , a) →∙ Ω (B , b) ]
              ((e : a ≡ a) → toΩ→ (fst h) e ≡ g))
          (Σ[ w ∈ ((e : a ≡ a) → toΩ→ (fst g) e ≡ g) ]
               w refl ≡ toΩ→-homotopy g)
    rewrite-pre-alt-fibΩ₂ g =
      compIso (Σ-cong-iso-snd
        (λ h →
         compIso
          (compIso (addSignlIsoDep
            λ w → toΩ→-homotopy h ⁻¹ ∙ w refl) idIso)
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
                             → toΩ→ (fst (fst h)) e ≡ g) ]
                                 toΩ→-homotopy (fst h) ⁻¹ ∙ z (λ _ → a)
                              ≡ sym (snd h)}
                   (invIso singl≅signl'))
                (compIso
                  singlΣIso
                  (Σ-cong-iso-snd
                    λ h →
                    compIso
                     (congIso (equivToIso
                       (compPathlEquiv (toΩ→-homotopy g))))
                     (equivToIso
                        (compEquiv
                          (compPathrEquiv
                            (sym (rUnit (toΩ→-homotopy g))))
                          (compPathlEquiv
                          (lUnit (h refl)
                        ∙ cong (_∙ h refl)
                            (sym (rCancel (toΩ→-homotopy g)))
                        ∙ sym (assoc _ _ _)))))))))))


    rewrite-pre-alt-fibΩ : (g : Ω (A , a) →∙ Ω (B , b)) →
      Iso (Σ[ y ∈ B ] pre-alt-fibΩ a y g)
          (Σ[ w ∈ ((e : a ≡ a) → toΩ→ (fst g) e ≡ g) ]
              w refl ≡ toΩ→-homotopy g)
    rewrite-pre-alt-fibΩ g =
      compIso (rewrite-pre-alt-fibΩ₁ g) (rewrite-pre-alt-fibΩ₂ g)

    private
      pre-main : (n k : ℕ) (g : Ω (A , a) →∙ Ω (B , b))
        → isConnected (suc (suc n)) A
        → isOfHLevel (suc (suc (n + n + k))) B
        → isOfHLevel k (Σ[ w ∈ ((e : a ≡ a) → toΩ→ (fst g) e ≡ g) ]
                               w refl ≡ toΩ→-homotopy g)
      pre-main n k g conA hLevB =
        isOfHLevelPointedFib n k r
          λ q → subst (λ m → isOfHLevel m (toΩ→ (fst g) q ≡ g))
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

    isOfHLevel-Total-pre-alt-fibΩ :
         (n k : ℕ) (g : Ω (A , a) →∙ Ω (B , b))
      → isConnected (suc (suc n)) A
      → isOfHLevel (suc (suc (n + n + k))) B
      → (x : _) → isOfHLevel k (Σ[ y ∈ B ] pre-alt-fibΩ x y g)
    isOfHLevel-Total-pre-alt-fibΩ n k g conA hLevB =
      (invEq (_ , L)
            λ _ →
              isOfHLevelRetractFromIso k
                (rewrite-pre-alt-fibΩ g)
                (pre-main n k g conA hLevB))
      where
      L = elim.isEquivPrecompose (λ (x : Unit) → a) 1
           (λ x → isOfHLevel k (Σ-syntax B (λ y → pre-alt-fibΩ x y g))
                , isPropIsOfHLevel k)
           λ p → isConnectedSubtr 1 n
             (subst (λ m → isConnected m (fiber (λ (x : Unit) → a) p))
                    (+-comm 1 n)
                    (isConnectedPoint (suc n) conA a p))

    isOfHLevel-fiberΩ→ : (n k : ℕ) (g : Ω (A , a) →∙ Ω (B , b))
      → isConnected (suc (suc n)) A
      → isOfHLevel (suc (suc (n + n + k))) B
      → isOfHLevel k (fiber Ω→ g)
    isOfHLevel-fiberΩ→ n k g conA hLevB =
      isOfHLevelRetractFromIso k
        (invIso (Iso/alt-fibΩ/fibΩ→ g))
        (isOfHLevelΠ k (
          (invEq (_ , L)
            λ _ →
              isOfHLevelRetractFromIso k
                (rewrite-pre-alt-fibΩ g)
                (pre-main n k g conA hLevB))))
      where
      L = elim.isEquivPrecompose (λ (x : Unit) → a) 1
           (λ x → isOfHLevel k (Σ-syntax B (λ y → pre-alt-fibΩ x y g))
                , isPropIsOfHLevel k)
           λ p → isConnectedSubtr 1 n
             (subst (λ m → isConnected m (fiber (λ (x : Unit) → a) p))
                    (+-comm 1 n)
                    (isConnectedPoint (suc n) conA a p))

      -- asd : (f g : A → B) (p : f ≡ g)
      --    → (p : f a ≡ b) (q : g a ≡ b)
      --    → {!Path (f !}
      --    → {!!}
      -- asd = {!!}

      -- fibasd : (h : Ω (A , a) →∙ Ω (B , b))
      --   → (s : ∀ {ℓ}  → (B : (A → Type ℓ)) → (B a) → ((x : _) → B x))
      --   → (b₁ b₂ : B)
      --   → (k : b₁ ≡ b₂)
      --   → (h₁ : a ≡ a → b₁ ≡ b)
      --   → (h₂ : a ≡ a → b₂ ≡ b)
      --   → PathP (λ i → (p : a ≡ a) → k i ≡ b) h₁ h₂
      --   → (r₁ : (e : a ≡ a) → toΩ→ h₁ e ≡ h)
      --   → (r₂ : (e : a ≡ a) → toΩ→ h₂ e ≡ h)
      --   -- → (r : f a .fst ≡ g a .fst)
      --   -- → ((p : a ≡ a) → PathP (λ i → r i ≡ b) (f a .snd .fst p) (g a .snd .fst p))
      --   → Path (alt-fibΩ h) (s _ (b₁ , h₁ , r₁)) (s _ (b₂ , h₂ , r₂)) -- f ≡ g
      -- fibasd h s b₁ =
      --      J> λ h₁
      --   → J> λ r₁ r₂ → cong (s _) (ΣPathP ({!!} , {!!}))
      
      --   -- funExt
      --   --   (ind _
      --   --    {!J (λ b₂ r → ((p : a ≡ a) → PathP (λ i → r i ≡ b) (f a .snd .fst p) ?) → ?) ? p !})
