{-# OPTIONS --safe #-}

module Cubical.Homotopy.Loopspace where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.SetTruncation
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

{- loop space of a pointed type -}
Ω : {ℓ : Level} → Pointed ℓ → Pointed ℓ
Ω (_ , a) = ((a ≡ a) , refl)

{- n-fold loop space of a pointed type -}
Ω^_ : ∀ {ℓ} → ℕ → Pointed ℓ → Pointed ℓ
(Ω^ 0) p = p
(Ω^ (suc n)) p = Ω ((Ω^ n) p)

{- loop space map -}
Ω→ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
      → (A →∙ B) → (Ω A →∙ Ω B)
fst (Ω→ {A = A} {B = B} (f , p)) q = sym p ∙∙ cong f q ∙∙ p
snd (Ω→ {A = A} {B = B} (f , p)) = ∙∙lCancel p

Ω^→ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
  → (A →∙ B) → ((Ω^ n) A →∙ (Ω^ n) B)
Ω^→ zero f = f
Ω^→ (suc n) f = Ω→ (Ω^→ n f)

{- loop space map functoriality (missing pointedness proof) -}
Ω→∘ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  (g : B →∙ C) (f : A →∙ B)
  → ∀ p → Ω→ (g ∘∙ f) .fst p ≡ (Ω→ g ∘∙ Ω→ f) .fst p
Ω→∘ g f p k i =
  hcomp
    (λ j → λ
      { (i = i0) → compPath-filler' (cong (g .fst) (f .snd)) (g .snd) (~ k) j
      ; (i = i1) → compPath-filler' (cong (g .fst) (f .snd)) (g .snd) (~ k) j
      })
    (g .fst (doubleCompPath-filler (sym (f .snd)) (cong (f .fst) p) (f .snd) k i))

Ω→∘∙ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  (g : B →∙ C) (f : A →∙ B)
  → Ω→ (g ∘∙ f) ≡ (Ω→ g ∘∙ Ω→ f)
Ω→∘∙ g f = →∙Homogeneous≡ (isHomogeneousPath _ _) (funExt (Ω→∘ g f))

Ω→const : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
          → Ω→ {A = A} {B = B} ((λ _ → pt B) , refl) ≡ ((λ _ → refl) , refl)
Ω→const = →∙Homogeneous≡ (isHomogeneousPath _ _) (funExt λ _ → sym (rUnit _))

{- Ω→ is a homomorphism -}
Ω→pres∙filler : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
        → (p q : typ (Ω A))
        → I → I → I → fst B
Ω→pres∙filler f p q i j k =
  hfill
    (λ k → λ
       { (i = i0) → doubleCompPath-filler (sym (snd f)) (cong (fst f) (p ∙ q)) (snd f) k j
        ; (i = i1) →
          (doubleCompPath-filler
            (sym (snd f)) (cong (fst f) p) (snd f) k
         ∙ doubleCompPath-filler
            (sym (snd f)) (cong (fst f) q) (snd f) k) j
       ; (j = i0) → snd f k
       ; (j = i1) → snd f k})
    (inS (cong-∙ (fst f) p q i j))
    k

Ω→pres∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
        → (p q : typ (Ω A))
        → fst (Ω→ f) (p ∙ q) ≡ fst (Ω→ f) p ∙ fst (Ω→ f) q
Ω→pres∙ f p q i j = Ω→pres∙filler f p q i j i1

Ω→pres∙reflrefl : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
                  → Ω→pres∙ {A = A} {B = B} f refl refl
                   ≡ cong (fst (Ω→ f)) (sym (rUnit refl))
                   ∙ snd (Ω→ f)
                   ∙ rUnit _
                   ∙ cong₂ _∙_ (sym (snd (Ω→ f))) (sym (snd (Ω→ f)))
Ω→pres∙reflrefl {A = A} {B = B} =
  →∙J (λ b₀ f → Ω→pres∙ {A = A} {B = (fst B , b₀)} f refl refl
                   ≡ cong (fst (Ω→ f)) (sym (rUnit refl))
                   ∙ snd (Ω→ f)
                   ∙ rUnit _
                   ∙ cong₂ _∙_ (sym (snd (Ω→ f))) (sym (snd (Ω→ f))))
       λ f → lem f
         ∙ cong (cong (fst (Ω→ (f , refl))) (sym (rUnit refl)) ∙_)
                (((lUnit (cong₂ _∙_ (sym (snd (Ω→ (f , refl))))
                                    (sym (snd (Ω→ (f , refl))))))
                ∙ cong (_∙ (cong₂ _∙_ (sym (snd (Ω→ (f , refl))))
                                      (sym (snd (Ω→ (f , refl))))))
                   (sym (rCancel (snd (Ω→ (f , refl))))))
                ∙ sym (assoc (snd (Ω→ (f , refl)))
                  (sym (snd (Ω→ (f , refl))))
                    (cong₂ _∙_ (sym (snd (Ω→ (f , refl))))
                               (sym (snd (Ω→ (f , refl)))))))
  where
  lem : (f : fst A → fst B) → Ω→pres∙ (f , refl) (λ _ → snd A) (λ _ → snd A) ≡
      (λ i → fst (Ω→ (f , refl)) (rUnit (λ _ → snd A) (~ i))) ∙
      (λ i → snd (Ω→ (f , refl)) (~ i) ∙ snd (Ω→ (f , refl)) (~ i))
  lem f k i j =
    hcomp (λ r → λ { (i = i0) → doubleCompPath-filler
                                   refl (cong f ((λ _ → pt A) ∙ refl)) refl (r ∨ k) j
                    ; (i = i1) → (∙∙lCancel (λ _ → f (pt A)) (~ r)
                                 ∙ ∙∙lCancel (λ _ → f (pt A)) (~ r)) j
                    ; (j = i0) → f (snd A)
                    ; (j = i1) → f (snd A)
                    ; (k = i0) → Ω→pres∙filler {A = A} {B = fst B , f (pt A)}
                                   (f , refl) refl refl i j r
                    ; (k = i1) → compPath-filler
                                   ((λ i → fst (Ω→ (f , refl))
                                                (rUnit (λ _ → snd A) (~ i))))
                                   ((λ i → snd (Ω→ (f , refl)) (~ i)
                                          ∙ snd (Ω→ (f , refl)) (~ i))) r i j})
     (hcomp (λ r → λ { (i = i0) → doubleCompPath-filler refl (cong f (rUnit (λ _ → pt A) r)) refl k j
                    ; (i = i1) → rUnit (λ _ → f (pt A)) (r ∨ k) j
                    ; (j = i0) → f (snd A)
                    ; (j = i1) → f (snd A)
                    ; (k = i0) → cong-∙∙-filler f (λ _ → pt A) (λ _ → pt A) (λ _ → pt A) r i j
                    ; (k = i1) → fst (Ω→ (f , refl)) (rUnit (λ _ → snd A) (~ i ∧ r)) j})
             (rUnit (λ _ → f (pt A)) k j))

{- Ω^→ is homomorphism -}
Ω^→pres∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
        → (n : ℕ)
        → (p q : typ ((Ω^ (suc n)) A))
        → fst (Ω^→ (suc n) f) (p ∙ q)
         ≡ fst (Ω^→ (suc n) f) p ∙ fst (Ω^→ (suc n) f) q
Ω^→pres∙ {A = A} {B = B} f n p q = Ω→pres∙ (Ω^→ n f) p q

Ω^→∘∙ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''} (n : ℕ)
  (g : B →∙ C) (f : A →∙ B)
  → Ω^→ n (g ∘∙ f) ≡ (Ω^→ n g ∘∙ Ω^→ n f)
Ω^→∘∙ zero g f = refl
Ω^→∘∙ (suc n) g f = cong Ω→ (Ω^→∘∙ n g f) ∙ Ω→∘∙ (Ω^→ n g) (Ω^→ n f)

Ω^→const : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
          → Ω^→ {A = A} {B = B} n ((λ _ → pt B) , refl)
          ≡ ((λ _ → snd ((Ω^ n) B)) , refl)
Ω^→const zero = refl
Ω^→const (suc n) = cong Ω→ (Ω^→const n) ∙ Ω→const

isEquivΩ→ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
           → (f : (A →∙ B))
           → isEquiv (fst f) → isEquiv (Ω→ f .fst)
isEquivΩ→ {B = (B , b)} =
  uncurry λ f →
    J (λ b y → isEquiv f
             → isEquiv (λ q → (λ i → y (~ i)) ∙∙ (λ i → f (q i)) ∙∙ y))
      λ eqf → subst isEquiv (funExt (rUnit ∘ cong f))
                     (isoToIsEquiv (congIso (equivToIso (f , eqf))))

isEquivΩ^→ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
           → (f : A →∙ B)
           → isEquiv (fst f)
           → isEquiv (Ω^→ n f .fst)
isEquivΩ^→ zero f iseq = iseq
isEquivΩ^→ (suc n) f iseq = isEquivΩ→ (Ω^→ n f) (isEquivΩ^→ n f iseq)

Ω≃∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
     → (e : A ≃∙ B)
     → (Ω A) ≃∙ (Ω B)
fst (fst (Ω≃∙ e)) = fst (Ω→ (fst (fst e) , snd e))
snd (fst (Ω≃∙ e)) = isEquivΩ→ (fst (fst e) , snd e) (snd (fst e))
snd (Ω≃∙ e) = snd (Ω→ (fst (fst e) , snd e))

Ω≃∙pres∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
     → (e : A ≃∙ B)
     → (p q : typ (Ω A))
     → fst (fst (Ω≃∙ e)) (p ∙ q)
     ≡ fst (fst (Ω≃∙ e)) p
     ∙ fst (fst (Ω≃∙ e)) q
Ω≃∙pres∙ e p q = Ω→pres∙ (fst (fst e) , snd e) p q

Ω^≃∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
     → (e : A ≃∙ B)
     → ((Ω^ n) A) ≃∙ ((Ω^ n) B)
Ω^≃∙ zero e = e
fst (fst (Ω^≃∙ (suc n) e)) =
  fst (Ω→ (fst (fst (Ω^≃∙ n e)) , snd (Ω^≃∙ n e)))
snd (fst (Ω^≃∙ (suc n) e)) =
  isEquivΩ→ (fst (fst (Ω^≃∙ n e)) , snd (Ω^≃∙ n e)) (snd (fst (Ω^≃∙ n e)))
snd (Ω^≃∙ (suc n) e) =
  snd (Ω→ (fst (fst (Ω^≃∙ n e)) , snd (Ω^≃∙ n e)))

ΩfunExtIso : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ')
  → Iso (typ (Ω (A →∙ B ∙))) (A →∙ Ω B)
fst (fun (ΩfunExtIso A B) p) x = funExt⁻ (cong fst p) x
snd (fun (ΩfunExtIso A B) p) i j = snd (p j) i
fst (inv (ΩfunExtIso A B) (f , p) i) x = f x i
snd (inv (ΩfunExtIso A B) (f , p) i) j = p j i
rightInv (ΩfunExtIso A B) _ = refl
leftInv (ΩfunExtIso A B) _ = refl

{- Commutativity of loop spaces -}
isComm∙ : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
isComm∙ A = (p q : typ (Ω A)) → p ∙ q ≡ q ∙ p

private
  mainPath : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → (α β : typ ((Ω^ (2 + n)) A))
           → (λ i → α i ∙ refl) ∙ (λ i → refl ∙ β i)
            ≡ (λ i → refl ∙ β i) ∙ (λ i → α i ∙ refl)
  mainPath n α β i = (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j)

EH-filler : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → typ ((Ω^ (2 + n)) A)
  → typ ((Ω^ (2 + n)) A) → I → I → I → _
EH-filler {A = A} n α β i j z =
  hfill (λ k → λ { (i = i0) → ((cong (λ x → rUnit x (~ k)) α)
                                ∙ cong (λ x → lUnit x (~ k)) β) j
                  ; (i = i1) → ((cong (λ x → lUnit x (~ k)) β)
                                ∙ cong (λ x → rUnit x (~ k)) α) j
                  ; (j = i0) → rUnit refl (~ k)
                  ; (j = i1) → rUnit refl (~ k)})
        (inS (mainPath n α β i j)) z

{- Eckmann-Hilton -}
EH : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ ((Ω^ (suc n)) A)
EH {A = A} n α β i j = EH-filler n α β i j i1

{- Lemmas for the syllepsis : EH α β ≡ (EH β α) ⁻¹ -}

EH-refl-refl : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
             → EH {A = A} n refl refl ≡ refl
EH-refl-refl {A = A} n k i j =
  hcomp (λ r → λ { (k = i1) → (refl ∙ (λ _ → basep)) j
                  ; (j = i0) → rUnit basep (~ r ∧ ~ k)
                  ; (j = i1) → rUnit basep (~ r ∧ ~ k)
                  ; (i = i0) → (refl ∙ (λ _ → lUnit basep (~ r ∧ ~ k))) j
                  ; (i = i1) → (refl ∙ (λ _ → lUnit basep (~ r ∧ ~ k))) j})
        (((cong (λ x → rUnit x (~ k)) (λ _ → basep))
         ∙ cong (λ x → lUnit x (~ k)) (λ _ → basep)) j)
  where
  basep = snd (Ω ((Ω^ n) A))

{- Generalisations of EH α β when α or β is refl -}
EH-gen-l : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → {x y : typ ((Ω^ (suc n)) A)} (α : x ≡ y)
       → α ∙ refl ≡ refl ∙ α
EH-gen-l {ℓ = ℓ} {A = A} n {x = x} {y = y} α i j z =
  hcomp (λ k → λ { (i = i0) → ((cong (λ x → rUnit x (~ k)) α) ∙ refl) j z
                  ; (i = i1) → (refl ∙ cong (λ x → rUnit x (~ k)) α) j z
                  ; (j = i0) → rUnit (refl {x = x z}) (~ k) z
                  ; (j = i1) → rUnit (refl {x = y z}) (~ k) z
                  ; (z = i0) → x i1
                  ; (z = i1) → y i1})
        (((λ j → α (j ∧ ~ i) ∙ refl) ∙ λ j → α (~ i ∨ j) ∙ refl) j z)

EH-gen-r : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → {x y : typ ((Ω^ (suc n)) A)} (β : x ≡ y)
        → refl ∙ β ≡ β ∙ refl
EH-gen-r {A = A} n {x = x} {y = y} β i j z =
  hcomp (λ k → λ { (i = i0) → (refl ∙ cong (λ x → lUnit x (~ k)) β) j z
                  ; (i = i1) → ((cong (λ x → lUnit x (~ k)) β) ∙ refl) j z
                  ; (j = i0) → lUnit (λ k → x (k ∧ z)) (~ k) z
                  ; (j = i1) → lUnit (λ k → y (k ∧ z)) (~ k) z
                  ; (z = i0) → x i1
                  ; (z = i1) → y i1})
        (((λ j → refl ∙ β (j ∧ i)) ∙ λ j → refl ∙ β (i ∨ j)) j z)

{- characterisations of EH α β when α or β is refl  -}
EH-α-refl : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
             → (α : typ ((Ω^ (2 + n)) A))
             → EH n α refl ≡ sym (rUnit α) ∙ lUnit α
EH-α-refl {A = A} n α i j k =
  hcomp (λ r → λ { (i = i0) → EH-gen-l n (λ i → α (i ∧ r)) j k
                  ; (i = i1) → (sym (rUnit λ i → α (i ∧ r)) ∙ lUnit λ i → α (i ∧ r)) j k
                  ; (j = i0) → ((λ i → α (i ∧ r)) ∙ refl) k
                  ; (j = i1) → (refl ∙ (λ i → α (i ∧ r))) k
                  ; (k = i0) → refl
                  ; (k = i1) → α r})
        ((EH-refl-refl n ∙ sym (lCancel (rUnit refl))) i j k)

EH-refl-β : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
             → (β : typ ((Ω^ (2 + n)) A))
             → EH n refl β ≡ sym (lUnit β) ∙ rUnit β
EH-refl-β {A = A} n β i j k =
  hcomp (λ r → λ { (i = i0) → EH-gen-r n (λ i → β (i ∧ r)) j k
                  ; (i = i1) → (sym (lUnit λ i → β (i ∧ r)) ∙ rUnit λ i → β (i ∧ r)) j k
                  ; (j = i0) → (refl ∙ (λ i → β (i ∧ r))) k
                  ; (j = i1) → ((λ i → β (i ∧ r)) ∙ refl) k
                  ; (k = i0) → refl
                  ; (k = i1) → β r})
        ((EH-refl-refl n ∙ sym (lCancel (rUnit refl))) i j k)

syllepsis : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (α β : typ ((Ω^ 3) A))
         → EH 0 α β ≡ sym (EH 0 β α)
syllepsis {A = A} n α β k i j =
  hcomp (λ r → λ { (i = i0) → i=i0 r j k
                  ; (i = i1) → i=i1 r j k
                  ; (j = i0) → j-filler r j k
                  ; (j = i1) → j-filler r j k
                  ; (k = i0) → EH-filler 1 α β i j r
                  ; (k = i1) → EH-filler 1 β α (~ i) j r})
        (btm-filler (~ k) i j)
  where
  guy = snd (Ω (Ω A))

  btm-filler : I → I → I → typ (Ω (Ω A))
  btm-filler j i k =
    hcomp (λ r
      → λ {(j = i0) → mainPath 1 β α (~ i) k
          ; (j = i1) → mainPath 1 α β i k
          ; (i = i0) → (cong (λ x → EH-α-refl 0 x r (~ j)) α
                       ∙ cong (λ x → EH-refl-β 0 x r (~ j)) β) k
          ; (i = i1) → (cong (λ x → EH-refl-β 0 x r (~ j)) β
                       ∙ cong (λ x → EH-α-refl 0 x r (~ j)) α) k
          ; (k = i0) → EH-α-refl 0 guy r (~ j)
          ; (k = i1) → EH-α-refl 0 guy r (~ j)})
      (((λ l → EH 0 (α (l ∧ ~ i)) (β (l ∧ i)) (~ j))
       ∙ λ l → EH 0 (α (l ∨ ~ i)) (β (l ∨ i)) (~ j)) k)

  link : I → I → I → _
  link z i j =
    hfill (λ k → λ { (i = i1) → refl
                    ; (j = i0) → rUnit refl (~ i)
                    ; (j = i1) → lUnit guy (~ i ∧ k)})
          (inS (rUnit refl (~ i ∧ ~ j))) z

  i=i1 : I → I → I → typ (Ω (Ω A))
  i=i1 r j k =
    hcomp (λ i → λ { (r = i0) → (cong (λ x → compPath-filler (sym (lUnit x)) (rUnit x) i k) β
                                ∙ cong (λ x → compPath-filler (sym (rUnit x)) (lUnit x) i k) α) j
                    ; (r = i1) → (β ∙ α) j
                    ; (k = i0) → (cong (λ x → lUnit x (~ r)) β ∙
                                   cong (λ x → rUnit x (~ r)) α) j
                    ; (k = i1) → (cong (λ x → rUnit x (~ r ∧ i)) β ∙
                                   cong (λ x → lUnit x (~ r ∧ i)) α) j
                    ; (j = i0) → link i r k
                    ; (j = i1) → link i r k})
          (((cong (λ x → lUnit x (~ r ∧ ~ k)) β
           ∙ cong (λ x → rUnit x (~ r ∧ ~ k)) α)) j)

  i=i0 : I → I → I → typ (Ω (Ω A))
  i=i0 r j k =
    hcomp (λ i → λ { (r = i0) → (cong (λ x → compPath-filler (sym (rUnit x)) (lUnit x) i k) α
                                ∙ cong (λ x → compPath-filler (sym (lUnit x)) (rUnit x) i k) β) j
                    ; (r = i1) → (α ∙ β) j
                    ; (k = i0) → (cong (λ x → rUnit x (~ r)) α ∙
                                   cong (λ x → lUnit x (~ r)) β) j
                    ; (k = i1) → (cong (λ x → lUnit x (~ r ∧ i)) α ∙
                                   cong (λ x → rUnit x (~ r ∧ i)) β) j
                    ; (j = i0) → link i r k
                    ; (j = i1) → link i r k})
          ((cong (λ x → rUnit x (~ r ∧ ~ k)) α
           ∙ cong (λ x → lUnit x (~ r ∧ ~ k)) β) j)

  j-filler : I → I → I → typ (Ω (Ω A))
  j-filler r i k =
    hcomp (λ j → λ { (i = i0) → link j r k
                    ; (i = i1) → link j r k
                    ; (r = i0) → compPath-filler (sym (rUnit guy))
                                                  (lUnit guy) j k
                    ; (r = i1) → refl
                    ; (k = i0) → rUnit guy (~ r)
                    ; (k = i1) → rUnit guy (j ∧ ~ r)})
          (rUnit guy (~ r ∧ ~ k))

------ Ωⁿ⁺¹ A ≃ Ωⁿ(Ω A) ------
flipΩPath : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
                → ((Ω^ (suc n)) A) ≡ (Ω^ n) (Ω A)
flipΩPath {A = A} zero = refl
flipΩPath {A = A} (suc n) = cong Ω (flipΩPath {A = A} n)

flipΩIso : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
              → Iso (fst ((Ω^ (suc n)) A)) (fst ((Ω^ n) (Ω A)))
flipΩIso {A = A} n = pathToIso (cong fst (flipΩPath n))

flipΩIso⁻pres· : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
                      → (f g : fst ((Ω^ (suc n)) (Ω A)))
                      → inv (flipΩIso (suc n)) (f ∙ g)
                      ≡ (inv (flipΩIso (suc n)) f)
                      ∙ (inv (flipΩIso (suc n)) g)
flipΩIso⁻pres· {A = A} n f g i =
    transp (λ j → flipΩPath {A = A} n (~ i ∧ ~ j) .snd
                 ≡ flipΩPath n (~ i ∧ ~ j) .snd) i
                  (transp (λ j → flipΩPath {A = A} n (~ i ∨ ~ j) .snd
                 ≡ flipΩPath n (~ i ∨ ~ j) .snd) (~ i) f
                 ∙ transp (λ j → flipΩPath {A = A} n (~ i ∨ ~ j) .snd
                 ≡ flipΩPath n (~ i ∨ ~ j) .snd) (~ i) g)

flipΩIsopres· : {ℓ : Level} {A : Pointed ℓ} (n : ℕ)
                      → (f g : fst (Ω ((Ω^ (suc n)) A)))
                      → fun (flipΩIso (suc n)) (f ∙ g)
                      ≡ (fun (flipΩIso (suc n)) f)
                      ∙ (fun (flipΩIso (suc n)) g)
flipΩIsopres· n =
  morphLemmas.isMorphInv _∙_ _∙_
    (inv (flipΩIso (suc n)))
    (flipΩIso⁻pres· n)
    (fun (flipΩIso (suc n)))
    (Iso.leftInv (flipΩIso (suc n)))
    (Iso.rightInv (flipΩIso (suc n)))

flipΩrefl : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → fun (flipΩIso {A = A} (suc n)) refl ≡ refl
flipΩrefl {A = A} n j =
  transp (λ i₁ → fst (Ω (flipΩPath {A = A} n ((i₁ ∨ j)))))
         j (snd (Ω (flipΩPath n j)))

---- Misc. ----

isCommA→isCommTrunc : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ A
                    → isOfHLevel (suc n) (typ A)
                    → isComm∙ (∥ typ A ∥ (suc n) , ∣ pt A ∣)
isCommA→isCommTrunc {A = (A , a)} n comm hlev p q =
    ((λ i j → (leftInv (truncIdempotentIso (suc n) hlev) ((p ∙ q) j) (~ i)))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣)
                 (cong (trRec hlev (λ x → x)) (p ∙ q)))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣)
                 (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) p q i)))
 ∙ ((λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣)
                 (comm (cong (trRec hlev (λ x → x)) p) (cong (trRec hlev (λ x → x)) q) i))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣)
                 (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) q p (~ i)))
 ∙∙ (λ i j → (leftInv (truncIdempotentIso (suc n) hlev) ((q ∙ p) j) i)))

ptdIso→comm : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} (e : Iso (typ A) B)
  → isComm∙ A → isComm∙ (B , fun e (pt A))
ptdIso→comm {A = (A , a)} {B = B} e comm p q =
       sym (rightInv (congIso e) (p ∙ q))
    ∙∙ (cong (fun (congIso e)) ((invCongFunct e p q)
                            ∙∙ (comm (inv (congIso e) p) (inv (congIso e) q))
                            ∙∙ (sym (invCongFunct e q p))))
    ∙∙ rightInv (congIso e) (q ∙ p)

flipIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : A → B → Type ℓ''}
  → Iso ((a : A) (b : B) → C a b) ((b : B) (a : A) → C a b)
fun flipIso f b a = f a b
inv flipIso f a b = f b a
rightInv flipIso _ = refl
leftInv flipIso _ = refl

isContrSinglIso : ∀ {ℓ ℓ''} {A : Type ℓ} {a₀ : A}
     {C : Σ[ x ∈ A ] (x ≡ a₀) → Type ℓ''}
  → Iso ((p : Σ[ x ∈ A ] (x ≡ a₀)) → C p)
         (C (a₀ , refl))
fun isContrSinglIso p = p  (_ , refl)
inv (isContrSinglIso {C = C}) c = uncurry λ x p
  → subst C (ΣPathP ((sym p) , λ i j → p (~ i ∨ j))) c
rightInv isContrSinglIso = {!!}
leftInv isContrSinglIso = {!!}
s = J>_
{- Homotopy group version -}
π-comp : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → ∥ typ ((Ω^ (suc n)) A) ∥₂
      → ∥ typ ((Ω^ (suc n)) A) ∥₂ → ∥ typ ((Ω^ (suc n)) A) ∥₂
π-comp n = elim2 (λ _ _ → isSetSetTrunc) λ p q → ∣ p ∙ q ∣₂

EH-π : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : ∥ typ ((Ω^ (2 + n)) A) ∥₂)
               → π-comp (1 + n) p q ≡ π-comp (1 + n) q p
EH-π  n = elim2 (λ x y → isOfHLevelPath 2 isSetSetTrunc _ _)
                             λ p q → cong ∣_∣₂ (EH n p q)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Equality as Eq renaming (_≡_ to _≡'_ ; refl to refl' ; _∙_ to _c_ ; funExt to funExt*) hiding (_≃_ ; isEquiv)

rUnit-∙ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡' y) → (p c refl') ≡' p
rUnit-∙ refl' = refl'

rCancel-∙ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡' y) → (p c Eq.sym p) ≡' refl'
rCancel-∙ refl' = refl'

lCancel-∙ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡' y) → (Eq.sym p c p) ≡' refl'
lCancel-∙ refl' = refl'

assocLem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : y ≡' x) (q : x ≡' z) → Eq.sym p c (p c q) ≡' q
assocLem refl' q = refl'

Ω' : ∀ {ℓ} (A : Pointed ℓ) → Pointed ℓ
Ω' A = (snd A ≡' snd A) , refl'

_→∙'_ : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') → Type _
_→∙'_  A B = Σ[ f ∈ (fst A → fst B) ] f (pt A) ≡' snd B


Ω→' : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → (A →∙' B) → Ω' A →∙' Ω' B
Ω→' {A = A} {B = B , b} (f , f₀) = (λ p → (Eq.sym f₀) c (ap f p c f₀)) , lCancel-∙ f₀ -- refl'

subst' : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') {x y : A} (p : x ≡' y) → B x → B y
subst' B refl' x = x

subst2' : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {A' : Type ℓ'} (B : A → A' → Type ℓ'') {x y : A} {x' y' : A'} (p : x ≡' y) (q : x' ≡' y') → B x x' → B y y'
subst2' B {x = x} refl' q = subst' (B x) q

Sq : ∀ {ℓ} {A : Type ℓ} {x y z w : A} (p : x ≡' y) (q : z ≡' w) (l : x ≡' z) (w : y ≡' w) → Type ℓ
Sq p q l w = subst2'(λ x y → x ≡' y) p q l ≡ w

Σ≡ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → (f g : A →∙' B) → Type _
Σ≡ {A = A} {B = B} f g =
  Σ[ p ∈ ((x : fst A) → fst f x ≡' fst g x) ]
    subst' (λ z → z ≡' pt B) (p (pt A)) (snd f) ≡' snd g

LTyp : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω' (A , a) →∙' Ω' (B , b)) → Type _
LTyp {A = A} {B = B} a b g = (Σ[ f ∈ (A → B) ] (Σ[ p ∈ f a ≡' b ] (Σ≡ (Ω→' (f , p)) g)))

ΣPathP' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B} (p : fst x ≡' fst y)
  → subst' B p (snd x) ≡' snd y
  → x ≡' y
ΣPathP' refl' refl' = refl'

FF : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {a : A} {x : A} {b : B} {y : B}
     (h : ((x ≡' a) → y ≡' b))
  → x ≡' a
  → Ω' (A , a) →∙' Ω' (B , b)
fst (FF h e) p = Eq.sym (h e) c h (e c p)
snd (FF h e) = ap (Eq.sym (h e) c_) (ap h (rUnit-∙ e)) c lCancel-∙ (h e)

RTyp : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω' (A , a) →∙' Ω' (B , b)) → Type _
RTyp {A = A} {B = B} a b g =
  ((x : A) → Σ[ y ∈ B ] (Σ[ h ∈ ((x ≡' a) → y ≡' b) ]
      ((e : x ≡' a)
      → Σ[ gid ∈ ((x : fst (Ω' (A , a))) → FF h e .fst x ≡' fst g x) ]
                  subst' (λ z → z ≡' refl') (gid refl') (FF h e .snd) ≡' snd g)))




aLem : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω' (A , a) →∙' Ω' (B , b))
  → (f : A → B) (f₀ : f a ≡' b) (p : (x : _) → fst (Ω→' (f , f₀)) x ≡' fst g x) (x : A) (h : x ≡' a) (q : fst (Ω' (A , a)))
  → (Eq.sym (ap f h c f₀) c (ap f (h c q) c f₀)) ≡' fst g q
aLem a b g f f₀ p .a refl' q = p q

LTyp→RTyp : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω' (A , a) →∙' Ω' (B , b))
          → LTyp a b g → RTyp a b g
fst (LTyp→RTyp a b g (f , f₀ , p) x) = f x
fst (snd (LTyp→RTyp a b g (f , f₀ , p) x)) q = ap f q c f₀
fst (snd (snd (LTyp→RTyp a b g (f , f₀ , p) x)) h) q = aLem a b g f f₀ (fst p) x h q
snd (snd (snd (LTyp→RTyp a .(f a)
  (fst₁ , .(subst' (λ z → z ≡' pt ((f a ≡' f a) , snd (Ω' (_ , f a))))
    (p (pt ((a ≡' a) , refl'))) (snd (Ω→' (f , refl'))))) (f , refl' , p , refl') .a)) refl')
  = refl'

RTyp→LTypLem : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω' (A , a) →∙' Ω' (B , b))
  → (F : RTyp a b g) → (y : A) (p : y ≡' a) → ((ap (λ x → fst (F x)) p c F a .snd .fst refl')) ≡' fst (F y .snd) p
RTyp→LTypLem a b g F .a refl' = refl'

RTyp→LTyp : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω' (A , a) →∙' Ω' (B , b))
          → RTyp a b g → LTyp a b g
fst (RTyp→LTyp a b g F) = fst ∘ F
fst (snd (RTyp→LTyp a b g F)) = F a .snd .fst refl'
fst (snd (snd (RTyp→LTyp {A = A} {B = B} a b g F))) p =
   (ap (Eq.sym (F a .snd .fst refl') c_)
      (RTyp→LTypLem a b g F a p)
  c F a .snd .snd refl' .fst p)
snd (snd (snd (RTyp→LTyp a b g F))) =
  T a b (fst ∘ F) (snd (F a) .fst refl')
    g
    (F a .snd .snd refl' .fst refl')
    c
    F a .snd .snd refl' .snd
  where
  T : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (f : A → B) (f₀ : f a ≡' b) (g : Ω' (A , a) →∙' Ω' (B , b))
    → (l : (Eq.sym f₀ c f₀) ≡' fst g refl')
   → subst' (λ z → z ≡' refl' {x = b}) l (snd (Ω→' (f , f₀)))
   ≡' subst' (λ z → z ≡' refl') l (lCancel-∙ f₀)
  T a .(f a) f refl' g l = refl'


isHomogeneousPath* : ∀ {ℓ} {A : Type ℓ} {x y : A} {p : x ≡' y} → isHomogeneous ((x ≡' y) , p)
isHomogeneousPath* {A = A} {x = x} {p = refl'} =
  subst isHomogeneous (ΣPathP (PathPathEq {x = x} {y = x}
  , toPathP λ i → transportRefl (transportRefl refl' i) i))
    (isHomogeneousPath A {x = x} {y = x} refl)

Pointed→∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → (A →∙ B) ≡ (A →∙' B)
Pointed→∙ {A = A} {B = B} i = Σ[ f ∈ (fst A → fst B) ] PathPathEq {x = f (pt A)} {y = pt B} i

→∙Homogeneous≡' : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → isHomogeneous B → {f g : A →∙' B}
                → ((x : fst A) → fst f x ≡' fst g x)
                → f ≡' g
→∙Homogeneous≡' {A = A} {B = B} ishom {f} {g} =
  transp (λ j → {f g : Pointed→∙ {A = A} {B = B} j}
                → ((x : fst A) → fst f x ≡' fst g x)
                → f ≡' g) i0 (λ {f} {g} h → pathToEq (→∙Homogeneous≡ ishom (funExt λ x → eqToPath (h x)))) {f} {g}

→∙'Iso : {!!}
→∙'Iso = {!!}

→∙HomogeneousSq'' : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → isHomogeneous B → (f g : A →∙' B)
                → (p q : Σ≡ f g)
                → (fst p) ≡' fst q
                → p ≡' q
→∙HomogeneousSq'' {A = A} {B = B} ishom =
  transp (λ i → (f g : Pointed→∙ {A = A} {B = B} i)
                 (p q : Σ[ id ∈ ((x : fst A) → PathPathEq {x = fst f x} { y = fst g x} i) ]
                         PathPathEq {x = subst' (λ b → b ≡' pt B)
                               (transp (λ j → PathPathEq {x = fst f (pt A)}
                                 {y = fst g (pt A)} (i ∨ j)) i (id (pt A)))
                               (transp (λ j → PathPathEq {x = fst f (pt A)}
                                 {y = pt B} (i ∨ j)) i (snd f))}
                           {y = transp (λ j → PathPathEq {x = fst g (pt A)}
                                 {y = pt B} (i ∨ j)) i (snd g)} i)
                 → PathPathEq {x = fst p} {y = fst q} i
                 → PathPathEq {x = p} {y = q} i) i0
         λ f g → transp (λ i → (p q : Σ[ id ∈ ((x : fst A) → (fst f x) ≡ (fst g x)) ] (LOL f g id (~ i)))
                              → Path (((x : fst A) → (fst f x) ≡ (fst g x))) (fst p) (fst q)
                              → Path (Σ[ id ∈ ((x : fst A) → (fst f x) ≡ (fst g x)) ] (LOL f g id (~ i))) p q) i0
                        λ p q r → λ i → (λ x j → PP f g q p r i j .fst x)
                                          , λ j → (PP f g q p r i j .snd)
  where
  PP : (f g : A →∙ B) (q     : Σ-syntax ((x : fst A) → fst f x ≡ fst g x)
        (λ id₁ → PathP (λ i → id₁ (pt A) i ≡ pt B) (snd f) (snd g)))
                       (p     : Σ-syntax ((x : fst A) → fst f x ≡ fst g x)
                               (λ id₁ → PathP (λ i → id₁ (pt A) i ≡ pt B) (snd f) (snd g)))
     → Path ((x : fst A) → fst f x ≡ fst g x) (fst p) (fst q)
     → Path (Path (A →∙ B) f g) (ΣPathP (funExtPath (fst p) , snd p))
               (ΣPathP (funExtPath (fst q) , snd q))
  PP f g q p r =
    →∙Homogeneous≡Path {f∙ = f} {g∙ = g}
         ishom (ΣPathP (funExt (fst p) , snd p))
           (ΣPathP (funExt (fst q) , snd q)) (cong funExt r)
  LOL : (f g : A →∙ B) (id : ((x : fst A) → (fst f x) ≡ (fst g x)))
    → (subst' (λ b → b ≡' pt B)
                 (transp (λ j → PathPathEq {x = fst f (pt A)}
                                 {y = fst g (pt A)} j) i0 (id (pt A)))
                 (transp (λ j → PathPathEq {x = fst f (pt A)}
                                 {y = pt B} j) i0 (snd f))
          ≡ transp (λ j → PathPathEq {x = fst g (pt A)} {y = pt B} j) i0 (snd g))
    ≡ PathP (λ i → id (pt A) i ≡ pt B) (snd f) (snd g)
  LOL (f , fp) (g , gp) id' = J-funExt' {f = f} (λ g id → (f₀ : f (pt A) ≡ pt B) (g₀ : g (pt A) ≡ pt B)
    → ((subst' (λ b → b ≡' pt B)
                 (transp (λ j → PathPathEq {x = f (pt A)}
                                 {y = g (pt A)} j) i0 (id (pt A)))
                 (transp (λ j → PathPathEq {x = f (pt A)}
                                 {y = pt B} j) i0 f₀)
          ≡ transp (λ j → PathPathEq {x = g (pt A)} {y = pt B} j) i0 g₀)
       ≡ PathP (λ i → id (pt A) i ≡ pt B) f₀ g₀ ))
         (λ f₀ g₀ → C f₀ g₀)
         g id' fp gp
     where
     C : (f₀ g₀ : f (pt A) ≡ pt B)
       → (subst' (λ b → b ≡' pt B)
       (transp (λ j → PathPathEq {x = f (pt A)} {y = f (pt A)} j) i0 refl)
       (transp (λ j → PathPathEq {x = f (pt A)} {y = pt B} j) i0 f₀)
       ≡ transp (λ j → PathPathEq {x = f (pt A)} {y = pt B} j) i0 g₀)
      ≡ (f₀ ≡ g₀)
     C f₀ g₀ = (λ j → (subst' (λ b → b ≡' pt B)
                         (help j)
                         (transp (λ j → PathPathEq {x = f (pt A)} {y = pt B} j) i0 f₀)
                         ≡ transp (λ j → PathPathEq {x = f (pt A)} {y = pt B} j) i0 g₀))
             ∙ help2 _ (PathPathEq {x = f (pt A)} {y = pt B}) {f₀} {g₀}
       where
       help : transp (λ j → PathPathEq {x = f (pt A)} {y = f (pt A)} j) i0 refl ≡ refl'
       help i = transportRefl (transportRefl refl' i) i

       help2 : ∀ {ℓ} {A : Type ℓ} (B : Type ℓ) → (p : A ≡ B) {x y : A}
         → (transp (λ i → p i) i0 x ≡ transp (λ i → p i) i0 y) ≡ (x ≡ y)
       help2 {A = A} = J> λ {x} {y} → λ j → transportRefl x j ≡ transportRefl y j

CL : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω' (A , a) →∙' Ω' (B , b))
          → (x : RTyp a b g) → LTyp→RTyp a b g (RTyp→LTyp a b g x) ≡' x
CL {A = A} {B = B} a b g F =
  Eq.funExt
    λ z → ΣPathP' refl'
           (ΣPathP' (lem z)
             (funExt* λ q → →∙HomogeneousSq'' isHomogeneousPath* _ _ _ _
               (lem2 {p = lem z} {f = (snd (snd (LTyp→RTyp a b g (RTyp→LTyp a b g F) z)))} {g = (snd (snd (F z)))}
                 (lem1 {B = λ a₁ x → (Eq.sym (a₁ q) c a₁ (q c x)) ≡' fst g x} (lem z)
                       {f = (snd (snd (LTyp→RTyp a b g (RTyp→LTyp a b g F) z)) q .fst)}
                       {g = fst (snd (snd (F z)) q)}
                   λ {p} → main z q p))))
  where

  lem : (z : A) → (λ q → ap (λ x → fst (F x)) q c F a .snd .fst refl') ≡' fst (snd (F z))
  lem z = funExt* (RTyp→LTypLem a b g F z)

  PTypeTransp : ∀ {ℓ ℓ'} {A : Type ℓ} → (_≡'_ _≡''_ : (x y : A) → Type ℓ) (e : _≡'_ ≡ _≡''_)
    → (f : (x : A) → x ≡' x)
    → (g : (x : A) → x ≡'' x)
    → ((x : A) → transp (λ i → e i x x) i0 (f x) ≡ g x)
    → (D : (_≡'_ : (x y : A) → Type ℓ) (f : (x : A) → x ≡' x) → Type ℓ')
    → D _≡'_ f → D _≡''_ g
  PTypeTransp _≡'_ = J> λ f g id D h → transp (λ i → D _≡'_ λ x → ((transportRefl _) ⁻¹ ∙ id x) i) i0 h

  PTypeInst : ∀ {ℓ} {A : Type ℓ} (x : A) → transp (λ i → PathPathEq {x = x} {y = x} i) i0 refl ≡ refl' {x = x}
  PTypeInst x i = transportRefl (transportRefl refl' i) i

  ap₂ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : A → B → Type ℓ''} → (f : (x : A) (y : B) → C x y)
    → {x y : A} {z w : B} (p : x ≡' y) (q : z ≡' w)
    → (subst2' C p q (f x z)) ≡' f y w
  ap₂ f refl' refl' = refl'

  ap₂-nonDep : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (f : A → B → C)
    → {x y : A} {z w : B} (p : x ≡' y) (q : z ≡' w) → f x z ≡' f y w
  ap₂-nonDep r {x = x} refl' p = ap (r x) p

  apConst : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡' y) → ap (λ x → x) p ≡' p
  apConst refl' = refl'

  lemzB : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f g : A → B} (r : f ≡' g) (x y : A)
          {h : B → B → C}
          {c' : C}
          (p : h (f x) (f y) ≡' c')
          (q : h (g x) (g y) ≡' c')
       → (ap₂-nonDep h (Eq.sym (Eq.funExt⁻ r x)) (Eq.sym (Eq.funExt⁻ r y)) c p) ≡' q
       → subst' (λ s → h (s x) (s y) ≡' c') r p ≡' q
  lemzB refl' x y p q a = a

  lemz : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} (r : f ≡' g) (x y : A)
    → {C : B x → B y → Type ℓ''}
    → {h k : (a : B x) (b : B y) → C a b}
    → (p : h (f x) (f y) ≡' k (f x) (f y))
    → (q : h (g x) (g y) ≡' k (g x) (g y))
    → (Eq.sym (ap₂ h (Eq.funExt⁻ r x) (Eq.funExt⁻ r y))
      c (ap (subst2' (λ z z₁ → C z z₁) (Eq.funExt⁻ r x) (Eq.funExt⁻ r y))
        p
        c ap₂ k ( (Eq.funExt⁻ r x)) ((Eq.funExt⁻ r y))))
      ≡' q
    → subst' (λ s → h (s x) (s y) ≡' k (s x) (s y)) r p
    ≡' q
  lemz refl' x y p q id1 = (Eq.sym (apConst p) c Eq.sym (rUnit-∙ _)) c id1

  main : (z : A) (q : z ≡' a) (p : a ≡' a) → subst'
      (λ a₁ → (Eq.sym (a₁ q) c a₁ (q c p)) ≡' fst g p) (lem z)
      (snd (snd (LTyp→RTyp a b g (RTyp→LTyp a b g F) z)) q .fst p)
      ≡' fst (snd (snd (F z)) q) p
  main z refl' p = lemzB {A = z ≡' z} {B = fst (F z) ≡' b}
                          {C = fst (Ω' (B , b))} (lem z) refl' p
                          {h = λ id1 id2 → Eq.sym id1 c id2} {c' = fst g p}
                          (snd (snd (LTyp→RTyp z b g (RTyp→LTyp z b g F) z)) refl' .fst p)
                          (fst (snd (snd (F z)) refl') p)
                          (ap (_c snd (snd (LTyp→RTyp z b g (RTyp→LTyp z b g F) z)) refl' .fst p)
                              (Lem c ap-sym (λ id2 → Eq.sym (fst (F z .snd) refl') c id2) (RTyp→LTypLem z b g F z p))
                         c assocLem ((ap (λ id2 → Eq.sym (fst (F z .snd) refl') c id2)
                                      (RTyp→LTypLem z b g F z p)))
                                      (fst (snd (snd (F z)) refl') p))
     where
     ap-sym : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) {x y : A} (p : x ≡' y) → ap f (Eq.sym p) ≡' Eq.sym (ap f p)
     ap-sym f refl' = refl'

     Lem1 : (p : _) → Eq.sym (Eq.funExt⁻ (lem z) p) ≡' Eq.sym (RTyp→LTypLem a b g F z p)
     Lem1 p = ap Eq.sym (Eq.funExt⁻ (funExt⁻-funExt (RTyp→LTypLem a b g F z)) p)

     Lem : ap₂-nonDep (λ id1 id2 → Eq.sym id1 c id2)
            (Eq.sym (Eq.funExt⁻ (lem z) refl')) (Eq.sym (Eq.funExt⁻ (lem z) p))
          ≡' ap₂-nonDep (λ id1 id2 → Eq.sym id1 c id2)
              refl'
              (Eq.sym (RTyp→LTypLem a b g F z p))
     Lem = ap (λ q → ap₂-nonDep (λ id1 id2 → Eq.sym id1 c id2)
                     q (Eq.sym (Eq.funExt⁻ (lem z) p)))
               (Lem1 refl')
         c ap (ap₂-nonDep (λ id1 id2 → Eq.sym id1 c id2)
              (Eq.sym (RTyp→LTypLem a b g F z refl')))
                (Lem1 p)

  lem1 : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {A' : Type ℓ'} {B : A → A' → Type ℓ''}
    {x y : A} (p : x ≡' y)
    → {f : (a' : A') → B x a'} {g : (a' : A') → B y a'}
    → ({a' : A'}
    → subst' (λ a → B a a') p (f a') ≡' g a')
    → subst' (λ a → (a' : A') → B a a') p f ≡' g
  lem1 refl' {f = f} {g = g} x = funExt* (λ _ → x)

  lem2 : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {A' : Type ℓ'} {B : A → A' → Type ℓ''} {C : (a : A) (a' : A') → B a a' → Type ℓ'''}
    {x y : A} {p : x ≡' y}
    → {f : (a' : A') → Σ (B x a') (C x a')} {g : (a' : A') → Σ (B y a') (C y a')}
    → {a' : A'}
    → subst' (λ a → B a a') p (f a' .fst) ≡' g a' .fst
    →  fst ((subst' (λ a → (a' : A') → Σ (B a a') (C a a')) p f) a') ≡' fst (g a')
  lem2 {p = refl'} q = q

LC : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω' (A , a) →∙' Ω' (B , b))
          → (x : LTyp a b g) → RTyp→LTyp a b g (LTyp→RTyp a b g x) ≡' x
LC {A = A} {B = B} a .(f a) g (f , refl' , p) =
  ΣPathP' refl' (ΣPathP' refl'
    (→∙HomogeneousSq'' isHomogeneousPath* _ _
      _ _ (funExt* λ r → ap (λ x → ap (λ q → q) x c fst p r) (LEM p a r))))

  where
  LEM : (p : _) (y : A) (q : y ≡' a)
    → (RTyp→LTypLem a (f a) g (LTyp→RTyp a (f a) g (f , refl' , p)) y q)
     ≡' refl'
  LEM p y refl' = refl'

FF' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {a : A} {x : A} {b : B} {y : B}
         (h : ((x ≡ a) → y ≡ b))
      → x ≡ a
      → Ω (A , a) →∙ Ω (B , b)
fst (FF' h e) p = h e ⁻¹ ∙ h (e ∙ p)
snd (FF' h e) = cong (h e ⁻¹ ∙_) (cong h ((rUnit e) ⁻¹)) ∙ lCancel (h e)

RTyp' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω (A , a) →∙ Ω (B , b)) → Type _
RTyp' {A = A} {B = B} a b g =
  ((x : A) → Σ[ y ∈ B ] (Σ[ h ∈ ((x ≡ a) → y ≡ b) ]
      ((e : x ≡ a)
      → Σ[ gid ∈ ((x : fst (Ω (A , a))) → FF' h e .fst x ≡ fst g x) ]
                  PathP (λ i → gid refl i ≡ refl) (FF' h e .snd) (snd g))))

reflPathPathEq : ∀ {ℓ} {A : Type ℓ} (x : A)
  → PathP (λ i → PathPathEq {x = x} {y = x} i) refl refl'
reflPathPathEq x = toPathP λ i → transportRefl (transportRefl refl' i) i

lem1 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B)
  → (Ω (A , a) →∙ Ω (B , b)) ≡ (Ω' (A , a) →∙' Ω' (B , b))
lem1 a b i = Pointed→∙ {A = (PathPathEq {x = a} {y = a} i) , reflPathPathEq a i}
                        {B = (PathPathEq {x = b} {y = b} i) , reflPathPathEq b i} i

trans' : {!!}
trans' = {!!}


RTyp≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B)
  → PathP (λ j → (g : lem1 a b j) → Type _) (λ g → RTyp' a b g) λ g → RTyp a b g
RTyp≡ = {!!}




-- {-
-- Ω→' : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
--   → (A →∙ B) → Ω A →∙ Ω B
-- fst (Ω→' f) p = sym (snd f) ∙ cong (fst f) p ∙ snd f
-- snd (Ω→' f) = cong (sym (snd f) ∙_) (sym (lUnit (snd f))) ∙ lCancel (snd f)

-- r' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B)
--   → (f : A → B) (p : f a ≡ b) (g : Ω (A , a) →∙ Ω (B , b)) → (Ω→' (f , p) ≡ g)
--   → (x : A) (e : x ≡ a)
--   → (l : a ≡ a)
--   → sym ((λ i₁ → f (e i₁)) ∙ p) ∙ (λ i₁ → f ((e ∙ l) i₁)) ∙ p ≡ fst g l
-- r' a b f p g q x e l = 
--   (λ k → sym (compPath-filler' (cong f e) p (~ k))
--            ∙ (λ i₁ → f ((compPath-filler' e l (~ k) i₁))) ∙ p)
--     ∙ funExt⁻ (cong fst q) l

-- asd' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B)
--   → (f : A → B) (p : f a ≡ b) (g : Ω (A , a) →∙ Ω (B , b)) → (Ω→' (f , p) ≡ g)
--   → ((x : A) → Σ[ y ∈ B ] (Σ[ h ∈ ((x ≡ a) → y ≡ b) ]
--                       ((e : x ≡ a) → ((λ p → sym (h e) ∙ h (e ∙ p))
--                                      , cong (sym (h e) ∙_) (cong h (sym (rUnit e)))
--                                           ∙ lCancel (h e))
--                                      ≡ g)))
-- fst (asd' a b f p g q x) = f x
-- fst (snd (asd' a b f p g q x)) l = cong f l ∙ p
-- fst (snd (snd (asd' a b f p g q x)) e i) l = r' a b f p g q x e l i
-- snd (snd (snd (asd' a b f p g q x)) e i) j = {!cong snd q!}
-- -}
-- LTyp : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω (A , a) →∙ Ω (B , b)) → Type _
-- LTyp {A = A} {B = B} a b g = (Σ[ f ∈ (A → B) ] (Σ[ p ∈ f a ≡ b ] Ω→' (f , p) ≡ g))

-- RTyp : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω (A , a) →∙ Ω (B , b)) → Type _
-- RTyp {A = A} {B = B} a b g =
--   ((x : A) → Σ[ y ∈ B ] (Σ[ h ∈ ((x ≡ a) → y ≡ b) ]
--                       ((e : x ≡ a) → ((λ p → sym (h e) ∙ h (e ∙ p))
--                                      , cong (sym (h e) ∙_) (cong h (sym (rUnit e)))
--                                           ∙ lCancel (h e))
--                                      ≡ g)))

-- PP* : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (x : A)
--          (f : A → B)(b : B) (f₀ : f x ≡ b) (g : Ω (A , x) →∙ Ω (B , b)) (p : Ω→' (f , f₀) ≡ g)
--       → PathP (λ i → (cong₂ _∙_ (cong sym (sym (lUnit f₀)))
--                                        (cong (_∙ f₀) (cong (cong f) (sym (lUnit refl))))
--                     ∙ funExt⁻ (cong fst p) (refl {x = x})) i  ≡ refl {x = b}) (((λ i →
--         (λ i₁ → ((λ i₂ → f x) ∙ f₀) (~ i₁)) ∙
--         (λ i₁ → f (rUnit (refl {x = x}) (~ i) i₁)) ∙ f₀)
--      ∙ lCancel ((λ i → f x) ∙ f₀))) (snd g)
-- PP* x f = J> (J> {!!})

-- P-typ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (x : A) (a : A) (e : x ≡ a) (b : B)
--            (f : A → B) (f₀ : f a ≡ b) (g : Ω (A , a) →∙ Ω (B , b)) (p : Ω→' (f , f₀) ≡ g)
--         → Type _
-- P-typ x a e b f f₀ g p =
--   ((λ p → sym (cong f e ∙ f₀) ∙ cong f (e ∙ p) ∙ f₀)
--     , (λ i →
--           (λ i₁ → ((λ i₂ → f (e i₂)) ∙ f₀) (~ i₁)) ∙
--           (λ i₁ → f (rUnit e (~ i) i₁)) ∙ f₀)
--        ∙ lCancel ((λ i → f (e i)) ∙ f₀))
--      ≡ g

-- J-lemL→R-Base : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A)  (b : B)
--            (f : A → B) (f₀ : f a ≡ b) (g : Ω (A , a) →∙ Ω (B , b)) (p : Ω→' (f , f₀) ≡ g)
--   → P-typ a a refl b f f₀ g p 
-- J-lemL→R-Base x b f f₀ g id' =
--   ΣPathP ((funExt (λ p → cong₂ _∙_ (cong sym (sym (lUnit f₀)))
--                                          (cong (_∙ f₀) (cong (cong f) (sym (lUnit p))))
--                       ∙ funExt⁻ (cong fst id') p))
--             , PP* x f b f₀ g id')



-- J-lemL→R :
--   ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (x : A) (a : A) (e : x ≡ a) (b : B)
--            (f : A → B) (f₀ : f a ≡ b) (g : Ω (A , a) →∙ Ω (B , b)) (p : Ω→' (f , f₀) ≡ g)
--   → P-typ x a e b f f₀ g p
-- J-lemL→R x =
--   J> (J-lemL→R-Base x)


-- J-lemL→R-refl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (x : A) (f : A → B)  (b : B)
--            (f₀ : f x ≡ b) (g : Ω (A , x) →∙ Ω (B , b)) (id : Ω→' (f , f₀) ≡ g)
--            → J-lemL→R x x refl b f f₀ g id
--             ≡ J-lemL→R-Base x b f f₀ g id
-- J-lemL→R-refl {A = A} {B = B} x f b f₀ g id' i =
--   JRefl (λ a e → (b : B)
--            (f : A → B) (f₀ : f a ≡ b) (g : Ω (A , a) →∙ Ω (B , b)) (p : Ω→' (f , f₀) ≡ g)
--   → P-typ x a e b f f₀ g p) (J-lemL→R-Base x) i b f f₀ g id'

-- L→R : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω (A , a) →∙ Ω (B , b)) → LTyp a b g → RTyp a b g
-- fst (L→R a b g (f , f₀ , p) x) = f x
-- fst (snd (L→R a b g (f , f₀ , p) x)) q = cong f q ∙ f₀
-- snd (snd (L→R a b g (f , f₀ , p) x)) e = J-lemL→R x a e b f f₀ g p

-- R→L-fst : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω (A , a) →∙ Ω (B , b)) (F : RTyp a b g)
--   → (p : a ≡ a) → cong (fst ∘ F) p ∙ F a .snd .fst (λ _ → a) ≡ fst (F a .snd) ((λ _ → a) ∙ p)
-- R→L-fst a b g F p =
--     (λ j → (λ i → (fst (F (p (~ j ∧ i)))))
--       ∙ F (p (~ j)) .snd .fst λ i → p (~ j ∨ i))
--   ∙ sym (lUnit (fst (F a .snd) p))
--   ∙ cong (fst (F a .snd)) (lUnit p)

-- R→LPP : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω (A , a) →∙ Ω (B , b))
--   → (F : RTyp a b g)
--   → PathP
--       (λ i →
--          funExt
--          (λ p i₁ →
--             (λ i₂ → F a .snd .fst (λ _ → a) (~ i₂)) ∙ R→L-fst a b g F p i₁)
--          i (snd (Ω (A , a)))
--          ≡ snd (Ω (B , b)))
--       (snd (Ω→' (fst ∘ F , F a .snd .fst refl)))
--       ((λ i →
--           (λ i₁ → fst (F a .snd) (λ _ → a) (~ i₁)) ∙
--           fst (F a .snd) (rUnit (λ _ → a) (~ i)))
--        ∙ lCancel (fst (F a .snd) (λ _ → a)))
-- R→LPP = {!!}

-- R→L : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω (A , a) →∙ Ω (B , b)) → RTyp a b g → LTyp a b g
-- fst (R→L a b g F) = fst ∘ F
-- fst (snd (R→L a b g F)) = F a .snd .fst refl
-- snd (snd (R→L a b g F)) = ΣPathP ((funExt (λ p → cong (sym (F a .snd .fst (λ _ → a)) ∙_)
--     (R→L-fst a b g F p)))
--   , R→LPP a b g F)
--   ∙  F a .snd .snd refl

-- R→L→R₁ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (x : A) (a : A) (e : x ≡ a) (b : B) (g : Ω (A , a) →∙ Ω (B , b))
--   → (F : RTyp a b g)
--   → (λ i₁ → fst (F (e i₁))) ∙ F a .snd .fst (λ _ → a) ≡ fst (snd (F x)) e
-- R→L→R₁ x = J> λ b g F → sym (lUnit (F x .snd .fst (λ _ → x)))

-- L→R→L : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω (A , a) →∙ Ω (B , b))
--   → (x : LTyp a b g) → R→L a b g (L→R a b g x) ≡ x
-- fst (L→R→L a b g (f , f₀ , id') i) = f
-- fst (snd (L→R→L a b g (f , f₀ , id') i)) = lUnit f₀ (~ i)
-- snd (snd (L→R→L {A = A} a b g (f , f₀ , id') i)) = Lol a f b f₀ g id' i
--   where
--   Lol : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (f : A → B)
--     (b : B) (f₀ : f a ≡ b) (g : Ω (A , a) →∙ Ω (B , b)) (id' : Ω→' (f , f₀) ≡ g)
--       → PathP (λ i → Ω→' (f , lUnit f₀ (~ i)) ≡ g) (snd (snd (R→L a b g (L→R a b g (f , f₀ , id'))))) id'
--   Lol {A = A} a f = J> (J> →∙HomogeneousSquare (isHomogeneousPath _ _) _ _ _ _
--               ((cong-∙ fst (ΣPathP
--        (funExt
--         (λ p i₁ →
--            (λ i₂ → ((λ i₃ → f a) ∙ refl) (~ i₂)) ∙
--            R→L-fst a (f a) (Ω→' (f , refl))
--            (L→R a (f a) (Ω→' (f , refl)) (f , refl , refl)) p i₁)
--         ,
--         R→LPP a (f a) (Ω→' (f , refl))
--         (L→R a (f a) (Ω→' (f , refl)) (f , refl , refl))))
--         (J-lemL→R a a (λ _ → a) (f a) f refl (Ω→' (f , refl)) refl)
--               ∙ (λ i → funExt (λ p → cong ((refl {x = f a} ∙ refl) ∙_)
--                                             (R→L-fst a (f a) (Ω→' (f , refl))
--                                               (L→R a (f a) (Ω→' (f , refl))
--                                              (f , refl , refl)) p)
--                                           ∙ λ j → J-lemL→R-refl a f (f a) refl (Ω→' (f , refl)) refl i j .fst p))
--               ∙ (λ _ → funExt λ p →
--                          cong ((refl {x = f a} ∙ refl) ∙_)
--                                  ((R→L-fst a (f a) (Ω→' (f , refl))
--                                               (L→R a (f a) (Ω→' (f , refl))
--                                              (f , refl , refl)) p))
--                             ∙ cong₂ _∙_ (sym (lUnit refl))
--                                          (cong (_∙ refl) (cong (cong f) (sym (lUnit p))))
--                                        ∙ refl)
--               )
--               ◁ ((λ _ → funExt λ p → cong ((refl {x = f a} ∙ refl) ∙_)
--                                              ((λ j → (λ i → f (p (~ j ∧ i)))
--                                                     ∙ (λ i → f (p (~ j ∨ i))) ∙ refl)
--                                             ∙ sym (lUnit ((λ i → f (p i)) ∙ refl))
--                                             ∙ λ i → (λ i₁ → f (lUnit p i i₁)) ∙ (λ _ → f a))
--                                     ∙ cong₂ _∙_ (sym (lUnit refl))
--                                          (cong (_∙ refl) (cong (cong f) (sym (lUnit p))))
--                                        ∙ refl)
--                ◁ {!!})))

--       where
--       lem1 : (a x : A) (p : a ≡ x) → ((λ j → (λ i → f (p (~ j ∧ i)))
--                                    ∙ (λ i → f (p (~ j ∨ i))) ∙ refl))
--                          ≡ cong (cong f p ∙_) (sym (rUnit refl))
--                          ∙ lUnit ((λ i → f (p i)) ∙ refl)
--       lem1 a = J> {!!} ∙ sym {!!}

--       lem2 : {!!}
--       lem2 = {!!}

--       lem : PathP
--         (λ i₁ →
--          (λ p → (rUnit refl (~ i₁) ∙ (cong f p ∙ rUnit refl (~ i₁)))) ≡
--          (λ p → (refl ∙ (cong f p ∙ refl)))) _ _ -- L→R a (f a) (Ω→' (f , refl)) (f , refl , refl) ≡ λ x → {!!}
--       lem i j p k =
--         hcomp (λ r → λ {(i = i0) → {!L→R a (f a) (Ω→' (f , refl))
--                                              (f , refl , refl)!}
--                        ; (i = i1) → {!!} -- (refl ∙ (cong f p ∙ refl)) k
--                        ; (j = i0) → {!!}
--                        ; (j = i1) → {!!}
--                        ; (k = i0) → {!!}
--                        ; (k = i1) → {!!}})
--               {!!}

-- -- R→L→R : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω (A , a) →∙ Ω (B , b)) → (x : RTyp a b g) → L→R a b g (R→L a b g x) ≡ x
-- -- fst (R→L→R a b g F i x) = fst (F x)
-- -- fst (snd (R→L→R a b g F i x)) e = R→L→R₁ x a e b g F i
-- -- snd (snd (R→L→R a b g F i x)) e = Lol x a e b g F i
-- --   where
-- --   Lol : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (x : A) (a : A) (e : x ≡ a) (b : B) (g : Ω (A , a) →∙ Ω (B , b))
-- --     → (F : RTyp a b g)
-- --     → PathP (λ i → ((λ p →
-- --           (λ i₁ → R→L→R₁ x a e b g F i (~ i₁)) ∙ R→L→R₁ x a (e ∙ p) b g F i)
-- --            ,
-- --            (λ i₁ →
-- --               (λ i₂ → R→L→R₁ x a e b g F i (~ i₂)) ∙
-- --               R→L→R₁ x a (rUnit e (~ i₁)) b g F i)
-- --            ∙ lCancel (R→L→R₁ x a e b g F i))
-- --           ≡ g) (snd (snd (L→R a b g (R→L a b g F) x)) e) (snd (snd (F x)) e)
-- --   Lol x = J> λ b g F → →∙HomogeneousSquare (isHomogeneousPath _ _) _ _ _ _ (((λ _ → cong fst
-- --       (J-lemL→R x x refl b (λ x₂ → fst (F x₂)) (F x .snd .fst (λ _ → x))
-- --        g
-- --        (R→L x b g F .snd .snd)))
-- --        ∙ (cong (cong fst) (J-lemL→R-refl x b (λ x₂ → fst (F x₂)) (F x .snd .fst (λ _ → x)) g (R→L x b g F .snd .snd)))
-- --        ∙ (λ _ → funExt (λ p → cong₂ _∙_ (cong sym (sym (lUnit (F x .snd .fst (λ _ → x)))))
-- --                                          (cong (_∙ (F x .snd .fst (λ _ → x))) (cong (cong (fst ∘ F)) (sym (lUnit p))))
-- --                       ∙ {!sym (cong (sym (F x .snd .fst (λ _ → x)) ∙_)
-- --                           (R→L-fst x b g F p))!}))
-- --        ∙ {!!})
-- --        ◁ {!!})

-- -- -- l' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω (A , a) →∙ Ω (B , b))
-- -- --   → (F : (((x : A) → Σ[ y ∈ B ] (Σ[ h ∈ ((x ≡ a) → y ≡ b) ]
-- -- --                       ((e : x ≡ a) → ((λ p → sym (h e) ∙ h (e ∙ p))
-- -- --                                      , cong (sym (h e) ∙_) (cong h (sym (rUnit e)))
-- -- --                                           ∙ lCancel (h e))
-- -- --                                      ≡ g)))))
-- -- --   → (p : a ≡ a)
-- -- --   → (λ i₁ → F a .snd .fst (λ _ → a) (~ i₁)) ∙
-- -- --        (λ i₁ → F (p i₁) .fst) ∙ F a .snd .fst (λ _ → a)
-- -- --      ≡ fst g p
-- -- -- l' a b g F p = cong (sym (fst (F a .snd) (λ _ → a)) ∙_)
-- -- --          ((λ i → (λ j → fst (F (p (j ∧ ~ i)))) ∙ F (p (~ i)) .snd .fst λ j → p (~ i ∨ j))
-- -- --         ∙ sym (lUnit (fst (F a .snd) p))
-- -- --         ∙ cong (fst (F a .snd)) (lUnit p))
-- -- --   ∙ funExt⁻ (cong fst (F a .snd .snd refl)) p

-- -- -- L2 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) (g : Ω (A , a) →∙ Ω (B , b))
-- -- --   → (((x : A) → Σ[ y ∈ B ] (Σ[ h ∈ ((x ≡ a) → y ≡ b) ]
-- -- --                       ((e : x ≡ a) → ((λ p → sym (h e) ∙ h (e ∙ p))
-- -- --                                      , cong (sym (h e) ∙_) (cong h (sym (rUnit e)))
-- -- --                                           ∙ lCancel (h e))
-- -- --                                      ≡ g))))
-- -- --   → (Σ[ f ∈ (A → B) ] (Σ[ p ∈ f a ≡ b ] Ω→' (f , p) ≡ g))
-- -- -- fst (L2 a b g F) x = F x .fst
-- -- -- fst (snd (L2 a b g F)) = F a .snd .fst refl
-- -- -- fst (snd (snd (L2 a b g F)) i) p = l' a b g F p i
-- -- -- snd (snd (snd (L2 a b g F)) i) j k = {!!}

-- -- -- asd : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B)
-- -- --   → (g : Ω (A , a) →∙ Ω (B , b))
-- -- --   → Iso (Σ[ f ∈ (A → B) ] (Σ[ p ∈ f a ≡ b ] Ω→' (f , p) ≡ g))
-- -- --          ((x : A) → Σ[ y ∈ B ] (Σ[ h ∈ ((x ≡ a) → y ≡ b) ]
-- -- --                       ((e : x ≡ a) → ((λ p → sym (h e) ∙ h (e ∙ p))
-- -- --                                      , cong (sym (h e) ∙_) (cong h (sym (rUnit e)))
-- -- --                                           ∙ lCancel (h e))
-- -- --                                      ≡ g)))
-- -- -- fun (asd a b g) F x = asd' a b (fst F) (fst (snd F)) g (snd F .snd) x
-- -- -- inv (asd a b g) x = L2 a b g x 
-- -- -- rightInv (asd {A = A} {B = B} a b g) F =
-- -- --   funExt λ x →
-- -- --     ΣPathP (refl ,
-- -- --       (ΣPathP ((funExt (λ q → (λ i → (λ j → F (q (j ∧ ~ i)) .fst)
-- -- --                                     ∙ F (q (~ i)) .snd .fst λ j → q (j ∨ ~ i))
-- -- --                             ∙ sym (lUnit (fst (snd (F x)) q))))
-- -- --                             , help λ q → →∙HomogeneousSquare (isHomogeneousPath _ _) _ _ _ _
-- -- --                               (L1 x a q g F))))
-- -- --   where
-- -- --   L1 : (x : A) (a : A) (q : x ≡ a) (g : Ω (A , a) →∙ Ω (B , b))
-- -- --     → (F : (x₁ : A) →
-- -- --            Σ-syntax B
-- -- --            (λ y →
-- -- --               Σ-syntax (x₁ ≡ a → y ≡ b)
-- -- --               (λ h →
-- -- --                  (e : x₁ ≡ a) →
-- -- --                  ((λ p → sym (h e) ∙ h (e ∙ p)) ,
-- -- --                   cong (_∙_ (sym (h e))) (cong h (sym (rUnit e))) ∙ lCancel (h e))
-- -- --                  ≡ g)))
-- -- --     → Square (funExt (λ l → r' a b (fst ∘ F)
-- -- --                                      (snd (F a) .fst refl)
-- -- --                                      g
-- -- --                                      (snd (inv (asd a b g) F) .snd)
-- -- --                                      x q l))
-- -- --           (cong fst (snd (snd (F x)) q))
-- -- --               (funExt (λ p → cong₂ _∙_ (cong sym ((λ i → (λ j → F (q (j ∧ ~ i)) .fst)
-- -- --                                     ∙ F (q (~ i)) .snd .fst λ j → q (j ∨ ~ i))
-- -- --                                                   ∙ sym (lUnit (fst (snd (F x)) q))))
-- -- --                                                   ((λ i → (λ j → F ((q ∙ p) (j ∧ ~ i)) .fst)
-- -- --                                     ∙ F ((q ∙ p) (~ i)) .snd .fst λ j → (q ∙ p) (j ∨ ~ i))
-- -- --                                           ∙ sym (lUnit (fst (snd (F x)) (q ∙ p))))))
-- -- --               refl
-- -- --   L1 x = J> λ g F → λ i j l k
-- -- --     → hcomp (λ r → λ {(i = i0) → {!!}
-- -- --                    ; (i = i1) → fst (snd (snd (F x)) refl j) l k
-- -- --                    ; (j = i0) → ({!!} i
-- -- --                                 ∙ {!!}) k
-- -- --                    ; (j = i1) → l' x b g F l (i ∨ r) k
-- -- --                    ; (k = i0) → b
-- -- --                    ; (k = i1) → b})
-- -- --        {!!}

-- -- -- {-
-- -- --     hcomp (λ r → λ {(i = i0) → compPath-filler ((λ k → sym (compPath-filler' (cong (fst ∘ F) q) ((snd (F a) .fst refl)) (~ k))
-- -- --                                ∙ (λ i₁ → (fst ∘ F) ((compPath-filler' q l (~ k) i₁))) ∙ (snd (F a) .fst refl)))
-- -- --                                  (l' a b g F l) r j k
-- -- --                    ; (i = i1) → fst (snd (snd (F x)) q j) l k
-- -- --                    ; (j = i0) → FF i l k
-- -- --                    ; (j = i1) → l' a b g F l (i ∨ r) k
-- -- --                    ; (k = i0) → b
-- -- --                    ; (k = i1) → b})
-- -- --        (hcomp (λ r → λ {(i = i0) → {!l' a b g F l!}
-- -- --                    ; (i = i1) → {!sym (compPath-filler' (cong (fst ∘ F) q) ((snd (F a) .fst refl)) (~ k))!}
-- -- --                    ; (j = i0) → {!F!}
-- -- --                    ; (j = i1) → {!!}
-- -- --                    ; (k = i0) → {!!}
-- -- --                    ; (k = i1) → {!!}})
-- -- --               {!!})
-- -- --     where
-- -- --     FF : _ ≡ _
-- -- --     FF = (funExt (λ p → cong₂ _∙_ (cong sym ((λ i → (λ j → F (q (j ∧ ~ i)) .fst)
-- -- --                                     ∙ F (q (~ i)) .snd .fst λ j → q (j ∨ ~ i))
-- -- --                                                   ∙ sym (lUnit (fst (snd (F x)) q))))
-- -- --                                                   ((λ i → (λ j → F ((q ∙ p) (j ∧ ~ i)) .fst)
-- -- --                                     ∙ F ((q ∙ p) (~ i)) .snd .fst λ j → (q ∙ p) (j ∨ ~ i))
-- -- --                                           ∙ sym (lUnit (fst (snd (F x)) (q ∙ p))))))
-- -- -- -}
-- -- --   help : ∀ {ℓ ℓ'} {A : Type ℓ} {B B' : A → Type ℓ'} {p : (x : A) → B x ≡ B' x}
-- -- --     → {f : (x : A) → B x} {g : (x : A) → B' x}
-- -- --     → ((x : A) → PathP (λ i → p x i) (f x) (g x)) → PathP (λ i → (x : A) → p x i) f g 
-- -- --   help p i x = p x i
-- -- -- leftInv (asd {A = A} {B = B} a b g) =
-- -- --   uncurry λ f → uncurry λ p q → J (λ b x → (g : Ω (A , a) →∙ Ω (B , b)) → (y : Ω→' (f , x) ≡ g) →
-- -- --       L2 a b g (λ x₁ → asd' a b f x g y x₁) ≡ (f , x , y))
-- -- --         (J> ΣPathP (refl , (ΣPathP ({!!} , {!!}))))
-- -- --         p g q

-- -- -- {-
-- -- -- asd : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B)
-- -- --   → (g : Ω (A , a) →∙ Ω (B , b))
-- -- --   → Iso (Σ[ f ∈ (A → B) ] (Σ[ p ∈ f a ≡ b ] Ω→ (f , p) ≡ g))
-- -- --          ((x : A) → Σ[ y ∈ B ] (Σ[ h ∈ ((x ≡ a) → y ≡ b) ]
-- -- --                       ((e : x ≡ a) → ((λ p → sym (h e) ∙ h (e ∙ p))
-- -- --                                      , cong (sym (h e) ∙_) (cong h (sym (rUnit e)))
-- -- --                                           ∙ lCancel (h e))
-- -- --                                      ≡ g)))
-- -- -- fun (asd a b g) (f , f₀ , P) x = (f x)
-- -- --                              , ((λ p → cong f p ∙ f₀)
-- -- --                              , λ e → (ΣPathP ({!!} , {!!}) ∙ P))
-- -- -- inv (asd a b g) F = (λ x → F x .fst)
-- -- --                   , (F a .snd .fst refl)
-- -- --                   , ΣPathP ((funExt (λ p → ((λ j → ((λ i → F a .snd .fst refl (~ i)) ∙∙
-- -- --        (λ i → F (p (i ∧ ~ j)) .fst) ∙∙ F (p (~ j)) .snd .fst λ i → p (~ j ∨ i)))
-- -- --        ∙ {!!}
-- -- --        ∙ {!!})
-- -- --        ∙ funExt⁻ (cong fst (F a .snd .snd refl)) p))
-- -- --        , {!!}) -- ΣPathP ((funExt (λ p → {!!})) , {!!}) ∙ F a .snd .snd refl -- (ΣPathP ((funExt (λ p → (λ i → {!!}) ∙ {!!})) , {!!}))
-- -- -- rightInv (asd a b g) F =
-- -- --   funExt λ x → ΣPathP
-- -- --     (refl
-- -- --     , ΣPathP ((funExt (λ q → (λ j → (λ i → F (q (i ∧ ~ j)) .fst) ∙ F (q (~ j)) .snd .fst λ i → q (~ j ∨ i)) ∙ sym (lUnit _)))
-- -- --     , toPathP {!!}))
-- -- -- leftInv (asd a b g)  (f , f₀ , P) = {!!}
-- -- -- -}


-- -- -- -- -- private
-- -- -- -- --   fold : ∀ {i j} {A : Type i} {B : Type j} {a : A} {x : A} 
-- -- -- -- --     → (x ≡ a)
-- -- -- -- --     → {b y : B}
-- -- -- -- --     → (h : x ≡ a → y ≡ b)
-- -- -- -- --     → fst (Ω (A , a)) → fst (Ω (B , b))
-- -- -- -- --   fold α h w =
-- -- -- -- --     sym (h α) ∙ h (α ∙ w)

-- -- -- -- -- module _ {ℓ ℓ'} {A' : Pointed ℓ} {B' : Pointed ℓ'} (g' : Ω A' →∙ Ω B') where
-- -- -- -- --   private
-- -- -- -- --     A = fst A'
-- -- -- -- --     B = fst B'
-- -- -- -- --     a = snd A'
-- -- -- -- --     b₀ = snd B'
-- -- -- -- --     ΩA = fst (Ω A')
-- -- -- -- --     ΩB = fst (Ω B')
-- -- -- -- --     g : ΩA → ΩB
-- -- -- -- --     g = fst g'

-- -- -- -- --   module _ (f : A → B) where
-- -- -- -- --     D : {b : B} (g : ΩA → fst (Ω (B , b))) → Type _
-- -- -- -- --     D {b = b} g =
-- -- -- -- --          (x : A)
-- -- -- -- --       → Σ[ h ∈ (x ≡ a → f x ≡ b) ]
-- -- -- -- --            ((α : x ≡ a) → fold α h ≡ g)

-- -- -- -- --     push' : {b : B} {{f₀ : f a ≡ b}} {x : A} → x ≡ a → f x ≡ b
-- -- -- -- --     push' {{f₀}} α = cong f α ∙ f₀

-- -- -- -- --     fold-is-Ωf : {b : B} {{f₀ : f a ≡ b}}
-- -- -- -- --       {x : A} (α : x ≡ a)
-- -- -- -- --       → fold α push' ≡ fst (Ω→ (f , f₀))
-- -- -- -- --     fold-is-Ωf {{f₀}} {x = x} α =
-- -- -- -- --       J (λ x α → fold (sym α) push' ≡ fst (Ω→ (f , f₀)))
-- -- -- -- --         (funExt λ p → (λ i → sym (push' {{f₀}} refl) ∙ push' (lUnit p (~ i)))
-- -- -- -- --                     ∙∙ cong (_∙ (cong f p ∙ f₀)) (cong sym (sym (lUnit f₀)))
-- -- -- -- --                     ∙∙ sym (doubleCompPath≡compPath (sym f₀) (cong f p) f₀))
-- -- -- -- --         (sym α)

-- -- -- -- --     fiber-lemma : {b : B} {{f₀ : f a ≡ b}} → D (fst (Ω→ (f , f₀)))
-- -- -- -- --     fiber-lemma x = push' , fold-is-Ωf


-- -- -- -- --   module recover (f : A → B)(H : D f g) where
-- -- -- -- --     f₀ : f a ≡ b₀
-- -- -- -- --     f₀ = fst (H a) refl

-- -- -- -- --     ∙f : A' →∙ B'
-- -- -- -- --     ∙f = f , f₀

-- -- -- -- --     Ωf : ΩA → ΩB
-- -- -- -- --     Ωf = fst (Ω→ ∙f)

-- -- -- -- --     push-is-h : {x : A} (α : x ≡ a)
-- -- -- -- --       → push' f {{f₀}} α ≡ fst (H x) α
-- -- -- -- --     push-is-h {x = x} α =
-- -- -- -- --       (λ i → cong f (λ j → α (~ i ∧ j)) ∙ fst (H (α (~ i))) λ j → α (~ i ∨ j))
-- -- -- -- --       ∙ sym (lUnit _)

-- -- -- -- --     is-fiber-∙f : Ω→ ∙f ≡ g'
-- -- -- -- --     is-fiber-∙f =
-- -- -- -- --       ΣPathP ((sym (fold-is-Ωf f {{f₀}} refl)
-- -- -- -- --              ∙∙ cong (fold refl) (funExt push-is-h)
-- -- -- -- --              ∙∙ snd (H a) refl)
-- -- -- -- --             , {!snd ∙f!})

-- -- -- -- --   module asd2 (f : A → B) where
-- -- -- -- --     F : Type _
-- -- -- -- --     F = Σ[ f₀ ∈ (f a ≡ b₀) ]
-- -- -- -- --          Ω→ (f , f₀) ≡ g'

-- -- -- -- --     to : F → D f g
-- -- -- -- --     fst (to ϕ x) = push' f {{fst ϕ}}
-- -- -- -- --     snd (to ϕ x) α = fold-is-Ωf f {{fst ϕ}} α ∙ cong fst (snd ϕ)

-- -- -- -- --     from : D f g → F
-- -- -- -- --     from ψ = (recover.f₀ f ψ) , (recover.is-fiber-∙f f ψ)

-- -- -- -- --     to-from : (ψ : D f g) → to (from ψ) ≡ ψ
-- -- -- -- --     to-from ψ =
-- -- -- -- --       funExt λ x → ΣPathP ((funExt (recover.push-is-h f ψ))
-- -- -- -- --       , toPathP (funExt {!snd (ψ x) ?!}))


-- -- -- -- module asd0 {ℓ ℓ'} {X : Pointed ℓ} {Y : Pointed ℓ'} where
-- -- -- --   private
-- -- -- --     X' = fst X
-- -- -- --     Y' = fst Y
-- -- -- --     x₀ = snd X
-- -- -- --     y₀ = snd Y
-- -- -- --   F : {x' : X'} {y' : Y'} (h : x' ≡ x₀ → y' ≡ y₀) (e : x' ≡ x₀)
-- -- -- --     → Ω X →∙ Ω Y
-- -- -- --   fst (F {x' = x'} {y' = y'} h e) p = sym (h e) ∙ h (e ∙ p)
-- -- -- --   snd (F {x' = x'} {y' = y'} h e) =
-- -- -- --     cong (sym (h e) ∙_) (cong h (sym (rUnit e))) ∙ lCancel (h e)


-- -- -- -- module asd {ℓ ℓ'} {X : Pointed ℓ} {Y : Pointed ℓ'} (g : Ω X →∙ Ω Y) where
-- -- -- --   private
-- -- -- --     X' = fst X
-- -- -- --     Y' = fst Y
-- -- -- --     x₀ = snd X
-- -- -- --     y₀ = snd Y

-- -- -- --   open asd0 {X = X} {Y = Y}

-- -- -- --   f₁ : {x' : X'} (e : x' ≡ x₀)
-- -- -- --     → Ω X →∙ ((x' ≡ x₀) , e)
-- -- -- --   fst (f₁ e) p = e ∙ p
-- -- -- --   snd (f₁ e) = sym (rUnit e)

-- -- -- --   f₂ : {x' : X'} {y' : Y'} (e : x' ≡ x₀) (h : x' ≡ x₀ → y' ≡ y₀)
-- -- -- --     → ((y' ≡ y₀) , h e) →∙ Ω Y
-- -- -- --   fst (f₂ e h) p = sym (h e) ∙ p
-- -- -- --   snd (f₂ e h) = lCancel (h e)


-- -- -- --   C : X' → Y' → Type _
-- -- -- --   C x' y' = (h : x' ≡ x₀ → y' ≡ y₀) (e : x' ≡ x₀)
-- -- -- --          → F h e ≡ g

-- -- -- --   F' : {y' : Y'} (h : x₀ ≡ x₀ → y' ≡ y₀)
-- -- -- --     → F h refl ≡ ((λ p → sym (h refl) ∙ h p) , lCancel (h refl))
-- -- -- --   F' h = →∙Homogeneous≡ (isHomogeneousPath _ _)
-- -- -- --            (funExt λ p → cong (sym (h refl) ∙_) (cong h (sym (lUnit _))))

-- -- -- --   is- : (f : X' → Y')
-- -- -- --     → Iso ((x' : X') → C x' (f x'))
-- -- -- --        (Σ[ h ∈ ((x : X') → x ≡ x₀ → f x ≡ y₀) ] F (h x₀) refl ≡ g)
-- -- -- --   is- f =
-- -- -- --     compIso (codomainIsoDep λ x → flipIso)
-- -- -- --             {!(f : (x : X') (a ≡ x₀) (r : x₀ ≡ x₀) (r ≡ refl) → f a ≡ y₀) → f x b !}
-- -- -- --   {-
-- -- -- --     compIso
-- -- -- --       ((compIso (compIso
-- -- -- --         (codomainIsoDep λ x → flipIso) (invIso curryIso))
-- -- -- --           isContrSinglIso))
-- -- -- --         {!!}
-- -- -- --         -}

-- -- -- -- l : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} (f : fst A → B) (x : fst A)
-- -- -- --   → (e : snd A ≡ x)
-- -- -- --   → (p : snd A ≡ x → f x ≡ f (pt A))
-- -- -- --   → asd0.F {X = A} {Y = (B , f (pt A))} (p ∘ sym) (sym e)
-- -- -- --   ≡ (cong f , refl)
-- -- -- -- l f x e p = ΣPathP (funExt {!!} , {!!})

-- -- -- -- module asd3 {ℓ ℓ'} {X : Pointed ℓ} {Y : Pointed ℓ'} (g : Ω X →∙ Ω Y) where
-- -- -- --   private
-- -- -- --     X' = fst X
-- -- -- --     Y' = Y
-- -- -- --     x₀ = snd X
-- -- -- --     open asd0 {X = X} {Y = Y , f (pt X)}
-- -- -- --     open asd g

-- -- -- --   is₁ : Iso (Σ[ f ∈ (X →∙ Y) ] ((x' : X') → C x' (fst f x'))) (fiber Ω→ g)
-- -- -- --   fun (is₁) h = (f , {!!}) , {!!}
-- -- -- --   inv (is₁) (h , q) x p e = {!!}
-- -- -- --     where
-- -- -- --     abr : {!!}
-- -- -- --     abr = {!!}

-- -- -- --   rightInv (is₁) = {!!}
-- -- -- --   leftInv (is₁) = {!!}



-- -- -- --   {-
-- -- -- --     compIso
-- -- -- --       (compIso (compIso
-- -- -- --         (codomainIsoDep λ x → flipIso)
-- -- -- --         (compIso (compIso
-- -- -- --           (compIso (invIso curryIso) isContrSinglIso)
-- -- -- --           (compIso l
-- -- -- --             (Σ-cong-iso-fst
-- -- -- --                        (compIso idIso
-- -- -- --                          (invIso isContrSinglIso)))))
-- -- -- --                  (idIso {A = (Σ ((a : Σ X' (λ z → z ≡ x₀)) → f (fst a) ≡ y₀)
-- -- -- --        ((λ a → F (λ q → a (_ , q)) refl ≡ g)))})))
-- -- -- --                (Σ-cong-iso-fst curryIso))
-- -- -- --       (Σ-cong-iso-snd
-- -- -- --                      λ h → compIso
-- -- -- --                        (invIso isContrSinglIso) curryIso)
-- -- -- --     where
-- -- -- --     l : Iso ((a : x₀ ≡ x₀ → f x₀ ≡ y₀) → F a refl ≡ g)
-- -- -- --            (Σ[ q ∈ (f x₀ ≡ y₀) ] F (λ a → subst (λ z → f z ≡ y₀) (sym a) q) refl ≡ g) 
-- -- -- --     fun l h = {!h!} , {!!}
-- -- -- --     inv l = {!!}
-- -- -- --     rightInv l = {!!}
-- -- -- --     leftInv l = {!!}
-- -- -- -- -}  {-
-- -- -- --     compIso (codomainIsoDep λ x → flipIso)
-- -- -- --       (compIso (invIso curryIso)
-- -- -- --                (compIso
-- -- -- --                  isContrSinglIso
-- -- -- --                  (compIso
-- -- -- --                    (compIso
-- -- -- --                        (compIso (pathToIso (λ i → (a : x₀ ≡ x₀ → f x₀ ≡ y₀) → F' a i ≡ g))
-- -- -- --                          (compIso {!!}
-- -- -- --                            (pathToIso λ i → Σ ((a : Σ X' (λ z → z ≡ x₀)) → f (fst a) ≡ y₀)
-- -- -- --                                                 ((λ a → F' (λ p → a (_ , p)) (~ i) ≡ g)))))
-- -- -- --                      (Σ-cong-iso-fst
-- -- -- --                        (curryIso)))
-- -- -- --                    (Σ-cong-iso-snd
-- -- -- --                      λ h → compIso
-- -- -- --                        (invIso isContrSinglIso) curryIso))))
-- -- -- -- -}
-- -- -- --      where
-- -- -- --      L : Iso ((a : x₀ ≡ x₀ → f x₀ ≡ y₀) → F a refl ≡ g)
-- -- -- --       (Σ ((a : Σ X' (λ z → z ≡ x₀)) → f (fst a) ≡ y₀)
-- -- -- --        ((λ a → F (λ p → a (_ , p)) refl ≡ g)))
-- -- -- --      fun L h = (uncurry (λ x p → cong f p ∙ {!!} ∙ {!!}))
-- -- -- --              , ΣPathP ({!!} , {!!})
-- -- -- --      inv L = {!!}
-- -- -- --      rightInv L = {!!}
-- -- -- --      leftInv L = {!!}


-- -- -- -- {-

-- -- -- -- Kₙ → Kₘ
-- -- -- --      ΩKₘ₊₁

-- -- -- -- ΣKₙ → Kₘ₊₁
-- -- -- --  |
-- -- -- --  |
-- -- -- -- ΣKₙ₊₁

-- -- -- -- -}
