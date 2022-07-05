{-# OPTIONS --safe #-}
module Cubical.HITs.SmashProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Pushout.Base
open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.HITs.Wedge
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

data Smash {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') : Type (ℓ-max ℓ ℓ') where
  basel : Smash A B
  baser : Smash A B
  proj  : (x : typ A) → (y : typ B) → Smash A B
  gluel : (a : typ A) → proj a (pt B) ≡ basel
  gluer : (b : typ B) → proj (pt A) b ≡ baser

private
  variable
    ℓ ℓ' : Level
    A B C D : Pointed ℓ

Smash-map : (f : A →∙ C) (g : B →∙ D) → Smash A B → Smash C D
Smash-map f g basel = basel
Smash-map f g baser = baser
Smash-map (f , fpt) (g , gpt) (proj x y) = proj (f x) (g y)
Smash-map (f , fpt) (g , gpt) (gluel a i) = ((λ j → proj (f a) (gpt j)) ∙ gluel (f a)) i
Smash-map (f , fpt) (g , gpt) (gluer b i) = ((λ j → proj (fpt j) (g b)) ∙ gluer (g b)) i

-- Commutativity
comm : Smash A B → Smash B A
comm basel       = baser
comm baser       = basel
comm (proj x y)  = proj y x
comm (gluel a i) = gluer a i
comm (gluer b i) = gluel b i

commK : (x : Smash A B) → comm (comm x) ≡ x
commK basel       = refl
commK baser       = refl
commK (proj x y)  = refl
commK (gluel a x) = refl
commK (gluer b x) = refl

-- WIP below

SmashPt : (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
SmashPt A B = (Smash A B , basel)

SmashPtProj : (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
SmashPtProj A B = Smash A B , (proj (snd A) (snd B))

--- Alternative definition

i∧ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → A ⋁ B → (typ A) × (typ B)
i∧ {A = A , ptA} {B = B , ptB} (inl x) = x , ptB
i∧ {A = A , ptA} {B = B , ptB} (inr x) = ptA , x
i∧ {A = A , ptA} {B = B , ptB} (push tt i) = ptA , ptB

_⋀_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Type (ℓ-max ℓ ℓ')
A ⋀ B = Pushout {A = (A ⋁ B)} (λ _ → tt) i∧

_⋀∙_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
A ⋀∙ B = Pushout {A = (A ⋁ B)} (λ _ → tt) i∧ , (inl tt)


_⋀→_ : (f : A →∙ C) (g : B →∙ D)  → A ⋀ B → C ⋀ D
(f ⋀→ g) (inl tt) = inl tt
((f , fpt) ⋀→ (g , gpt)) (inr (x , x₁)) = inr (f x , g x₁)
_⋀→_ {B = B} {D = D} (f ,  fpt) (b , gpt)  (push (inl x) i) = (push (inl (f x)) ∙ (λ i → inr (f x , gpt (~ i)))) i
_⋀→_ (f , fpt) (g , gpt) (push (inr x) i) = (push (inr (g x)) ∙ (λ i → inr (fpt (~ i) , g x))) i
_⋀→_ {A = A} {C = C} {B = B} {D = D} (f , fpt) (g , gpt) (push (push tt j) i) =
  hcomp (λ k → λ { (i = i0) → inl tt
                  ; (i = i1) → inr (fpt (~ k) , gpt (~ k))
                  ; (j = i0) → compPath-filler (push (inl (fpt (~ k))))
                                                ((λ i → inr (fpt (~ k) , gpt (~ i)))) k i
                  ; (j = i1) → compPath-filler (push (inr (gpt (~ k))))
                                                ((λ i → inr (fpt (~ i) , gpt (~ k)))) k i})
        (push (push tt j) i)

⋀→Smash : A ⋀ B → Smash A B
⋀→Smash (inl x) = basel
⋀→Smash (inr (x , x₁)) = proj x x₁
⋀→Smash (push (inl x) i) = gluel x (~ i)
⋀→Smash {A = A} {B = B} (push (inr x) i) = (sym (gluel (snd A)) ∙∙ gluer (snd B) ∙∙ sym (gluer x)) i
⋀→Smash {A = A} {B = B} (push (push a j) i) =
  hcomp (λ k → λ { (i = i0) → gluel (snd A) (k ∨ ~ j)
                  ; (i = i1) → gluer (snd B) (~ k ∧ j)
                  ; (j = i0) → gluel (snd A) (~ i)})
        (invSides-filler (gluel (snd A)) (gluer (snd B)) j (~ i))

Smash→⋀ : Smash A B → A ⋀ B
Smash→⋀ basel = inl tt
Smash→⋀ baser = inl tt
Smash→⋀ (proj x y) = inr (x , y)
Smash→⋀ (gluel a i) = push (inl a) (~ i)
Smash→⋀ (gluer b i) = push (inr b) (~ i)

{- associativity maps for smash produts. Proof pretty much direcly translated from https://github.com/ecavallo/redtt/blob/master/library/pointed/smash.red -}
private
  pivotl : (b b' : typ B)
         → Path (Smash A B) (proj (snd A) b) (proj (snd A) b')
  pivotl b b' i = (gluer b ∙ sym (gluer b')) i

  pivotr : (a a' : typ A)
         → Path (Smash A B) (proj a (snd B)) (proj a' (snd B))
  pivotr a a' i = (gluel a ∙ sym (gluel a')) i

  pivotlrId : {A : Pointed ℓ} {B : Pointed ℓ'} → _
  pivotlrId {A = A} {B = B} = rCancel (gluer (snd B)) ∙ sym (rCancel (gluel (snd A)))

  rearrange-proj : (c : fst C)
                → (Smash A B) → Smash (SmashPtProj C B) A
  rearrange-proj c basel = baser
  rearrange-proj c baser = basel
  rearrange-proj c (proj x y) = proj (proj c y) x
  rearrange-proj {C = C} c (gluel a i) =
    hcomp (λ k → λ { (i = i0) → proj (pivotr (snd C) c k) a
                    ; (i = i1) → baser})
          (gluer a i)
  rearrange-proj c (gluer b i) = gluel (proj c b) i

  rearrange-gluel : (s : Smash A B)
                 → Path (Smash (SmashPtProj C B) A) basel (rearrange-proj (snd C) s)
  rearrange-gluel {A = A} {B = B} {C = C} basel = sym (gluel (proj (snd C) (snd B))) ∙
                                                  gluer (snd A)
  rearrange-gluel baser = refl
  rearrange-gluel {A = A} {B = B} {C = C} (proj a b) i =
    hcomp (λ k → λ { (i = i0) → (sym (gluel (proj (snd C) (snd B))) ∙
                                                  gluer (snd A)) (~ k)
                    ; (i = i1) → proj (pivotl (snd B) b k) a})
          (gluer a (~ i))
  rearrange-gluel {A = A} {B = B} {C = C} (gluel a i) j =
    hcomp (λ k → λ { (i = i1) → ((λ i₁ → gluel (proj (snd C) (snd B)) (~ i₁)) ∙
                                  gluer (snd A)) (~ k ∨ j)
                    ; (j = i0) → ((λ i₁ → gluel (proj (snd C) (snd B)) (~ i₁)) ∙
                                  gluer (snd A)) (~ k)
                    ; (j = i1) → top-filler i k})
          (gluer a (i ∨ ~ j))
    where
      top-filler : I → I → Smash (SmashPtProj C B) A
      top-filler i j =
        hcomp (λ k → λ { (i = i0) → side-filler k j
                        ; (i = i1) → gluer a (j ∨ k)
                        ; (j = i0) → gluer a (i ∧ k)})
              (gluer a (i ∧ j))
       where
       side-filler : I → I → Smash (SmashPtProj C B) A
       side-filler i j =
         hcomp (λ k → λ { (i = i0) → proj (proj (snd C) (snd B)) a
                        ; (i = i1) → proj ((rCancel (gluel (snd C)) ∙ sym (rCancel (gluer (snd B)))) k j) a
                        ; (j = i0) → proj (proj (snd C) (snd B)) a
                        ; (j = i1) → (proj ((gluel (snd C) ∙ sym (gluel (snd C))) i) a)})
                (proj ((gluel (snd C) ∙ sym (gluel (snd C))) (j ∧ i)) a)
  rearrange-gluel {A = A} {B = B} {C = C} (gluer b i) j =
    hcomp (λ k → λ {(i = i1) → ((sym (gluel (proj (snd C) (snd B)))) ∙ gluer (snd A)) (~ k)
                   ; (j = i0) → ((sym (gluel (proj (snd C) (snd B)))) ∙ gluer (snd A)) (~ k)
                   ; (j = i1) → top-filler1 i k})
          (gluer (snd A) (i ∨ (~ j)))
    where
    top-filler1 : I → I → Smash (SmashPtProj C B) A
    top-filler1 i j =
      hcomp (λ k → λ { (i = i0) → congFunct (λ x → proj x (snd A)) (gluer (snd B)) (sym (gluer b)) (~ k) j
                   ; (i = i1) → (sym (gluel (proj (snd C) (snd B))) ∙ gluer (snd A)) (~ j)
                   ; (j = i0) → gluer (snd A) i
                   ; (j = i1) → gluel (proj (snd C) b) i})
          (top-filler2 i j)
      where
      top-filler2 : I → I → Smash (SmashPtProj C B) A
      top-filler2 i j =
        hcomp (λ k → λ { (j = i0) → gluer (snd A) (i ∧ k)
                          ; (j = i1) → gluel (gluer b (~ k)) i})
                (hcomp (λ k → λ { (j = i0) → gluel (gluer (snd B) i0) (~ k ∧ (~ i))
                                 ; (j = i1) → gluel (baser) (~ k ∨ i)
                                 ; (i = i0) → gluel (gluer (snd B) j) (~ k)
                                 ; (i = i1) → gluel (proj (snd C) (snd B)) j })
                       (gluel (proj (snd C) (snd B)) (j ∨ (~ i))))

  rearrange : Smash (SmashPtProj A B) C → Smash (SmashPtProj C B) A
  rearrange basel = basel
  rearrange baser = baser
  rearrange (proj x y) = rearrange-proj y x
  rearrange (gluel a i) = rearrange-gluel a (~ i)
  rearrange {A = A} {B = B} {C = C} (gluer b i) = ((λ j → proj (pivotr b (snd C) j) (snd A)) ∙
                                                  gluer (snd A)) i

  ⋀∙→SmashPtProj : (A ⋀∙ B) →∙ SmashPtProj A B
  ⋀∙→SmashPtProj {A = A} {B = B} = fun , refl
    where
    fun : (A ⋀ B) → Smash A B
    fun (inl x) = proj (snd A) (snd B)
    fun (inr (x , x₁)) = proj x x₁
    fun (push (inl x) i) = pivotr (snd A) x i
    fun (push (inr x) i) = pivotl (snd B) x i
    fun (push (push a j) i) = pivotlrId (~ j) i

  SmashPtProj→⋀∙ : (SmashPtProj A B) →∙ (A ⋀∙ B)
  SmashPtProj→⋀∙ {A = A} {B = B} = Smash→⋀ , sym (push (inr (snd B)))

SmashAssociate : Smash (SmashPtProj A B) C → Smash A (SmashPtProj B C)
SmashAssociate = comm ∘ Smash-map  (comm , refl) (idfun∙ _) ∘ rearrange

SmashAssociate⁻ : Smash A (SmashPtProj B C) → Smash (SmashPtProj A B) C
SmashAssociate⁻ = rearrange ∘ comm ∘ Smash-map (idfun∙ _) (comm , refl)

⋀-associate : (A ⋀∙ B) ⋀ C → A ⋀ (B ⋀∙ C)
⋀-associate = (idfun∙ _ ⋀→ SmashPtProj→⋀∙) ∘ Smash→⋀ ∘ SmashAssociate ∘ ⋀→Smash ∘ (⋀∙→SmashPtProj ⋀→ idfun∙ _)

⋀-associate⁻ : A ⋀ (B ⋀∙ C) → (A ⋀∙ B) ⋀ C
⋀-associate⁻ = (SmashPtProj→⋀∙ ⋀→ idfun∙ _) ∘ Smash→⋀ ∘ SmashAssociate⁻ ∘ ⋀→Smash ∘ (idfun∙ _ ⋀→ ⋀∙→SmashPtProj)


-- open import Cubical.Data.Sigma renaming (_×_ to _×'_)
-- →Point : ((A ⋀∙ B) →∙ C) → A →∙ (B →∙ C ∙)
-- fst (fst (→Point f) x) y = fst f (inr (x , y))
-- snd (fst (→Point f) x) = cong (fst f) (sym (push (inl x))) ∙ snd f
-- snd (→Point {B = B} f) =
--   ΣPathP ((funExt (λ x → cong (fst f) (sym (push (inr x))) ∙ snd f))
--         , ((λ i → cong (fst f) (sym (push (push tt i))) ∙ snd f)
--         ◁ λ i j → (cong (fst f) (sym (push (inr (pt B)))) ∙ snd f) (i ∨ j)))

-- →Point∙ : ((A ⋀∙ B) →∙ C ∙) →∙ (A →∙ B →∙ C ∙ ∙)
-- fst →Point∙ = →Point
-- snd (→Point∙ {A = A} {B = B} {C = C}) =
--   ΣPathP ((funExt (λ x → ΣPathP (refl , (sym (rUnit refl)))))
--     , {!!})

-- ←Point : A →∙ (B →∙ C ∙) → (A ⋀∙ B) →∙ C
-- fst (←Point {A = A} {B = B} {C = C} f) (inl x) = fst (fst f (pt A)) (pt B)
-- fst (←Point f) (inr (x , y)) = fst (fst f x) y
-- fst (←Point {A = A} f) (push (inl x) i) = (((fst f (pt A)) .snd) ∙ sym ((fst f x) .snd)) i
-- fst (←Point {B = B} f) (push (inr x) i) = (funExt⁻ (cong fst (snd f)) (pt B) ∙ sym (funExt⁻ (cong fst (snd f)) x)) i
-- fst (←Point {A = A} {B = B} f) (push (push a i) j) =
--   (rCancel (fst f (pt A) .snd) ∙ sym (rCancel (funExt⁻ (cong fst (snd f)) (pt B)))) i j
-- snd (←Point {A = A} f) = fst f (pt A) .snd

-- ←Point∙ : (A →∙ B →∙ C ∙ ∙) →∙ ((A ⋀∙ B) →∙ C ∙)
-- fst ←Point∙ = ←Point
-- snd ←Point∙ = {!!}

-- PointIso : Iso (A →∙ (B →∙ C ∙)) ((A ⋀∙ B) →∙ C)
-- Iso.fun PointIso = ←Point
-- Iso.inv PointIso = →Point
-- Iso.rightInv PointIso = {!!}
-- Iso.leftInv PointIso = {!!}

-- PointEquiv∙ : (A →∙ B →∙ C ∙ ∙) ≃∙ ((A ⋀∙ B) →∙ C ∙)
-- fst PointEquiv∙ = isoToEquiv PointIso
-- snd PointEquiv∙ = ←Point∙ .snd

-- open import Cubical.Data.Vec
-- open import Cubical.Data.Nat
-- open import Cubical.Data.FinData
-- open import Cubical.Foundations.Equiv
-- open import Cubical.HITs.S1
-- open import Cubical.HITs.S2


-- S²-fib : S² → Type
-- S²-fib x = {!!}



-- -- HasIso : ∀ {ℓ} (_×_ : Pointed ℓ → Pointed ℓ → Pointed ℓ) → Type _
-- -- HasIso {ℓ = ℓ} _×'_ = (A B C : Pointed ℓ) → (A ×' (B ×' C)) ≃∙ ((A ×' B) ×' C)

-- -- module gen {ℓ : Level} (_⋁_ _×_ : Pointed ℓ → Pointed ℓ → Pointed ℓ)
-- --        (inc : {A B : Pointed ℓ} → (A ⋁ B) →∙ (A × B))
-- --        (h∨ : HasIso _⋁_) (h× : HasIso _×_) where
-- --   P : (Pointed ℓ → Pointed ℓ → Pointed ℓ)
-- --   P X Y = Pushout (λ _ → tt) (inc {A = X} {B = Y} .fst) , inl tt

-- --   asd : {!(x : A ⋀ B) → x ≡ x!}
-- --   asd = {!!}

-- --   FF : (A B C : Pointed ℓ) (f g : fst A → (B ⋀ C))
-- --     → f ≡ g
-- --     → (fp : f (pt A) ≡ inl tt)
-- --       (gp : g (pt A) ≡ inl tt)
-- --     → Path (A →∙ (B ⋀∙ C)) (f , fp) (g , gp) -- f ≡ g
-- --   FF A B C f g = J (λ g _ → (fp : f (pt A) ≡ inl tt)
-- --       (gp : g (pt A) ≡ inl tt)
-- --     → Path (A →∙ (B ⋀∙ C)) (f , fp) (g , gp))
-- --     λ fp gp → ΣPathP ({!f!}
-- --                      , {!? ∙ ?!})

-- --   HasIsoP : HasIso P
-- --   fst (HasIsoP A B C) = isoToEquiv {!!}
-- --     where
-- --     help : Iso (fst (P A (P B C))) (fst (P (P A B) C))
-- --     Iso.fun help (inl x) = inl tt
-- --     Iso.fun help (inr x) = inr {!x!}
-- --     Iso.fun help (push a i) = push {!!} i
-- --     Iso.inv help = {!!}
-- --     Iso.rightInv help = {!!}
-- --     Iso.leftInv help = {!!}
-- --   snd (HasIsoP A B C) = {!!}

-- -- module PreSymMon {ℓ : Level} (_⊗_ : Pointed ℓ → Pointed ℓ → Pointed ℓ)
-- --               (i : {A B : Pointed ℓ} → typ A × typ B → typ (A ⊗ B))
-- --               (iₗ : {A B : Pointed ℓ} (x : typ A) → i (x , snd B) ≡ pt (A ⊗ B))
-- --               (iᵣ : {A B : Pointed ℓ} (x : typ B) → i (snd A , x) ≡ pt (A ⊗ B))
-- --               (iₗᵣ : {A B : Pointed ℓ} → iₗ {A = A} {B = B} (pt A) ≡ iᵣ (pt B)) where
-- --   Cur : {A B C : Pointed ℓ} → ((A ⊗ B) →∙ C) → A →∙ (B →∙ C ∙)
-- --   fst (fst (Cur f) x) y = fst f (i (x , y))
-- --   snd (fst (Cur f) x) = cong (fst f) (iₗ x) ∙ snd f
-- --   snd (Cur {B = B} f) =
-- --     ΣPathP (funExt (λ y → cong (fst f) (iᵣ y) ∙ snd f)
-- --           , (cong (_∙ snd f) (cong (cong (fst f)) iₗᵣ)
-- --           ◁ λ i j → (cong (fst f) (iᵣ (pt B)) ∙ snd f) (i ∨ j)))

-- --   Cur∙ : {A B C : Pointed ℓ} → ((A ⊗ B) →∙ C ∙) →∙ (A →∙ (B →∙ C ∙) ∙)
-- --   fst Cur∙ = Cur
-- --   snd Cur∙ = ΣPathP ((funExt (λ x → ΣPathP (refl , (sym (rUnit refl)))))
-- --     , {!!})

-- --   module _ (e : {A B C : Pointed ℓ} → isEquiv (Cur {A = A} {B = B} {C = C})) where
-- --     Cur⁻ : {A B C : Pointed ℓ} → (A →∙ (B →∙ C ∙)) → (A ⊗ B) →∙ C
-- --     Cur⁻ = invEq (_ , e)

-- --     CurEquiv : {A B C : Pointed ℓ} → ((A ⊗ B) →∙ C ∙) ≃∙ (A →∙ (B →∙ C ∙) ∙)
-- --     fst CurEquiv = Cur , e
-- --     snd CurEquiv = Cur∙ .snd

    

-- --     module _ {A B C D : Pointed ℓ} where
-- --       shareElim : (((A ⊗ B) ⊗ C) →∙ D ∙) ≃∙ ((A ⊗ (B ⊗ C)) →∙ D ∙)
-- --       shareElim =
-- --         compEquiv∙ CurEquiv
-- --           (compEquiv∙
-- --             CurEquiv
-- --             (compEquiv∙
-- --               ((isoToEquiv (pre∘∙equiv (invEquiv∙ CurEquiv))) , {!e .equiv-proof!})
-- --               (invEquiv∙ CurEquiv)))

      
      

-- --     {-
-- --     (A ⊗ B) ⊗ D → C
-- --     (A ⊗ B) → (D → C)
-- --     → (A → (B → (D → C)))
-- --     → 
-- --     -}
-- --       f : A →∙ (B →∙ C →∙ A ⊗ (B ⊗ C) ∙ ∙) -- A →∙ (B →∙ C ∙) ∙
-- --       fst (fst (fst f x) y) z = i (x , (i (y , z)))
-- --       snd (fst (fst f x) y) = cong (λ y → i (x , y)) (iₗ y) ∙ iₗ x
-- --       fst (snd (fst f x) j) z = (cong (λ y → i (x , y)) (iᵣ z) ∙ iₗ x) j
-- --       snd (snd (fst f x) j) = {!!}
-- --       snd f = {!!}
    
-- --       F1 : Iso (typ (((A ⊗ B) ⊗ C))) (typ (A ⊗ (B ⊗ C)))
-- --       Iso.fun F1 = {!!}
-- --       Iso.inv F1 = {!!}
-- --       Iso.rightInv F1 = {!!}
-- --       Iso.leftInv F1 = {!!}
    

-- -- module SymMon {ℓ : Level} (_⊗_ : Pointed ℓ → Pointed ℓ → Pointed ℓ)
-- --               (i : {A B : Pointed ℓ} → typ A × typ B → typ (A ⊗ B))
-- --               (iₗ : {A B : Pointed ℓ} (x : typ A) → i (x , snd B) ≡ pt (A ⊗ B))
-- --               (iᵣ : {A B : Pointed ℓ} (x : typ B) → i (snd A , x) ≡ pt (A ⊗ B))
-- --               (iₗᵣ : {A B : Pointed ℓ} → iₗ {A = A} {B = B} (pt A) ≡ iᵣ (pt B)) where
-- --   module M = PreSymMon _⊗_ i iₗ iᵣ iₗᵣ

  
-- -- open import Cubical.Data.Sum
-- -- {-
-- -- f : A × B → C
-- -- f(a, b₀) = ?
-- -- f(a₀, b) = ?
-- -- f(a₀, b₀) = ?
-- -- -}

-- -- Sm : {A B : Pointed₀} → (x : A ⋀ B) → Type
-- -- Sm {A = A} {B = B} (inl x) = {!!}
-- -- Sm {A = A} {B = B} (inr x) = {!!}
-- -- Sm {A = A} {B = B} (push a i) = {!!}


-- -- swap' : ∀ {ℓ} (n : ℕ) (m : Fin n) (B : Type ℓ) → (e : Vec (Type ℓ) n) → Vec (Type ℓ) n
-- -- swap' (suc n) zero B e = B ∷ tail (e )
-- -- swap' (suc n) (suc m) B e = head e ∷ swap' n m B (tail e)

-- -- lookup-swap : ∀ {ℓ} (n : _) (m : _) (X : Vec (Type ℓ) n) → swap' n m (lookup m X) X ≡ X
-- -- lookup-swap (suc n) zero (x ∷ X) = refl
-- -- lookup-swap (suc n) (suc m) (x ∷ X) = cong (x ∷_) (lookup-swap n m X)

-- -- Nat' : ∀ {ℓ ℓ'} (n : ℕ) (C C' : Vec (Type ℓ) (suc n) → Type ℓ')
-- --      → (e : (∀ {ℓ''} (D : Type ℓ'') (X : Vec (Type ℓ) (suc n)) → Iso (C X → D) (C' X → D)))
-- --      → (ind : ((m : Fin (suc n))  (X : Vec (Type ℓ) (suc n)) (D : Type ℓ)
-- --        → (F : lookup m X → D)
-- --        → C X → C (swap' (suc n) m D X)))
-- --      → ((m : _) (X : _) → ind m X _ (idfun (lookup m X))
-- --                           ≡ subst C (sym (lookup-swap (suc n) m X)))
-- --      → {!!}
-- -- Nat' = {!!}

-- -- Nati∙ : ∀ {ℓ ℓ'} (A : Type ℓ) → (C C' : A → Pointed ℓ')
-- --   → (e : (∀ {ℓ'''} (D : Pointed ℓ''') (a : A) → Iso (C a →∙ D) (C' a →∙ D)))
-- --   → (funct : (a : A) → Iso.inv (e (C' a) a) (idfun∙ _) ∘∙ (Iso.fun (e (C a) a) (idfun∙ _)) ≡ idfun∙ _)
-- --   → ((a : A) → Iso.fun (e (C a) a) (idfun∙ _) ∘∙ (Iso.inv (e (C' a) a) (idfun∙ _)) ≡ idfun∙ _)
-- --   → (a : _) → Iso (fst (C a)) (fst (C' a))
-- -- Nati∙ = {!!}

-- -- Nati : ∀ {ℓ ℓ'} (A : Type ℓ) → (C C' : A → Type ℓ')
-- --   → (e : (∀ {ℓ'''} (D : Type ℓ''') (a : A) → Iso (C a → D) (C' a → D)))
-- --   → (funct : (a : A) (x : _) → Iso.inv (e (C' a) a) (idfun _) (Iso.fun (e (C a) a) (idfun _) x) ≡ x)
-- --   → ((a : A) (x : _) → Iso.fun (e (C a) a) (idfun (C a))
-- --       (Iso.inv (e (C' a) a) (idfun (C' a)) x)
-- --       ≡ x)
-- --   → (a : _) → Iso (C a) (C' a)
-- -- Iso.fun (Nati A C C' e func f2 a) = Iso.inv (e (C' a) a) (idfun _)
-- -- Iso.inv (Nati A C C' e func f2 a) = Iso.fun (e (C a) a) (idfun _)
-- -- Iso.rightInv (Nati A C C' e func f2 a) x = func a x
-- -- Iso.leftInv (Nati A C C' e func f2 a) x = f2 a x

-- -- open import Cubical.Foundations.Pointed
-- -- open import Cubical.Foundations.Equiv

-- -- codom≃∙ : ∀ {ℓ} {A B C : Pointed ℓ} → B ≃∙ C → (A →∙ B ∙) ≃∙ (A →∙ C ∙)
-- -- fst (codom≃∙ {A = A} {B = B} {C = C} e) = isoToEquiv (pre∘∙equiv e)
-- -- snd (codom≃∙ (e , p)) = ΣPathP ((λ i _ → p i) , (sym (lUnit p) ◁ λ i j → p (i ∨ j)))

-- -- assocIso : ∀ {ℓ} (A B C : Pointed ℓ) → Iso (A ⋀ (B ⋀∙ C )) ((A ⋀∙ B) ⋀ C)
-- -- assocIso {ℓ = ℓ} A B C =
-- --   Nati∙ (Pointed ℓ ×' Pointed ℓ ×' Pointed ℓ)
-- --        (λ A → (fst A) ⋀∙ ((fst (snd A)) ⋀∙ (snd (snd A))))
-- --        (λ A → ((fst A) ⋀∙ (fst (snd A))) ⋀∙ (snd (snd A)))
-- --        (λ {D (A , B , C) → compIso (invIso PointIso) (compIso (compIso (pre∘∙equiv (invEquiv∙ PointEquiv∙))
-- --                                     PointIso)
-- --                                     PointIso)})
-- --        {!!}
-- --        {!!}
-- --        (A , B , C)

-- -- Nat : ∀ {ℓ ℓ'} → (C C' : Type ℓ → Type ℓ')
-- --   → ((x y : Type ℓ) (f : x → y) → C x → C y)
-- --   → (∀ {ℓ'''} (D : Type ℓ''') (a : Type ℓ) → Iso (C a → D) (C' a → D))
-- --   → (a : _) → Iso (C a) (C' a)
-- -- Iso.fun (Nat C C' ind is a) = Iso.inv (is (C' a) a) (idfun _)
-- -- Iso.inv (Nat C C' ind is a) = Iso.fun (is (C  a) a) (idfun _)
-- -- Iso.rightInv (Nat C C' ind is a) x = {!Iso.inv (is (C' a) a) (idfun (C' a))!}
-- -- Iso.leftInv (Nat C C' ind is a) = {!!}

-- -- NatInCod : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
-- --   → (e : ∀ {ℓ''} (C : Type ℓ'') → Iso (A → C) (B → C))
-- --   → (∀ {ℓ''} (C : Type ℓ'') (a : A) → {!Iso.fun (e C) !})
-- --   → Iso A B
-- -- NatInCod = {!!}
