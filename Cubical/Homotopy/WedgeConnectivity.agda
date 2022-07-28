{-# OPTIONS --safe #-}
module Cubical.Homotopy.WedgeConnectivity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as Trunc

open import Cubical.Homotopy.Connected



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

  hom : left (pt A) ⁻¹ ∙ right (pt B) ≡ p
  hom i j = hcomp (λ k → λ { (i = i1) → p j
                           ; (j = i0) → (cong snd (funExt⁻ (main .fst .snd) tt)) i (~ j)
                           ; (j = i1) → right (pt B) (i ∨ k)})
                  (cong snd (funExt⁻ (main .fst .snd) tt) i (~ j))

  hom' : left (pt A) ≡ right (pt B) ∙ sym p
  hom' = (lUnit (left _) ∙ cong (_∙ left (pt A)) (sym (rCancel (right (pt B)))))
       ∙∙ sym (assoc _ _ _)
       ∙∙ cong (right (pt B) ∙_) (sym (symDistr (left (pt A) ⁻¹) (right (pt B))) ∙ (cong sym hom))

  homSquare : PathP (λ i → extension (pt A) (pt B) ≡ p i) (left (pt A)) (right (pt B))
  homSquare i j = hcomp (λ k → λ { (i = i0) → left (pt A) j
                                 ; (i = i1) → compPath-filler (right (pt B)) (sym p) (~ k) j
                                 ; (j = i0) → extension (pt A) (pt B)
                                 ; (j = i1) → p (i ∧ k) })
                        (hom' i j)

open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.Sn
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Join
open Iso

S¹-act : (x : S¹) → Iso S¹ S¹
fun (S¹-act x) y = x * y
inv (S¹-act x) y = invLooper x * y
rightInv (S¹-act x) y = assocS¹ x (invLooper x) y ∙ cong (_* y) (sym (rCancelS¹ x))
leftInv (S¹-act x) y = assocS¹ (invLooper x) x y ∙ cong (_* y) (commS¹ (invLooper x) x ∙ sym (rCancelS¹ x))

open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge

fonction : Susp (S¹ × S¹) → S₊ 2
fonction north = north
fonction south = south
fonction (merid (a , b) i) = merid (a * invLooper b) i

Hopf : join S¹ S¹ → S₊ 2
Hopf (inl x) = north
Hopf (inr x) = south
Hopf (push a b i) = merid (a * (invLooper b)) i

joinT : join S¹ S¹ → Susp (S¹ × S¹)
joinT (inl x) = north
joinT (inr x) = south
joinT (push a b i) = merid (a , b) i

SuspT : Susp (S¹ × S¹) → join S¹ S¹
SuspT north = inr base
SuspT south = inl base
SuspT (merid (a , b) i) = (sym (push a base) ∙∙ push a b ∙∙ sym (push base b)) i

CP = Pushout Hopf λ x → tt
ΣCP = hLevelTrunc 6 (Susp CP)

conCP2 : isConnected 3 (Susp CP)
fst conCP2 = ∣ north ∣
snd conCP2 = {!!}

suspCP : CP → Path (Susp CP) north north
suspCP (inl x) = merid (inl x) ∙ sym (merid (inr tt))
suspCP (inr x) = refl
suspCP (push a i) = ((λ j → merid (push a j) ∙ sym (merid (inr tt))) ∙ rCancel (merid (inr tt))) i
{-
  hcomp {!!}
        ((merid (push a j) ∙ sym (merid (inr tt))) i)
-}



CP2Mult : Susp CP → Susp CP → ΣCP
CP2Mult north y = ∣ y ∣ₕ
CP2Mult south y = ∣ y ∣ₕ
CP2Mult (merid a i) north = ∣ suspCP a i ∣ₕ
CP2Mult (merid a i) south = ∣ (sym (merid (inr tt)) ∙∙ suspCP a ∙∙ merid (inr tt)) i ∣ₕ
CP2Mult (merid a i) (merid b j) = {!!}

Extend : Susp CP → Type
Extend north = CP
Extend south = CP
Extend (merid a i) = {!!}

PP : (x : (Susp ( S¹ × S¹))) → Hopf (SuspT x) ≡ fonction x
PP north = sym (merid base)
PP south = merid base
PP (merid (a , b) i) = {!!}
  where
  help : cong Hopf ((sym (push a base) ∙∙ push a b ∙∙ sym (push base b)))
       ≡ (sym (merid a) ∙∙ merid (a * (invLooper b))  ∙∙ sym (merid (invLooper b)))
  help = cong-∙∙ Hopf (sym (push a base)) (push a b) (sym (push base b))
       ∙ cong (λ x → x ∙∙ merid (a * (invLooper b))  ∙∙ sym (merid (invLooper b)))
              λ i → sym (merid (rUnitS¹ a i))

Suspi : (x : Susp (Susp ( S¹ × S¹))) → suspFun Hopf (suspFun (SuspT) x) ≡ suspFun fonction x
Suspi north = refl
Suspi south = refl
Suspi (merid north i) j = merid (merid base (~ j)) i
Suspi (merid south i) j = merid (merid base j) i
Suspi (merid (merid (a , b) k) i) j = {!!}
  where
  help : {!!}
  help = {!!}

SuspEQ : {!!}
SuspEQ = {!!}
