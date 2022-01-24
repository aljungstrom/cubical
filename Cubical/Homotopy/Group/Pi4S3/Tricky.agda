{-# OPTIONS --safe #-}
module Cubical.Homotopy.Group.Pi4S3.Tricky where

open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Group.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open Iso
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Morphism

open import Cubical.Data.Unit
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3
          ; map to sMap)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1 hiding (decode ; encode)

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool

open import Cubical.Algebra.Group hiding (Unit)
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid


open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge
open import Cubical.Homotopy.Freudenthal hiding (Code ; encode)
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation renaming
  (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)
open import Cubical.Foundations.Function
open import Cubical.HITs.S2

open import Cubical.Homotopy.BlakersMassey
open import Cubical.Homotopy.Whitehead


W' = joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1}

W : S₊ 3 → (S₊∙ 2 ⋁ S₊∙ 2)
W = W' ∘ Iso.inv (IsoSphereJoin 1 1)

fold∘W : S₊ 3 → S₊ 2
fold∘W = fold⋁ ∘ W

thePushout : Type
thePushout = Pushout (λ _ → tt) fold∘W

thePullback : Type
thePullback = Σ[ x ∈ Unit ] Σ[ y ∈ S₊ 2 ] Path thePushout (inl x) (inr y)

S₊3→thePullback : S₊ 3 → thePullback
fst (S₊3→thePullback x) = tt
fst (snd (S₊3→thePullback x)) = fold∘W x
snd (snd (S₊3→thePullback x)) = push x

data Pushout' {ℓ : Level}  (X : Type ℓ) (Y : Type ℓ) (Q : X → Y → Type ℓ) : Type ℓ
    where
      inl : X → Pushout' X Y Q
      inr : Y → Pushout' X Y Q
      push : {x : X}{y : Y} → Q x y → inl x ≡ inr y

Iso2 : Iso (Path (Pushout' Unit (S₊ 2)
            λ x y → Path thePushout (inl x) (inr y)) (inl tt) (inr north)) thePullback
Iso2 = {!!}

black : isConnectedFun 4 S₊3→thePullback
black = uncurry
  λ x → uncurry
    (sphereElim 1 (λ _ → isProp→isOfHLevelSuc 1 (isPropΠ λ _ → isPropIsContr))
      λ p → trRec {!!} {!λ _ → ∣ ? ∣₂!} {!!})

test : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
       (f : A → B) (g : A → C)
     → B → C → Type _
test {A = A} f g x y = Σ[ a ∈ A ] (f a ≡ x) × (g a ≡ y)

module _ {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ} {C : Type ℓ''}
       (f : A → B) (g : A → C) (n m : ℕ)
       (b₀ : B) (c₀ : C)
       (con-f : isConnectedFun (suc n) f)
       (con-g : isConnectedFun (suc m) g) where

  Push-f-g : Type _
  Push-f-g = Pushout f g

  Q2 : B → C → Type _
  Q2 b c = Σ[ x ∈ A ] (f x ≡ b) × (g x ≡ c)

  Bcon : (x : B) → isConnected (suc n) (Σ-syntax C (Q2 x))
  Bcon x =
    isConnectedRetractFromIso (suc n) h (con-f x)
    where
    zz : Iso (Σ-syntax C (Q2 x)) (Σ[ a ∈ A ] ((Σ[ c ∈ C ] (g a ≡ c)) × (f a ≡ x)))
    fun zz (c , (a , p , q)) = a , (c , q) , p
    inv zz (a , (c , q) , p) = (c , (a , p , q))
    rightInv zz x = refl
    leftInv zz x = refl

    UnitIso : ∀ {ℓ} {A : Type ℓ} → Iso (Unit × A) A
    fun UnitIso = snd
    inv UnitIso = tt ,_
    rightInv UnitIso x = refl
    leftInv UnitIso x = refl

    zz2 : Iso ((Σ[ a ∈ A ] ((Σ[ c ∈ C ] (g a ≡ c)) × (f a ≡ x)))) (fiber f x)
    zz2 = Σ-cong-iso-snd
      λ a → compIso (Σ-cong-iso-fst (isContr→Iso (isContrSingl (g a)) isContrUnit))
                     UnitIso

    h : Iso (Σ-syntax C (Q2 x)) (fiber f x)
    h = compIso zz zz2

  Ccon : (x : C) → isConnected (suc m) (Σ-syntax B (λ a → Q2 a x))
  Ccon x = {!!}

  module testmod = BlakersMassey B C Q2 {m = n} Bcon {n = m} Ccon

  open testmod renaming (Pushout to PushoutQ) 

  PushGen' : Type _
  PushGen' = testmod.Pushout

  Push1→Push2 : Pushout f g → PushoutQ
  Push1→Push2 (inl x) = inl x
  Push1→Push2 (inr x) = inr x
  Push1→Push2 (push a i) = push (a , refl , refl) i

  Push2→Push1 : PushoutQ → Pushout f g
  Push2→Push1 (inl x) = inl x
  Push2→Push1 (inr x) = inr x
  Push2→Push1 (push (x , p , q) i) =
    ((λ i → inl (p (~ i))) ∙∙ push x ∙∙ (λ i → inr (q i))) i

  IsoPushGen : Iso (Pushout f g) (PushoutQ)
  fun IsoPushGen = Push1→Push2
  inv IsoPushGen = Push2→Push1
  rightInv IsoPushGen (inl x) = refl
  rightInv IsoPushGen (inr x) = refl
  rightInv IsoPushGen (push (x , p , q) i) j = help _ _ x p q j i
    where
    help : (b : B) (c : C) (x : A) (p : f x ≡ b) (q : g x ≡ c)
      → cong Push1→Push2 (((λ i → inl (p (~ i))) ∙∙ push x ∙∙ (λ i → inr (q i))))
      ≡ push (x , p , q) 
    help b c x =
      J (λ b p → (q : g x ≡ c)
        → cong Push1→Push2 (cong Push2→Push1 (push (x , p , q)))
         ≡ push (x , p , q))
        (J (λ c q → cong Push1→Push2 (cong Push2→Push1 (push (x , refl , q)))
         ≡ push (x , refl , q))
         (cong (cong Push1→Push2) (sym (rUnit (push x)))))
  leftInv IsoPushGen (inl x) = refl
  leftInv IsoPushGen (inr x) = refl
  leftInv IsoPushGen (push a i) j = rUnit (push a) (~ j) i


  conLem : (b : B) (c : C) (x : Path (PushoutQ) (inl b) (inr c))
         → isContr (hLevelTrunc (n + m)  (fiber push x))
  conLem = testmod.Excision

  isOfHLevelIsConnected : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isOfHLevel n (isConnected n A)
  isOfHLevelIsConnected {A = A} zero =
    (tt* , (λ {tt* → refl}))
    , (uncurry (λ {tt* p → Σ≡Prop
      (λ _ → isPropΠ (λ _ → isProp→isSet isPropUnit* _ _)) refl}))
  isOfHLevelIsConnected {A = A} (suc n) =
    isProp→isOfHLevelSuc n isPropIsContr 

  PB : A → Σ[ b ∈ B ] Σ[ c ∈ C ] Path (Pushout f g) (inl b) (inr c)
  PB a = (f a) , ((g a) , (push a))

  ready? : isConnectedFun (n + m) PB
  ready? (b , c , y) =
    trRec (isOfHLevelIsConnected (n + m))
      (λ A → haha (A . fst) y)
      ((testmod.Excision b c (cong Push1→Push2 y) .fst))
    where
    haha : Q2 b c →
       (y : Path (Pushout f g) (inl b) (inr c))
      → isConnected (n + m) (fiber PB (b , c , y))
    haha = uncurry λ x → uncurry (J (λ b _ → (y₂ : g x ≡ c) →
      (y : Path (Pushout f g) (inl b) (inr c)) →
      isConnected (n + m) (fiber PB (b , c , y)))
      (J (λ c _ → (y₂ : Path (Pushout f g) (inl (f x)) (inr c)) →
      isConnected (n + m) (fiber PB (f x , c , y₂)))
        λ y → isConnectedRetract (n + m)
                (haha2 x y)
                (hehe2 x y)
                (hahahehe x y)
                (testmod.Excision (f x) (g x)
                   (cong (fun IsoPushGen) y))))
      where
      hehe2 : (x : _) (y : _)
           → fiber push (cong Push1→Push2 y)
           → fiber PB (f x , g x , y)
      hehe2 x y =
        uncurry
          (uncurry λ x2
            → uncurry λ p q P
             → x2
             , (ΣPathP (p , ΣPathP (q
             , H x2 p q P))))
        where
        H : (x2 : A) (p : f x2 ≡ f x) (q : g x2 ≡ g x)
          → push (x2 , p , q) ≡ cong Push1→Push2 y
          → PathP (λ i → Path (Pushout f g) (inl (p i)) (inr (q i)))
                   (push x2) y
        H x2 p q P i j =
          hcomp (λ k → λ {(i = i0) → push x2 j
                         ; (i = i1) → leftInv IsoPushGen (y j) k
                         ; (j = i0) → inl (p i)
                         ; (j = i1) → inr (q i)})
            (hcomp (λ k → λ {(i = i0) → push x2 j
                         ; (i = i1) → Push2→Push1 (P k j)
                         ; (j = i0) → inl (p i)
                         ; (j = i1) → inr (q i)})
                   (doubleCompPath-filler (λ i → inl (p (~ i))) (push x2) (λ i → inr (q i)) i j))

      HFill : (x x2 : A) (y : _) (P : PB x2 ≡ (f x , g x , y))
            → I → I → I → PushoutQ
      HFill x x2 y P i j k =
        hfill (λ k → λ {(i = i0) → push (x2 , ((λ i → fst (P (i ∧ k))) , λ i → fst (snd (P (i ∧ k))))) j
                         ; (i = i1) → Push1→Push2 (snd (snd (P k)) j)
                         ; (j = i0) → inl (fst (P k))
                         ; (j = i1) → inr (fst (snd (P k)))})
                (inS (push (x2 , refl , refl) j))
                k

      haha2 : (x : _) (y : _)
           → fiber PB (f x , g x , y)
           → fiber push (cong Push1→Push2 y)
      haha2 x y =
        uncurry λ x2
          → λ P → (x2 , ((cong fst P) , (λ i → fst (snd (P i)))))
            , H x2 P
        where
        H : (x2 : A) → (P : PB x2 ≡ (f x , g x , y))
          → push (x2 , (λ i → fst (P i)) , (λ i → fst (snd (P i)))) ≡ cong Push1→Push2 y
        H x2 P i j = HFill x x2 y P i j i1

      pathCharac : {p1 p2 : _} {q1 q2 : _} {r1 : _} {r2 : _}
        → {P Q : Path (Σ[ b ∈ B ] (Σ[ c ∈ C ] Path (Pushout f g) (inl b) (inr c)))
                (p1 , q1 , r1)
                (p2 , q2 , r2)}
        → (f' : cong fst P ≡ cong fst Q)
        → (s : Path (q1 ≡ q2) (λ i → fst (snd (P i))) (λ i → fst (snd (Q i))))
        → SquareP (λ i j → Path (Pushout f g) (inl (f' i j)) (inr (s i j)))
                   (λ j → snd (snd (P j))) (λ j → snd (snd (Q j)))
                   refl
                   refl
        → P ≡ Q
      fst (pathCharac f s r i j) = f i j
      fst (snd (pathCharac f s r i j)) = s i j
      snd (snd (pathCharac f' s r i j)) = r i j

      hahahehe : (x : A) (y : _) (x₁ : fiber PB (f x , g x , y)) →
        hehe2 x y (haha2 x y x₁) ≡ x₁
      hahahehe x y =
        uncurry
          λ x2 P
          → ΣPathP (refl
            , pathCharac
               refl refl (help x2 y P))
        where
        help : (x2 : A) (y : _) (P : _)
          → SquareP
             (λ i j →
                Path (Pushout f g)
                (inl (cong fst (snd (hehe2 x y (haha2 x y (x2 , P)))) j))
                (inr (fst (snd (snd (hehe2 x y (haha2 x y (x2 , P))) j)))))
             (λ j → snd (snd (snd (hehe2 x y (haha2 x y (x2 , P))) j)))
             (λ j → snd (snd (P j))) refl refl
        help x2 y P i j k =
          hcomp (λ r → λ {(i = i1) → leftInv IsoPushGen (snd (snd (P j)) k) r
                         ; (j = i0) → doubleCompPath-filler refl (push x2) refl (~ r ∧ i) k
                         ; (j = i1) → leftInv IsoPushGen (y k) r
                         ; (k = i0) → inl (p j)
                         ; (k = i1) → inr (q j)})
                (hcomp (λ r → λ {(i = i1) → HH r j k
                         ; (j = i0) → doubleCompPath-filler (λ i → inl (p (~ r ∧ ~ i)))
                                         (push x2)
                                         (λ i → inr (q (~ r ∧ i))) i k
                         ; (j = i1) → Push2→Push1 (snd (haha2 x y (x2 , P)) r k)
                         ; (k = i0) → inl (p (j ∨ (~ r  ∧ i)))
                         ; (k = i1) → inr (q (j ∨ (~ r  ∧ i)))})
                       (doubleCompPath-filler (λ i → inl (p (~ i)))
                                         (push x2)
                                         (λ i → inr (q i)) (i ∨ j) k))
          where
          p : f x2 ≡ f x
          p = cong fst P

          q : g x2 ≡ g x
          q i = fst (snd (P i))

          HH : Cube (λ _ k → ((λ i₁ → inl (p (~ i₁))) ∙∙ push x2 ∙∙ (λ i₁ → inr (q i₁))) k)
                    (λ j k → Push2→Push1 (Push1→Push2 (snd (snd (P j)) k)))
                    (λ r k → ((λ i → inl (p (~ r ∧ ~ i)))
                            ∙∙ (push x2)
                            ∙∙ (λ i → inr (q (~ r ∧ i)))) k)
                    (λ r k → Push2→Push1 (snd (haha2 x y (x2 , P)) r k))
                    (λ r j → inl (p (j ∨ ~ r)))
                    λ r j → inr (q (j ∨ ~ r))
          HH r j k =
            hcomp (λ i → λ { (r = i0) → ((λ i₁ → inl (fst (P (~ i₁ ∧ i))))
                                       ∙∙ push x2
                                       ∙∙ (λ i₁ → inr (fst (snd (P (i₁ ∧ i)))))) k
                            ; (r = i1) → Push2→Push1 (Push1→Push2 (snd (snd (P (i ∧ (j ∨ ~ r)))) k))
                            ; (j = i0) → ((λ i₁ → inl (fst (P (~ i₁ ∧ (i ∧ ~ r)))))
                                       ∙∙ push x2
                                       ∙∙ λ i₁ → inr (fst (snd (P (i₁ ∧ (i ∧ ~ r)))))) k
                            ; (j = i1) → Push2→Push1 (HFill x x2 y P r k i)
                            ; (k = i0) → inl (fst (P (i ∧ (j ∨ ~ r))))
                            ; (k = i1) → inr (fst (snd (P (i ∧ (j ∨ ~ r)))))})
                      ((push x2 ∙ refl) k)
{-
r = i0 ⊢ ((λ i₁ → inl (p (~ i₁))) ∙∙ push x2 ∙∙
          (λ i₁ → inr (q i₁)))
         k
r = i1 ⊢ Push2→Push1 (Push1→Push2 (snd (snd (P j)) k))
j = i0 ⊢ ((λ i₁ → inl (p (~ r ∧ ~ i₁))) ∙∙ push x2 ∙∙
          (λ i₁ → inr (q (~ r ∧ i₁))))
         k
j = i1 ⊢ Push2→Push1 (snd (haha2 x y (x2 , P)) r k)
k = i0 ⊢ inl (p (j ∨ ~ r))
k = i1 ⊢ inr (q (j ∨ ~ r))
-}

  -- Q-test : Iso PushQ (Pushout f g)
  -- fun Q-test (inl x) = inl x
  -- fun Q-test (inr x) = inr x
  -- fun Q-test (push b c x i) = x i
  -- inv Q-test (inl x) = inl x
  -- inv Q-test (inr x) = inr x
  -- inv Q-test (push a i) = push (f a) (g a) (push a) i
  -- rightInv Q-test (inl x) = refl
  -- rightInv Q-test (inr x) = refl
  -- rightInv Q-test (push a i) = refl
  -- leftInv Q-test (inl x) = refl
  -- leftInv Q-test (inr x) = refl
  -- leftInv Q-test (push b c x i) j = {!!}
  --   where
  --   invGen : (Pushout f g) → {!!}
  --   invGen = {!!}

  -- PB : Type _
  -- PB = Σ[ b ∈ B ] Σ[ c ∈ C ] (Q b c)

  -- PB∙ : PB
  -- PB∙ = b₀ , c₀ , {!!}
  
  -- A→PB : A → PB -- (b : PB) → Iso {!fiber PB!} {!!}
  -- A→PB a = f a , g a , push a

  -- gzz : (a : A) → Path (Pushout f g) (inl (f a)) (inr (g a))
  -- gzz = push

  -- fibreEq : (x : PB) → Iso (fiber A→PB x) {!Σ[ x ∈ fiber gzz ? ] ?!}
  -- fibreEq = {!!}

  -- PBmap : Iso (A → PB) (Σ[ l ∈ (A → B) ] Σ[ r ∈ (A → C) ] {!!})
  -- PBmap = {!!}

  -- ll : (x : B) → isConnected (suc n) (Σ-syntax C (test f g x))
  -- ll x = {!con-f x!}
  --   where
  --   is : Iso (Σ-syntax C (test f g x)) (fiber f x)
  --   fun is (c , a , pa , pc) = a , pa
  --   inv is = {!!}
  --   rightInv is = {!!}
  --   leftInv is = {!!}

  -- module B = BlakersMassey B C Q {m = n} {!!} {n = {!!}} {!!}
