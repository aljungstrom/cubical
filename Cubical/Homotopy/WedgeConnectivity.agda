{-# OPTIONS --safe --lossy-unification #-}
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




AC : ∀ {ℓ} (A : Type ℓ) → Type ℓ
AC A = isContr (Susp A)

data HH (A : Type) (a : A) : Type where
  int : A → HH A a
  _plus_ : HH A a → HH A a → HH A a
  left : (t : HH A a) → int a plus t ≡ t
  right : (t : HH A a) → t plus (int a) ≡ t

fss : (A : Type) (a : A) (z : HH A a) → int a ≡ z
fss A a (int x) = {!a ≡ x!}
fss A a (z plus z₁) = {!!}
fss A a (left z i) = {!!}
fss A a (right z i) = {!!}

open import Cubical.Homotopy.Loopspace
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR


module _ (A : Type) (a : A) (con : isConnected 3 A) (contr : isContr (Susp A)) where

  A* = hLevelTrunc 4 A

  conA : (a' : A) → ∥ a ≡ a' ∥₂
  conA a' = TR.rec squash₂ ∣_∣₂
    (Iso.fun (PathIdTruncIso 2)
      (isContr→isProp con ∣ a ∣ ∣ a' ∣))

  conA* : (a' : A*) → ∥ ∣ a ∣ ≡ a' ∥₂
  conA* = TR.elim (λ _ → isOfHLevelPlus {n = 2} 2 squash₂)
    λ a' → ST.map (cong ∣_∣ₕ) (conA a')

  0A : A*
  0A = ∣ a ∣ₕ




  module M = WedgeConnectivity 2 2
    (A , a) con (A , a) con
    (λ _ _  → A* , isOfHLevelTrunc 4) ∣_∣ ∣_∣ refl

  _+A_ : A* → A* → A*
  _+A_ = TR.rec2 (isOfHLevelTrunc 4) M.extension

  module N = WedgeConnectivity 2 2
    (A , a) con (A , a) con
    (λ x y → ((∣ x ∣ +A ∣ y ∣) ≡ (∣ y ∣ +A ∣ x ∣))
      , isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)


  lUnitA : (a' : A*) → 0A +A a' ≡ a'
  lUnitA = TR.elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _) M.right

  rUnitA : (a' : A*) → a' +A 0A  ≡ a'
  rUnitA = TR.elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _) M.left

  l≡r : lUnitA 0A ≡ rUnitA 0A
  l≡r = (lUnit (lUnitA 0A)
    ∙ cong (_∙ M.right a) (sym (rCancel _))
    ∙ sym (assoc (M.left a) (sym (M.left a)) (M.right a)))
    ∙ (cong (M.left a ∙_) M.hom)
    ∙ sym (rUnit (M.left a ))

  commA : (x y : A*) → x +A y ≡ y +A x
  commA =
    TR.elim2 (λ _ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
    (N.extension
      (λ x → rUnitA ∣ x ∣ ∙ sym (lUnitA ∣ x ∣))
      (λ y → lUnitA ∣ y ∣ ∙ sym (rUnitA ∣ y ∣))
      (cong₂ _∙_ (sym l≡r) (cong sym l≡r)))

  isEq : (a' : A*) → isEquiv (a' +A_)
  isEq a' = ST.rec (isProp→isSet (isPropIsEquiv _))
    (J (λ a' _ → isEquiv (a' +A_))
      (subst isEquiv
        (funExt (λ t → sym (lUnitA t))) (idIsEquiv _)))
    (conA* a')

  +Eq : (a' : A*) → A* ≃ A*
  fst (+Eq a') = a' +A_
  snd (+Eq a') = isEq a'

  gr : Susp A → Type
  gr north = A*
  gr south = A*
  gr (merid a i) = ua (_ , isEq ∣ a ∣) i

  invA* : A* → A*
  invA* a' = invEq (+Eq a') 0A

  _-A_ : A* → A* → A*
  x -A y = x +A invA* y

  rCancelA : (x : A*) → x -A x ≡ 0A
  rCancelA x = secEq (+Eq x) 0A

  lCancelA : (x : A*) → (invA* x) +A x ≡ 0A
  lCancelA x = commA _ _ ∙ rCancelA x

  assocA : (x y z : A*) → (x +A (y +A z)) ≡ ((x +A y) +A z)
  assocA = TR.elim3 (λ _ _ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
    (WedgeConnectivity.extension 2 2 (A , a) con (A , a) con
      (λ a₁ b → ((c : A) → (∣ a₁ ∣ +A (∣ b ∣ +A ∣ c ∣)) ≡ ((∣ a₁ ∣ +A ∣ b ∣) +A ∣ c ∣))
        , {!λ _ _!})
        {!!}
        {!!}
        {!!})

  +A-Iso : (a : A*) → Iso A* A*
  Iso.fun (+A-Iso a) x = x +A a
  Iso.inv (+A-Iso a) x = x -A a
  Iso.rightInv (+A-Iso a) z =
    sym (assocA z (invA* a) a) ∙ cong (z +A_) (lCancelA a) ∙ rUnitA z
  Iso.leftInv (+A-Iso a) z =
    sym (assocA z a (invA* a) ) ∙ cong (z +A_) (rCancelA a) ∙ rUnitA z

  H = HH A a

  Code : Susp A → Type
  Code north = A*
  Code south = A*
  Code (merid a i) = isoToPath (+A-Iso ∣ a ∣) (~ i)

  Code5 : hLevelTrunc 5 (Susp A) → TypeOfHLevel ℓ-zero 4
  Code5 = TR.rec (isOfHLevelTypeOfHLevel 4)
        λ x → Code x , suspToPropElim {B = λ x → isOfHLevel 4 (Code x)}
        a (λ _ → isPropIsOfHLevel 4)
        (isOfHLevelTrunc 4)
        x

  open import Cubical.Data.Sum
  ps : {A : H → Type} (a₀ : A (int a)) (x : H) → int a ≡ x → A x
  ps a₀ = J> a₀

  isEq-ps : {A : H → Type} (a₀ : A (int a)) (x : H) → isEquiv (ps {A = A} a₀ x)
  isEq-ps {A = A} a₀ = {!!}

  open import Cubical.Foundations.GroupoidLaws
  open import Cubical.Foundations.Path

  t1 : (x : Susp A)  → Type 
  t1 north = typ (Ω (Susp∙ A))
  t1 south = typ (Ω (Susp∙ A))
  t1 (merid b i) =
    ua (compPathrEquiv {A = Susp A}
         {x = north} {y = north} (toSusp (A , a) b)) i

  t12 : (x : Susp A)  → Type 
  t12 north = typ (Ω (A , a))
  t12 south = typ (Ω (A , a))
  t12 (merid b i) = {!!}

  meow : (x : Susp A) → (north ≡ x) → t1 x → t1 x
  meow = J> λ p → p

  FIB : Susp A → Type
  FIB north = Susp (Ω (A , a) .fst)
  FIB south = Susp (Ω (A , a) .fst)
  FIB (merid a i) = {!a!}

  contr1 : isContr (Susp (Ω (A , a) .fst))
  fst contr1 = north
  snd contr1 north = refl
  snd contr1 south = merid refl
  snd contr1 (merid b i) j = {!contr .snd (merid (b i) i)!}

  m3 : Susp A → Type
  m3 north = Susp (Ω (A , a) .fst)
  m3 south = Susp (Ω (A , a) .fst)
  m3 (merid a i) = {!a!}

  m1 : Susp (typ (Ω (A , a))) → Type
  m1 north = typ ((Ω^ 2) (Susp∙ A))
  m1 south = typ ((Ω^ 2) (Susp∙ A))
  m1 (merid x i) = ua c (~ i)
    where
    pth : (Ω^ 2) (Susp∙ A) .fst
    pth = sym (rCancel _) ∙∙ cong (toSusp (A , a)) x ∙∙ rCancel _

    c : typ (Ω (Ω (Susp∙ A))) ≃ typ (Ω (Ω (Susp∙ A)))
    c = compPathrEquiv pth

  isContr-m1 : (x : _) → isContr (m1 x)
  isContr-m1 =
    suspToPropElim refl (λ _ → isPropIsContr)
      (refl
      , (λ p → isOfHLevelPlus {n = 1} 2
        (isContr→isProp contr) north north refl refl _ p))

  masdd : Susp (typ ((Ω^ 2) (A , a))) → Type
  masdd north = typ ((Ω^ 2) (A , a))
  masdd south = typ ((Ω^ 2) (A , a))
  masdd (merid p i) =
    ua (compPathrEquiv {A = a ≡ a} {x = refl {x = a}} p) (~ i)



  masdd* : (x : _) → masdd x → north ≡ x
  masdd* north = toSusp ((Ω^ 2) (A , a))
  masdd* south = merid
  masdd* (merid p i) = c i
    where
    c : PathP (λ i → ua (compPathrEquiv {x = refl {x = a}} p) (~ i) → north ≡ merid p i)
              (toSusp ((Ω^ 2) (A , a)))
              merid
    c = toPathP (funExt λ q
      → cong (transport (λ i₁ → north ≡ merid p i₁))
              (cong (toSusp ((Ω^ 2) (A , a))) (transportRefl (q ∙ p)))
       ∙ {!!})

  masd : Susp (typ (Ω (A , a))) → Type
  masd north = a ≡ a
  masd south = a ≡ a
  masd (merid b i) =
    ua (compPathrEquiv {A = A} {x = a} {y = a} b) i

  masd' : (x : _) → masd x → north ≡ x
  masd' north = toSusp (Ω (A , a))
  masd' south p = merid p
  masd' (merid b i) = {!!}
    where
    l2 : (t : A) (r : a ≡ t) (p : a ≡ a)
      → PathP (λ i → typ (Ω (Susp∙ ((a ≡ r (~ i)))))) (toSusp (_ , r) (p ∙ r)) (toSusp ((a ≡ a) , refl) p)
    l2 = J> λ p → cong (toSusp (Ω (A , a))) (sym (rUnit p))

    sr : (t : A) (b : a ≡ t) (r : a ≡ t)
      → PathP (λ i → ua (compPathrEquiv {x = a} {y = a} b) (~ i)
                    → north ≡ merid b i)
                    (toSusp ((a ≡ t) , r))
                    λ p → merid (p ∙ r)
    sr = J> λ r → toPathP (funExt λ q
      → cong (transport (λ i₁ → Path (Susp (typ (Ω (A , a)))) north (merid (λ _ → a) i₁)))
               (cong (toSusp ((a ≡ a) , r))
                 (λ i → transportRefl (rUnit q (~ i)) i))
      ∙∙ (λ j → transp (λ i → Path (Susp (typ (Ω (A , a))))
                        north (merid (λ _ → a) (i ∨ j))) j
         (compPath-filler (toSusp ((a ≡ a) , r) q) (merid refl) j))
      ∙∙ {!!})
        where
        tr : (q r : a ≡ a)
          → (toSusp ((a ≡ a) , r) q ∙ merid (λ _ → a)) ∙ sym (merid r) ≡ merid (q ∙ r) ∙ sym (merid r)
        tr q r = sym {!!}
    comp' : (t : A) → Susp (a ≡ t) → Susp (t ≡ a) → Susp (a ≡ a)
    comp' t x s = {!Goal: transp (λ i₁ → north ≡ merid (λ _ → a) i₁) i0
      (λ i₁ →
         hcomp (doubleComp-faces (λ _ → north) (λ i₂ → merid r (~ i₂)) i₁)
         (merid
          (transp (λ i₂ → a ≡ a) i0
           (λ i₂ → hcomp (doubleComp-faces (λ _ → a) (λ _ → a) i₂) (q i₂)))
          i₁))!}

--     mrs : (t : A) (p q r : a ≡ t)
--       → toSusp ((a ≡ a) , refl) (p ∙ sym q)
--         ≡ subst (λ t → typ (Ω (Susp∙ (a ≡ t)))) (sym r) (toSusp ((a ≡ t) , r) p)
--         ∙ subst (λ t → typ (Ω (Susp∙ (t ≡ a)))) (sym r) (toSusp ((t ≡ a) , sym r) (sym q))
--     mrs = J> λ q r
--       → cong (toSusp ((a ≡ a) , refl)) (sym (lUnit (sym q)))
--       ∙∙ ((λ _ → toSusp (Ω (A , a)) (sym q))
--         ∙ {!!})
--        ∙ cong₂ _∙_ (λ _ → toSusp (Ω (A , a)) (sym r))
--                    (λ _ → toSusp (Ω (A , a)) (r ∙ sym q))
--       ∙∙ cong₂ _∙_
--            (sym ((λ j → transport (λ i → typ (Ω (Susp∙ (a ≡ r (~ i ∧ ~ j)))))
--                    (merid (λ i → r (~ j ∨ ~ i))
--                    ∙ sym (merid λ i → r (i ∧ ~ j))))
--                ∙ transportRefl (merid (sym r) ∙ sym (merid refl))))
--            (sym ((λ j → transport (λ i → typ (Ω (Susp∙ (r (~ i ∧ ~ j) ≡ a))))
--                    (merid (λ i → compPath-filler' r (sym q) j i)
--                         ∙ sym (merid λ i → r (~ i ∧ ~ j))))
--                ∙ transportRefl (merid (r ∙ sym q) ∙ sym (merid refl))))

--     col : PathP (λ i → ua (compPathrEquiv {x = a} b) (~ i) → north ≡ merid b i)
--                 (toSusp (Ω (A , a)))
--                 λ p → toSusp (Ω (A , a)) p ∙ merid refl
--     col = toPathP (funExt λ p
--       → cong (transport (λ i → north ≡ merid b i))
--               (cong (toSusp (Ω (A , a)))
--                 (transportRefl (p ∙ b)))
--       ∙∙ {!!}
--       ∙∙ {!!})


-- --   m1-ind : {B : (x : _) (y : m1 x) → Type}
-- --     → (b : B north refl)
-- --     → Σ[ f ∈ ((x : Susp _) (y : m1 x) → B x y) ]
-- --          f north refl ≡ b
-- --   m1-ind b = {!!}

-- --   m2 : (x : _) → m1 x → north ≡ x
-- --   m2 north p i = north -- refl -- λ _ → refl -- = toSusp (Ω (A , a)) {!p!}
-- --   m2 south = λ _ → merid refl
-- --   m2 (merid x i) = {!!}
-- --     where
-- --     c : PathP (λ i → m1 (merid x i) → north ≡ merid x i)
-- --                (λ _ → refl) λ _ → merid refl
-- --     c = toPathP (funExt λ p → {!!})

-- --   fs : {!!} → {!!}
-- --   fs = {!!}

-- --   ad : H → Type
-- --   w : (x : H) → ad x → ad x
-- --   ad (int x) = a ≡ x
-- --   ad (v plus w) = v ≡ w -- ad v × ad w
-- --   ad (left x i) = {!!}
-- --   ad (right x i) = {!!}
-- --   w (int x) = {!x!}
-- --   w (x plus x₁) = {!!}
-- --   w (left x i) = {!!}
-- --   w (right x i) = {!!}

-- --   C' : Susp (Susp A) → Type
-- --   C' north = a ≡ a
-- --   C' south = a ≡ a
-- --   C' (merid b i) = {!!}



-- -- --   HH→ : H → typ (Ω (Susp∙ A))
-- -- --   HH→ (int x) = toSusp (A , a) x
-- -- --   HH→ (x plus m) = HH→ x ∙ HH→ m
-- -- --   HH→ (left x i) = (cong (_∙ HH→ x) (rCancel (merid a)) ∙ sym (lUnit (HH→ x))) i
-- -- --   HH→ (right x i) = (cong (HH→ x ∙_) (rCancel (merid a)) ∙ sym (rUnit (HH→ x))) i

-- -- --   a-act : (x : A) → H → H
-- -- --   a-act x m = int x plus m

-- -- --   SSt : Susp (typ (Ω (A , a))) → A
-- -- --   SSt north = a
-- -- --   SSt south = a
-- -- --   SSt (merid q i) = q i

-- -- --   open import Cubical.Functions.Embedding
-- -- --   tSS : isEquiv SSt
-- -- --   equiv-proof tSS = {!!}
-- -- --     where
-- -- --     help : isContr (fiber SSt a)
-- -- --     fst help = north , refl
-- -- --     snd help y = isEmbedding→hasPropFibers {!!} _ _ y

-- -- --   SS : Susp A → Type
-- -- --   SS north = a ≡ a
-- -- --   SS south = a ≡ a
-- -- --   SS (merid b i) = {!!}

-- -- --   Fr : {!!}
-- -- --   Fr = {!!}

-- -- --   a-eq : (x : A) → isEquiv (a-act a)
-- -- --   a-eq = {!elim!}

-- -- --   SuspF : Susp A → Type
-- -- --   SuspF north = H
-- -- --   SuspF south = H
-- -- --   SuspF (merid b j) = ua (_ , a-eq b) (~ j)

-- -- --   myf : Ω (Susp∙ A) .fst → H
-- -- --   myf p = subst SuspF p (int a)



-- -- --   enc : (x : Susp A) → north ≡ x → SuspF x
-- -- --   enc x p = subst SuspF p (int a)

-- -- --   enc-hom : (p q : Path (Susp A) north north)
-- -- --     → myf (p ∙ q)
-- -- --      ≡ myf p plus myf q
-- -- --   enc-hom p q = {!!}

-- -- --   dec : (x : Susp A) → SuspF x → north ≡ x
-- -- --   dec north w = HH→ w
-- -- --   dec south w = HH→ w ∙ merid a
-- -- --   dec (merid b i) = h i
-- -- --     where
-- -- --     h : PathP (λ i → ua (a-act a , a-eq b) (~ i) → north ≡ merid b i)
-- -- --                HH→
-- -- --                λ w → HH→ w ∙ merid a
-- -- --     h = isProp→PathP
-- -- --       (λ i → isPropΠ λ _ → isOfHLevelPath 1 (isContr→isProp contr) _ _) _ _

-- -- --   enc-dec : (x : Susp A) (p : north ≡ x) → dec x (enc x p) ≡ p
-- -- --   enc-dec = J> cong (toSusp (A , a)) (transportRefl a) ∙ rCancel (merid a)


-- -- --   dec* : H → Ω (Susp∙ A) .fst
-- -- --   dec* = dec north

-- -- --   dec' : A → Ω (Susp∙ A) .fst
-- -- --   dec' a = dec north (int a)

-- -- --   dec'' : Ω (A , a) →∙ (Ω^ 2) (Susp∙ A)
-- -- --   dec'' = Ω→ (dec' , rCancel (merid a))



-- -- --   pl : (x : A) → enc north (toSusp (A , a) x) ≡ int x
-- -- --   pl x = {!!}

-- -- --   dec-enc : (w : _) → enc north (HH→ w) ≡ w
-- -- --   dec-enc (int x) = pl x
-- -- --   {-
-- -- --     cong₂ _plus_ (cong int (transportRefl a))
-- -- --                  (transportRefl (invEq (_ , a-eq a) (int x)))
-- -- --     ∙ {!!} -}
-- -- --   dec-enc (w plus w') =
-- -- --     enc-hom (HH→ w) (HH→ w')
-- -- --     ∙ cong₂ _plus_ (dec-enc w) (dec-enc w')
-- -- --   dec-enc (left w i) = {!!}
-- -- --   dec-enc (right w i) = {!!}


-- -- --   TR : Susp A → Type
-- -- --   TR north = {!!}
-- -- --   TR south = {!!}
-- -- --   TR (merid x i) = {!merid x i!}

-- -- --   H→Type : H → Type
-- -- --   H→Type (int x) = a ≡ a
-- -- --   H→Type (x plus z) = {!!}
-- -- --   H→Type (left x i) = {!x!}
-- -- --   H→Type (right x i) = {!!}

-- -- -- --   main : Iso (fst (Ω (Susp∙ A))) H
-- -- -- --   Iso.fun main = enc north
-- -- -- --   Iso.inv main = dec north
-- -- -- --   Iso.rightInv main (int x) = {!!}
-- -- -- --   Iso.rightInv main (p plus p₁) = {!!}
-- -- -- --   Iso.rightInv main (left p i) = {!!}
-- -- -- --   Iso.rightInv main (right p i) = {!!}
-- -- -- --   Iso.leftInv main = enc-dec north

-- -- -- -- PP : ∀ {ℓ} (A : Type ℓ)
-- -- -- --   → isConnected 1 A
-- -- -- --   → A → Susp A
-- -- -- -- PP A con = {!!}
