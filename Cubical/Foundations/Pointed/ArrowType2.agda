module Cubical.Foundations.Pointed.ArrowType2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed.Base

open import Cubical.Data.Sigma

open import Cubical.Homotopy.Loopspace

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

open WildCat
open WildFunctor

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

{- Wild arrow category (A : Type) × (B : Type) × (f : A → B) -}
Arrow : (ℓ : Level) → Type _
Arrow ℓ = Σ[ B ∈ Type ℓ ] (B → Type ℓ)

-- Source
ArrowS : Arrow ℓ → Type ℓ
ArrowS (B , P) = Σ B P

-- Target
ArrowT : Arrow ℓ → Type ℓ
ArrowT = fst

-- ArrowArrow
ArrowFun : (A : Arrow ℓ) → ArrowS A → ArrowT A
ArrowFun A = fst

-- Maps of arrow cats
ArrowHom : Arrow ℓ → Arrow ℓ' → Type (ℓ-max ℓ ℓ')
ArrowHom (B , P) (B' , P') =
  (x : B) → Σ[ b ∈ B' ] (P x → P' b)

-- composition
compArrowHom : {A : Arrow ℓ}
  {B : Arrow ℓ'} {C : Arrow ℓ''}
  → ArrowHom A B → ArrowHom B C
  → ArrowHom A C
compArrowHom f g x .fst = g (f x .fst) .fst
compArrowHom f g x .snd y = g (f x .fst) .snd (f x .snd y)

-- identity
idArrowHom : {A : Arrow ℓ} → ArrowHom A A
idArrowHom x .fst = x
idArrowHom x .snd = idfun _

-- Associativity holds by refl
compArrowAssoc : {A : Arrow ℓ}
  {B : Arrow ℓ'} {C : Arrow ℓ''} {D : Arrow ℓ'''}
  (f : ArrowHom A B) (g : ArrowHom B C) (h : ArrowHom C D)
  → compArrowHom {A = A} {B} {D} f (compArrowHom {A = B} {C} {D} g h)
  ≡ compArrowHom {A = A} {C} {D} (compArrowHom {A = A} {B} {C} f g) h
compArrowAssoc f g h = refl

-- as a wild cat
ArrowWildCat : (ℓ : Level) → WildCat (ℓ-suc ℓ) ℓ
ArrowWildCat ℓ .ob = Arrow ℓ
ArrowWildCat ℓ .Hom[_,_] = ArrowHom
ArrowWildCat ℓ .WildCat.id = idArrowHom
ArrowWildCat ℓ ._⋆_ = compArrowHom
ArrowWildCat ℓ .⋆IdL f = refl
ArrowWildCat ℓ .⋆IdR f = refl
ArrowWildCat ℓ .⋆Assoc f g h = refl

-- Embedding of pointed types into arrow cat
Pointed→Arrow : Pointed ℓ → Arrow ℓ
Pointed→Arrow A .fst = fst A
Pointed→Arrow A .snd a = snd A ≡ a

-- This induces an iso on hom types
Iso-→∙-ArrowHom : {A : Pointed ℓ} {B : Pointed ℓ'}
  → Iso (A →∙ B) (ArrowHom (Pointed→Arrow A) (Pointed→Arrow B))
Iso-→∙-ArrowHom {A = A} {B} .Iso.fun f x .fst = fst f x
Iso-→∙-ArrowHom {A = A} {B} .Iso.fun f x .snd q = sym (snd f) ∙ cong (fst f) q
Iso-→∙-ArrowHom {A = A} {B} .Iso.inv f .fst x = f x .fst
Iso-→∙-ArrowHom {A = A} {B} .Iso.inv f .snd = sym (f (A .snd) .snd refl)
Iso-→∙-ArrowHom {A = A} {B} .Iso.rightInv f =
  funExt (λ x → ΣPathP (refl , (funExt
    (J (λ x q → (λ i → f (A .snd) .snd (λ _ → snd A) i)
               ∙ (λ i → f (q i) .fst)
               ≡ f x .snd q) (sym (rUnit _))))))
Iso-→∙-ArrowHom {A = A} {B} .Iso.leftInv f =
  ΣPathP (refl , cong sym (sym (rUnit (sym (snd f)))))

-- Definition of 'loop spaces' (these with Ω on image of Pointed→Arrow)
ΩArrow : Arrow ℓ → Arrow ℓ
ΩArrow (B , P) .fst = Σ[ x ∈ B ] P x × (x ≡ x)
ΩArrow (B , P) .snd (b , p , q) = refl ≡ q

-- Functoriality
ΩArrow→ : {A : Arrow ℓ} {B : Arrow ℓ'}
  → ArrowHom A B
  → ArrowHom (ΩArrow A) (ΩArrow B)
ΩArrow→ f (t , s , q) .fst .fst = f t .fst
ΩArrow→ f (t , s , q) .fst .snd .fst = f t .snd s
ΩArrow→ f (t , s , q) .fst .snd .snd i = f (q i) .fst
ΩArrow→ f (t , s , q) .snd r i j = f (r i j) .fst

Iso-ΩArrow-Ω : ∀ {ℓ} (A : Pointed ℓ)
  → Iso (ΩArrow (Pointed→Arrow A) .fst) (Pointed→Arrow (Ω A) .fst)
Iso-ΩArrow-Ω A .Iso.fun (_ , q , p) = q ∙∙ p ∙∙ sym q
Iso-ΩArrow-Ω A .Iso.inv p = (pt A) , (refl , p)
Iso-ΩArrow-Ω A .Iso.rightInv p = sym (rUnit p)
Iso-ΩArrow-Ω A .Iso.leftInv (_ , q , p) =
  ΣPathP (q , ΣPathP ((λ i j → q (i ∧ j))
    , symP (doubleCompPath-filler q p (sym q))))

ArrowHomΩ : {B : Pointed ℓ}
  → ArrowHom (ΩArrow (Pointed→Arrow B)) (Pointed→Arrow (Ω B))
ArrowHomΩ {B = B} (b , p , q) .fst = p ∙∙ q ∙∙ sym p
ArrowHomΩ {B = B} (b , p , q) .snd r =
  sym (∙∙lCancel (sym p)) ∙ cong (p ∙∙_∙∙ sym p) r

ArrowHomΩ← : {B : Pointed ℓ}
  → ArrowHom (Pointed→Arrow (Ω B)) (ΩArrow (Pointed→Arrow B))
ArrowHomΩ← {B = B}  p .fst = (pt B) , (refl , p)
ArrowHomΩ← {B = B} p .snd q = q

ΩArrow→-presComp : {A : Arrow ℓ} {B : Arrow ℓ'} {C : Arrow ℓ''}
  (f : ArrowHom A B) (g : ArrowHom B C)
  → ΩArrow→ (compArrowHom f g)
   ≡ compArrowHom (ΩArrow→ f) (ΩArrow→ g)
ΩArrow→-presComp f g = refl

Iso-→∙-ArrowHom-presΩ : ∀ {ℓ} (A B : Pointed ℓ) (f : A →∙ B)
  → ΩArrow→ (Iso.fun Iso-→∙-ArrowHom f)
   ≡ compArrowHom (compArrowHom ArrowHomΩ
                                (Iso.fun Iso-→∙-ArrowHom (Ω→ f)))
                  ArrowHomΩ←
Iso-→∙-ArrowHom-presΩ A B f = funExt (uncurry λ a
  → uncurry (J (λ a x → (y : a ≡ a) →
      ΩArrow→ (Iso.fun Iso-→∙-ArrowHom f) (a , x , y) ≡
      compArrowHom
      (compArrowHom ArrowHomΩ (Iso.fun Iso-→∙-ArrowHom (Ω→ f)))
      ArrowHomΩ← (a , x , y))
      λ q → ΣPathP ((ΣPathP ((snd f)
           , ΣPathP ((sym (rUnit _) ◁ (λ i j → snd f (~ j ∨ i)))
           , (doubleCompPath-filler (sym (snd f)) (cong (fst f) q) (snd f)
           ▷ cong₃ _∙∙_∙∙_ refl (cong (cong (fst f)) (rUnit q) ) refl))))
           , funExt (lem (fst f) _ (snd f) q))))
  where
  lem : ∀ {ℓ} {B : Type ℓ} (f : fst A → B) (b : B) (fp : f (pt A) ≡ b)
              (q : pt A ≡ pt A) (x : refl ≡ q)
    → SquareP (λ i j → fp i ≡ fp i)
              (λ i j → f (x i j))
              (sym (∙∙lCancel fp)
              ∙ cong (sym fp ∙∙_∙∙ fp)
                     (cong (cong f)
                      (rUnit refl ∙ cong₃ _∙∙_∙∙_ refl x refl)))
              (λ i _ → fp i)
              (doubleCompPath-filler (sym fp) (cong f q) fp
              ▷ cong (λ q → sym fp ∙∙ cong f q ∙∙ fp) (rUnit q))
  lem f = J> (J> compPathL→PathP ((λ i → lUnit (lUnit (rUnit refl
    ∙ cong (λ q → sym refl ∙∙ cong f q ∙∙ refl) (rUnit refl)) (~ i)) (~ i))
    ∙ cong₂ _∙_ refl (cong (cong (λ p → refl ∙∙ p ∙∙ refl))
        (cong (cong (cong f)) (rUnit (rUnit refl))))))

-- Ω as a wild functor
ΩArrowFunctor : WildFunctor (ArrowWildCat ℓ) (ArrowWildCat ℓ)
ΩArrowFunctor .F-ob = ΩArrow
ΩArrowFunctor .F-hom = ΩArrow→
ΩArrowFunctor .F-id = refl
ΩArrowFunctor .F-seq f g = refl



open import Cubical.Foundations.Pointed
module _ (ℓA ℓB : Level) where
  ∙Tripl : Type (ℓ-suc (ℓ-max ℓA ℓB))
  ∙Tripl = Σ[ A ∈ Pointed ℓA ] Σ[ B ∈ Pointed ℓB ] (A →∙ B)

module _ (ℓA ℓB : Level) where
  ∙Tripl' : Type (ℓ-suc (ℓ-max ℓA ℓB))
  ∙Tripl' = Σ[ A ∈ Pointed ℓA ] Σ[ B ∈ Type ℓB ] (typ A → B)

  Tripl* : Type (ℓ-suc (ℓ-max ℓA ℓB))
  Tripl* = Σ[ B ∈ Type ℓB ] Σ[ P ∈ (B → Type ℓA) ]
            (Σ B P → Type (ℓ-max ℓA ℓB))

  

  Tripl** : Type (ℓ-suc (ℓ-max ℓA ℓB))
  Tripl** = {!!}

  Iso-Tripl-Tripl' : Iso (∙Tripl ℓA ℓB) ∙Tripl'
  Iso-Tripl-Tripl' .Iso.fun (A , B , f) = A , fst B , fst f
  Iso-Tripl-Tripl' .Iso.inv (A , BB , f) = A , (BB , f (pt A)) , f , refl
  Iso-Tripl-Tripl' .Iso.rightInv _ = refl
  Iso-Tripl-Tripl' .Iso.leftInv (A , B , f) i .fst = A
  Iso-Tripl-Tripl' .Iso.leftInv (A , B , f) i .snd .fst .fst = fst B
  Iso-Tripl-Tripl' .Iso.leftInv (A , B , f) i .snd .fst .snd = snd f i
  Iso-Tripl-Tripl' .Iso.leftInv (A , B , f) i .snd .snd .fst = fst f
  Iso-Tripl-Tripl' .Iso.leftInv (A , B , f) i .snd .snd .snd j = snd f (i ∧ j)

module _ {ℓA ℓB ℓA' ℓB' : Level} where
  ∙TriplHom : ∙Tripl ℓA ℓB → ∙Tripl ℓA' ℓB' → Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓA' ℓB'))
  ∙TriplHom (A , B , f) (A' , B' , g) = Σ[ α ∈ A →∙ A' ] Σ[ β ∈ B →∙ B' ] (β ∘∙ f) ≡ (g ∘∙ α)

  ∙TriplHom* : Tripl* ℓA ℓB → Tripl* ℓA' ℓB' → Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓA' ℓB'))
  ∙TriplHom* (B , A , ptA) (B' , A' , ptB) =
    Σ[ f ∈ (B → B') ] Σ[ h ∈ ((b : B) → A b → A' (f b)) ]
      ((b : B) (a : A b) → ptA (b , a) → ptB ((f b) , h b a))

ΣSquareP : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y z w : Σ A B}
  {p : x ≡ y} {q : z ≡ w} {l : x ≡ z} {r : y ≡ w}
  → Σ[ P ∈ Square (cong fst p) (cong fst q) (cong fst l) (cong fst r)]
            SquareP (λ i j → B (P i j))
                    (cong snd p) (cong snd q) (cong snd l) (cong snd r)
  → Square p q l r
ΣSquareP (p , q) i j .fst = p i j
ΣSquareP (p , q) i j .snd = q i j

-- (A : U) × (B : U) × (A → B)


module _ {ℓA ℓB ℓA' ℓB' : Level} where
  -- ∙TriplHom'' : ∙Tripl' ℓA ℓB → ∙Tripl' ℓA' ℓB' → Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓA' ℓB'))
  -- ∙TriplHom'' (A , B , f) (A' , B' , g) =
  --   Σ[ α ∈ A →∙ A' ] Σ[ β ∈ (B → B') ] Σ[ βpt ∈ β (f (pt A)) ≡ g (pt A') ]
  --     Σ[ h ∈ ((x : typ A) → β (f x) ≡ g (fst α x)) ] βpt ≡ h (pt A) ∙ cong g (snd α)

  ∙TriplHom' : ∙Tripl' ℓA ℓB → ∙Tripl' ℓA' ℓB'
    → Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓA' ℓB'))
  ∙TriplHom' (A , B , f) (A' , B' , g) =
    Σ[ α ∈ A →∙ A' ] Σ[ β ∈ (B → B') ]
      (((x : typ A) → β (f x) ≡ g (fst α x)))

  ∙TriplHomS : ∙Tripl' ℓA ℓB → ∙Tripl' ℓA' ℓB'
    → Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓA' ℓB'))
  ∙TriplHomS (A , B , f) (A' , B' , g) = {!!}

  Iso-TriplHom* : (A : ∙Tripl' ℓA ℓB) (B : ∙Tripl' ℓA' ℓB')
    → Iso (∙TriplHom (Iso.inv (Iso-Tripl-Tripl' _ _) A)
                      (Iso.inv (Iso-Tripl-Tripl' _ _) B))
           (∙TriplHom' A B)
  Iso-TriplHom* A B = Σ-cong-iso-snd λ f → compIso
    Σ-assoc-Iso (Σ-cong-iso-snd λ g
      → compIso (Σ-cong-iso-snd (λ gp
        → invIso ΣPathIsoPathΣ))
          (compIso (invIso Σ-assoc-Iso)
            (compIso
              (Σ-cong-iso-fst Σ-swap-Iso)
              (compIso Σ-assoc-Iso
                (compIso
                  (Σ-cong-iso (iso funExt⁻ funExt (λ _ → refl) (λ _ → refl))
                    λ q → compIso (Σ-cong-iso-snd
                     λ p → Cubical.Foundations.Transport.pathToIso
                        (cong₂ (PathP (λ i → q i (A .fst .snd)
                                            ≡ B .snd .snd (pt (B .fst))))
                               (sym (lUnit p))
                               (sym (rUnit _))
                       ∙ (λ j → Square p
                                     (compPath-filler'
                                        (funExt⁻ q (pt (fst A)))
                                        (λ i → snd (snd B) (snd f i)) j)
                                     (λ i → q (~ j ∧ i) (pt (fst A))) refl)
                       ∙ isoToPath symIso))
                            (isContr→Iso (isContrSingl
                              (funExt⁻ q (pt (fst A))
                              ∙ cong (snd (snd B)) (snd f)))
                              isContrUnit))
                  rUnit×Iso)))))
    where
    open import Cubical.Data.Unit
    open import Cubical.Foundations.Transport

  test' : (A : ∙Tripl' ℓA ℓB) (B : ∙Tripl' ℓA' ℓB') (t : _)
    → Iso.fun (Iso-TriplHom* A B) t
     ≡ (fst t , fst (snd t .fst) , funExt⁻ (cong fst (snd (snd t))))
  test' A B t = refl

--   Iso-TriplHom A B .Iso.fun (f , g , h) = f , ((fst g) , (λ x i → h i .fst x))
--   Iso-TriplHom A B .Iso.inv (f , g , h) .fst = f
--   Iso-TriplHom A B .Iso.inv (f , g , h) .snd .fst .fst = g
--   Iso-TriplHom A B .Iso.inv (f , g , h) .snd .fst .snd = h (pt (fst A)) ∙ cong (B .snd .snd) (snd f)
--   Iso-TriplHom A B .Iso.inv (f , g , h) .snd .snd =
--     ΣPathP ((funExt h) , (sym (lUnit _)
--     ◁ symP (compPath-filler' (h (pt (fst A))) (cong (B .snd .snd) (snd f))) ▷ rUnit _))
--   -- f , (g , h (pt (fst A)) ∙ cong (B .snd .snd) (snd f)) , ΣPathP ((funExt h) , {!!})
--   Iso-TriplHom A B .Iso.rightInv (f , g , h) = refl
--   Iso-TriplHom A B .Iso.leftInv (f , g , h) = ΣPathP (refl ,
--     ΣPathP (ΣPathP (refl
--     , sym (PathP→compPathR∙∙ {!r!}))
--     , ΣSquareP (refl
--     , {!transport (doubleCompPath≡compPath refl _ _)!})))
--     where -- lUnit (snd g) ◁ cong snd h ▷ sym (rUnit ?)
--     r = lUnit (snd g) ◁ cong snd h ▷ sym (rUnit (cong (B .snd .snd) (snd f)))
--     rrr = PathP≡doubleCompPathʳ

-- -- -- module _ {ℓA ℓB ℓA' ℓB' : Level} where
-- -- --   ∙TriplHom : ∙Tripl ℓA ℓB → ∙Tripl ℓA' ℓB' → Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓA' ℓB'))
-- -- --   ∙TriplHom (A , B , f) (A' , B' , g) = Σ[ α ∈ A →∙ A' ] Σ[ β ∈ B →∙ B' ] (β ∘∙ f) ≡ (g ∘∙ α)

-- -- module _ {ℓA ℓB ℓA' ℓB' ℓA'' ℓB'' : Level} where
-- --   compTriplHom : (T1 : ∙Tripl ℓA ℓB) (T2 : ∙Tripl ℓA' ℓB') (T3 : ∙Tripl ℓA'' ℓB'')
-- --     → ∙TriplHom T1 T2 → ∙TriplHom T2 T3
-- --     → ∙TriplHom T1 T3
-- --   compTriplHom (A , B , f) (A' , B' , g) (A'' , B'' , h) (α , β , t) (α' , β' , t') .fst = α' ∘∙ α
-- --   compTriplHom (A , B , f) (A' , B' , g) (A'' , B'' , h) (α , β , t) (α' , β' , t') .snd .fst = β' ∘∙ β
-- --   compTriplHom (A , B , f) (A' , B' , g) (A'' , B'' , h) (α , β , t) (α' , β' , t') .snd .snd =
-- --     ∘∙-assoc β' β f
-- --     ∙ cong (β' ∘∙_) t
-- --     ∙ sym (∘∙-assoc β' g α)
-- --     ∙ cong (_∘∙ α) t'
-- --     ∙ ∘∙-assoc h α' α

-- --   compTriplHom' : (T1 : ∙Tripl' ℓA ℓB) (T2 : ∙Tripl' ℓA' ℓB') (T3 : ∙Tripl' ℓA'' ℓB'')
-- --     → ∙TriplHom' T1 T2 → ∙TriplHom' T2 T3
-- --     → ∙TriplHom' T1 T3
-- --   compTriplHom' (A , B , f) (A' , B' , g) (A'' , B'' , h) (α , β , t) (α' , β' , t') .fst = α' ∘∙ α
-- --   compTriplHom' (A , B , f) (A' , B' , g) (A'' , B'' , h) (α , β , t) (α' , β' , t') .snd .fst x = β' (β x)
-- --   compTriplHom' (A , B , f) (A' , B' , g) (A'' , B'' , h) (α , β , t) (α' , β' , t') .snd .snd x = cong β' (t x) ∙ t' (α .fst x)

-- -- module _ {ℓA ℓB ℓA' ℓB' ℓA'' ℓB'' ℓA''' ℓB''' : Level} where
-- --   compTriplAssoc' : (T1 : ∙Tripl' ℓA ℓB) (T2 : ∙Tripl' ℓA' ℓB') (T3 : ∙Tripl' ℓA'' ℓB'') (T4 : ∙Tripl' ℓA''' ℓB''')
-- --     (F : ∙TriplHom' T1 T2) (G : ∙TriplHom' T2 T3) (H : ∙TriplHom' T3 T4)
-- --     → compTriplHom' T1 T2 T4 F (compTriplHom' T2 T3 T4 G H)
-- --      ≡ compTriplHom' T1 T3 T4 (compTriplHom' T1 T2 T3 F G) H
-- --   compTriplAssoc' T1 T2 T3 T4 (α , β , t) (α' , β' , t') (α'' , β'' , t'') = ΣPathP (∘∙-assoc α''  α' α
-- --    , ΣPathP (refl , funExt λ a
-- --      → assoc (λ i → β'' (β' (t a i))) (λ i → β'' (t' (α .fst a) i)) (t'' (α' .fst (α .fst a)))
-- --       ∙ cong₂ _∙_ (sym (cong-∙ β'' (cong β' (t a)) (t' (α .fst a)))) refl))



-- -- Penta : ∀ {ℓ} {A : Type ℓ} {x y z w t : A} (b : x ≡ y) (bl : x ≡ z)
-- --   (br : y ≡ w) (tl : z ≡ t) (tr : w ≡ t) → Type ℓ
-- -- Penta {z = z} {w = w} b bl br tl tr = Σ[ edge ∈ z ≡ w ] (Square edge tl refl tr × Square b edge bl br)

-- -- PentaDep : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ'} {x y z w t : A}
-- --   {x' : B x} {y' : B y} {z' : B z} {w' : B w} {t' : B t}
-- --   {b : x ≡ y} {bl : x ≡ z} {br : y ≡ w} {tl : z ≡ t} {tr : w ≡ t}
-- --   (b' : PathP (λ i → B (b i)) x' y')
-- --   (bl' : PathP (λ i → B (bl i)) x' z')
-- --   (br' : PathP (λ i → B (br i)) y' w')
-- --   (tl' : PathP (λ i → B (tl i)) z' t')
-- --   (tr' : PathP (λ i → B (tr i)) w' t')
-- --   → Penta b bl br tl tr
-- --    → Type _
-- -- PentaDep {B = B} {z' = z'} {w' = w'} b' bl' br' tl' tr' pent =
-- --   Σ[ edge ∈ PathP (λ j → B (pent .fst j)) z' w' ]
-- --     (SquareP (λ i j → B (pent .snd .fst i j)) edge tl' (λ _ → z') tr'
-- --     × SquareP (λ i j → B (pent .snd .snd i j)) b' edge bl' br')

-- -- PentaΣ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y z w t : Σ A B} {b : x ≡ y} {bl : x ≡ z}
-- --   {br : y ≡ w} {tl : z ≡ t} {tr : w ≡ t}
-- --   → (p1 : Penta (cong fst b) (cong fst bl) (cong fst br) (cong fst tl) (cong fst tr))
-- --   → PentaDep {B = B} (cong snd b) (cong snd bl) (cong snd br) (cong snd tl) (cong snd tr) p1
-- --   → Penta b bl br tl tr
-- -- PentaΣ p1 pd .fst = ΣPathP ((fst p1) , fst pd)
-- -- PentaΣ p1 pd .snd .fst i j .fst = p1 .snd .fst i j
-- -- PentaΣ p1 pd .snd .fst i j .snd = pd .snd .fst i j
-- -- PentaΣ p1 pd .snd .snd i j .fst = p1 .snd .snd i j
-- -- PentaΣ p1 pd .snd .snd i j .snd = pd .snd .snd i j

-- -- module _ {ℓA ℓB ℓA' ℓB' ℓA'' ℓB'' ℓA''' ℓB''' ℓA'''' ℓB'''' : Level}
-- --   (T1 : ∙Tripl' ℓA ℓB) (T2 : ∙Tripl' ℓA' ℓB') (T3 : ∙Tripl' ℓA'' ℓB'') (T4 : ∙Tripl' ℓA''' ℓB''') (T5 : ∙Tripl' ℓA'''' ℓB'''')
-- --     (F : ∙TriplHom' T1 T2) (G : ∙TriplHom' T2 T3) (H : ∙TriplHom' T3 T4) (J : ∙TriplHom' T4 T5)
-- --     where
-- --   pentagon : Penta (sym (compTriplAssoc' T1 T2 T4 T5 F (compTriplHom' T2 T3 T4 G H) J))
-- --                    (cong (λ L → compTriplHom' T1 T4 T5 L J) (compTriplAssoc' T1 T2 T3 T4 F G H))
-- --                    (cong (compTriplHom' T1 T2 T5 F) (sym (compTriplAssoc' T2 T3 T4 T5 G H J)))
-- --                    (sym (compTriplAssoc' T1 T3 T4 T5 (compTriplHom' T1 T2 T3 F G) H J))
-- --                    (compTriplAssoc' T1 T2 T3 T5 F G (compTriplHom' T3 T4 T5 H J))
-- --   pentagon = PentaΣ (PentaΣ (refl , (refl , refl))
-- --                     {!!})
-- --                     (PentaΣ (refl , (refl , refl))
-- --                     {!!})

-- -- {-
-- -- pentagonHom : WildCat ℓ ℓ' → Type _
-- -- pentagonHom C = {a b c d e : ob}
-- --   (f : Hom[ a , b ]) (g : Hom[ b , c ]) (h : Hom[ c , d ]) (j : Hom[ d , e ])
-- --   → Square (cong (_⋆ j) (⋆Assoc f g h) ∙ ⋆Assoc f (g ⋆ h) j)
-- --            (⋆Assoc f g (h ⋆ j))
-- --            (⋆Assoc (f ⋆ g) h j)
-- --            (cong (f ⋆_) (⋆Assoc g h j))
-- -- -}
