{-

  Homotopy colimits of graphs

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Colimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Graph

{-
-- Cones under a diagram

record Cocone ℓ {ℓd ℓv ℓe} {I : Graph ℓv ℓe} (F : Diag ℓd I) (X : Type ℓ)
              : Type (ℓ-suc (ℓ-max ℓ (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc ℓd)))) where
  field
    leg : ∀ (j : Obj I) → F $ j → X
    com : ∀ {j k} (f : Hom I j k) → leg k ∘ F <$> f ≡ leg j

  postcomp : ∀ {ℓ'} {Y : Type ℓ'} → (X → Y) → Cocone ℓ' F Y
  leg (postcomp h) j = h ∘ leg j
  com (postcomp h) f = cong (h ∘_) (com f)

open Cocone public


-- Σ (Type ℓ) (Cocone ℓ F) forms a category:

module _ {ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} where

  private
    -- the "lower star" functor
    _* : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} → (X → Y) → Cocone _ F X → Cocone _ F Y
    (h *) C = postcomp C h

  CoconeMor : ∀ {ℓ ℓ'} → Σ (Type ℓ) (Cocone ℓ F) → Σ (Type ℓ') (Cocone ℓ' F) → Type _
  CoconeMor (X , C) (Y , D) = Σ[ h ∈ (X → Y) ] (h *) C ≡ D

  idCoconeMor : ∀ {ℓ} (Cp : Σ (Type ℓ) (Cocone ℓ F)) → CoconeMor Cp Cp
  idCoconeMor Cp = (λ x → x) , refl

  compCoconeMor : ∀ {ℓ ℓ' ℓ''} {C : Σ (Type ℓ) (Cocone ℓ F)} {D : Σ (Type ℓ') (Cocone ℓ' F)}
                    {E : Σ (Type ℓ'') (Cocone ℓ'' F)}
                  → CoconeMor D E → CoconeMor C D → CoconeMor C E
  compCoconeMor (g , q) (f , p) = g ∘ f , (cong (g *) p) ∙ q


-- Universal cocones are initial objects in the category Σ (Type ℓ) (Cocone ℓ F)

module _ {ℓ ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} {X : Type ℓ} where

  isUniversalAt : ∀ ℓq → Cocone ℓ F X → Type (ℓ-max ℓ (ℓ-suc (ℓ-max ℓq (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc ℓd)))))
  isUniversalAt ℓq C = ∀ (Y : Type ℓq) → isEquiv {A = (X → Y)} {B = Cocone ℓq F Y} (postcomp C)
                  -- (unfolding isEquiv, this ^ is equivalent to what one might expect:)
                  -- ∀ (Y : Type ℓ) (D : Cocone ℓ F Y) → ∃![ h ∈ (X → Y) ] (h *) C ≡ D
                  --                                  (≡ isContr (CoconeMor (X , C) (Y , D)))

  isPropIsUniversalAt : ∀ ℓq (C : Cocone ℓ F X) → isProp (isUniversalAt ℓq C)
  isPropIsUniversalAt ℓq C = isPropΠ (λ Y → isPropIsEquiv (postcomp C))

  isUniversal : Cocone ℓ F X → Typeω
  isUniversal C = ∀ ℓq → isUniversalAt ℓq C


-- Colimits are universal cocones

record isColimit {ℓ ℓd ℓv ℓe} {I : Graph ℓv ℓe} (F : Diag ℓd I) (X : Type ℓ) : Typeω where
  field
    cone : Cocone ℓ F X
    univ : isUniversal cone
open isColimit public

module _ {ℓ ℓ' ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} {X : Type ℓ} {Y : Type ℓ'} where

  postcomp⁻¹ : isColimit F X → Cocone ℓ' F Y → (X → Y)
  postcomp⁻¹ cl = invEq (_ , univ cl _ Y)

  postcomp⁻¹-inv : (cl : isColimit F X) (D : Cocone ℓ' F Y) → (postcomp (cone cl) (postcomp⁻¹ cl D)) ≡ D
  postcomp⁻¹-inv cl D = retEq (_ , univ cl _ Y) D

  postcomp⁻¹-mor : (cl : isColimit F X) (D : Cocone ℓ' F Y) → CoconeMor (X , cone cl) (Y , D)
  postcomp⁻¹-mor cl D = (postcomp⁻¹ cl D) , (postcomp⁻¹-inv cl D)

-- Colimits are unique

module _ {ℓ ℓ' ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} {X : Type ℓ} {Y : Type ℓ'} where

  uniqColimit : isColimit F X → isColimit F Y → X ≃ Y
  uniqColimit cl cl'
    = isoToEquiv (iso (fst fwd) (fst bwd)
                      (λ x i → fst (isContr→isProp (equiv-proof (univ cl' ℓ' Y) (cone cl'))
                                                   (compCoconeMor fwd bwd)
                                                   (idCoconeMor (Y , cone cl')) i) x)
                      (λ x i → fst (isContr→isProp (equiv-proof (univ cl ℓ  X) (cone cl))
                                                   (compCoconeMor bwd fwd)
                                                   (idCoconeMor (X , cone cl)) i) x))
    where fwd : CoconeMor (X , cone cl ) (Y , cone cl')
          bwd : CoconeMor (Y , cone cl') (X , cone cl )
          fwd = postcomp⁻¹-mor cl (cone cl')
          bwd = postcomp⁻¹-mor cl' (cone cl)

-- Colimits always exist

data colim {ℓd ℓe ℓv} {I : Graph ℓv ℓe} (F : Diag ℓd I) : Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc ℓd))) where
  colim-leg : ∀ (j : Obj I) → F $ j → colim F
  colim-com : ∀ {j k} (f : Hom I j k) → colim-leg k ∘ F <$> f ≡ colim-leg j

module _ {ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} where

  colimCone : Cocone _ F (colim F)
  leg colimCone = colim-leg
  com colimCone = colim-com

  rec : ∀ {ℓ} {X : Type ℓ} → Cocone ℓ F X → (colim F → X)
  rec C (colim-leg j A)   = leg C j A
  rec C (colim-com f i A) = com C f i A

  colimIsColimit : isColimit F (colim F)
  cone colimIsColimit = colimCone
  univ colimIsColimit ℓq Y
    = isoToIsEquiv record { fun = postcomp colimCone
                          ; inv = rec
                          ; rightInv = λ C → refl
                          ; leftInv  = λ h → funExt (eq h) }
    where eq : ∀ h (x : colim _) → rec (postcomp colimCone h) x ≡ h x
          eq h (colim-leg j A)   = refl
          eq h (colim-com f i A) = refl

-}



---
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Sn
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.HITs.Truncation.FromNegOne renaming (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.Empty

record Graph2 {ℓ ℓ'} : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  field
    Obj2 : Type ℓ
    Fam : Obj2 → Obj2 → Type ℓ' -- condition on arrows

open Graph2
record Diagram {ℓ ℓ' ℓ''} (G : Graph2 {ℓ} {ℓ'}) : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') ℓ'')) where
  no-eta-equality
  field
    Types : Obj2 G → Type ℓ''
    Funs : (x y : Obj2 G) → (Fam G x y) → Types x → Types y

open Diagram

data Colim2 {ℓ ℓ' ℓ''} (G : Graph2 {ℓ} {ℓ'}) (d : Diagram {ℓ'' = ℓ''} G) : Type (ℓ-suc (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') ℓ''))) where
 inc : (x : Obj2 G) → Types d x → Colim2 G d
 inc≡ : (x y : Obj2 G) (γ : Fam G x y) (a : Types d x) → inc y (Funs d x y γ a) ≡ inc x a

2×Graph :  ∀ {ℓ ℓ'} (G : Graph2 {ℓ} {ℓ'}) → Graph2
Obj2 (2×Graph G) = Obj2 G ⊎ Obj2 G
Fam (2×Graph G) (inl x) (inl x₁) = Fam G x x₁
Fam (2×Graph G) (inl x) (inr x₁) = Fam G x x₁
Fam (2×Graph G) (inr x) (inl x₁) = Fam G x x₁
Fam (2×Graph G) (inr x) (inr x₁) = Fam G x x₁

2×Dia : ∀ {ℓ ℓ' ℓ''} (G : Graph2 {ℓ} {ℓ'}) (d d' : Diagram {ℓ'' = ℓ''} G) → Diagram (2×Graph G)
Types (2×Dia G d d') (inl x) = Types d x
Types (2×Dia G d d') (inr x) = Types d' x
Funs (2×Dia G d d') (inl x) (inl x₁) = Funs d x x₁
Funs (2×Dia G d d') (inl x) (inr x₁) z = {!!}
Funs (2×Dia G d d') (inr x) y _ = {!!}

module _ {ℓ ℓ'} {A : ℕ → Type ℓ} {B : ℕ → Type ℓ} (F : (n : ℕ) → A n → B n) (Afam : (n : ℕ) → A n → A (suc n)) (Bfam : (n : ℕ) → B n → B (suc n)) (comm : (n : ℕ) → Bfam n ∘ F n ≡ F (suc n) ∘ Afam n) where
  theGraph : Graph2
  Obj2 theGraph = ℕ × Bool -- true = left, false = right
  Fam theGraph (n , false) (m , false) = suc n ≡ m
  Fam theGraph (n , true) (m , false) = n ≡ m
  Fam theGraph (n , false) (m , true) = ⊥
  Fam theGraph (n , true) (m , true) = suc n ≡ m

  theDiag : Diagram theGraph
  Types theDiag (n , false) = B n
  Types theDiag (n , true) = A n
  Funs theDiag (n , false) (m , false) p x = subst B p (Bfam n x)
  Funs theDiag (n , true) (m , false) p x = subst B p (F n x)
  Funs theDiag (n , true) (m , true) p x = subst A p (Afam n x)

  mainGraph : Graph2
  Obj2 mainGraph = ℕ
  Fam mainGraph n m = suc n ≡ m

  diagL : Diagram mainGraph
  Types diagL = A
  Funs diagL x y p a = subst A p (Afam x a)

  diagR : Diagram mainGraph
  Types diagR = B
  Funs diagR x y p b = subst B p (Bfam x b)

  indFun : Colim2 mainGraph diagL → Colim2 mainGraph diagR
  indFun (inc x x₁) = inc x (F x x₁)
  indFun (inc≡ x y γ a i) = helper γ i
    where
    helper : (γ : suc x ≡ y) → Path (Colim2 mainGraph diagR) (inc y (F y (subst A γ (Afam x a)))) (inc x (F x a))
    helper = J (λ y γ →  Path (Colim2 mainGraph diagR) (inc y (F y (subst A γ (Afam x a)))) (inc x (F x a)))
               ((λ i → inc (suc x) (F (suc x) (transportRefl (Afam x a) i)))
             ∙∙ (λ i → inc (suc x) (comm x (~ i) a))
             ∙∙ ((λ i → inc (suc x) (transportRefl (Bfam x (F x a)) (~ i)))
             ∙ inc≡ x (suc x) refl (F x a)))

  colim→Prop : ∀ {ℓ ℓ' ℓ'' ℓ'''} → {G : Graph2 {ℓ} {ℓ'}} {d : Diagram {ℓ'' = ℓ''} G}
             → {P : Colim2 G d → Type ℓ'''}
             → ((x : Colim2 G d) → isProp (P x))
             → ((x : Obj2 G) (y : Types d x) → P (inc x y))
             → (x : Colim2 G d) → P x
  colim→Prop {P = P} h indhyp (inc x x₁) = indhyp x x₁
  colim→Prop  {G = G} {d = d} {P = P} h indhyp (inc≡ x y γ a i) =
    isProp→PathP {B = λ i → P (inc≡ x y γ a i)} (λ i → h _) (indhyp y (Funs d x y γ a)) (indhyp x a) i

  connectedIndFun : (n : ℕ) → ((m : ℕ) → isConnectedFun n (F m)) → isConnectedFun n indFun
  connectedIndFun zero iscon = λ _ → tt* , (λ {tt* → refl})
  connectedIndFun (suc zero) iscon = 
    colim→Prop (λ _ → isPropIsContr)
               λ n b → trRec {!!} (λ fibpt → ∣ (inc n (fibpt .fst)) , (cong (inc n) (fibpt .snd)) ∣ , (λ _ → isOfHLevelTrunc {A = fiber indFun (inc n b)} 1 _ _)) (iscon n b .fst)
  connectedIndFun (suc (suc n)) iscon = {!!}

colimDiag : ∀ {ℓ ℓ' ℓ''} (G : Graph2 {ℓ} {ℓ'}) (d d' : Diagram {ℓ'' = ℓ''} G) → Diagram {!!}
Types (colimDiag G d d') x = {!!}
Funs (colimDiag G d d') = {!!}

colimIndFun : ∀ {ℓ ℓ' ℓ''} (G : Graph2 {ℓ} {ℓ'}) (d d' : Diagram {ℓ'' = ℓ''} G)
              → (x y : Obj2 G) (z : Fam G x y)
              → Colim2 {!!} {!!}
colimIndFun = {!!}
 
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence
open import Cubical.HITs.Susp

data James {ℓ} (A : Pointed ℓ) : Type ℓ where
  € : James A
  α : typ A → James A → James A
  δ : (x : James A) → x ≡ α (pt A) x 

natδ : ∀ {ℓ} {A : Pointed ℓ} → (x : James A) → Path (Path (James A) _ _) (cong (α (pt A)) (δ x)) (δ (α (pt A) x))
natδ {A = (A , a)} x = {!!}
{-
mainlemma : ∀ {ℓ} {A : Pointed ℓ} → isConnected 2 (typ A) → Iso (James A) (Path (Susp (typ A)) north north)
mainlemma {ℓ} {A = A , a} con = {!!}
  where
  IsoJam : (x : A) → isEquiv (α {A = (A , a)} x)
  IsoJam x = trRec (isPropIsEquiv _)
                   (λ r → subst (λ x → isEquiv (α x)) r
                           (subst isEquiv (funExt δ) (idIsEquiv (James _))) )
                   (Iso.fun (PathIdTruncIso 1)
                            (isOfHLevelSuc 0 con ∣ a ∣ ∣ x ∣))
  
  open import Cubical.HITs.Pushout
  open import Cubical.HITs.Pushout.Flattening

  PushA : Type _
  PushA = Pushout {A = A} (λ _ → tt) (λ _ → tt)

  Codes : PushA → Type ℓ
  Codes (inl x) = James (A , a)
  Codes (inr x) = James (A , a)
  Codes (push x i) = ua ((α x) , IsoJam x) i

  isContrTotal : isContr (Σ[ x ∈ PushA ] Codes x)
  isContrTotal = ((inl tt) , €)
                , {!!}

  open import Cubical.HITs.S2 

  testS2 : Iso (hLevelTrunc 4 (James (S² , base))) (hLevelTrunc 4 S²)
  Iso.fun testS2 = trRec (isOfHLevelTrunc 4) λ {€ → ∣ base ∣ ; (α s x) → ∣ s ∣ ; (δ € i) → ∣ base ∣ ; (δ (α base x) i) → ∣ base ∣ ; (δ (α (surf j k) x) i) → {!!} ; (δ (δ € j) i) → {!!} ; (δ (δ (α base x) j) i) → {!!} ; (δ (δ (α (surf j k) x) l) m) → {!!} ; (δ (δ (δ x i) j) k) → {!!}}
    where
    testi : (x : James (hLevelTrunc 4 S² , ∣ base ∣)) → PathP {!!} {!!} {!!}
    testi = {!!}
  Iso.inv testS2 = trRec (isOfHLevelTrunc 4) λ {base → ∣ € ∣
                                ; (surf i j) → hcomp (λ k → λ {(i = i0) → ∣ δ € (~ k) ∣ ; (i = i1) → ∣ δ € (~ k) ∣ ; (j = i0) → ∣ δ € (~ k) ∣ ; (j = i1) → ∣ δ € (~ k) ∣})
                                                      ∣ (α (surf i j) €) ∣}
  Iso.rightInv testS2 = {!!}
  Iso.leftInv testS2 = {!!}

    where

    αcurry : A × James (A , a) → James (A , a)
    αcurry (a , c) = α a c



    T : Type ℓ
    T = Pushout {A = A × James (A , a)} snd αcurry

    T=James : Iso _ _
    T=James = (FlatteningLemma.FlattenIso.isom {A = A} (λ _ → tt) (λ _ → tt) (λ _ → James (A , a)) (λ _ → James (A , a)) (λ x → (α x) , IsoJam x))

    T≡JamesREAL : Iso (Σ PushA Codes) T
    T≡JamesREAL = compIso lIso (compIso T=James rIso)
      where
      lIso : Iso _ _
      Iso.fun lIso (inl x , b) = (inl x) , b
      Iso.fun lIso (inr x , b) = (inr x) , b
      Iso.fun lIso (push a i , b) = push a i , b
      Iso.inv lIso (inl x , b) = inl x , b
      Iso.inv lIso (inr x , b) = inr x , b
      Iso.inv lIso (push a i , b) = push a i , b
      Iso.rightInv lIso (inl x , b) = refl
      Iso.rightInv lIso (inr x , b) = refl
      Iso.rightInv lIso (push a i , b) = refl
      Iso.leftInv lIso (inl x , b) = refl
      Iso.leftInv lIso (inr x , b) = refl
      Iso.leftInv lIso (push a i , b) = refl

      rIso : Iso _ _
      Iso.fun rIso (inl x) = inl (snd x)
      Iso.fun rIso (inr x) = inr (snd x)
      Iso.fun rIso (push (a , b) i) = push (a , b) i
      Iso.inv rIso (inl x) = inl (tt , x)
      Iso.inv rIso (inr x) = inr (tt , x)
      Iso.inv rIso (push a i) = push a i
      Iso.rightInv rIso (inl x) = refl
      Iso.rightInv rIso (inr x) = refl
      Iso.rightInv rIso (push a i) = refl
      Iso.leftInv rIso (inl x) = refl
      Iso.leftInv rIso (inr x) = refl
      Iso.leftInv rIso (push a i) = refl

    TPathHelp : (x : James (A , a)) → Path T (inl x) (inl €)
    TPathHelp € = refl
    TPathHelp (α x x₁) = ((push (a , α x x₁) ∙∙ (λ i → inr (δ (α x x₁) (~ i))) ∙∙ sym (push (x , x₁)))) ∙ TPathHelp x₁
    TPathHelp (δ x i) j = hcomp (λ k → λ { (i = i0) → TPathHelp x (j ∧ k)
                     ; (j = i0) → inl (δ x i)
                     ; (j = i1) → TPathHelp x k})
                     (hcomp (λ k → λ { (i = i0) → inl (δ x (~ j ∧ ~ k))
                                     ; (i = i1) → (push (a , α a x) ∙∙ (λ i → inr (δ (α a x) (~ i))) ∙∙ sym (push (a , x))) j
                                     ; (j = i0) → inl (δ x (i ∨ ~ k))
                                     ; (j = i1) → inl x})
                                            (help (~ i) j))

      where
      help : Path (Path T _ _)
         (push (a , α a x)
         ∙∙ (λ i → inr (δ (α a x) (~ i)))
        ∙∙ sym (push (a , x)))
        (λ i → inl (δ x (~ i)))
      help = {!!}

    TPath : (x : T) → x ≡ inl €
    TPath (inl x) = TPathHelp x
    TPath (inr x) = ((λ i → inr (δ x i)) ∙ sym (push (a , x))) ∙ TPathHelp x
    TPath (push (b , x) j) i = 
      hcomp (λ k → λ { (i = i0) → push (b , x) j
                     ; (j = i1) → {!compPath-filler ((λ i → inr (δ x i)) ∙ sym (push (a , x))) (TPathHelp x)!}
                     ; (j = i0) → TPathHelp x (i ∧ k)
                     ; (i = i1) → TPathHelp x k})
            {!!}
-}
{-
j = i0 ⊢ TPathHelp x i
j = i1 ⊢ ((λ i₁ → inr (δ (αcurry (a , x)) i₁)) ∙∙
          (λ i₁ → push (a₁ , αcurry (a , x)) (~ i₁)) ∙∙
          ((push (a₁ , α a x) ∙∙ (λ i₁ → inr (δ (α a x) (~ i₁))) ∙∙
            (λ i₁ → push (a , x) (~ i₁)))
           ∙ TPathHelp x))
         i
i = i0 ⊢ push (a , x) j
i = i1 ⊢ inl €
-}

open import Cubical.HITs.S2

J=S1 : Iso (hLevelTrunc 3 (James (S¹ , base))) (hLevelTrunc 3 (S¹))
J=S1 = {!trRec (isOfHLevelTrunc 3) theFun!}
  where
  module _ where
  indPrincGroupoid : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'}
                     → (isOfHLevel 3 B)
                     → (€c : B)
                     → (αc : ((x : typ A) (y : James A) → B))
                     → (δ€ : Path B €c (αc (pt A) €))
                     → (δα : ((x : typ A) (y : James A) → Path B (αc x y) (αc (pt A) (α x y))))
                     → (δδ€ : PathP (λ i → Path B (δ€ i) (αc (pt A) (δ € i))) δ€ (δα (pt A) €))
                     → (δδα : ((x : typ A) (y : James A) → PathP (λ i → Path B (δα x y i) (δα (pt A) (α x y) i)) (δα x y) λ i₁ → αc (pt A) (δ (α x y) i₁)))
                     → (x : James A) → B
  indPrincGroupoid hlev €c αc δ€ δα δδ€ δδα € = €c
  indPrincGroupoid hlev €c αc δ€ δα δδ€ δδα (α x x₁) = αc x x₁
  indPrincGroupoid hlev €c αc δ€ δα δδ€ δδα (δ € i) = δ€ i
  indPrincGroupoid hlev €c αc δ€ δα δδ€ δδα (δ (α x x₁) i) = δα x x₁ i
  indPrincGroupoid hlev €c αc δ€ δα δδ€ δδα (δ (δ € i₁) i) = δδ€ i₁ i -- δδ€ i₁ i
  indPrincGroupoid hlev €c αc δ€ δα δδ€ δδα (δ (δ (α x x₁) i₁) i) = δδα x x₁ i i₁
  indPrincGroupoid {A = A} {B = B} hlev €c αc δ€ δα δδ€ δδα (δ (δ (δ x i₂) i₁) i) = {!isOfHLevel→isOfHLevelDep 3 {A = James A} {B = λ _ → B}  !}

  theFun : (James (S¹ , base)) → S¹
  theFun € = base
  theFun (α base x₁) = theFun x₁
  theFun (α (loop i) €) = loop (~ i)
  theFun (α (loop i) (α base x₁)) = theFun (α (loop i) x₁)
  theFun (α (loop i) (α (loop i₁) x₁)) = {!!}
  theFun (α (loop i) (δ € i₁)) = {!!}
  theFun (α (loop i) (δ (α base €) i₁)) = {!!}
  theFun (α (loop i) (δ (α base (α x x₁)) i₁)) = {!!}
  theFun (α (loop i) (δ (α base (δ x₁ i₂)) i₁)) = {!!}
  theFun (α (loop i) (δ (α (loop i₂) x₁) i₁)) = {!!} -- not needed
  theFun (α (loop i) (δ (δ x₁ i₂) i₁)) = {!!} -- not needed
  theFun (δ x i) = theFun x

-- J=S2 : Iso (hLevelTrunc 4 (James (S² , base))) (hLevelTrunc 4 (S²))
-- Iso.fun J=S2 = {!trRec (isOfHLevelTrunc 4) theFun!}
--   module _ where
--   theFun : (James (S² , base)) → (hLevelTrunc 4 (S²))
--   theFun € = ∣ base ∣
--   theFun (α base y) = ∣ base ∣
--   theFun (α (surf i i₁) €) = ∣ base ∣
--   theFun (α (surf i i₁) (α base y)) = ∣ base ∣
--   theFun (α (surf i i₁) (α (surf i₂ i₃) y)) = ∣ base ∣
--   theFun (α (surf i i₁) (δ € i₂)) = ∣ base ∣
--   theFun (α (surf i i₁) (δ (α x y) i₂)) = {!!}
--   theFun (α (surf i i₁) (δ (δ y i₃) i₂)) = {!!}
--   theFun (δ € i) = ∣ base ∣
--   theFun (δ (α x x₁) i) = {!!} -- theFun (α x x₁)
--   theFun (δ (δ € i₁) i) = ∣ base ∣
--   theFun (δ (δ (α base €) i₁) i) = {!!}
--   theFun (δ (δ (α (surf i₂ i₃) €) i₁) i) = {!!}
--   theFun (δ (δ (α x (α x₁ x₂)) i₁) i) = {!!}
--   theFun (δ (δ (α x (δ x₁ i₂)) i₁) i) = {!!}
--   theFun (δ (δ (δ x i₂) i₁) i) = {!!}
-- Iso.inv J=S2 = {!!}
-- Iso.rightInv J=S2 = {!!}
-- Iso.leftInv J=S2 = {!!}


-- -- J=S2 : Iso (hLevelTrunc 4 (James (S² , base))) (hLevelTrunc 4 (S²))
-- -- Iso.fun J=S2 = trRec (isOfHLevelTrunc 4) theFun
-- --   module _ where
-- --   theFun : (James (S² , base)) → (hLevelTrunc 4 (S²))
-- --   theFun € = ∣ base ∣
-- --   theFun (α x €) = ∣ x ∣
-- --   theFun (α base (α x₁ y)) = theFun (α x₁ y)
-- --   theFun (α (surf i i₁) (α base y)) = theFun (α (surf i i₁) y)
-- --   theFun (α (surf i i₁) (α (surf i₂ i₃) y)) = {!!}
-- --   theFun (α base (δ y i)) = theFun (α base y) -- theFun (α base y)
-- --   theFun (α (surf i₁ i₂) (δ € i)) = ∣ surf i₁ i₂ ∣
-- --   theFun (α (surf i₁ i₂) (δ (α base y) i)) = theFun (α (surf i₁ i₂) y)
-- --   theFun (α (surf i₁ i₂) (δ (α (surf i₃ i₄) y) i)) = {!!}
-- --   theFun (α (surf i₁ i₂) (δ (δ y i₃) i)) = {!!}
-- --   theFun (δ € i) = ∣ base ∣
-- --   theFun (δ (α x x₁) i) = theFun (α x x₁)
-- --   theFun (δ (δ € i₁) i) = ∣ base ∣
-- --   theFun (δ (δ (α x x₁) i₁) i) = theFun (α x x₁)
-- --   theFun (δ (δ (δ € i₂) i₁) i) = ∣ base ∣
-- --   theFun (δ (δ (δ (α x x₁) i₂) i₁) i) = theFun (α x x₁)
-- --   theFun (δ (δ (δ (δ x i₃) i₂) i₁) i) = {!!}
-- -- Iso.inv J=S2 = trMap λ {base → α base € ; (surf i j) → α (surf i j) €} 
-- -- Iso.rightInv J=S2 = trElim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _) help
-- --   where
-- --   help : (x : S²) → Iso.fun J=S2 (Iso.inv J=S2 ∣ x ∣) ≡ ∣ x ∣
-- --   help base j = ∣ base ∣
-- --   help (surf i i₁) k = ∣ surf i i₁ ∣
-- -- Iso.leftInv J=S2 x = {!x!}
-- --   where
-- --   stupidAgda : (x : James (S² , base)) → Iso.inv J=S2 (Iso.fun J=S2 ∣ α base x ∣) ≡ ∣ α base x ∣
-- --   stupidAgda € = {!!}
-- --   stupidAgda (α base x₁) = {!λ i → ∣ δ (α base x₁) i ∣!} -- stupidAgda x₁ ∙ λ i → ∣ δ (α base x₁) i ∣
-- --   stupidAgda (α (surf i i₁) €) = {!!}
-- --   stupidAgda (α (surf i i₁) (α x x₁)) = {!!}
-- --   stupidAgda (α (surf i i₁) (δ x₁ i₂)) = {!!}
-- --   stupidAgda (δ x i) = {!!}
  
-- --   help : (x : James (S² , base)) → Iso.inv J=S2 (Iso.fun J=S2 ∣ x ∣) ≡ ∣ x ∣
-- --   help € i = ∣ δ € (~ i) ∣
-- --   help (α base €) = refl
-- --   help (α base (α x x₁)) = help (α x x₁) ∙ λ i → ∣ δ (α x x₁) i ∣ --  λ i → ∣ δ (α x x₁) i ∣ -- λ i → ∣ δ (α base x₁) i ∣
-- --   help (α base (δ € i)) j =
-- --     hcomp (λ k → λ { (i = i0) → ∣ α base € ∣
-- --                    ; (i = i1) → ((λ _ → ∣ α base € ∣) ∙ (λ i₁ → ∣ δ (α (pt (S² , base)) €) i₁ ∣)) (j ∨ ~ k)
-- --                    ; (j = i0) → ((λ _ → ∣ α base € ∣) ∙ (λ i₁ → ∣ δ (α (pt (S² , base)) €) i₁ ∣)) (i ∧ ~ k)
-- --                    ; (j = i1) → ∣ α base (δ € i) ∣})
-- --             (testi j i) -- compPath-filler refl (λ i → ∣ α base (δ € i) ∣) i j
-- --     where
-- --     open import Cubical.Foundations.GroupoidLaws

-- --     testi : Path (Path (hLevelTrunc 4 (James (S² , base))) _ _) (refl ∙ (λ i₁ → ∣ δ (α base €) i₁ ∣)) λ i → ∣ α base (δ € i) ∣
-- --     testi = sym (lUnit _) ∙ λ i j → ∣ natδ € (~ i) j ∣

-- --   help (α base (δ (α base x₁) i)) j = {!!} {-hcomp (λ k → λ { (i = i0) → (help (α base x₁) ∙ (λ i₁ → ∣ δ (α base x₁) i₁ ∣)) j
-- --                                                       ; (j = i0) → Iso.inv J=S2 (theFun (δ (α base x₁) i))
-- --                                                       ; (j = i1) → ∣ natδ € (i ∨ k) {!i ∧ k!} ∣})
-- --                                              {!!} -}

-- --   help (α base (δ (α (surf i₁ i₂) x₁) i)) j = {!∣ α base (δ (α base x₁) i) ∣!} -- not needed
-- --   help (α base (δ (δ € i₁) i)) j = {!!}
-- --   help (α base (δ (δ (α base x₁) i₁) i)) j = {!!}
-- --   help (α base (δ (δ (α (surf i₂ i₃) x₁) i₁) i)) j = {!!} -- not needed
-- --   help (α base (δ (δ (δ x₁ i₂) i₁) i)) j = {!!} -- not needed
-- --   help (α (surf i i₁) €) = refl
-- --   help (α (surf i i₁) (α base x₁)) = {!!}
-- --   help (α (surf i i₁) (α (surf i₂ i₃) x₁)) = {!!} -- not needed
-- --   help (α (surf i i₁) (δ x₁ i₂)) = {!!} -- not needed
-- --   help (δ € i) j = ∣ δ € (~ j ∨ i) ∣
-- --   help (δ (α base x₁) i) j = {!!}
-- --   help (δ (α (surf i₁ i₂) x₁) i) = {!!} -- not needed
-- --   help (δ (δ € i₁) i) j = {!!}
-- --   help (δ (δ (α base x₁) i₁) i) j = {!!}
-- --   help (δ (δ (α (surf i₂ i₃) x₁) i₁) i) = {!!} -- not needed
-- --   help (δ (δ (δ x i₂) i₁) i) = {!!} -- not needed

-- -- -- J=S2' : Iso (hLevelTrunc 4 (James (S₊ 2 , north))) (hLevelTrunc 4 (S₊ 2))
-- -- -- Iso.fun J=S2' = trRec {!!} {!!}
-- -- --   where
-- -- --   theFun : (James (S₊ 2 , north)) → (hLevelTrunc 4 (S₊ 2))
-- -- --   theFun € = ∣ north ∣
-- -- --   theFun (α x €) = {!!}
-- -- --   theFun (α x (α x₁ y)) = {!!}
-- -- --   theFun (α x (δ y i)) = {!!}
-- -- --   theFun (δ x i) = {!!}
-- -- -- Iso.inv J=S2' = {!!}
-- -- -- Iso.rightInv J=S2' = {!!}
-- -- -- Iso.leftInv J=S2' = {!!}
