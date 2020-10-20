{-

Freudenthal suspension theorem

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Homotopy.Freudenthal where

open import Cubical.Foundations.Everything
-- open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec ; elim to trElim)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.SmashProduct

open import Cubical.HITs.S1 hiding (encode)
open import Cubical.HITs.Sn
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.Foundations.Equiv.HalfAdjoint


module _ (n : HLevel) where
  σS : S₊ (2 + n) → typ (Ω (S₊∙ (3 + n)))
  σS a = merid a ∙ merid north ⁻¹

  S2+n = S₊ (2 + n)
  S3+n = S₊ (3 + n)
  4n+2 = (2 + n) + (2 + n)

  module WC-S (p : north ≡ north) where
    P : (a b : S₊ (2 + n)) → Type₀
    P a b = σS b ≡ p → hLevelTrunc 4n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p)

    hLevelP : (a b : S₊ (2 + n)) → isOfHLevel 4n+2 (P a b)
    hLevelP _ _ = isOfHLevelΠ 4n+2 λ _ → isOfHLevelTrunc 4n+2

    leftFun : (a : S₊ (2 + n)) → P a north
    leftFun a r = ∣ a , (rCancel' (merid a) ∙ rCancel' (merid north) ⁻¹) ∙ r ∣

    rightFun : (b : S₊ (2 + n)) → P north b
    rightFun b r = ∣ b , r ∣

    funsAgree : leftFun north ≡ rightFun north
    funsAgree =
      funExt λ r →
        cong′ (λ w → ∣ north , w ∣)
          (cong (_∙ r) (rCancel' (rCancel' (merid north)))
           ∙ lUnit r ⁻¹)

    totalFun : (a b : S2+n) → P a b
    totalFun =  hLevelS2'' (suc n) (suc n) hLevelP rightFun leftFun funsAgree .fst

    rightId : totalFun north ≡ rightFun
    rightId = refl

    leftId : (λ x → totalFun x north) ≡ leftFun
    leftId x i = hLevelS2'' (suc n) (suc n) hLevelP rightFun leftFun funsAgree .snd .snd i x

  fwdS : (p : north ≡ north) (a : S2+n)
    → hLevelTrunc 4n+2 (fiber σS p)
    → hLevelTrunc 4n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p)
  fwdS p a = Trunc.rec (isOfHLevelTrunc 4n+2) (uncurry (WC-S.totalFun p a))

  fwdSnorth : (p : north ≡ north) → fwdS p north ≡ idfun _
  fwdSnorth p = funExt (trElim (λ _ → isOfHLevelPath 4n+2 (isOfHLevelTrunc 4n+2) _ _)
                      λ p → refl)

  isEquivFwdS : (p : north ≡ north) (a : S2+n) → isEquiv (fwdS p a)
  isEquivFwdS p =
    suspToPropElim (ptSn (suc n))
                   (λ _ → isPropIsEquiv _)
                   helper
    where
    helper : isEquiv (fwdS p north)
    helper = subst isEquiv (sym (fwdSnorth p)) (idIsEquiv _)

  interpolateS : (a : S2+n)
          → PathP (λ i → S2+n → north ≡ merid a i) (λ x → merid x ∙ merid a ⁻¹) merid
  interpolateS a i x j = compPath-filler (merid x) (merid a ⁻¹) (~ i) j

  CodeS : (y : Susp S2+n) → north ≡ y → Type₀
  CodeS north p = hLevelTrunc 4n+2 (fiber σS p)
  CodeS south q = hLevelTrunc 4n+2 (fiber merid q)
  CodeS (merid a i) p =
    Glue
      (hLevelTrunc 4n+2 (fiber (interpolateS a i) p))
      (λ
        { (i = i0) → _ , (fwdS p a , isEquivFwdS p a)
        ; (i = i1) → _ , idEquiv _
        })

  encodeS : (y : S3+n) (p : north ≡ y) → CodeS y p
  encodeS y = J CodeS ∣ north , rCancel' (merid north) ∣

  encodeMeridS : (a : S2+n) → encodeS south (merid a) ≡ ∣ a , refl ∣
  encodeMeridS a =
    cong (transport (λ i → gluePath i))
      (funExt⁻ (funExt⁻ (WC-S.leftId refl) a) _ ∙ λ i → ∣ a , lem (rCancel' (merid a)) (rCancel' (merid north)) i ∣)
    ∙ transport (PathP≡Path gluePath _ _)
      (λ i → ∣ a , (λ j k → rCancel-filler' (merid a) i j k) ∣)
    where
    gluePath : I → Type _
    gluePath i = hLevelTrunc 4n+2 (fiber (interpolateS a i) (λ j → merid a (i ∧ j)))

    lem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y) → (p ∙ q ⁻¹) ∙ q ≡ p
    lem p q = assoc p (q ⁻¹) q ⁻¹ ∙ cong (p ∙_) (lCancel q) ∙ rUnit p ⁻¹

  contractCodeSouthS : (p : north ≡ south) (c : CodeS south p) → encodeS south p ≡ c
  contractCodeSouthS p =
    Trunc.elim
      (λ _ → isOfHLevelPath 4n+2 (isOfHLevelTrunc 4n+2) _ _)
      (uncurry λ a →
        J (λ p r → encodeS south p ≡ ∣ a , r ∣) (encodeMeridS a))

  isConnectedMeridS : isConnectedFun 4n+2 (merid {A = S2+n})
  isConnectedMeridS p = encodeS south p , contractCodeSouthS p

  isConnectedσS : isConnectedFun 4n+2 σS
  isConnectedσS =
    transport (λ i → isConnectedFun 4n+2 (interpolateS north (~ i))) isConnectedMeridS
  

module _ {ℓ} (n : HLevel) {A : Pointed ℓ} (connA : isConnected (suc (suc n)) (typ A)) where

  σ : typ A → typ (Ω (∙Susp (typ A)))
  σ a = merid a ∙ merid (pt A) ⁻¹

  private
    2n+2 = suc n + suc n

    module WC (p : north ≡ north) =
      WedgeConnectivity (suc n) (suc n) A connA A connA
        (λ a b →
          ( (σ b ≡ p → hLevelTrunc 2n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p))
          , isOfHLevelΠ 2n+2 λ _ → isOfHLevelTrunc 2n+2
          ))
        (λ a r → ∣ a , (rCancel' (merid a) ∙ rCancel' (merid (pt A)) ⁻¹) ∙ r ∣)
        (λ b r → ∣ b , r ∣)
        (funExt λ r →
          cong′ (λ w → ∣ pt A , w ∣)
            (cong (_∙ r) (rCancel' (rCancel' (merid (pt A))))
              ∙ lUnit r ⁻¹))

    fwd : (p : north ≡ north) (a : typ A)
      → hLevelTrunc 2n+2 (fiber σ p)
      → hLevelTrunc 2n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p)
    fwd p a = Trunc.rec (isOfHLevelTrunc 2n+2) (uncurry (WC.extension p a))

    isEquivFwd : (p : north ≡ north) (a : typ A) → isEquiv (fwd p a)
    isEquivFwd p a .equiv-proof =
      elim.isEquivPrecompose (λ _ → pt A) (suc n)
        (λ a →
          ( (∀ t → isContr (fiber (fwd p a) t))
          , isProp→isOfHLevelSuc n (isPropΠ λ _ → isPropIsContr)
          ))

        (isConnectedPoint (suc n) connA (pt A))
        .equiv-proof
        (λ _ → Trunc.elim
          (λ _ → isProp→isOfHLevelSuc (n + suc n) isPropIsContr)
         (λ fib →
            subst (λ k → isContr (fiber k ∣ fib ∣))
              (cong (Trunc.rec (isOfHLevelTrunc 2n+2) ∘ uncurry)
                (funExt (WC.right p) ⁻¹))
              (subst isEquiv
                (funExt (Trunc.mapId) ⁻¹)
                (idIsEquiv _)
                .equiv-proof ∣ fib ∣)
             ))
        .fst .fst a

    interpolate : (a : typ A)
      → PathP (λ i → typ A → north ≡ merid a i) (λ x → merid x ∙ merid a ⁻¹) merid
    interpolate a i x j = compPath-filler (merid x) (merid a ⁻¹) (~ i) j

  Code : (y : Susp (typ A)) → north ≡ y → Type ℓ
  Code north p = hLevelTrunc 2n+2 (fiber σ p)
  Code south q = hLevelTrunc 2n+2 (fiber merid q)
  Code (merid a i) p =
    Glue
      (hLevelTrunc 2n+2 (fiber (interpolate a i) p))
      (λ
        { (i = i0) → _ , (fwd p a , isEquivFwd p a)
        ; (i = i1) → _ , idEquiv _
        })

  encode : (y : Susp (typ A)) (p : north ≡ y) → Code y p
  encode y = J Code ∣ pt A , rCancel' (merid (pt A)) ∣

  encodeMerid : (a : typ A) → encode south (merid a) ≡ ∣ a , refl ∣
  encodeMerid a =
    cong (transport (λ i → gluePath i))
      (funExt⁻ (WC.left refl a) _ ∙ λ i → ∣ a , lem (rCancel' (merid a)) (rCancel' (merid (pt A))) i ∣)
    ∙ transport (PathP≡Path gluePath _ _)
      (λ i → ∣ a , (λ j k → rCancel-filler' (merid a) i j k) ∣)
    where
    gluePath : I → Type _
    gluePath i = hLevelTrunc 2n+2 (fiber (interpolate a i) (λ j → merid a (i ∧ j)))

    lem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y) → (p ∙ q ⁻¹) ∙ q ≡ p
    lem p q = assoc p (q ⁻¹) q ⁻¹ ∙ cong (p ∙_) (lCancel q) ∙ rUnit p ⁻¹

  contractCodeSouth : (p : north ≡ south) (c : Code south p) → encode south p ≡ c
  contractCodeSouth p =
    Trunc.elim
      (λ _ → isOfHLevelPath 2n+2 (isOfHLevelTrunc 2n+2) _ _)
      (uncurry λ a →
        J (λ p r → encode south p ≡ ∣ a , r ∣) (encodeMerid a))

  isConnectedMerid : isConnectedFun 2n+2 (merid {A = typ A})
  isConnectedMerid p = encode south p , contractCodeSouth p

  isConnectedσ : isConnectedFun 2n+2 σ
  isConnectedσ =
    transport (λ i → isConnectedFun 2n+2 (interpolate (pt A) (~ i))) isConnectedMerid

isConn→isConnSusp : ∀ {ℓ} {A : Pointed ℓ} → isConnected 2 (typ A) → isConnected 2 (Susp (typ A))
isConn→isConnSusp {A = A} iscon = ∣ north ∣
                                , trElim (λ _ → isOfHLevelSuc 1 (isOfHLevelTrunc 2 _ _))
                                         (suspToPropElim (pt A) (λ _ → isOfHLevelTrunc 2 _ _)
                                         refl)

FreudenthalEquiv : ∀ {ℓ} (n : HLevel) (A : Pointed ℓ)
                → isConnected (2 + n) (typ A)
                → hLevelTrunc ((suc n) + (suc n)) (typ A)
                 ≃ hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north)))
FreudenthalEquiv n A iscon = connectedTruncEquiv _
                                                 (σ n {A = A} iscon)
                                                 (isConnectedσ _ iscon)
FreudenthalIso : ∀ {ℓ} (n : HLevel) (A : Pointed ℓ)
                → isConnected (2 + n) (typ A)
                → Iso (hLevelTrunc ((suc n) + (suc n)) (typ A))
                      (hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north))))
FreudenthalIso n A iscon = connectedTruncIso _ (σ n {A = A} iscon) (isConnectedσ _ iscon)
