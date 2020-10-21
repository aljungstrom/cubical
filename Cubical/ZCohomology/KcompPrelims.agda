{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.KcompPrelims where

open import Cubical.ZCohomology.Base
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Hopf
open import Cubical.Homotopy.Freudenthal hiding (encode)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec ; map to trMap)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.Data.Int renaming (_+_ to +Int)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Unit

open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification
open import Cubical.Data.Prod.Base
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Bool
open import Cubical.Data.Sum.Base
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.HITs.S3

private
  variable
    ℓ : Level
    A : Type ℓ

{- We want to prove that Kn≃ΩKn+1. For this we use the map ϕ-}

ϕ : (pt a : A) → typ (Ω (Susp A , north))
ϕ pt a = (merid a) ∙ sym (merid pt)

private
  d-map : typ (Ω ((Susp S¹) , north)) → S¹
  d-map p = subst HopfSuspS¹ p base

  d-mapId : (r : S¹) → d-map (ϕ base r) ≡ r
  d-mapId r = substComposite HopfSuspS¹ (merid r) (sym (merid base)) base ∙
              rotLemma r
    where
    rotLemma : (r : S¹) → r · base ≡ r
    rotLemma base = refl
    rotLemma (loop i) = refl

sphereConnectedSpecCase : isConnected 4 (Susp (Susp S¹))
sphereConnectedSpecCase = sphereConnected 3

d-mapComp : Iso (fiber d-map base) (Path (S₊ 3) north north)
d-mapComp = compIso (IsoΣPathTransportPathΣ {B = HopfSuspS¹} _ _)
                     (congIso (invIso IsoS³TotalHopf))

is1Connected-dmap : isConnectedFun 3 d-map
is1Connected-dmap = toPropElim (λ _ → isPropIsOfHLevel 0)
                               (isConnectedRetractFromIso 3 d-mapComp
                                 (isOfHLevelRetractFromIso 0 (invIso (PathIdTruncIso 3))
                                              contrHelper))
  where
  contrHelper : isContr (Path (∥ Susp (Susp S¹) ∥ 4) ∣ north ∣ ∣ north ∣)
  fst contrHelper = refl
  snd contrHelper = isOfHLevelPlus {n = 0} 2 (sphereConnected 3) ∣ north ∣ ∣ north ∣ refl

d-Iso : Iso (∥ Path (S₊ 2) north north ∥ 3) (coHomK 1)
d-Iso = connectedTruncIso _ d-map is1Connected-dmap

d-mapId2 : Iso.fun d-Iso ∘ trMap (ϕ base) ≡ idfun (coHomK 1)
d-mapId2 = funExt (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) λ a i → ∣ d-mapId a i ∣)

Iso∥ϕ₁∥ : Iso (coHomK 1) (∥ Path (S₊ 2) north north ∥ 3)
Iso∥ϕ₁∥ = composesToId→Iso d-Iso (trMap (ϕ base)) d-mapId2

--- the maps
private
  helper : (n : ℕ) → n + (4 + n) ≡ 2 + (n + (2 + n))
  helper n = +-suc n (3 + n) ∙ (λ i → suc (+-suc n (2 + n) i))

  anIso : (n : ℕ) → Iso (coHomK (2 + n)) (loopSpaceK (2 + n))
  anIso n = (connectedTruncIso2 (4 + n) _ (ϕ north) (n , helper n)
            (isConnectedσ (suc n) (sphereConnected _)))

private
  Kn→ΩKn+1 : (n : ℕ) → coHomK n → loopSpaceK n
  Kn→ΩKn+1 zero a = intLoop a
  Kn→ΩKn+1 (suc zero) =  trMap (ϕ base)
  Kn→ΩKn+1 (suc (suc n)) = trMap (ϕ north)

  ΩKn+1→Kn : (n : ℕ) → loopSpaceK n → coHomK n
  ΩKn+1→Kn zero = winding
  ΩKn+1→Kn (suc zero) = Iso.inv Iso∥ϕ₁∥
  ΩKn+1→Kn (suc (suc n)) = Iso.inv (stabSpheres-n≥2 n)

  ΩKn+1→Kn→ΩKn+1 : (n : ℕ) → (x : loopSpaceK n) → Kn→ΩKn+1 n (ΩKn+1→Kn n x) ≡ x
  ΩKn+1→Kn→ΩKn+1 zero = decodeEncode base
  ΩKn+1→Kn→ΩKn+1 (suc zero) = Iso.rightInv Iso∥ϕ₁∥
  ΩKn+1→Kn→ΩKn+1 (suc (suc n)) = Iso.rightInv (stabSpheres-n≥2 n)

  Kn→ΩKn+1→Kn : (n : ℕ) → (x : coHomK n) → ΩKn+1→Kn n (Kn→ΩKn+1 n x) ≡ x
  Kn→ΩKn+1→Kn zero = windingIntLoop
  Kn→ΩKn+1→Kn (suc zero) = Iso.leftInv Iso∥ϕ₁∥
  Kn→ΩKn+1→Kn (suc (suc n)) = Iso.leftInv (stabSpheres-n≥2 n)

Iso-Kn-ΩKn+1 : (n : HLevel) → Iso (coHomK n) (loopSpaceK n)
Iso.fun (Iso-Kn-ΩKn+1 n) = Kn→ΩKn+1 n
Iso.inv (Iso-Kn-ΩKn+1 n) = ΩKn+1→Kn n
Iso.rightInv (Iso-Kn-ΩKn+1 n) = ΩKn+1→Kn→ΩKn+1 n
Iso.leftInv (Iso-Kn-ΩKn+1 n) = Kn→ΩKn+1→Kn n
