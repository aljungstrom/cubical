{-

Freudenthal suspension theorem

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Homotopy.Freudenthal where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation.FromNegOne as Trunc renaming (rec to trRec ; elim to trElim)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.SmashProduct

open import Cubical.HITs.S1 hiding (encode)
open import Cubical.HITs.Sn
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.Pushout
open import Cubical.HITs.Pushout.Flattening

{-
myProof : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → Iso (hLevelTrunc (2 + n) A) (S₊ (suc n) → hLevelTrunc (2 + n) A) 
Iso.fun (myProof zero) x = λ _ → x
Iso.inv (myProof zero) x = x base
Iso.rightInv (myProof zero) f = funExt λ x → sym (spoke f base) ∙ spoke f x
Iso.leftInv (myProof zero) x = refl
myProof (suc n) = {!!}

test2 : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → Iso (hLevelTrunc (4 + n) (S₊ (2 + n))) (S₊ (3 + n) → hLevelTrunc (4 + n) (Path (S₊ (3 + n)) north south))
Iso.fun (test2 n) = trElim {!!} λ a x → ∣ merid a ∣
Iso.inv (test2 n) f = {!f north!}
Iso.rightInv (test2 n) = {!!}
Iso.leftInv (test2 n) = {!!}
  where
  test3 : Iso (S₊ (3 + n) → hLevelTrunc (4 + n) (Path (S₊ (3 + n)) north north))
              ((x : S₊ (3 + n)) → hLevelTrunc (4 + n) (Path (S₊ (3 + n)) north x))
  Iso.fun test3 f north = f north
  Iso.fun test3 f south = subst (λ x → hLevelTrunc (4 + n) (Path (S₊ (3 + n)) north x)) (merid north) (f south)
  Iso.fun test3 f (merid a i) = {!!}
  Iso.inv test3 = {!!}
  Iso.rightInv test3 = {!!}
  Iso.leftInv test3 = {!!}
    where
    helperIso : Iso ((x : S₊ (3 + n)) → hLevelTrunc (4 + n) (Path (S₊ (3 + n)) north x))
                    (Σ[ p ∈ hLevelTrunc (4 + n) (Path (S₊ (3 + n)) north north) ]
                     Σ[ q ∈ hLevelTrunc (4 + n) (Path (S₊ (3 + n)) north south) ]
                     ((a : S₊ (2 + n)) → PathP (λ i → hLevelTrunc (4 + n) (north ≡ (merid a i))) p q))
    Iso.fun helperIso f = (f north) , ((f south) , (λ a i → f (merid a i)))
    Iso.inv helperIso (fn , fs , fm) north = fn
    Iso.inv helperIso (fn , fs , fm) south = fs
    Iso.inv helperIso (fn , fs , fm) (merid a i) = fm a i
    Iso.rightInv helperIso (fn , fs , fm) = ΣPathP (refl , (ΣPathP (refl , refl)))
    Iso.leftInv helperIso f = funExt λ {north → refl ; south → refl ; (merid a i) → refl}
-}
{-
Code' : (n : ℕ) → S₊ (3 + n) → Type₀
Code' n north = S₊ (2 + n)
Code' n south = S₊ (2 + n)
Code' n (merid a i) = ua (isoToEquiv help) i
  where
  tihi : S₊ (2 + n) → S₊ (2 + n)
  tihi north = north
  tihi south = south -- south
  tihi (merid a i) = {!!} -- (merid a ∙ (sym (merid (pt (S₊∙ (suc n)))))) i
  tihiId : (x : S₊ (2 + n)) → tihi (tihi x) ≡ x
  tihiId north = refl -- refl
  tihiId south = {!!} -- merid (pt (S₊∙ (suc n))) -- refl
  tihiId (merid a i) j = {!compPath-filler ? ? j i!} -- refl
  help : Iso (Code' n north) (Code' n south)
  Iso.fun help = tihi
  Iso.inv help = tihi
  Iso.rightInv help = tihiId
  Iso.leftInv help = tihiId

  tihi2 : {!!}
  tihi2 = {!!}


i = i0 ⊢ north
i = i1 ⊢ merid north j
j = i0 ⊢ north
j = i1 ⊢ merid a i
-}

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
                .equiv-proof ∣ fib ∣)))
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
                                         (suspToPropRec (pt A) (λ _ → isOfHLevelTrunc 2 _ _)
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
