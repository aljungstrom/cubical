{-

Freudenthal suspension theorem

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Homotopy.Freudenthal where

open import Cubical.Foundations.Everything
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation.FromNegOne as Trunc renaming (rec to trRec ; elim to trElim)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.S1 hiding (encode)
open import Cubical.HITs.Sn


incP : ∀ n m → S₊ (suc n) → typ (Ω (S₊∙ (suc (suc (m + n)))))
incP zero zero x = merid x ∙ sym (merid base)
incP zero (suc m) x = (λ i → merid (incP zero m x i) i) ∙ sym (merid north)
incP (suc n) zero x = merid x ∙ sym (merid north)
incP (suc n) (suc m) x = (λ i → merid (incP (suc n) m x i) i) ∙ sym (merid north)

test15 : (n : ℕ) → Iso (∥ Σ[ f ∈ ( S₊ 1  → S₊ (suc (suc n))) ] f base ≡ north ∥ (3 + n)) (Σ[ f ∈ ∥ (S₊ 1 → S₊ (suc (suc n))) ∥ (3 + n) ] (∥ Trunc.map (λ g → g base) f ≡ ∣ north ∣  ∥ (3 + n)))
Iso.fun (test15 zero) = trElim (λ x → isOfHLevelΣ 3 (isOfHLevelTrunc 3) λ _ → isOfHLevelTrunc 3) λ {(f , pt) → ∣ f ∣ , ∣ (λ i → ∣ pt i ∣) ∣}
Iso.inv (test15 zero) = uncurry (trElim (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelTrunc 3) λ f → trElim (λ _ → isOfHLevelTrunc 3) λ a → trRec {!!} (λ p → ∣ f , p ∣) (Iso.fun (PathIdTruncIso 2) a) )
Iso.rightInv (test15 zero) = uncurry (trElim {!!} λ f → trElim {!!} λ p → ΣPathP ({!!} , {!!}))
Iso.leftInv (test15 zero) = {!!}
test15 (suc n) = {!!}

typId : ∀ n → Iso (typ ((Ω^ (suc (suc n))) (Type₀ , hLevelTrunc (3 + n) (S₊ (suc n)))))
                    ((x : hLevelTrunc (3 + n) (S₊ (suc n))) → typ ((Ω^ (suc n)) (_ , x)))
typId zero = {!!}
typId (suc zero) = {!!}
Iso.fun (typId (suc (suc n))) p = {! !}
Iso.inv (typId (suc (suc n))) = {!!}
Iso.rightInv (typId (suc (suc n))) = {!!}
Iso.leftInv (typId (suc (suc n))) = {!!}

CoDeS : ∀ n → S₊ (suc (suc n)) → Type
simul : ∀ n → (CoDeS n north ≡ hLevelTrunc (3 + n) (S₊ (suc n))) × (CoDeS n north ≡ hLevelTrunc (3 + n) (S₊ (suc n)))

CoDeS zero north = (hLevelTrunc 3 (S₊ 1))
CoDeS zero south = (hLevelTrunc 3 (S₊ 1))
CoDeS zero (merid base i) = (hLevelTrunc 3 (S₊ 1))
CoDeS zero (merid (loop j) i) = {!!}
CoDeS (suc zero) north = (hLevelTrunc 4 (S₊ 2))
CoDeS (suc zero) south = (hLevelTrunc 4 (S₊ 2))
CoDeS (suc zero) (merid north i) = (hLevelTrunc 4 (S₊ 2))
CoDeS (suc zero) (merid south i) = (hLevelTrunc 4 (S₊ 2))
CoDeS (suc zero) (merid (merid a i₁) i) = {!!}
CoDeS (suc (suc n)) north = hLevelTrunc (5 + n) (S₊ (3 + n))
CoDeS (suc (suc n)) south = hLevelTrunc (5 + n) (S₊ (3 + n))
CoDeS (suc (suc n)) (merid a i) = {!!}
simul zero = refl , refl
simul (suc zero) = refl , refl
simul (suc (suc n)) = refl , refl

iso? : ∀ n m → {!!}
iso? = {!!}

open import Cubical.Data.Bool
incS : ∀ n m → S₊ n → S₊ (n + m)
incS zero zero x = x
incS zero (suc zero) false = base
incS zero (suc zero) true = base
incS zero (suc (suc m)) false = north
incS zero (suc (suc m)) true = south
incS (suc n) zero x = subst S₊ (cong suc (sym (+-zero n))) x
incS (suc zero) (suc m) base = north
incS (suc zero) (suc m) (loop i) = {!!}
incS (suc (suc n)) (suc m) x = {!!}

isCommSusp : (A : Type₀) → ((x : A) (p q : x ≡ x) → p ∙ q ≡ q ∙ p) → (x : Susp A) (p q : x ≡ x ) → p ∙ q ≡ q ∙ p
isCommSusp A comm x p q = {!!}

open import Cubical.Foundations.Pointed

CODES : (n : ℕ) (y : hLevelTrunc (5 + n) (S₊ (3 + n))) → (∣ north ∣ ≡ y) → TypeOfHLevel ℓ-zero (4 + n)
CODES n = trElim (λ _ → isOfHLevelΠ (5 + n) λ _ → isOfHLevelTypeOfHLevel (4 + n))
                 {!!}
  where
  helpfun : (a : Susp (Susp (S₊ (suc n)))) → Path (hLevelTrunc (5 + n) (S₊ (3 + n))) ∣ north ∣ ∣ a ∣ → TypeOfHLevel ℓ-zero (suc (suc (suc (suc n))))
  helpfun north p = (hLevelTrunc (4 + n) (S₊ (2 + n))) , (isOfHLevelTrunc (4 + n))
  helpfun south p = (hLevelTrunc (4 + n) (S₊ (2 + n))) , (isOfHLevelTrunc (4 + n))
  helpfun (merid a i) p = {!hLevelTrunc (4 + n) (S₊ (2 + n))!} , {!!}
    where
    uaAp : (hLevelTrunc (4 + n) (S₊ (2 + n))) ≡ (hLevelTrunc (4 + n) (S₊ (2 + n)))
    uaAp = isoToPath (iso (trRec (isOfHLevelTrunc (4 + n)) (λ {north → ∣ north ∣ ; south → ∣ south ∣ ; (merid b i) → {!!}})) {!!} {!!} {!!})

higherPath : (n m : ℕ) → S₊ (suc n) → (S₊ (suc (suc (m + n))))
higherPath n zero x = {!!}
higherPath zero (suc m) x = {!!}
higherPath (suc n) (suc m) north = north
higherPath (suc n) (suc m) south = south
higherPath (suc n) (suc m) (merid a i) = {!merid (higherPath _ _ a) i!}

test : (n : ℕ) (A : Type₀) → Iso (∥ S₊ (2 + n) ∥ (4 + n)) (Ω (hLevelTrunc 4 (S₊ 2) , ∣ north ∣) →∙ ((hLevelTrunc (5 + n) (S₊ (3 + n))) , ∣ north ∣))
test zero A = {!!}
Iso.fun (test (suc n) A) = trRec {!!} λ {north → (λ _ → ∣ north ∣) , refl ; south → (λ _ → ∣ south ∣) , λ i → ∣ merid north (~ i) ∣ ; (merid a i) → (λ x → {!!}) , {!!}}
Iso.inv (test (suc n) A) = {!!}
Iso.rightInv (test (suc n) A) = {!!}
Iso.leftInv (test (suc n) A) = {!!}

-- test2 : (n : ℕ) (x y : Susp (S₊ ((suc n + suc n)))) → (q : south ≡ x) → (p : Path (Susp (S₊ (suc n + suc n))) north x)  → Σ[ a ∈ (S₊ (suc n + suc n)) ] p ≡ merid a ∙ q 
-- test2 n x = {!!}

-- test3 : (n : ℕ) → isConnectedFun ((suc n) + (suc n)) λ (x : S₊ (suc n + suc n)) → merid x
-- test3 zero = λ b → {!!} , {!!}
-- test3 (suc n) = elim.isConnectedPrecompose _ _ λ P → (λ f b → {!!}) , {!!}

--   where
--   module _ (P : {!!} → TypeOfHLevel ℓ-zero (suc (suc (n + suc (suc n))))) where
 
--     maybe : hasSection (λ s → s ∘ (λ z → merid z))
--     maybe = {!!} , {!!}

-- module _ {ℓ} (n : HLevel) {A : Pointed ℓ} (connA : isConnected (suc (suc n)) (typ A)) where

--   σ : typ A → typ (Ω (∙Susp (typ A)))
--   σ a = merid a ∙ merid (pt A) ⁻¹

--   private
--     2n+2 = suc n + suc n

--     module WC (p : north ≡ north) =
--       WedgeConnectivity (suc n) (suc n) A connA A connA
--         (λ a b →
--           ( (σ b ≡ p → hLevelTrunc 2n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p))
--           , isOfHLevelΠ 2n+2 λ _ → isOfHLevelTrunc 2n+2
--           ))
--         (λ a r → ∣ a , (rCancel' (merid a) ∙ rCancel' (merid (pt A)) ⁻¹) ∙ r ∣)
--         (λ b r → ∣ b , r ∣)
--         (funExt λ r →
--           cong′ (λ w → ∣ pt A , w ∣)
--             (cong (_∙ r) (rCancel' (rCancel' (merid (pt A))))
--               ∙ lUnit r ⁻¹))

--     fwd : (p : north ≡ north) (a : typ A)
--       → hLevelTrunc 2n+2 (fiber σ p)
--       → hLevelTrunc 2n+2 (fiber (λ x → merid x ∙ merid a ⁻¹) p)
--     fwd p a = Trunc.rec (isOfHLevelTrunc 2n+2) (uncurry (WC.extension p a))

--     isEquivFwd : (p : north ≡ north) (a : typ A) → isEquiv (fwd p a)
--     isEquivFwd p a .equiv-proof =
--       elim.isEquivPrecompose (λ _ → pt A) (suc n)
--         (λ a →
--           ( (∀ t → isContr (fiber (fwd p a) t))
--           , isProp→isOfHLevelSuc n (isPropΠ λ _ → isPropIsContr)
--           ))

--         (isConnectedPoint (suc n) connA (pt A))
--         .equiv-proof
--         (λ _ → Trunc.elim
--           (λ _ → isProp→isOfHLevelSuc (n + suc n) isPropIsContr)
--          (λ fib →
--             subst (λ k → isContr (fiber k ∣ fib ∣))
--               (cong (Trunc.rec (isOfHLevelTrunc 2n+2) ∘ uncurry)
--                 (funExt (WC.right p) ⁻¹))
--               (subst isEquiv
--                 (funExt (Trunc.mapId) ⁻¹)
--                 (idIsEquiv _)
--                 .equiv-proof ∣ fib ∣)
--              ))
--         .fst .fst a

--     interpolate : (a : typ A)
--       → PathP (λ i → typ A → north ≡ merid a i) (λ x → merid x ∙ merid a ⁻¹) merid
--     interpolate a i x j = compPath-filler (merid x) (merid a ⁻¹) (~ i) j

--   Code : (y : Susp (typ A)) → north ≡ y → Type ℓ
--   Code north p = hLevelTrunc 2n+2 (fiber σ p)
--   Code south q = hLevelTrunc 2n+2 (fiber merid q)
--   Code (merid a i) p =
--     Glue
--       (hLevelTrunc 2n+2 (fiber (interpolate a i) p))
--       (λ
--         { (i = i0) → _ , (fwd p a , isEquivFwd p a)
--         ; (i = i1) → _ , idEquiv _
--         })

--   encode : (y : Susp (typ A)) (p : north ≡ y) → Code y p
--   encode y = J Code ∣ pt A , rCancel' (merid (pt A)) ∣

--   encodeMerid : (a : typ A) → encode south (merid a) ≡ ∣ a , refl ∣
--   encodeMerid a =
--     cong (transport (λ i → gluePath i))
--       (funExt⁻ (WC.left refl a) _ ∙ λ i → ∣ a , (lem (rCancel' (merid a)) (rCancel' (merid (pt A)))) i ∣)
--     ∙ transport (PathP≡Path gluePath _ _)
--       (λ i → ∣ a , (λ j k → rCancel-filler' (merid a) i j k) ∣)
--     where
--     gluePath : I → Type _
--     gluePath i = hLevelTrunc 2n+2 (fiber (interpolate a i) (λ j → merid a (i ∧ j)))

--     lem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y) → (p ∙ q ⁻¹) ∙ q ≡ p
--     lem p q = assoc p (q ⁻¹) q ⁻¹ ∙ cong (p ∙_) (lCancel q) ∙ rUnit p ⁻¹

--   contractCodeSouth : (p : north ≡ south) (c : Code south p) → encode south p ≡ c
--   contractCodeSouth p =
--     Trunc.elim
--       (λ _ → isOfHLevelPath 2n+2 (isOfHLevelTrunc 2n+2) _ _)
--       (uncurry λ a →
--         J (λ p r → encode south p ≡ ∣ a , r ∣) (encodeMerid a))

--   isConnectedMerid : isConnectedFun 2n+2 (merid {A = typ A})
--   isConnectedMerid p = encode south p , contractCodeSouth p

--   isConnectedσ : isConnectedFun 2n+2 σ
--   isConnectedσ =
--     transport (λ i → isConnectedFun 2n+2 (interpolate (pt A) (~ i))) isConnectedMerid

-- open import Cubical.Foundations.Pointed
-- open import Cubical.Data.Bool

-- isConn→isConnSusp : ∀ {ℓ} {A : Pointed ℓ} → isConnected 2 (typ A) → isConnected 2 (Susp (typ A))
-- isConn→isConnSusp {A = A} iscon = ∣ north ∣ , (trElim (λ _ → isOfHLevelSuc 1 (isOfHLevelTrunc 2 _ _)) (suspToPropRec (pt A) (λ _ → isOfHLevelTrunc 2 _ _) refl))

-- FreudenthalIso1 : ∀ {ℓ} (n : HLevel) (A : Pointed ℓ)
--                 → isConnected (2 + n) (typ A)
--                 → Iso (hLevelTrunc ((suc n) + (suc n)) (typ A))
--                       (hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north))))
-- FreudenthalIso1 zero A iscon = isContr→Iso iscon isConnΩ
--   where
--   isConnΩ : isContr (hLevelTrunc 2 (typ (Ω (Susp (typ A) , north)))) 
--   isConnΩ = {!Iso.inv (Trunc.PathIdTruncIso {A = Susp (typ A)} {a = north} {b = north} 2) !}
-- FreudenthalIso1 (suc n) A iscon = {!!}


-- FreudenthalEquiv : ∀ {ℓ} (n : HLevel) (A : Pointed ℓ)
--                 → isConnected (2 + n) (typ A)
--                 → hLevelTrunc ((suc n) + (suc n)) (typ A)
--                  ≃ hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north)))
-- FreudenthalEquiv n A iscon = connectedTruncEquiv _
--                                                  (σ n {A = A} iscon)
--                                                  (isConnectedσ _ iscon)
-- FreudenthalIso : ∀ {ℓ} (n : HLevel) (A : Pointed ℓ)
--                 → isConnected (2 + n) (typ A)
--                 → Iso (hLevelTrunc ((suc n) + (suc n)) (typ A))
--                       (hLevelTrunc ((suc n) + (suc n)) (typ (Ω (Susp (typ A) , north))))
-- FreudenthalIso zero A iscon = iso (Trunc.map (σ 0 {A = A} iscon))
--                                   {!!}
--                                   {!!}
--                                   {!!}
-- -- connectedTruncIso _ (σ 0 {A = A} iscon) (isConnectedσ _ iscon) -- pattern matching to prevent Agda from expanding
-- FreudenthalIso (suc zero) A iscon = connectedTruncIso _ (σ 1 {A = A} iscon) (isConnectedσ _ iscon)
-- FreudenthalIso (suc (suc zero)) A iscon = connectedTruncIso _ (σ 2 {A = A} iscon) (isConnectedσ _ iscon)
-- FreudenthalIso (suc (suc (suc zero))) A iscon = connectedTruncIso _ (σ 3 {A = A} iscon) (isConnectedσ _ iscon)
-- FreudenthalIso (suc (suc (suc (suc zero)))) A iscon = connectedTruncIso _ (σ 4 {A = A} iscon) (isConnectedσ _ iscon)
-- FreudenthalIso (suc (suc (suc (suc (suc n))))) A iscon = connectedTruncIso _ (σ (5 + n) {A = A} iscon) (isConnectedσ _ iscon)

-- -- -- Tests
-- -- open import Cubical.Homotopy.Loopspace
-- -- open import Cubical.HITs.Sn

-- -- truncIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : HLevel)
-- --          → Iso A B
-- --          → Iso (hLevelTrunc n A) (hLevelTrunc n B)
-- -- Iso.fun (truncIso n i) = map (Iso.fun i)
-- -- Iso.inv (truncIso n i) = map (Iso.inv i)
-- -- Iso.rightInv (truncIso n i) = Trunc.elim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → cong ∣_∣ (Iso.rightInv i a)
-- -- Iso.leftInv (truncIso n i) = Trunc.elim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → cong ∣_∣ (Iso.leftInv i a)

-- -- π₀-S¹ : Iso (hLevelTrunc 2 (S₊ 1)) {!!}
-- -- π₀-S¹ = {!!}

-- -- LoopSpaceIso : {!!}
-- -- LoopSpaceIso = {!!}
-- -- open import Cubical.Foundations.Equiv.HalfAdjoint


-- -- base-change : (x : ∥ S₊ 2 ∥ 4) →  Iso (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , x))) (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , ∣ north ∣)))
-- -- Iso.fun (base-change x) =
-- --   Trunc.elim {B = λ x → (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , x))) → (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , ∣ north ∣)))}
-- --              (λ _ → isOfHLevelΠ 4 {!!})
-- --              (λ {north → idfun _
-- --                ; south → transport (λ i → typ ((Ω^ 2) ((∥ S₊ 2 ∥ 4) , ∣ merid north (~ i) ∣)))
-- --                ; (merid north i) → {!!}
-- --                ; (merid south i) → {!!}
-- --                ; (merid (merid a j) i) → {!isOfHLevelDep!}}) x
-- -- Iso.inv (base-change x) = {!!}
-- -- Iso.rightInv (base-change x) = {!!}
-- -- Iso.leftInv (base-change x) = {!!}

-- -- FreudTest-2 : (π 3 (S₊ 3 , north)) ≡ (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , ∣ north ∣)))
-- -- FreudTest-2 = isoToPath (compIso (invIso (ΩTrunc.IsoFinal 2 ∣ refl ∣ ∣ refl ∣))
-- --                 (compIso
-- --                   (congIso (invIso (ΩTrunc.IsoFinal 3 ∣ refl ∣ ∣ refl ∣)))
-- --                   (congIso (congIso helper))))
-- --            ∙∙ isoToPath {!!}
-- --            ∙∙ {!!}
-- --   where
-- --   helper : Iso (∥ typ (Ω (S₊ 3 , north)) ∥ 4) (∥ S₊ 2 ∥ 4)
-- --   helper = invIso (FreudenthalIso 1 (S₊ 2 , north) (sphereConnected 2))

-- --   test2 : Iso.inv helper ∣ north ∣ ≡ ∣ refl ∣
-- --   test2 = cong ∣_∣ (rCancel (merid north))

-- --   test4 : ΩTrunc.decode-fun {B = Path (S₊ 3) north north} {n = 4} (∣ refl {x = north} ∣) (∣ refl {x = north} ∣) (∣ (λ _ → snd (Ω (S₊ 3 , north))) ∣) ≡ refl
-- --   test4 = refl

-- --   test : Iso.fun helper ∣ refl ∣ ≡ ∣ north ∣ -- cannot normalise LHS (or very slow/big)
-- --   test = cong (Iso.fun helper) (sym test2) ∙ Iso.rightInv helper _

-- --   test5 : (Iso.fun (congIso helper) (ΩTrunc.decode-fun (∣ (λ _ → north) ∣) ∣ (λ _ → north) ∣
-- --         ∣ (λ _ → snd (Ω (S₊ 3 , north))) ∣)) ≡ {!!}
-- --   test5 = refl

-- -- -- FreudTest-1 : Iso (π 3 (S₊ 3 , north)) (typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , ∣ north ∣)))
-- -- -- FreudTest-1 = compIso (invIso (ΩTrunc.IsoFinal 2 ∣ refl ∣ ∣ refl ∣))
-- -- --                 (compIso
-- -- --                   (congIso (invIso (ΩTrunc.IsoFinal 3 ∣ refl ∣ ∣ refl ∣)))
-- -- --                   (compIso (congIso (congIso helper))
-- -- --                   (compIso
-- -- --                     (pathToIso {!λ i → typ ((Ω^ 2) (∥ S₊ 2 ∥ 4 , test i))!})
-- -- --                     (compIso {!!} {!!}))))
-- -- --   where
-- -- --   helper : Iso (∥ typ (Ω (S₊ 3 , north)) ∥ 4) (∥ S₊ 2 ∥ 4)
-- -- --   helper = invIso (FreudenthalIso 1 (S₊ 2 , north) (sphereConnected 2))

-- -- --   test2 : Iso.inv helper ∣ north ∣ ≡ ∣ refl ∣
-- -- --   test2 = cong ∣_∣ (rCancel (merid north))

-- -- --   test4 : ΩTrunc.decode-fun {B = Path (S₊ 3) north north} {n = 4} (∣ refl {x = north} ∣) (∣ refl {x = north} ∣) (∣ (λ _ → snd (Ω (S₊ 3 , north))) ∣) ≡ refl
-- -- --   test4 = refl

-- -- --   test : Iso.fun helper ∣ refl ∣ ≡ ∣ north ∣ -- cannot normalise LHS (or very slow/big)
-- -- --   test = {!Iso.fun helper ∣ refl ∣!} -- cong (Iso.fun helper) (sym test2) ∙ Iso.rightInv helper _

-- -- --   test5 : (Iso.fun (congIso helper) (ΩTrunc.decode-fun (∣ (λ _ → north) ∣) ∣ (λ _ → north) ∣
-- -- --         ∣ (λ _ → snd (Ω (S₊ 3 , north))) ∣)) ≡ {!!}
-- -- --   test5 = refl




-- -- -- -- testIso : Iso (hLevelTrunc 2 (typ (Ω (S₊ 2 , north)))) (hLevelTrunc 2 (S₊ 1))
-- -- -- -- testIso = invIso (FreudenthalIso 0 (S₊ 1 , north) (sphereConnected 1))


-- -- -- -- stabSpheres : Iso (π 2 (S₊ 2 , north)) (π 1 (S₊ 1 , north)) 
-- -- -- -- stabSpheres =
-- -- -- --   compIso (invIso (ΩTrunc.IsoFinal 2 ∣ refl ∣ ∣ refl ∣))
-- -- -- --       (compIso helper
-- -- -- --                (ΩTrunc.IsoFinal 2 ∣ north ∣ ∣ north ∣))
-- -- -- --   where
-- -- -- --   helper1 : Iso (∥ typ (Ω ((S₊ 2) , north)) ∥ 3) (∥ S₊ 1 ∥ 3)
-- -- -- --   helper1 = {!FreudenthalIso 1!}

  

-- -- -- --   helper : Iso (typ (Ω ((∥ typ (Ω ((S₊ 2) , north)) ∥ 3) , ∣ refl ∣))) (typ (Ω ((∥ (S₊ 1) ∥ 3) , ∣ north ∣)))
-- -- -- --   helper =
-- -- -- --     compIso (congIso (truncOfTruncIso 3 1))
-- -- -- --       (compIso {!truncIso 3 ?!} {!!})
-- -- -- --       where
-- -- -- --       test2 : Iso.fun (truncOfTruncIso {A = typ (Ω (S₊ 2 , north))} 3 1) ∣ refl ∣ ≡ ∣ ∣ refl ∣ ∣
-- -- -- --       test2 = refl

-- -- -- --       test : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → Iso (p ∙ sym p ≡ p ∙ sym p) (refl {x = x} ≡ refl {x = x}) 
-- -- -- --       test = {!!}



