{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Algebra.Group.EilenbergMacLane.Cup-i where


open import Cubical.Algebra.Group.EilenbergMacLane.Base
open import Cubical.Algebra.Group.EilenbergMacLane.GroupStructure
open import Cubical.Algebra.Group.EilenbergMacLane.Properties
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Group.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.Group.EilenbergMacLane.CupProduct
open import Cubical.Algebra.Group.EilenbergMacLane.CupProductTensor
open import Cubical.Algebra.Semigroup.Base

open import Cubical.Algebra.Ring
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Algebra.Monoid.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport

open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as Trunc

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Nat hiding (_·_) renaming (elim to ℕelim ; _+_ to _+ℕ_)
open import Cubical.Data.Sigma

open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.Ring

open import Cubical.Data.Nat.Order

open AbGroupStr renaming (_+_ to _+Gr_ ; -_ to -Gr_)
open RingStr
open IsRing

open PlusBis

private
  variable
    ℓ ℓ' : Level

¬<2 : {n : ℕ} → suc (suc n) < 2 → ⊥
¬<2 p = snotz (cong (λ x → predℕ (predℕ x)) (+-comm _ (fst p) ∙ snd p))

_·₂_ : Fin 2 → Fin 2 → Fin 2
_·₂_ (zero , p) (y , r) = zero , p
_·₂_ (suc zero , p) q = q
_·₂_ (suc (suc x) , p) (y , r) = ⊥.rec (¬<2 p)

·₂-assoc : (x y z : Fin 2) → x ·₂ (y ·₂ z) ≡ (x ·₂ y) ·₂ z
·₂-assoc (zero , p) y z = refl
·₂-assoc (suc zero , p) y z = refl
·₂-assoc (suc (suc x) , p) y z = ⊥.rec (¬<2 p)

·0 : (x : _) {q : zero < 2} → x ·₂ (0 , q) ≡ (0 , q)
·0 (zero , p) = Σ≡Prop (λ _ → isProp≤) refl
·0 (suc zero , p) = Σ≡Prop (λ _ → isProp≤) refl
·0 (suc (suc x) , p) = ⊥.rec (¬<2 p)

rUnit·₂ : {p : 1 < 2} (x : Fin 2) → x ·₂ (1 , p) ≡ x
rUnit·₂ (zero , snd₁) = refl
rUnit·₂ (suc zero , p) = Σ≡Prop (λ _ → isProp≤) refl
rUnit·₂ (suc (suc x) , p) = ⊥.rec (¬<2 p)

distr·₂ : (x y z : Fin 2) → (x ·₂ (y +ₘ z)) ≡ (x ·₂ y) +ₘ (x ·₂ z)
distr·₂ (zero , p) y z = Σ≡Prop (λ _ → isProp≤) refl
distr·₂ (suc zero , p) y z = Σ≡Prop (λ _ → isProp≤) refl
distr·₂ (suc (suc x) , p) y z = ⊥.rec (¬<2 p)

distr·₂l : (x y z : Fin 2) → ((x +ₘ y) ·₂ z) ≡ (x ·₂ z) +ₘ (y ·₂ z)
distr·₂l x y (zero , p) = ·0 (x +ₘ y) ∙ sym (Σ≡Prop (λ _ → isProp≤) refl) ∙ sym (cong₂ _+ₘ_ (·0 x) (·0 y))
distr·₂l x y (suc zero , p) = rUnit·₂ (x +ₘ y) ∙ cong₂ _+ₘ_ (sym (rUnit·₂ x)) (sym (rUnit·₂ y))
distr·₂l x y (suc (suc n) , p) = ⊥.rec (¬<2 p)




open IsGroup
open IsMonoid
open IsSemigroup
open GroupStr

ℤ/2 : Ring ℓ-zero
fst ℤ/2 = Fin 2
0r (snd ℤ/2) = 1g (snd (ℤGroup/ 2)) 
1r (snd ℤ/2) = 1
_+_ (snd ℤ/2) = _·_ (snd (ℤGroup/ 2))  -- _+ₘ_
_·_ (snd ℤ/2) = _·₂_
(- snd ℤ/2) = inv (snd (ℤGroup/ 2)) -- 0 -ₘ x
+IsAbGroup (isRing (snd ℤ/2)) = isAbGroup (snd (Group→AbGroup (ℤGroup/ 2) +ₘ-comm))
is-set (isSemigroup (·IsMonoid (isRing (snd ℤ/2)))) = is-set (snd (ℤGroup/ 2)) 
·Assoc (isSemigroup (·IsMonoid (isRing (snd ℤ/2)))) = ·₂-assoc
·IdR (·IsMonoid (isRing (snd ℤ/2))) = rUnit·₂
·IdL (·IsMonoid (isRing (snd ℤ/2))) _ = refl
·DistR+ (isRing (snd ℤ/2)) = distr·₂
·DistL+ (isRing (snd ℤ/2)) = distr·₂l
open import Cubical.HITs.SetTruncation as sT

H[_,_,_] : ∀ {ℓ ℓ'} (A : Type ℓ) (G : AbGroup ℓ') (n : ℕ) → Type _
H[ A , G , n ] = ∥ (A → EM G n) ∥₂

H₂ : ∀ {ℓ} (A : Type ℓ) (n : ℕ) → Type _
H₂ A n = H[ A , Ring→AbGroup ℤ/2 , n ]

-- H[_,_,_] = ?

KZ/2 : (n : ℕ) → Type
KZ/2 n = EM (Ring→AbGroup ℤ/2) n

open import Cubical.Foundations.Pointed
KZ/2∙ : (n : ℕ) → Pointed ℓ-zero
KZ/2∙ n = EM∙ (Ring→AbGroup ℤ/2) n

cp = Cubical.Algebra.Group.EilenbergMacLane.CupProduct._⌣ₖ_ {G'' = ℤ/2}

open import Cubical.Data.Int renaming (ℤ to INT)
open import Cubical.HITs.S1 renaming (_·_ to _*_)
isIso : Σ[ g ∈ (S¹ → S¹) ] ((x : S¹) → g x ≡ x) × ((x : S¹) → g x ≡ x)
isIso = (λ x → x) , ((λ { base → loop ; (loop i) j → loop i * loop j}) , λ { base → loop ; (loop i) j → loop i * loop j})

isIso' : Σ[ g ∈ (S¹ → S¹) ] ((x : S¹) → g x ≡ x) × ((x : S¹) → g x ≡ x)
isIso' = (λ x → x) , ((λ x → refl) , λ { base → loop ; (loop i) j → loop i * loop j})

test : Σ[ g ∈ (S¹ → S¹) ] ((x : S¹) → g x ≡ x) × ((x : S¹) → g x ≡ x)
     → INT
test (g , x , q) = winding (sym (q base) ∙ x base)

{-
f : S¹ → S¹
f base = base
f loop = loop



-}

daLem : (n : ℕ) → KZ/2 (suc (suc n)) → KZ/2 (suc n)
daLem n = Trunc.rec (isOfHLevelSuc (3 +ℕ n) (hLevelEM _ (suc n)))
                    λ { north → 0ₖ (suc n)
                      ; south → 0ₖ (suc n)
                      ; (merid a i) → EM→ΩEM+1 n {!!} i}

x=-x : (x : Fin 2) → x ≡ (-ₘ x)
x=-x (zero , p) =  Σ≡Prop (λ _ → isProp≤) refl
x=-x (suc zero , p) =  Σ≡Prop (λ _ → isProp≤) refl
x=-x (suc (suc x) , p) = ⊥.rec (¬<2 p)

f=g : (n : ℕ) (x : KZ/2 n) → x ≡ (-ₖ x)
f=g zero = x=-x
f=g (suc zero) =
  EM-rawer-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
    λ { embase-raw → refl
      ; (emloop-raw g i) j → (cong emloop (x=-x g) ∙ emloop-sym _ g) j i}
f=g (suc (suc n)) =
  Trunc.elim (λ _ → isOfHLevelPath (4 +ℕ n) (hLevelEM _ (2 +ℕ n)) _ _)
    λ { north → refl
      ; south → cong ∣_∣ₕ (sym (merid (EM-raw∙ _ (suc n) .snd)))
      ; (merid a i) j → help a j i}
  where
  help : (a : _) → PathP (λ i → Path (KZ/2 (suc (suc n))) ∣ north ∣ₕ ∣ merid (EM-raw∙ _ (suc n) .snd) (~ i) ∣ₕ) (cong ∣_∣ₕ (merid a)) (sym (cong ∣_∣ₕ (σ-EM n a)))
  help a =
      {!!}
    ▷ ({!σ-EM n a ≡ EM→ΩEM+1!}
     ∙ {!!})
    where
    lem : {!Path!}
    lem = {!!}

cupComm : {n m : ℕ} (x : KZ/2 n) (y : KZ/2 m) → subst KZ/2 (+'-comm n m) (cp x y) ≡ cp y x
cupComm = {!!}

cupCommf : {n m : ℕ} (x : KZ/2 n) (y : KZ/2 m) → (cp x y) ≡ subst KZ/2 (+'-comm m n) (cp y x)
cupCommf = {!!}

cupComm' : {n : ℕ} (x y : KZ/2 n) → (cp y x) ≡ cp x y
cupComm' = {!!}

cup-i-base : (n : ℕ) → KZ/2 n → KZ/2 1 → KZ/2 n
cup-i-base n x y = {!!}

idid : Path (S¹ → S¹) (λ x → x) (λ x → x) → INT
idid f = winding (funExt⁻ f base)

test1 : Path (S¹ → S¹) (λ x → x) (λ x → x)
test1 = funExt λ { base → loop ; (loop i) j → loop i * loop j}



test2 : {n : ℕ} (x : KZ/2 n) → Path (KZ/2 (n PlusBis.+' n)) (0ₖ (n PlusBis.+' n)) (0ₖ (n PlusBis.+' n))
test2 {n = n} x = sym (rCancelₖ _ (cp x x))
               ∙∙ cong (λ y → y -ₖ (cp x x)) (cupComm' {n = n} x x)
               ∙∙ rCancelₖ _ (cp x x)

testi : {n : ℕ} (x : KZ/2 (suc n)) → KZ/2 (suc (n +ℕ n))
testi x = ΩEM+1→EM _ (test2 x)

subtrK : (n i : ℕ) → KZ/2 (suc n ∸ i) → KZ/2 (n ∸ i) 
subtrK n zero x = {!t!}
subtrK n (suc i) x = {!!}

comm→pred : (n m i : ℕ) → KZ/2 (suc n) → KZ/2 (suc m) → KZ/2 (((suc n) PlusBis.+' (suc m)))
comm→pred = {!!}

predKn : (n : ℕ) → (x : KZ/2 (suc n)) → (x ≡ x) → KZ/2 n
predKn n x p = {!!}

open import Cubical.HITs.Truncation as Tr

ΩEM+1→EM-b : (n : ℕ) {x : KZ/2 (suc n)} → x ≡ x → KZ/2 n
ΩEM+1→EM-b n {x = x} p = {!!}


cuu-i : (n m i : ℕ) → KZ/2 n → KZ/2∙ m →∙ KZ/2∙ ((n PlusBis.+' m) ∸ i)
cuu-i n m zero x = {!!}
fst (cuu-i zero zero (suc i) x) y = {!y!}
fst (cuu-i zero (suc m) (suc i) x) y = {!!}
fst (cuu-i (suc n) m (suc i) x) y = {!!}
snd (cuu-i n m (suc i) x) = {!!}

alr : (n : ℕ) → KZ/2 n → KZ/2 1 → KZ/2 (n PlusBis.+' n)
alr zero x y = x
alr (suc zero) x y = cp {n = suc zero} {m = suc zero} x y
alr (suc (suc n)) x y = {!alr (suc n) !}

cup-i'' : (n m i : ℕ) → KZ/2 n → KZ/2 m → KZ/2 ((n PlusBis.+' m) ∸ i)
cup-i'' n m zero x y = {!cong (cup-i'' ((n PlusBis.+' m) ∸ i') 1 1 (cup-i'' n m i' x y)) (emloop 1) ?!}
cup-i'' n zero (suc i') x y = {!!}
cup-i'' n (suc zero) (suc i') x y = {!!}
  where
  l : {!ΩEM+1→EM-b
{- cong (cup-i'' ((n PlusBis.+' suc (suc m)) ∸ i') 1 1 (cup-i'' n (suc (suc m)) i' x y)) (emloop 1)-}!}
  l = {!!}
{- {!ΩEM+1→EM-b
{- cong (cup-i'' ((suc n PlusBis.+' suc (suc m)) ∸ i') 1 1 (cup-i'' (suc n) (suc (suc m)) i' x y)) (emloop 1)-}!} -}
cup-i'' n (suc (suc m)) (suc i') x y =
    ΩEM+1→EM-b ((n PlusBis.+' suc (suc m)) ∸ suc i') {x = {!cup-i'' n 1 1!}}
      {!cong  (cong (cup-i'' ((n PlusBis.+' suc (suc m)) ∸ i') 1 1 (cup-i'' n (suc (suc m)) i' x y)) (emloop 1))!}
  where
  c : ((((n PlusBis.+' suc (suc m)) ∸ i') PlusBis.+' 1) ∸ 1)
    ≡ (suc ((n PlusBis.+' suc (suc m)) ∸ suc i')) -- suc (n +ℕ suc m) ∸ i' ≡ suc ((n +ℕ (suc m)) ∸ i')
  c = {!!}

cup-i' : (n m i : ℕ) → KZ/2 n → KZ/2 m → KZ/2 ((n PlusBis.+' m) ∸ i)
cup-i' n m zero x y = cp x y
cup-i' zero m (suc i) x y = {!!}
cup-i' (suc zero) m (suc i) x y = {!!}
cup-i' (suc (suc n)) zero (suc i) x y = {!!}
cup-i' (suc (suc n)) (suc zero) (suc i) x y = {!cup-i' (suc (suc n)) (suc (suc m)) i' x y!}
cup-i' (suc (suc n)) (suc (suc m)) (suc i') x y = {!cong (cup-i' (((suc (suc n)) PlusBis.+' (suc (suc m))) ∸ i') 1 1 (cup-i' (suc (suc n)) (suc (suc m)) i' x y)) (emloop 1) i0!}
 --  Tr.rec {!!} λ x → Tr.rec {!x!} λ y → {!cup-i' (suc (suc n)) (suc (suc m)) (suc i') ? ?!}
  where
  open import Cubical.Homotopy.Loopspace
  c : Susp (EM-raw (Ring→AbGroup ℤ/2) (suc n)) → Susp (EM-raw (Ring→AbGroup ℤ/2) (suc m)) → KZ/2 (suc (suc ((suc (n +ℕ m)) ∸ i')))
  c north y = 0ₖ (suc (suc ((suc (n +ℕ m)) ∸ i')))
  c south y = 0ₖ (suc (suc ((suc (n +ℕ m)) ∸ i')))
  c (merid a i) north = 0ₖ (suc (suc ((suc (n +ℕ m)) ∸ i')))
  c (merid a i) south = 0ₖ (suc (suc ((suc (n +ℕ m)) ∸ i')))
  c (merid a i) (merid b j) = asd i j
    where
    asd : (Ω^ 2) (KZ/2∙ (suc (suc (suc (n +ℕ m) ∸ i')))) .fst
    asd = {!EM→ΩEM+1 (suc (suc (n +ℕ m)) ∸ i')
                     (cup-i' (suc n) (suc m) i'
                       (EM-raw→EM _ _ a) (EM-raw→EM _ _ b))!}

    p : _
    p = EM→ΩEM+1 {G = Ring→AbGroup ℤ/2} (suc ((suc (n +ℕ m)) ∸ i'))
                  (EM→ΩEM+1 (suc (n +ℕ m) ∸ i')
                    (cup-i' (suc n) (suc m) (suc i') (EM-raw→EM _ _ a) (EM-raw→EM _ _ b)) j) i



cup-i : (n m i : ℕ) → KZ/2 n → KZ/2 m → KZ/2 ((n PlusBis.+' m) ∸ i)
cup-i n m zero = cp
cup-i zero zero (suc i) x y = {!!}
cup-i zero (suc zero) (suc i) x y = {!!}
cup-i zero (suc (suc m)) (suc i) x =
  Tr.rec {!!} λ { north → 0ₖ (suc m ∸ i)
                 ; south → 0ₖ (suc m ∸ i)
                 ; (merid a j) → transport (λ k → 0ₖ {G = Ring→AbGroup ℤ/2}  (h (~ k)) ≡ 0ₖ {G = Ring→AbGroup ℤ/2} (h (~ k))) (EM→ΩEM+1 {G = Ring→AbGroup ℤ/2} (m ∸ i)
                                            (cup-i zero (suc m) (suc i) x (EM-raw→EM _ _ a))) j}
  where
  h : suc m ∸ i ≡ suc (m ∸ i)
  h = {!!}
cup-i (suc zero) zero (suc i) x y = {!!}
cup-i (suc zero) (suc m) (suc i) x y = subst KZ/2 (sym h) {!!}
  where
  r : EM-rawer (Ring→AbGroup ℤ/2) 1 → KZ/2 (suc m) → KZ/2 (suc (m ∸ i))
  r embase-raw y = 0ₖ (suc (m ∸ i))
  r (emloop-raw g j) y = EM→ΩEM+1 (m ∸ i) (cup-i zero (suc m) (suc i) g y) j

  h : suc m ∸ i ≡ suc (m ∸ i)
  h = {!!}
cup-i (suc (suc n)) m (suc i) x y = {!!}

steen : (n i : ℕ) → KZ/2 (suc n) → KZ/2 (((suc n) PlusBis.+' (suc n)) ∸ i)
steen n zero x = cp x x
steen n (suc zero) = testi
steen zero (suc (suc i)) _ = 0ₖ (0 ∸ i)
steen (suc n) (suc (suc i)) x =
  subst KZ/2 (sym lem)
    (predKn _ (subst KZ/2 lem2 (steen (suc n) (suc i) x))
      (sym (lUnitₖ (suc (suc (n +ℕ suc n ∸ i))) (subst KZ/2 lem2 (steen (suc n) (suc i) x)))
    ∙∙ cong (λ z → z -ₖ subst KZ/2 lem2 (steen (suc n) (suc i) x))
            (EM→ΩEM+1 (suc (n +ℕ suc n ∸ i))
              {!steen (suc n) (suc i) x!})
    ∙∙ lUnitₖ (suc (suc (n +ℕ suc n ∸ i))) (subst KZ/2 lem2 (steen (suc n) (suc i) x))))
  where
  lem : suc (n +ℕ suc n) ∸ i ≡ suc (n +ℕ (suc n) ∸ i)
  lem = {!!}

  lem2 :  (suc (suc (n +ℕ suc n)) ∸ i) ≡ (suc (suc (n +ℕ suc n ∸ i)))
  lem2 = {!!}

open import Cubical.Algebra.Group.EilenbergMacLane.Base

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
Fin2eq : Iso (Fin 2) (Fin 2)
Iso.fun Fin2eq x = 1 +ₘ x
Iso.inv Fin2eq x = 1 +ₘ x
Iso.rightInv Fin2eq = {!!}
Iso.leftInv Fin2eq = {!!}

fin2eq≡ : {!!}
fin2eq≡ = {!!}

RP→Kn : {!∀ {ℓ} (n : ℕ) x!}
RP→Kn = {!!}

open import Cubical.Data.Int renaming (ℤ to INT)
RP→-elim : ∀ {ℓ} {A : KZ/2 1 → Type ℓ}
  → (f : (x : EM-raw _ 1) → A (EM-raw→EM _ 1 x))
  → ((x y : EM-raw _ 1) (p q : x ≡ y) (r s : p ≡ q)
    → PathP (λ i → SquareP (λ j k → A (emsquash (EM-raw→EM _ 1 x) (EM-raw→EM _ 1 y) p q r s i j k))
             (λ k → f (p k)) (λ k → f (q k)) (λ _ → f x) λ _ → f y) (λ j k → f (r j k)) λ j k → f (s j k))
  → (x : _) → A x
RP→-elim f hlev embase = f embase
RP→-elim f hlev (emloop x i) = f (emloop x i)
RP→-elim f hlev (emcomp g h j i) = f (emcomp g h j i)
RP→-elim f hlev (emsquash x y p q r s i j k) = {!!}
  where
  lem : {!((x y : EM-raw _ 1) (p q : x ≡ y) (r s : p ≡ q)
    → PathP (λ i → SquareP (λ j k → A (emsquash (EM-raw→EM _ 1 x) (EM-raw→EM _ 1 y) p q r s i j k))
             (λ k → f (p k)) (λ k → f (q k)) (λ _ → f x) λ _ → f y) (λ j k → f (r j k)) λ j k → f (s j k))!}
  lem = {!!}

open import Cubical.Algebra.Group.EilenbergMacLane.WedgeConnectivity
open import Cubical.Foundations.Path
open import Cubical.Homotopy.Loopspace

data PushF {ℓ} (A : Type ℓ) : (B : Type ℓ) → Type (ℓ-suc ℓ) where
  left : {B : Type ℓ} → A → B → PushF A B
  right : {B : Type ℓ} → A → B → PushF A B
  lr : (x : A) → left x x ≡ right x x

data PushF' {ℓ} (A : ℕ → Type ℓ) : ℕ → ℕ → Type ℓ where
  left : {n m : ℕ} → A n → A m → PushF' A n m
  lr : (n : ℕ) (x : A n) → left x x ≡ left x x

KZ/2-raw = EM₁-raw (AbGroup→Group (Ring→AbGroup ℤ/2))

ℤ/2Gr = AbGroup→Group (Ring→AbGroup ℤ/2)

open import Cubical.HITs.GroupoidTruncation as GT


genie' : KZ/2∙ 1 →∙ (KZ/2∙ 1 →∙ KZ/2∙ 2 ∙)
fst (fst genie' x) y = cp {n = 1} {m = 1} x y
snd (fst genie' x) = Cubical.Algebra.Group.EilenbergMacLane.CupProduct.⌣ₖ-0ₖ 1 1 x
snd genie' = ΣPathP ((funExt (λ y → Cubical.Algebra.Group.EilenbergMacLane.CupProduct.0ₖ-⌣ₖ 1 1 y)) , (λ i j → (Cubical.Algebra.Group.EilenbergMacLane.CupProduct.0ₖ-⌣ₖ 1 1
       (snd (KZ/2∙ 1))) (i ∨ j)))

genie'' : (Ω^ 2) (KZ/2∙ 2) .fst
genie'' i j =
  hcomp (λ k → λ {(i = i0) → ∣ north ∣ ; (i = i1) → ∣ north ∣ ; (j = i0) → ∣ inducedFun-EM-raw TensorMultHom (2 +ℕ 0) (rCancel (merid embase) k i)  ∣ ; (j = i1) → ∣ inducedFun-EM-raw TensorMultHom (2 +ℕ 0) (rCancel (merid embase) k i)  ∣})
        (cp {n = 1} {m = 1} (emloop 1 i) (emloop 1 j))

genie : (KZ/2∙ 1 →∙ (KZ/2∙ 1 →∙ KZ/2∙ 2 ∙)) → fst ℤ/2
genie (g' , p) = ΩEM+1→EM {G = Ring→AbGroup ℤ/2} 0
                  λ i → ΩEM+1→EM {G = Ring→AbGroup ℤ/2} 1 (λ j → l2 i j)
  where
  g : KZ/2 1 → KZ/2 1 → KZ/2 2
  g x y = g' x .fst y

  l : Square (λ i → g embase (emloop 1 i))
             (λ i → g embase (emloop 1 i))
             (λ i → g (emloop 1 i) embase)
             λ i → g (emloop 1 i) embase
  l i j = g (emloop 1 i) (emloop 1 j)

  sP : Square (λ i → g (emloop 1 i) embase) refl (λ k → p k .fst embase) λ k → p k .fst embase
  sP k i = hcomp (λ r → λ {(i = i0) → p k .snd (~ r)
                          ; (i = i1) → p k .snd (~ r)
                          ; (k = i0) → g' (emloop 1 i) .snd (~ r)
                          ; (k = i1) → p k .snd (~ r)})
                 ∣ north ∣

  l2 : (Ω^ 2) (KZ/2∙ 2) .fst
  l2 i j =
    hcomp (λ k → λ {(i = i0) → p k .fst (emloop 1 j)
                   ; (i = i1) → p k .fst (emloop 1 j)
                   ; (j = i0) → sP k i
                   ; (j = i1) → sP k i})
          (l i j)

ab : ℕ
ab = fst (genie genie')

okCool : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : ℕ)
        → (isOfHLevel n B)
        → (f : (x : A) → B)
        → ((x y : A) (p q : x ≡ y) (r s : p ≡ q)
              → PathP (λ i → Square
                         (λ j → f (p j)) (λ j → f (q j))
                         (λ _ → f x) λ _ → f y)
                         (λ i j → f (r i j)) λ i j → f (s i j))
        → (x : ∥ A ∥₃)
        → Σ[ y ∈ B ] Σ[ x ∈ A ] f x ≡ y
okCool n hlev f pp ∣ x ∣₃ = f x , x , refl
okCool n hlev f pp (squash₃ x x₁ p q r s i i₁ i₂) = {!!}

ab1 : ab ≡ 1
ab1 = {!ab -- refl!} -- refl

{-
GT-lem : ∀ {ℓ ℓ'} {A : Type ℓ} {B : ∥ A ∥₃ → Type ℓ'} (n : ℕ)
        → ((x : _) → isOfHLevel n (B x))
        → (f : (x : A) → B ∣ x ∣₃)
        → ((x y : A) (p q : x ≡ y) (r s : p ≡ q)
              → PathP (λ i → SquareP (λ j k → B (squash₃ ∣ x ∣₃ ∣ y ∣₃ (cong ∣_∣₃ p) (cong ∣_∣₃ q) (cong (cong ∣_∣₃) r) (cong (cong ∣_∣₃) s) i j k))
                         (λ j → f (p j)) (λ j → f (q j))
                         (λ _ → f x) λ _ → f y)
                         (λ i j → f (r i j)) λ i j → f (s i j))
        → (x : _) → B x
GT-lem {B = B} zero hlev f ind x = hlev x .fst
GT-lem {B = B} (suc n) hlev f ind ∣ x ∣₃ = f x
GT-lem {A = A} {B = B} (suc n) hlev f ind (squash₃ x y p q r s i j k) = {!!} -- help x y p q r s i j k
  where
  help : ((x y : ∥ A ∥₃) (p q : x ≡ y) (r s : p ≡ q)
              → PathP (λ i → SquareP (λ j k → B (squash₃ x y p q r s i j k))
                         (λ j → GT-lem {A = A} {B = B} (suc n) hlev f ind (p j)) (λ j → GT-lem {A = A} {B = B} (suc n) hlev f ind (q j))
                         (λ _ → GT-lem {A = A} {B = B} (suc n) hlev f ind x) λ _ → GT-lem {A = A} {B = B} (suc n) hlev f ind y)
                         (λ i j → GT-lem {A = A} {B = B} (suc n) hlev f ind (r i j)) λ i j → GT-lem {A = A} {B = B} (suc n) hlev f ind (s i j))
  help = GT-lem n (λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ n λ _ → isOfHLevelPathP n (isOfHLevelPathP n (isOfHLevelPathP' n (hlev _) _ _) _ _) _ _)
                  (λ x → GT-lem n ((λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelPathP n (isOfHLevelPathP n (isOfHLevelPathP' n (hlev _) _ _) _ _) _ _))
                                   {!ind x!}
                                   {!!})
                  λ x y p q r s pp → {!!}
-}
genRP : ∀ {ℓ} {B : KZ/2 1 → Type ℓ} → (f : (x : KZ/2-raw) → B (EM₁-raw→EM₁ ℤ/2Gr x))
      → {!(x : !}
genRP = {!!}

-- br : (n i : ℕ) → KZ/2 (suc n) →  
-- br = ?

-- asd : {!(n : ℕ) → ? ≡ ?!}
-- asd = {!!}

-- -- data PushF'' {ℓ} (A : ℕ → Type ℓ) : ℕ → Type ℓ where
-- --   left : {n m : ℕ} → A n → A m → PushF'' A (n PlusBis.+' m)
-- --   lr : (n : ℕ) (x y : A n) → (left x y) ≡ (left y x)

-- -- PushFⁿ : ∀ {ℓ} (n : ℕ) (A : ℕ → Type ℓ) → ℕ → Type ℓ
-- -- PushFⁿ zero A k = PushF'' A k
-- -- PushFⁿ (suc n) A k = PushF'' (PushFⁿ n A) k

-- -- data seqColim {ℓ} (A : ℕ → Type ℓ) (f : (n : ℕ) → A n → A (suc n)) : Type ℓ where
-- --   incl : (n : ℕ) (x : A n) → seqColim A f
-- --   idi : (n : ℕ) (x : A n) → incl n x ≡ incl (suc n) (f n x)

-- -- data seqLim {ℓ} (A : ℕ → Type ℓ) (f : (n : ℕ) → A (suc n) → A n) : Type ℓ where
-- --   incl : (n : ℕ) (x : A n) → seqLim A f
-- --   idi : (n : ℕ) (x : A (suc n)) → incl (suc n) x ≡ incl n (f n x)


-- -- -- lema' : ∀ {ℓ} (A : ℕ → Type ℓ) (C : Type ℓ)
-- -- --   → (f : (n : ℕ) → PushF' A n → C)
-- -- --   → (Ωf : (x y : C) → x ≡ x → y ≡ y)
-- -- --   → (n : ℕ) (x : PushF' A n) (c : C) → c ≡ c -- (A B C : Type ℓ) → (f : PushF A B → C) → (x : PushF A B) → {!!} ≡ {!!}
-- -- -- lema' A C f Ωf .(_ PlusBis.+' _) (left {n = n} {m = m} x x₁) c = Ωf {!!} c (cong (f (n PlusBis.+' n)) (lr n x) ∙ {!!})
-- -- -- lema' A C f Ωf .(n PlusBis.+' n) (lr n x i) c = {!!}



-- -- -- calf : ∀ {ℓ} {A : Type ℓ} → Σ[ AB ∈ Type ℓ × Type ℓ ] (PushF (fst AB) (snd AB)) → Σ[ AB ∈ Type ℓ × Type ℓ ] (PushF (fst AB) (snd AB))
-- -- -- calf ((A , B) , left x x₁) = (A , A) , (left x x)
-- -- -- calf ((A , B) , right x x₁) = (B , B) , right x₁ x₁
-- -- -- calf ((A , .A) , lr x i) = (A , A) , (lr x i)

-- -- -- lema : ∀ {ℓ} (A B C : Type ℓ) → (f : PushF A B → C) → (x : PushF A B) → {!!} ≡ {!!}
-- -- -- lema A B C f (left x x₁) = {!!}
-- -- -- lema A B C f (right x x₁) = {!!}
-- -- -- lema A .A C f (lr x i) = {!!}
-- -- -- -- Push Kₙ Kₘ → Ω (PushF Kₙ Kₘ) → Ω (Kₙ₊ₘ₋₁)

-- -- -- -- blahem : ∀ {ℓ} {A B : Type ℓ} (a : A) (b : B) → PushF A B → Susp (PushF A B)
-- -- -- -- Iso.fun (blahem a b) north = left north b
-- -- -- -- Iso.fun (blahem a b) south = right north b
-- -- -- -- Iso.fun (blahem a b) (merid (left x x₁) i) = {!!}
-- -- -- -- Iso.fun (blahem a b) (merid (right x x₁) i) = {!!}
-- -- -- -- Iso.fun (blahem a b) (merid (lr x i₁) i) = {!!}
-- -- -- -- Iso.inv (blahem a b) = {!!}
-- -- -- -- Iso.rightInv (blahem a b) = {!!}
-- -- -- -- Iso.leftInv (blahem a b) = {!!}



-- -- -- -- _+''_ = PlusBis._+'_

-- -- -- -- prr : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → A → B) (x y : A) (b₀ : B)
-- -- -- --   → (comm : (x y : A) → f x y ≡ f y x)
-- -- -- --   → ((x : B) (n : ℕ) → fst ((Ω^ (suc n)) (B , x)) → fst ((Ω^ n) (B , b₀)))
-- -- -- --   → (n : ℕ)
-- -- -- --   → Σ[ X ∈ Pointed ℓ' ] (A → fst X)
-- -- -- -- prr {A = A} {B = B} f x y b₀ comm ind zero = (B , b₀) , (λ a → {!!})
-- -- -- -- prr {A = A} {B = B} f x y b₀ comm ind (suc n) = {!!}

-- -- -- -- comm : (i : ℕ) → Σ[ f ∈ ((n m : ℕ) → KZ/2 n → KZ/2 m → typ ((Ω^ (suc i)) (KZ/2∙ (n +'' m)))) ]
-- -- -- --                           ((n m : ℕ) (x : _) (y : _) → f n m x y
-- -- -- --                          ∙ subst (λ x → typ ((Ω^ (suc i)) (KZ/2∙ x))) (PlusBis.+'-comm m n) (f m n y x) ≡ refl)
-- -- -- -- comm zero = {!!}
-- -- -- -- fst (comm (suc i)) n m x y = ({!!} ∙ cong (subst (λ x → typ ((Ω^ (suc i)) (KZ/2∙ x))) (PlusBis.+'-comm m n)) (sym (comm i .snd m n y x))) ∙∙ {!cp x y = cp y x!} ∙∙ comm i .snd n m x y
-- -- -- -- snd (comm (suc i)) n m x y = {!!}

-- -- -- -- ⌣ᵢ' : (n m i : ℕ) → KZ/2 n → KZ/2 m → KZ/2 ((n PlusBis.+' m) ∸ i)
-- -- -- -- ⌣ᵢ' zero m zero = cp {n = zero} {m = m}
-- -- -- -- ⌣ᵢ' zero m (suc zero) = {!!}
-- -- -- -- ⌣ᵢ' zero m (suc (suc i)) = {!!}
-- -- -- -- ⌣ᵢ' (suc n) zero i = {!!}
-- -- -- -- ⌣ᵢ' (suc n) (suc m) zero = {!cp !}
-- -- -- -- ⌣ᵢ' (suc n) (suc m) (suc i) x y = {!wedgeConEM.fun!} -- cp x y ={ }= cp y x = cp x y -- ⌣ᵢ' (suc n) (suc m) i x y

-- -- -- -- ⌣ᵢ : (n m i : ℕ) → KZ/2 (suc n) → KZ/2 (suc m) → KZ/2 (((suc n) PlusBis.+' (suc m)) ∸ i)
-- -- -- -- ⌣ᵢ n m zero = cp
-- -- -- -- ⌣ᵢ n m (suc zero) x y =
-- -- -- --   ΩEM+1→EM _
-- -- -- --     ({!!}
-- -- -- --     ∙∙ cong (λ z → z -ₖ ((cp x y))) (cupCommf {n = suc n} {m = suc m} x y)
-- -- -- --     ∙∙ commₖ _ (subst KZ/2 (+'-comm (suc m) (suc n)) (cp y x)) (-ₖ (cp x y))
-- -- -- --     ∙∙ {!!}
-- -- -- --     ∙∙ {!!})
-- -- -- -- ⌣ᵢ n zero (suc (suc i)) x y = {!!}
-- -- -- -- ⌣ᵢ n (suc m) (suc (suc i)) x y = {!⌣ᵢ (n PlusBis.+' (suc m)) zero (suc (suc i)) (cp x y) !}
-- -- -- -- {-
-- -- -- --   subst KZ/2 (sym lem)
-- -- -- --     (predKn _ (subst KZ/2 lem2 (⌣ᵢ n m i x y))
-- -- -- --       (sym (lUnitₖ (suc (suc (n +ℕ m ∸ i)))
-- -- -- --         (subst KZ/2 lem2 (⌣ᵢ n m i x y)))
-- -- -- --         ∙∙ cong (λ s → s +ₖ subst KZ/2 lem2 (⌣ᵢ n m i x y)) (EM→ΩEM+1 (suc (n +ℕ m ∸ i)) {!⌣ᵢ n m i x y!})
-- -- -- --         ∙∙ lUnitₖ (suc (suc (n +ℕ m ∸ i))) (subst KZ/2 lem2 (⌣ᵢ n m i x y)))) -}
-- -- -- --   where
-- -- -- --   lem2 : suc (suc (n +ℕ m)) ∸ i ≡ suc (suc (n +ℕ m ∸ i))
-- -- -- --   lem2 = {!!}

-- -- -- --   lem : (suc (n +ℕ m)) ∸ i ≡ (suc ((n +ℕ m) ∸ i))
-- -- -- --   lem = {!!}

-- -- -- -- cup-i : (n i : ℕ) (x : KZ/2 (suc n)) → KZ/2 (((suc n) PlusBis.+' (suc n)) ∸ i)
-- -- -- -- cup-i zero i = {!!}
-- -- -- -- cup-i (suc n) zero = {!!}
-- -- -- -- cup-i (suc zero) (suc i) x = {!!}
-- -- -- -- cup-i (suc (suc n)) (suc zero) x = testi {n = 2 +ℕ n} x
-- -- -- -- cup-i (suc (suc n)) (suc (suc zero)) x = {!!}
-- -- -- -- cup-i (suc (suc n)) (suc (suc (suc i))) x = subst KZ/2 {!!} (cup-i (suc n) (suc i) {!testi {n = suc (suc n)} x!})

-- -- -- -- steenrod : (n i : ℕ) (x : KZ/2 n) → KZ/2 (i +ℕ n)
-- -- -- -- steenrod n zero x = x
-- -- -- -- steenrod zero (suc i) x = 0ₖ (suc (i +ℕ zero))
-- -- -- -- steenrod (suc zero) (suc zero) x = cp {n = 1} {m = 1} x x
-- -- -- -- steenrod (suc (suc n)) (suc zero) x = {!x!}
-- -- -- -- steenrod (suc n) (suc (suc i)) x = {! -- steenrod n (suc (suc (suc i)))!}

-- -- -- -- -- redEM : (k n : ℕ) → KZ/2 (n +ℕ suc k) → KZ/2 (suc n)
-- -- -- -- -- redEM zero n x = subst KZ/2 (+-comm n 1) x
-- -- -- -- -- redEM (suc zero) n x = {!!}
-- -- -- -- -- redEM (suc (suc k)) n x =
-- -- -- -- --   redEM (suc zero) n (subst KZ/2 (+-comm 2 n) (redEM (suc k) (suc n) (subst KZ/2 (+-suc n (suc (suc k))) x)))

-- -- -- -- -- steenrodSq : (k n : ℕ) → Trichotomy n k → KZ/2 k → KZ/2 (n +' k)
-- -- -- -- -- steenrodSq k zero p x = x
-- -- -- -- -- steenrodSq zero (suc n) p x = 0ₖ _
-- -- -- -- -- steenrodSq (suc k) (suc n) p x = {!cp (steenrodSq (suc k) n (_ ≟ _) x) x!}

-- -- -- -- -- -- steenrodSq k (suc n) (lt p) x = {!!}
-- -- -- -- -- -- steenrodSq k (suc n) (eq p) x = subst KZ/2 (λ i → p (~ i) +' k) (cp x x)
-- -- -- -- -- -- steenrodSq k (suc n) (gt p) x = {!cp (steenrodSq k n (_ ≟ _) x) x!}
-- -- -- -- -- --   where
-- -- -- -- -- --   l : {!!}
-- -- -- -- -- --   l = {!? ≟ ?!}


-- -- -- -- -- -- -- lem1 : (X : Type) (n i : ℕ) → H₂ X n → H₂ X (i +ℕ n)
-- -- -- -- -- -- -- lem1 X n zero x = x
-- -- -- -- -- -- -- lem1 X n (suc zero) =
-- -- -- -- -- -- --   sT.rec
-- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- --     λ f → {!stRec ?!}
-- -- -- -- -- -- -- lem1 X n (suc (suc i)) x = {!!}

-- -- -- -- -- -- -- lema : (n i : ℕ) → KZ/2 n → KZ/2 (i +ℕ n) 
-- -- -- -- -- -- -- lema n zero x = x
-- -- -- -- -- -- -- lema n (suc zero) = {!!}
-- -- -- -- -- -- -- lema n (suc (suc i)) x = lema1 (suc (i +ℕ n)) (lema n (suc i) x)
