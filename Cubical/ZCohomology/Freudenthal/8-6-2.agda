{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Freudenthal.8-6-2 where

open import Cubical.Foundations.Prelude


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Freudenthal.Prelim
open import Cubical.ZCohomology.Freudenthal.7-5-7
open import Cubical.ZCohomology.Freudenthal.trivFunConnected
open import Cubical.ZCohomology.Freudenthal.8-6-1
open import Cubical.HITs.Sn
open import Cubical.Foundations.Everything
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.NatMinusOne.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation 
open import Cubical.HITs.Nullification
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.HITs.Truncation

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

      
transpHelper : {a b c : A} (r : b ≡ c) (q : a ≡ b) (p : a ≡ c) → PathP (λ i → a ≡ r i) q p → q ∙ r ≡ p
transpHelper {ℓ} {A} {a} {b} {c} = J {ℓ} {A} {b} (λ c r →  (q : a ≡ b) (p : a ≡ c) → PathP (λ i → a ≡ r i) q p → q ∙ r ≡ p) λ p q path → sym (rUnit p) ∙ path
{- SORRY I HAD TO USE J -}


a₀-map : (A : Pointed ℓ)  → Unit → typ A
a₀-map A x = pt A

b₀-map : (B : Pointed ℓ) → Unit → typ B
b₀-map B x = pt B

conOfa₀-map : (A : Pointed ℓ) (n : ℕ) → (is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A)) → is- (pred₋₂ (ℕ→ℕ₋₂ n)) -Connected (a₀-map A)
conOfa₀-map A n conA = trivFunConnected (pred₋₂ (ℕ→ℕ₋₂ n)) (transport (λ i → (is- pmId n (~ i) -ConnectedType (typ A))) conA)

conOfb₀-map : (A : Pointed ℓ) (n : ℕ) → (is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A)) → is- (pred₋₂ (ℕ→ℕ₋₂ n)) -Connected (b₀-map A)
conOfb₀-map A n conA = trivFunConnected (pred₋₂ (ℕ→ℕ₋₂ n)) (transport (λ i → (is- pmId n (~ i) -ConnectedType (typ A))) conA)

module prelims (A : Pointed ℓ) (B : Pointed ℓ') (n m : ℕ)
               (conA : is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A))
               (conB : is- (ℕ→ℕ₋₂ m) -ConnectedType (typ B))
               (P : (typ A) → (typ B) → HLevel (ℓ-max ℓ ℓ') (2+ (ℕ→ℕ₋₂ (n + m))))
               (f : ((a : (typ A)) → fst (P a (pt B))))
               (g : ((b : (typ B)) → fst (P (pt A) b)))  (p : f (pt A) ≡ g (pt B))
       where
       Q : (typ A) → Type (ℓ-max ℓ ℓ')
       Q a = Σ ((b : (typ B)) → fst (P a b )) λ k → f a ≡ k (pt B)

       f-map : (a : typ A) → ((b : typ B) → fst (P a b)) → fst (P a (pt B))
       f-map a g = inducedFun {A = Unit} {B = typ B} {k = (ℕ→ℕ₋₂ (n +  m))} (b₀-map B) (P a) g tt

       QisFib : (a : typ A) → Q a ≡ fiber (f-map a) (f a)
       QisFib a = isoToPath (iso (λ x → (x .fst) , (sym (x .snd))) (λ b → (fst b) , (sym (snd b))) (λ a → refl) λ b → refl)

       QisFib2 : (a : typ A) → Q a  ≡ fiber (inducedFun {A = Unit} {B = typ B} {k = (ℕ→ℕ₋₂ (n + m))} (b₀-map B) (P a)) λ tt → (f a)
       QisFib2 a = QisFib a ∙ isoToPath (iso (λ x → (fst x) , (funExt (λ y → snd x))) (λ x → (fst x) , (cong (λ x → x tt) (snd x))) (λ x → refl) λ x → refl)

Lemma862 : (A : Pointed ℓ) (B : Pointed ℓ') (n m : ℕ) →
           (is- (ℕ→ℕ₋₂ n) -ConnectedType (typ A)) →
           (is- (ℕ→ℕ₋₂ m) -ConnectedType (typ B)) →
           (P : (typ A) → (typ B) → HLevel (ℓ-max ℓ ℓ') (2+ (ℕ→ℕ₋₂ (n + m)))) →
           (f : ((a : (typ A)) → fst (P a (pt B)))) →
           (g : ((b : (typ B)) → fst (P (pt A) b))) →
           (p : f (pt A) ≡ g (pt B)) →
           Σ ((a : typ A) → (b : typ B) → fst (P a b)) λ h → Σ (((a : typ A) → h a (pt B) ≡ f a) × ((b : typ B) → h (pt A) b ≡ g b) ) λ pair → p ≡ sym ((proj₁ pair) (pt A) ) ∙ (proj₂ pair) (pt B)
Lemma862 {ℓ = ℓ} {ℓ' = ℓ'} (A , a₀) (B , b₀) n zero conA conB P f g p = {!!}
Lemma862 {ℓ = ℓ} {ℓ' = ℓ'} (A , a₀) (B , b₀) n (suc m) conA conB P f g p = {!!} {- (λ a b → ((typesQ a₀ .fst) a) .fst b) , (((λ a → sym ((typesQ a₀) .fst a .snd)) , λ b → cong (λ x → (x .fst) b) (((typesQ) a₀) .snd)) , sym (transpHelper _ _ _ (cong (λ x → x .snd) (((typesQ) a₀) .snd)))) -}
  where
  {-
  Q : A → Type (ℓ-max ℓ ℓ')
  Q a = Σ ((b : B) → fst (P a b )) λ k → f a ≡ k (b₀)

  a₀-map : Unit → A
  a₀-map x = a₀

  b₀-map : Unit → B
  b₀-map x = b₀

  conOfa₀-map : is- (pred₋₂ (ℕ→ℕ₋₂ n)) -Connected a₀-map
  conOfa₀-map = trivFunConnected (pred₋₂ (ℕ→ℕ₋₂ n)) (transport (λ i → (is- pmId n (~ i) -ConnectedType A)) conA)

  conOfb₀-map : is- (pred₋₂ (ℕ→ℕ₋₂ (suc m))) -Connected b₀-map
  conOfb₀-map = trivFunConnected (pred₋₂ (ℕ→ℕ₋₂ (suc m))) (transport (λ i → (is- pmId (suc m) (~ i) -ConnectedType B)) conB)

  f-map : (a : A) → ((b : B) → fst (P a b)) → fst (P a b₀)
  f-map a g = inducedFun {A = Unit} {B = B} {k = (ℕ→ℕ₋₂ (n + (suc m)))} b₀-map (P a) g tt

  QisFib : (a : A) → Q a ≡ fiber (f-map a) (f a)
  QisFib a = isoToPath (iso (λ x → (x .fst) , (sym (x .snd))) (λ b → (fst b) , (sym (snd b))) (λ a → refl) λ b → refl)

  QisFib2 : (a : A) → Q a  ≡ fiber (inducedFun {A = Unit} {B = B} {k = (ℕ→ℕ₋₂ (n + (suc m)))} b₀-map (P a)) λ tt → (f a)
  QisFib2 a = QisFib a ∙ isoToPath (iso (λ x → (fst x) , (funExt (λ y → snd x))) (λ x → (fst x) , (cong (λ x → x tt) (snd x))) (λ x → refl) λ x → refl)

  lemma2 : (a : A) → isOfHLevel (2+ (-2+ ((n + suc m) - m))) (fiber (inducedFun {A = Unit} {B = B} {k = (ℕ→ℕ₋₂ (n + (suc m)))} prelims.b₀-map (P a)) λ tt → (f a))
  lemma2 a = Lemma861 m (n + (suc m)) (suc n) b₀-map conOfb₀-map (P a) (+-suc n m) λ tt → (f a)
  

  conOfQ : (a : A) → isOfHLevel (2+ ((pred₋₂ (ℕ→ℕ₋₂ n)))) (Q a)
  conOfQ a = transport (λ i → isOfHLevel (2+ ((pred₋₂ (ℕ→ℕ₋₂ n)))) (QisFib2 a (~ i))) ((transport (λ i → isOfHLevel (natLemma i) (QisFib2 a i1))) (lemma2 a ))
    where
    natLemma : (2+ (-2+ ((n + suc m) - m))) ≡ (2+ pred₋₂ (ℕ→ℕ₋₂ n))
    natLemma i = 2+ (((λ j → -2+ natLemma1 n m j) ∙ λ j → natLemma2 n j) i)
      where
      natLemma1 : (n m : ℕ) → ((n + suc m) - m) ≡  suc n
      natLemma1 n m = (λ i → ((+-suc n m i) - m)) ∙ (λ i → (suc (+-comm n m i) - m)) ∙ ((λ i → ((+-suc m n (~ i)) - m))) ∙ (λ i → (+-comm m (suc n) i) - m) ∙  -assocHelp {a = suc n} {b = m}
      natLemma2 : (n : ℕ) → (-2+ suc n) ≡ (pred₋₂ (ℕ→ℕ₋₂ n))
      natLemma2 zero = refl
      natLemma2 (suc n) = refl
      


  typesQ : (a : A) → Σ ((a : A) → Q a) λ ℓ → ℓ a₀ ≡ (g , p)
  typesQ a  = (fst (Lemma757i→iii a₀-map ((pred₋₂ (ℕ→ℕ₋₂ n))) conOfa₀-map (λ a → (Q a , conOfQ a ))) (λ x → (g , p))) ,
              cong (λ f → f tt) (snd (Lemma757i→iii a₀-map ((pred₋₂ (ℕ→ℕ₋₂ n))) conOfa₀-map (λ a → (Q a , conOfQ a ))) (λ x → (g , p)))
  -}

  lemma2 : (a : A) → isOfHLevel (2+ (-2+ ((n + suc m) - m))) (fiber (inducedFun {A = Unit} {B = B} {k = (ℕ→ℕ₋₂ (n + (suc m)))} (b₀-map (B , b₀)) (P a)) λ tt → (f a))
  lemma2 a = Lemma861 m (n + (suc m)) (suc n) (b₀-map (B , b₀)) (conOfb₀-map (B , b₀) (suc m) conB) (P a) (+-suc n m) λ tt → (f a)

  conOfQ : (a : A) → isOfHLevel (2+ ((pred₋₂ (ℕ→ℕ₋₂ n)))) (prelims.Q (A , a₀) (B , b₀) n (suc m) conA conB P f g p a)
  conOfQ a = transport (λ i → isOfHLevel (2+ ((pred₋₂ (ℕ→ℕ₋₂ n)))) (prelims.QisFib2 (A , a₀) (B , b₀) n (suc m) conA conB P f g p a (~ i))) ((transport (λ i → isOfHLevel (natLemma i) ((prelims.QisFib2 (A , a₀) (B , b₀) n (suc m) conA conB P f g p) a i1))) (lemma2 a ))
    where
    natLemma : (2+ (-2+ ((n + suc m) - m))) ≡ (2+ pred₋₂ (ℕ→ℕ₋₂ n))
    natLemma i = 2+ (((λ j → -2+ natLemma1 n m j) ∙ λ j → natLemma2 n j) i)
      where
      natLemma1 : (n m : ℕ) → ((n + suc m) - m) ≡  suc n
      natLemma1 n m = (λ i → ((+-suc n m i) - m)) ∙ (λ i → (suc (+-comm n m i) - m)) ∙ ((λ i → ((+-suc m n (~ i)) - m))) ∙ (λ i → (+-comm m (suc n) i) - m) ∙  -assocHelp {a = suc n} {b = m}
      natLemma2 : (n : ℕ) → (-2+ suc n) ≡ (pred₋₂ (ℕ→ℕ₋₂ n))
      natLemma2 zero = refl
      natLemma2 (suc n) = refl

