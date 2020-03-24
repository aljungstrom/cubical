{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.FreudenthalFix2.FinishingUpOuter where


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.FreudenthalFix2.Prelim
open import Cubical.ZCohomology.FreudenthalFix2.Code
open import Cubical.Foundations.Everything
open import Cubical.ZCohomology.FreudenthalFix2.FinishingUp4
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Prod
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_ ; _-_ ; +-comm )
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation
open import Cubical.Data.HomotopyGroup

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

{- funExt⁻ (Lemma296Funs.inv'' {X = Sutestsp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                                      (merid a) (λ p → ∥ fiber (λ y → σ y {a}) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                                      (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                                                      (equivTest' {X = Susp A} (merid a)
                                                                                                  {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                                  {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                        (λ q → ua' (RlFun2 a a n iscon q , RlFunEquiv2 a a n iscon q))))
                                                                                       (transport (λ i → north ≡ merid a i) (σ x1 {a}))) -}
littleCanceller : {a b c d e : A} → (p : a ≡ b) (q : a ≡ c) (r : c ≡ d) (s : d ≡ e) →
                                       p ∙ (sym p ∙ q ∙ r ∙ s) ∙ sym s ≡ q ∙ r
littleCanceller {a = a} {b = b} {c = c} p q r s  = p ∙ (sym p ∙ q ∙ r ∙ s) ∙ sym s     ≡⟨ assoc p (sym p ∙ q ∙ r ∙ s) (sym s) ⟩ 
                                                   (p ∙ sym p ∙ q ∙ r ∙ s) ∙ sym s     ≡⟨ (λ j → assoc p (sym p) (q ∙ r ∙ s) j ∙ sym s) ⟩ 
                                                   ((p ∙ sym p) ∙ q ∙ r ∙ s) ∙ sym s   ≡⟨ (λ j → (rCancel p j ∙ q ∙ r ∙ s) ∙ sym s) ⟩ 
                                                   (refl ∙ q ∙ r ∙ s) ∙ sym s          ≡⟨ (λ j → lUnit (q ∙ r ∙ s) (~ j) ∙ sym s) ⟩ 
                                                   (q ∙ r ∙ s) ∙ sym s                 ≡⟨ (λ j → assoc q r s j ∙ sym s) ⟩ 
                                                   ((q ∙ r) ∙ s) ∙ sym s               ≡⟨ sym (assoc (q ∙ r) s (sym s)) ⟩ 
                                                   (q ∙ r) ∙ s ∙ sym s                 ≡⟨ (λ j → (q ∙ r) ∙ (rCancel s j)) ⟩ 
                                                   (q ∙ r) ∙ refl                      ≡⟨ sym (rUnit (q ∙ r)) ⟩
                                                   q ∙ r ∎


littleCanceller2 : {a b c d e : A} → (p : a ≡ b) (q : b ≡ c) (r : b ≡ d) (s : b ≡ e) →
                                       (p ∙ q) ∙ ((sym q) ∙ r) ∙ sym r ∙ s ≡ p ∙ s
littleCanceller2 = {!!}




pairLemmaCancel : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) →
                  pairLemma3 (p ∙ sym (λ _ → y)) (λ _ → y) ∙ sym (assocJ p (λ _ → y) (λ _ → y)) ∙ (λ i → p ∙ lCancel (λ _ → y) i) ∙ sym (rUnit p)
                  ≡
                  transportRefl (p ∙ sym (λ _ → y)) ∙ sym (rUnit p)
pairLemmaCancel {x = x} =
        J (λ y p → pairLemma3 (p ∙ sym (λ _ → y)) (λ _ → y) ∙ sym (assocJ p (λ _ → y) (λ _ → y)) ∙ (λ i → p ∙ lCancel (λ _ → y) i) ∙ sym (rUnit p)
                    ≡
                   transportRefl (p ∙ sym (λ _ → y)) ∙ sym (rUnit p))
          ((λ k → pairLemma3Id (refl ∙ (λ i → x)) (λ _ → x) k ∙
                  (λ i → assocJ refl (λ _ → x) (λ _ → x) (~ i)) ∙
                  (λ i → refl ∙ lCancel (λ _ → x) i) ∙ (λ i → rUnit refl (~ i))) ∙
          (λ k → pairLemma3*Refl (refl ∙ (λ i → x)) k ∙
                  (λ i → assocJRefl k (~ i)) ∙
                  (λ i → refl ∙ lCancel (λ _ → x) i) ∙ (λ i → rUnit refl (~ i))) ∙
          (λ k → (transportRefl (refl ∙ (λ _ → x)) ∙ rUnit (refl ∙ (λ _ → x))) ∙
                  (symDistr (λ i → refl ∙ rCancel refl i) (rUnit (refl ∙ refl)) k ) ∙
                  (λ i → refl ∙ lCancel (λ _ → x) i) ∙ (λ i → rUnit refl (~ i))) ∙
          littleCanceller2 (transportRefl (refl ∙ (λ _ → x))) (rUnit (refl ∙ (λ _ → x))) (λ i → refl ∙ rCancel refl (~ i)) (λ i → rUnit refl (~ i)))




inv-rUnit : ∀ {ℓ} {A : Type ℓ} (x : A) → (λ i → rUnit (rUnit (λ _ → x) (~ i)) i ) ≡ refl
inv-rUnit x = transport (λ i → PathP (λ j → (lCancel (λ k → (λ _ → x) ∙ (λ _ → x) ≡ rUnit (λ _ → x) k) i) j)
                                 (λ i → rUnit (rUnit (λ _ → x) (~ i)) i )
                                 refl)
                    (lemma2 x)
  where
  lemma2 : ∀ {ℓ} {A : Type ℓ} (x : A) →
           PathP (λ i → ((λ k → (λ _ → x) ∙ (λ _ → x) ≡ rUnit (λ _ → x) (~ k)) ∙
                          λ k → (λ _ → x) ∙ (λ _ → x) ≡ rUnit (λ _ → x) k) i)
                 (λ i → rUnit (rUnit (λ _ → x) (~ i)) i )
                 refl
  lemma2 x = compPathP (λ k i → rUnit (rUnit (λ _ → x) (~ i)) (i ∧ (~ k)))
                       λ k i → rUnit (λ _ → x) (~ i ∨ k)


ok : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} {A B : x ≡ y → Type ℓ'} (p : x ≡ y) → 
                                        cong A (rUnit (transport (λ i → x ≡ y) (p ∙ (λ _ → y)))) ∙
                                        cong A (λ i → (transportRefl (p ∙ (λ _ → y)) i) ∙ refl) ∙
                                        refl ∙
                                        cong A (λ i → rUnit p (~ i) ∙ refl)
                                        ≡
                                        cong A (transportRefl (p ∙ (λ _ → y)))
ok {ℓ' = ℓ'} {x = x} {y = y} {A = A} {B = B} p = 
         J (λ y p → (A B : x ≡ y → Type ℓ') →
                    cong A (rUnit (transport (λ i → x ≡ y) (p ∙ (λ _ → y)))) ∙
                    (cong A (λ i → (transportRefl (p ∙ (λ _ → y)) i) ∙ refl)) ∙
                    refl ∙
                    (cong A (λ i → rUnit p (~ i) ∙ refl))
                    ≡
                    cong A (transportRefl (p ∙ (λ _ → y))))
                    (λ A B → ((λ k → (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (refl ∙ (λ _ → x))) (i ∧ (~ k)))) ∙
                                    (λ i → A (rUnit (transportRefl (refl ∙ (λ _ → x)) i) (~ k))) ∙
                                    (λ i → A (rUnit (rUnit ((λ _ → x)) ((~ k) ∨ (~ i))) ((~ k) ∨ i))) ∙
                                    λ i → A ((rUnit (λ _ → x) ((~ i) ∧ (~ k))) ∙ refl)) ) ∙
                             (λ k → lUnit ((λ i → A (transportRefl (refl ∙ (λ _ → x)) i)) ∙
                                           (rUnit (λ i → A (rUnit (rUnit ((λ _ → x)) (~ i)) i )) (~ k))) (~ k)) ∙
                             (λ k → cong A (transportRefl ((λ _ → x) ∙ (λ _ → x))) ∙
                                    λ i → A (inv-rUnit x k i)) ∙
                             sym (rUnit (cong A (transportRefl ((λ _ → x) ∙ (λ _ → x))))))
                    p A B


funExt-part' : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} (ma mx1 : x ≡ y)  →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                                                                  funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y}
                                                                                       ma A
                                                                                       B
                                                                                       (equivTest' {X = X} ma
                                                                                                   {A = A}
                                                                                                   {B = B}
                                                                                         r))
                                                                                        (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
                ≡
                cong (λ f → f (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))) (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} ma A) ∙
                transportRefl (A (transport (λ i → x ≡ ma (~ i)) (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))) ∙
                cong A (pairLemma3 (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)) (sym ma)) ∙
                r (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
funExt-part' {ℓ' = ℓ'} {X = X} {x = x} {y = y} {A = A} {B = B} ma mx1 =

              J (λ y ma → {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} (mx1 : x ≡ y)  →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                                                                  funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y}
                                                                                       ma A
                                                                                       B
                                                                                       (equivTest' {X = X} ma
                                                                                                   {A = A}
                                                                                                   {B = B}
                                                                                         r))
                                                                                        (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
                ≡
                cong (λ f → f (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))) (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} ma A) ∙
                transportRefl (A (transport (λ i → x ≡ ma (~ i)) (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))) ∙
                cong A (pairLemma3 (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)) (sym ma)) ∙
                r (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))
                (λ {A} {B} mx1 r → (λ k →  funExt⁻ (Lemma296Funs.inv''Id {X = X} {A = λ y → x ≡ y} (λ _ → x) A B (~ k)
                                                                         (equivTestId {X = X} (λ _ → x) {A = A} {B = B} r k))
                                                   (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                    (λ k →  funExt⁻ (ReflCases.invRefl {X = X} {A = λ y → x ≡ y} A B k 
                                                                         (equivTestRefl {X = X} {A = A} {B = B} k r))
                                                      (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                    (λ k →  funExt⁻ (transportRefl A ∙
                                                   funExt λ z → sym (transportRefl (A z))  ∙
                                                                (transportRefl (A z) ∙
                                                                cong A (rUnit z) ∙
                                                                r z ∙
                                                                cong B (sym (transportRefl z))) ∙
                                                                λ i → (B (transportRefl z i)))
                                                   (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                    (λ k →  funExt⁻ (transportRefl A ∙
                                                   funExt λ z → littleCanceller (sym (transportRefl (A z)))
                                                                                (cong A (rUnit z))
                                                                                (r z)
                                                                                (cong B (sym (transportRefl z))) k)
                                                   (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                    (λ k → funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                           cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                       (assoc (funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))
                                              ( cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))))
                                              (r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                       (λ k → lemma1 {X = X} {A = A} mx1 k ∙
                                              r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                      (sym (assoc (transportRefl
                                                    (A
                                                     (transport (λ i → x ≡ x)
                                                      (transport (λ i → x ≡ x) (mx1 ∙ (λ i → x))))))
                                                  ((λ i →
                                                       A
                                                       (pairLemma3
                                                        (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ i₁ → x)))
                                                        (λ i₁ → x) i)))
                                                  (r (transport (λ i → x ≡ x) (mx1 ∙ (λ i → x)))))) ∙
                                      (lUnit (transportRefl
                                                    (A
                                                     (transport (λ i → x ≡ x)
                                                      (transport (λ i → x ≡ x) (mx1 ∙ (λ i → x)))))
                                                    ∙
                                                    (λ i →
                                                       A
                                                       (pairLemma3
                                                        (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ i₁ → x)))
                                                        (λ i₁ → x) i))
                                                    ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ i → x))))) ∙
                                      λ k → (λ i →
                                                       Lemma294'Refl {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} A (~ k) i
                                                       (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ i₁ → x))))
                                                    ∙
                                                    transportRefl
                                                    (A
                                                     (transport (λ i → x ≡ x)
                                                      (transport (λ i → x ≡ x) (mx1 ∙ (λ i → x)))))
                                                    ∙
                                                    (λ i →
                                                       A
                                                       (pairLemma3
                                                        (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ i₁ → x)))
                                                        (λ i₁ → x) i))
                                                    ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ i → x))))

                ma {A} {B} mx1
                             where
                             lemma1 : ∀ {ℓ ℓ'} {X : Type ℓ} {x : X} {A : x ≡ x → Type ℓ'} (mx1 : x ≡ x) →
                                        funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                           cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ≡
                                        transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                        (λ i → A (pairLemma3 (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) (λ _ → x) i))
                             lemma1 {x = x} {A = A}  mx1 = sym ((λ k → transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                                                       (λ i → A (pairLemma3Id (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) (λ _ → x) k i))) ∙
                                                      (λ k → transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                                             (λ i → A (pairLemma3*Refl (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) k i))) ∙
                                                      (λ k → transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                                             λ i → A ((transportRefl (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                                                       rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x)))) i)) ∙
                                                      (λ k → transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                                             congComp2 A (transportRefl (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))))
                                                                         (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x)))) (~ k)) ∙
                                                      (λ k → (λ i → transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) (i ∨ k)) ∙
                                                            cong A (transportRefl (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                                             cong A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                                      (sym (lUnit (cong A (transportRefl (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                                             cong A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))))))))

funExt-part'' : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} (ma mx1 : x ≡ y)  →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                cong (λ f → f (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))) (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} ma A) ∙
                transportRefl (A (transport (λ i → x ≡ ma (~ i)) (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))) ∙
                cong A (pairLemma3 (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)) (sym ma)) ∙
                r (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
                ≡
                (cong (λ f → f (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))) (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} ma A) ∙
                transportRefl (A (transport (λ i → x ≡ ma (~ i)) (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))) ∙
                cong A (transpRCancel (λ i → x ≡ ma (~ i)) (mx1 ∙ sym ma))) ∙
                r mx1 ∙
                cong B (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙ sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1)))
funExt-part'' {ℓ' = ℓ'} {X = X} {x = x} {y = y} {A = A} {B = B} ma mx1 =
              J (λ y ma → ( mx1 : x ≡ y) {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'}
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                cong (λ f → f (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))) (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} ma A) ∙
                transportRefl (A (transport (λ i → x ≡ ma (~ i)) (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))) ∙
                cong A (pairLemma3 (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)) (sym ma)) ∙
                r (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
                ≡
                (cong (λ f → f (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))) (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} ma A) ∙
                transportRefl (A (transport (λ i → x ≡ ma (~ i)) (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma)))) ∙
                cong A (transpRCancel (λ i → x ≡ ma (~ i)) (mx1 ∙ sym ma))) ∙
                r mx1 ∙
                cong B (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙ sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1))))
                (λ p {A} {B} r → (λ k → cong (λ f → f (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) (Lemma294'Refl {A = λ y → x ≡ y} {B = λ _ → Type ℓ'}  A k) ∙
                                        transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (p ∙ (λ _ → x))))) ∙
                                        cong A (pairLemma3 (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) (λ _ → x)) ∙
                                        r (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                 (sym (lUnit (transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (p ∙ (λ _ → x))))) ∙
                                          cong A (pairLemma3 (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) (λ _ → x)) ∙
                                          r (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))))) ∙
                                 (sym (lUnit (cong A (pairLemma3 (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) (λ _ → x)) ∙
                                          r (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))))) ∙
                                 (λ k → cong A (pairLemma3Id (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) (λ _ → x) k) ∙
                                         r (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                 (λ k → cong A (pairLemma3*Refl (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) k) ∙
                                         r (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                 (λ k → cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        r (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                 (fixLater {A = A} {B = B} p r) ∙
                                 (λ k → cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        refl ∙ refl ∙
                                        r (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) ∙
                                        refl ∙ refl) ∙
                                 (λ k → cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        cong A (λ i → (transportRefl (p ∙ (λ _ → x)) (k ∧ i)) ∙ refl) ∙ refl ∙
                                        r (transportRefl (p ∙ (λ _ → x)) k) ∙
                                        refl ∙ cong B λ i → (transportRefl (p ∙ (λ _ → x)) (k ∧ (~ i)))) ∙
                                 (λ k → cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        cong A (λ i → (transportRefl (p ∙ (λ _ → x)) i) ∙ refl) ∙ cong A (λ i → rUnit p (~ k ∨ (~ i)) ∙ refl) ∙
                                        r (rUnit p (~ k)) ∙
                                        cong B (λ i → rUnit p (~ k ∨ i)) ∙ cong B λ i → ((transportRefl (p ∙ (λ _ → x)) (~ i)))) ∙
                                 (λ k → congComp2 A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x))))) (rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x))))
                                        (~ k) ∙
                                        cong A (λ i → (transportRefl (p ∙ (λ _ → x)) i) ∙ refl) ∙
                                        lUnit (cong A (λ i → rUnit p (~ i) ∙ refl)) k ∙
                                        r p ∙
                                        cong B (λ i → rUnit p i) ∙ cong B λ i → (transportRefl (p ∙ (λ _ → x)) (~ i))) ∙
                                 fixLater2 (cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x))))))
                                           (cong A ((rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x))))))
                                           (cong A (λ i → (transportRefl (p ∙ (λ _ → x)) i) ∙ refl))
                                           (cong A (λ i → rUnit p (~ i) ∙ refl))
                                           (r p)
                                           (cong B (λ i → rUnit p i) ∙ cong B λ i → (transportRefl (p ∙ (λ _ → x)) (~ i))) ∙
                                 (λ k → (cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x))))) ∙
                                        ok {A = A} {B = B} p k ) ∙
                                        r p ∙
                                        cong B (λ i → rUnit p i) ∙ cong B λ i → (transportRefl (p ∙ (λ _ → x)) (~ i))) ∙
                                 (λ k → congComp2 A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x))))) (transportRefl (p ∙ (λ _ → x))) k ∙
                                        r p ∙
                                        (congComp2 B (rUnit p) (λ i → (transportRefl (p ∙ (λ _ → x)) (~ i))) k)) ∙
                                 (λ k → cong A (transportRefl (transport refl (p ∙ (λ _ → x))) ∙ transportRefl (p ∙ (λ _ → x))) ∙
                                        r p ∙
                                        cong B (symDistr (transportRefl (p ∙ sym (λ _ → x))) (sym (rUnit p)) (~ k))) ∙
                                 (λ k → cong A (transportRefl (transport refl (p ∙ (λ _ → x))) ∙ transportRefl (p ∙ (λ _ → x))) ∙
                                        r p ∙
                                        cong B (sym (pairLemmaCancel p (~ k)))) ∙
                                 (λ k → cong A (transpRCancelRefl (p ∙ (λ _ → x)) (~ k)) ∙
                                        r p ∙
                                        cong B (sym (pairLemma3 (p ∙ sym (λ _ → x)) (λ _ → x) ∙
                                                    sym (assocJ p (λ _ → x) (λ _ → x)) ∙
                                                    (λ i → p ∙ lCancel (λ _ → x) i) ∙ sym (rUnit p)))) ∙
                                 (λ k → lUnit (lUnit (cong A (transpRCancel (λ i → x ≡ x) (p ∙ (λ _ → x)))) k) k ∙
                                        r p ∙
                                        cong B (sym (pairLemma3 (p ∙ (λ _ → x)) (λ _ → x) ∙
                                                    sym (assocJ p (λ _ → x) (λ _ → x)) ∙
                                                    (λ i → p ∙ lCancel (λ _ → x) i) ∙ sym (rUnit p)))) ∙
                                 λ k → (cong (λ f → f (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) (Lemma294'Refl {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} A (~ k)) ∙
                transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (p ∙ (λ _ → x))))) ∙
                cong A (transpRCancel (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                r p ∙
                cong B (sym (pairLemma3 (p ∙ (λ _ → x)) (λ _ → x) ∙
                            sym (assocJ p (λ _ → x) (λ _ → x)) ∙
                            (λ i → p ∙ lCancel (λ _ → x) i) ∙ sym (rUnit p))))
                ma mx1 {A} {B}
                where
                fixLater : {A : x ≡ x → Type ℓ'} {B : x ≡ x → Type ℓ'} (p : x ≡ x) (r : (mx2 : x ≡ x) → A (mx2 ∙ (λ _ → x)) ≡ B mx2) →
                           cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        r (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) ≡
                           cong A (transportRefl ((transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        rUnit (transport (λ i → x ≡ x) (p ∙ (λ _ → x)))) ∙
                                        refl ∙ refl ∙
                                        r (transport (λ i → x ≡ x) (p ∙ (λ _ → x))) ∙
                                        refl ∙ refl
                fixLater = {!!}

                fixLater2 : ∀ {ℓ} {A : Type ℓ} {a b c d e f g : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : e ≡ f) (u : f ≡ g) →
                                  (p ∙ q) ∙ r ∙ (refl ∙ s) ∙ t ∙ u ≡ (p ∙ q ∙ r ∙ refl ∙ s) ∙ t ∙ u
                fixLater2 p q r s t u = {!!}

funExt-part''' : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} (ma mx1 : x ≡ y)  →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                (λ i → A (transpRCancel (λ i₁ → x ≡ ma (~ i₁)) (mx1 ∙ sym ma) (~ i))) ∙ 
                funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y} ma A B (equivTest' {X = X} ma
                                                                                          {A = A}
                                                                                          {B = B}
                                                                                         r))
                         (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
                  ≡
                 r mx1 ∙
                 cong B (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙ sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1)))
funExt-part''' {ℓ' = ℓ'} {X = X} {x = x} {A = A} {B = B} ma mx1 r =
               J (λ y ma → (A : x ≡ x → Type ℓ') (B : x ≡ y → Type ℓ') (mx1 : x ≡ y)  →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                (λ i → A (transpRCancel (λ i₁ → x ≡ ma (~ i₁)) (mx1 ∙ sym ma) (~ i))) ∙ 
                funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y} ma A B (equivTest' {X = X} ma
                                                                                          {A = A}
                                                                                          {B = B}
                                                                                         r))
                         (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))
                  ≡
                 r mx1 ∙
                 cong B (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙ sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1))))
                 (λ A B mx1 r → (λ k → (λ i → A (transpRCancel (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x)) (~ i))) ∙ 
                                       ((funExt-part' {X = X} {x = x} {A = A} {B = B} (λ _ → x) mx1 r) ∙
                                        (funExt-part'' {X = X} {x = x} {A = A} {B = B} (λ _ → x) mx1 r)) k) ∙
                                (λ k → ((λ i → A (transpRCancelRefl (mx1 ∙ (λ _ → x)) k (~ i)))) ∙
                                       (cong (λ f → f (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) (Lemma294'Refl {A = λ y → x ≡ y} {B = λ _ → Type ℓ'} A k) ∙
                                       transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                       cong A (transpRCancelRefl (mx1 ∙ (λ _ → x)) k)) ∙
                                       r mx1 ∙
                                       cong B (sym (pairLemma3 (mx1 ∙ (λ _ → x)) (λ _ → x) ∙ sym (assocJ mx1 (λ _ → x) (λ _ → x)) ∙
                                                   (λ i → mx1 ∙ lCancel (λ _ → x) i) ∙ sym (rUnit mx1)))) ∙
                                (λ k → (λ i → A ((transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x))) (~ i))) ∙
                                       lUnit (transportRefl (A (transport (λ i → x ≡ x) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                              cong A (transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x)))) (~ k) ∙
                                       r mx1 ∙
                                       cong B (sym (pairLemma3 (mx1 ∙ (λ _ → x)) (λ _ → x) ∙ sym (assocJ mx1 (λ _ → x) (λ _ → x)) ∙
                                                   (λ i → mx1 ∙ lCancel (λ _ → x) i) ∙ sym (rUnit mx1)))) ∙
                                (λ k → (λ i → A ((transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x))) (~ i))) ∙
                                        (lUnit (cong A (transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x)))) (~ k)) ∙
                                       r mx1 ∙
                                       cong B (sym (pairLemma3 (mx1 ∙ (λ _ → x)) (λ _ → x) ∙ sym (assocJ mx1 (λ _ → x) (λ _ → x)) ∙
                                                   (λ i → mx1 ∙ lCancel (λ _ → x) i) ∙ sym (rUnit mx1)))) ∙
                                (assoc (sym (cong A (transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x)))))
                                       (cong A (transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x))))
                                       (r mx1 ∙
                                        cong B (sym (pairLemma3 (mx1 ∙ (λ _ → x)) (λ _ → x) ∙ sym (assocJ mx1 (λ _ → x) (λ _ → x)) ∙
                                                    (λ i → mx1 ∙ lCancel (λ _ → x) i) ∙ sym (rUnit mx1))))) ∙
                                (λ k → lCancel (cong A (transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x)))) k ∙
                                        r mx1 ∙
                                        cong B (sym (pairLemma3 (mx1 ∙ (λ _ → x)) (λ _ → x) ∙ sym (assocJ mx1 (λ _ → x) (λ _ → x)) ∙
                                                    (λ i → mx1 ∙ lCancel (λ _ → x) i) ∙ sym (rUnit mx1)))) ∙
                                sym (lUnit (r mx1 ∙
                                        cong B (sym (pairLemma3 (mx1 ∙ (λ _ → x)) (λ _ → x) ∙ sym (assocJ mx1 (λ _ → x) (λ _ → x)) ∙
                                                    (λ i → mx1 ∙ lCancel (λ _ → x) i) ∙ sym (rUnit mx1))))))
                 ma A B mx1 r




{-

funExt-part' : ∀ {ℓ ℓ'} {X : Type ℓ} {x y : X} {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} (ma mx1 : x ≡ y)  →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                (((λ i → A (transpRCancel (λ i₁ → x ≡ ma (~ i₁)) (mx1 ∙ sym ma) (~ i))) ∙
                                                                  funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y}
                                                                                       ma A
                                                                                       B
                                                                                       (equivTest' {X = X} ma
                                                                                                   {A = A}
                                                                                                   {B = B}
                                                                                         r))
                                                                                        (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))))
                ≡
                (λ i → A (transpRCancel (λ i₁ → x ≡ ma (~ i₁)) (mx1 ∙ sym ma) (~ i))) ∙
                {!r!} ∙
                {!!} ∙
                {!!}
                -- r mx1 ∙ cong B ((rUnit mx1) ∙ (λ i → mx1 ∙ lCancel ma (~ i)) ∙ (assocJ mx1 (sym ma) ma) ∙ sym (pairLemma3 (mx1 ∙ sym ma) ma))

funExt-part' {ℓ' = ℓ'} {X = X} {x = x} {y = y} {A = A} {B = B} ma mx1 =
              J (λ y ma → (mx1 : x ≡ y) {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'} →
                (r : ((mx1 : x ≡ y) → A (mx1 ∙ (sym ma)) ≡ B mx1)) →
                (((λ i → A (transpRCancel (λ i₁ → x ≡ ma (~ i₁)) (mx1 ∙ sym ma) (~ i))) ∙
                                                                  funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y}
                                                                                       ma A
                                                                                       B
                                                                                       (equivTest' {X = X} ma
                                                                                                   {A = A}
                                                                                                   {B = B}
                                                                                         r))
                                                                                        (transport (λ i → x ≡ ma i) (mx1 ∙ sym ma))))
                ≡
                   {!!}) -- r mx1 ∙ cong B ((rUnit mx1) ∙ (λ i → mx1 ∙ lCancel ma (~ i)) ∙ (assocJ mx1 (sym ma) ma) ∙ sym (pairLemma3 (mx1 ∙ sym ma) ma)))
                (λ mx1 {A} {B} r → (λ k → (λ i → A (transpRCancel (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                           funExt⁻ (Lemma296Funs.inv''Id {X = X} {A = λ y → x ≡ y} (λ _ → x) A B (~ k)
                                                                        (equivTestId {X = X} (λ _ → x) {A = A} {B = B} r k))
                                                     (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ) ∙
                                   (λ k → (λ i → A ((transpRCancelRefl (mx1 ∙ (λ _ → x)) k) (~ i))) ∙
                                           funExt⁻ (ReflCases.invRefl {X = X} {A = λ y → x ≡ y} A B k 
                                                                        (equivTestRefl {X = X} {A = A} {B = B} k r))
                                                     (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   (λ k → (λ i → A ((transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x))) (~ i))) ∙
                                          funExt⁻ (transportRefl A ∙
                                                  funExt λ z → sym (transportRefl (A z))  ∙
                                                               (transportRefl (A z) ∙
                                                               cong A (rUnit z) ∙
                                                               r z ∙
                                                               cong B (sym (transportRefl z))) ∙
                                                               λ i → (B (transportRefl z i)))
                                                  (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   (λ k → (λ i → A ((transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x))) (~ i))) ∙
                                           funExt⁻ (transportRefl A ∙
                                                  funExt λ z → littleCanceller (sym (transportRefl (A z)))
                                                                               (cong A (rUnit z))
                                                                               (r z)
                                                                               (cong B (sym (transportRefl z))) k)
                                                  (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   (λ k → (λ i → A ((transportRefl (transport refl (mx1 ∙ (λ _ → x))) ∙ transportRefl (mx1 ∙ (λ _ → x))) (~ i))) ∙
                                          funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                          cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   (λ k → (λ i → A ((symDistr (transportRefl (transport refl (mx1 ∙ (λ _ → x)))) (transportRefl (mx1 ∙ (λ _ → x))) k) i)) ∙
                                          funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                          cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   (λ k → congComp2 A (sym ((transportRefl (mx1 ∙ (λ _ → x))))) (sym (transportRefl (transport refl (mx1 ∙ (λ _ → x))))) (~ k) ∙
                                          funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                          cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   sym (assoc (cong A (sym ((transportRefl (mx1 ∙ (λ _ → x))))))
                                              (cong A (sym (transportRefl (transport refl (mx1 ∙ (λ _ → x))))))
                                              (funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))) ∙
                                              cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))) ∙
                                   (λ k → cong A (sym ((transportRefl (mx1 ∙ (λ _ → x))))) ∙
                                          assoc (cong A (sym (transportRefl (transport refl (mx1 ∙ (λ _ → x))))))
                                                (funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))
                                                (cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) k) ∙
                                   (λ k → cong A (sym ((transportRefl (mx1 ∙ (λ _ → x))))) ∙
                                          lCancel (funExt⁻ (transportRefl A) (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) k ∙
                                          cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙
                                   (λ k → cong A (sym ((transportRefl (mx1 ∙ (λ _ → x))))) ∙
                                          lUnit (cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) ∙ r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) (~ k) ) ∙
                                   assoc (cong A (sym ((transportRefl (mx1 ∙ (λ _ → x))))))
                                         (cong A (rUnit (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))))
                                         (r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x))))  ∙
                                   ((λ k → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                          (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) i))) ∙
                                          (rUnit (rUnit (lUnit (lUnit (r (transport (λ i → x ≡ x) (mx1 ∙ (λ _ → x)))) k) k ) k) k))) ∙
                                   (λ k → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                          (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) i))) ∙
                                          (((λ i → A ((transportRefl (mx1 ∙ (λ _ → x)) (i ∧ k)) ∙ (λ _ → x))) ∙ refl ∙
                                          (r (transportRefl (mx1 ∙ (λ _ → x)) k))) ∙ refl) ∙
                                          λ i → B (transportRefl (mx1 ∙ (λ _ → x)) (k ∧ (~ i)))) ∙
                                   (λ k → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                          (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) i))) ∙
                                          (((λ i → A ((transportRefl (mx1 ∙ (λ _ → x)) i) ∙ (λ _ → x))) ∙
                                          (λ i → A (rUnit mx1 ((~ k) ∨ (~ i)) ∙ refl)) ∙
                                          r (rUnit mx1 (~ k))) ∙
                                          λ i → B (rUnit mx1 (~ k ∨ i))) ∙
                                          λ i → B (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                   {!r!} ∙
                                   {!!} ∙
                                   {!(λ k → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                          (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) i))) ∙
                                          ((λ i → A ((transportRefl (mx1 ∙ (λ _ → x)) (i ∧ k)) ∙ (λ _ → x))) ∙
                                          (r (transportRefl (mx1 ∙ (λ _ → x)) k))) ∙
                                          λ i → B (transportRefl (mx1 ∙ (λ _ → x)) (k ∧ (~ i))))!})
                ma mx1 {A} {B}
              where
              check : (mx1 : x ≡ x) → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                          (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) i))) ∙
                                          (((λ i → A ((transportRefl (mx1 ∙ (λ _ → x)) i) ∙ (λ _ → x))) ∙
                                          (λ i → A (rUnit mx1 (~ i) ∙ refl)))) ≡ refl
              check mx1 = (λ k → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i))) ∙
                                          (λ i → A (rUnit (transport (λ i₁ → x ≡ x) (mx1 ∙ (λ _ → x))) i))) ∙
                                          (((λ i → A ((transportRefl (mx1 ∙ (λ _ → x)) i) ∙ (λ _ → x))) ∙
                                          (lUnit (λ i → A (rUnit mx1 (~ i) ∙ refl)) k)))) ∙
                          (λ k → 
                                       (((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i ∨ k))) ∙
                                       (λ i → A (rUnit (transportRefl (mx1 ∙ (λ _ → x)) k) (i ∧ (~ k))))) ∙
                                       (((λ i → A (rUnit (transportRefl (mx1 ∙ (λ _ → x)) (i ∨ k)) (~ k))) ∙
                                       (λ i → A ((rUnit (rUnit mx1 ((~ i) ∨ (~ k))) (~ k ∨ i))))
                                       ∙ (λ i → A (rUnit mx1 (~ i ∧ (~ k)) ∙ refl)) )))) ∙
                          {- (λ k → ((λ i → A (transportRefl (mx1 ∙ (λ _ → x)) (~ i ∨ k))) ∙
                                  (λ i → A (rUnit (transportRefl (mx1 ∙ (λ _ → x)) k) (i ∧ (~ k))))) ∙
                                  (((λ i → A (rUnit (transportRefl (mx1 ∙ (λ _ → x)) (i ∨ k)) (~ k))) ∙
                                  (λ i → A (hcomp {!!} {!!}))
                                  ∙ (λ i → A (rUnit mx1 (~ i ∧ (~ k)) ∙ refl)) ))) ∙ -}
                          (λ k → {!!}) ∙
                          (λ k i → A (rUnit (rUnit mx1 ((~ i))) i)) ∙
                          (λ k → {!!}) ∙
                          {!!} ∙
                          {!!} ∙
                          {!!} ∙
                          {!!}

                     where
                     rUnitCancel : ∀ {ℓ} {A : Type ℓ} {x : A} → _≡_ {A = (λ _ → x) ∙ (λ _ → x) ≡ (λ _ → x) ∙ (λ _ → x)}(λ i → (rUnit (rUnit (λ _ → x) (~ i) ) i)) (λ i → (rUnit (rUnit (λ _ → x) i ) (~ i)))
                     rUnitCancel {x = x} k i = rUnit (rUnit ((λ _ → x)) ((~ i ∧ k) ∨ (i ∧ k))) {!!}

-}

symDestroyer : {a b c d e : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) → sym (p ∙ q ∙ r ∙ s) ≡ sym s ∙ sym r ∙ sym q ∙ sym p 
symDestroyer p q r s = sym (p ∙ q ∙ r ∙ s)                          ≡⟨ symDistr p (q ∙ r ∙ s) ⟩
                       (sym (q ∙ r ∙ s)) ∙ sym p                    ≡⟨ (λ k → symDistr q (r ∙ s) k ∙ sym p) ⟩
                       (sym (r ∙ s) ∙ sym q) ∙ sym p                ≡⟨ (λ k → (symDistr r s k ∙ sym q) ∙ sym p) ⟩
                       ((sym s ∙ sym r) ∙ sym q) ∙ sym p            ≡⟨ sym (assoc (sym s ∙ sym r) (sym q) (sym p))  ⟩
                       (sym s ∙ sym r) ∙ sym q ∙ sym p              ≡⟨ sym (assoc (sym s) (sym r) (sym q ∙ sym p) ) ⟩
                       sym s ∙ sym r ∙ sym q ∙ sym p ∎

cancellerLemma : ∀ {ℓ} {A : Type ℓ} {a b c : A} (r : b ≡ c) (p : a ≡ b) → canceller r p p refl ≡ refl
cancellerLemma {a = a} {b = b} {c = c} = J (λ c r → (p : a ≡ b) → canceller r p p refl ≡ refl)
                                             (J (λ b p → canceller refl p p (λ _ → p ∙ refl) ≡ (λ _ → p))
                                                ((λ k → cancellerRefl k refl) ∙
                                                (λ k → rUnit refl ∙ (lUnit (sym (rUnit refl)) (~ k))) ∙
                                                rCancel (rUnit refl)))

funPart : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) → RlFun2 a a n iscon (merid x1) ∣ x1 , (λ _ → σ x1 {a}) ∣ ≡ ∣ x1 , refl ∣
funPart n a x1 iscon = (λ k → sufMap2 n a a x1 iscon (merid x1) refl) ∙
                       sufMap2Id2 n a x1 iscon ∙
                       (λ k → ∣ x1 , cancellerLemma (sym (merid a)) (merid x1) k ∣)

finalStep : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
                               transport (cong (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)) (sym (pairLemma3 ((merid x1) ∙ sym (merid a)) (merid a) ∙                                                   sym (assocJ (merid x1) (sym (merid a)) (merid a)) ∙ (λ i → (merid x1) ∙ lCancel (merid a) i) ∙ sym (rUnit (merid x1))))) ∣ x1 , refl ∣
                               ≡ ∣ x1 , rUnit (merid x1) ∙ sym (cong (λ x → merid x1 ∙ x) (lCancel (merid a))) ∙
                                                                                   assocJ (merid x1) (sym (merid a)) (merid a) ∙
                                                                                   sym (pairLemma3 {a1 = north} (merid x1 ∙ (sym (merid a))) (merid a)) ∣
finalStep n a x1 iscon  = (λ k → transport (cong (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                 (λ i → (sym (pairLemma3 ((merid x1) ∙ sym (merid a)) (merid a) ∙
                                                 sym (assocJ (merid x1) (sym (merid a)) (merid a)) ∙
                                                 (λ i → (merid x1) ∙ lCancel (merid a) i) ∙
                                                 sym (rUnit (merid x1)))) (i ∨ k) ))
                                 ∣ x1 , (λ i → (sym (pairLemma3 ((merid x1) ∙ sym (merid a)) (merid a) ∙
                                               sym (assocJ (merid x1) (sym (merid a)) (merid a)) ∙
                                               (λ i → (merid x1) ∙ lCancel (merid a) i) ∙
                                               sym (rUnit (merid x1)))) (i ∧ k)) ∣) ∙
                          (transportRefl ∣ x1 , sym (pairLemma3 ((merid x1) ∙ sym (merid a)) (merid a) ∙
                                                sym (assocJ (merid x1) (sym (merid a)) (merid a)) ∙
                                                (λ i → (merid x1) ∙ lCancel (merid a) i) ∙
                                                sym (rUnit (merid x1))) ∣) ∙
                          (λ k → ∣ x1 , symDestroyer (pairLemma3 ((merid x1) ∙ sym (merid a)) (merid a))
                                                      (sym (assocJ (merid x1) (sym (merid a)) (merid a)))
                                                      (λ i → (merid x1) ∙ lCancel (merid a) i)
                                                      (sym (rUnit (merid x1))) k ∣)



outerTranspId3' : (n : ℕ) (a x1 : A) (iscon : is- (ℕ→ℕ₋₂ n) -ConnectedType A) →
                 transport (λ i → uncurry (CODE' {a = a} n iscon) (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                           (transpRCancel (λ i → north ≡ (merid a (~ i))) (merid x1 ∙ (sym (merid a)))) i))
                           ∣ x1 , rUnit (merid x1) ∙ sym (cong (λ x → merid x1 ∙ x) (lCancel (merid a))) ∙
                                  assocJ (merid x1) (sym (merid a)) (merid a) ∙
                                  sym (pairLemma3 {a1 = north} (merid x1 ∙ (sym (merid a))) (merid a)) ∣ 
                ≡ ∣ x1 , refl ∣
outerTranspId3' {ℓ}{A = A} n a x1 iscon = transportLemma {B = uncurry (CODE' {a = a} n iscon)}
                                                        (sym (pair⁼'' (λ i₁ → merid a (~ i₁))
                                                                      (transpRCancel (λ i → north ≡ (merid a (~ i))) (merid x1 ∙ (sym (merid a))))))
                                                        (∣ x1 , refl ∣)
                                                        (∣ x1 , rUnit (merid x1) ∙ sym (cong (λ x → merid x1 ∙ x) (lCancel (merid a))) ∙
                                                                                   assocJ (merid x1) (sym (merid a)) (merid a) ∙
                                                                                   sym (pairLemma3 {a1 = north} (merid x1 ∙ (sym (merid a))) (merid a)) ∣)
                                         ((λ k → transport (λ i → uncurry (CODE' {a = a} n iscon)
                                                                           (pair⁼''Sym (λ i₁ → merid a (~ i₁))
                                                                                    (transpRCancel (λ i₁ → north ≡ merid a (~ i₁))
                                                                                                   (merid x1 ∙ (λ i₁ → merid a (~ i₁)))) k i))
                                                  ∣ x1 , (λ _ → σ x1 {a}) ∣)
                                         ∙ (λ k → transport (λ i → uncurry (CODE' {a = a} n iscon)
                                                                           (pair⁼'' (merid a) (transportLemma {B = λ y → north ≡ y} (sym (merid a)) (transport (λ i₁ → north ≡ merid a i₁) (merid x1 ∙ (sym (merid a) ))) (merid x1 ∙ (sym (merid a))) ((transpRCancel (λ i₁ → north ≡ merid a (~ i₁)) (merid x1 ∙ (λ i₁ → merid a (~ i₁)))))) i) )
                                                  ∣ x1 , (λ _ → σ x1 {a}) ∣) ∙
                                           (λ k → transport (λ i → uncurry (CODE' {a = a} n iscon)
                                                                           (pair⁼'' (merid a) (wowie south (merid a) (merid x1) k) i) )
                                                  ∣ x1 , (λ _ → σ x1 {a}) ∣) ∙
                                           -- cong (λ x → x ∣ x1 , (λ _ → σ x1 {a}) ∣) (Lemma8610Refl'' (CODE' {a = a} n iscon) (merid a) (σ x1 {a})) ∙
                                           (λ k → transport (λ i → uncurry (CODE''Id {A = A} {a = a} n iscon k)
                                                                           (pair⁼'' {x = north , σ x1 {a}} {y = south , _} (merid a) (λ _ → transport (λ i₁ → _≡_ {A = Susp A} north (merid a i₁)) (σ x1 {a})) i) )
                                                  ∣ x1 , (λ _ → σ x1 {a}) ∣) ∙
                                           cong (λ x → x ∣ x1 , (λ _ → σ x1 {a}) ∣) (Lemma8610Refl'' (CODE'' {a = a} n iscon) (merid a) (σ x1 {a})) ∙
                                           (λ k → transport ((λ i → ∥ fiber (λ y → σ y {a})
                                                              (transpRCancel
                                                                 (λ i₁ → north ≡ merid a (~ i₁)) (σ x1 {a}) (~ i)) ∥ ℕ→ℕ₋₂ (n + n)) ∙
                                                              funExt⁻ (toPathCancel {A = λ i → north ≡ merid a i → Type ℓ}
                                                                                {x = λ p → (∥ fiber (λ y → σ y {a}) p ∥ (ℕ→ℕ₋₂ (n + n)))}
                                                                                {y = λ q → ∥ fiber merid q ∥ (ℕ→ℕ₋₂ (n + n))}
                                                                        (Lemma296Funs.inv'' {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                                            (merid a) (λ p → ∥ fiber (λ y → σ y {a}) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                                            (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                                                            (equivTest' {X = Susp A} (merid a)
                                                                                                        {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                                        {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                              (λ q → ua' (RlFun2 a a n iscon q , RlFunEquiv2 a a n iscon q)))) k )
                                                                      (transport (λ i → north ≡ merid a i) (σ x1 {a})))
                                                             ∣ x1 , (λ _ → σ x1 {a}) ∣)  ∙
                                           (λ k → transport ((((λ i → ∥ fiber (λ y → σ y {a})
                                                              (transpRCancel
                                                                 (λ i₁ → north ≡ merid a (~ i₁)) (σ x1 {a}) (~ i)) ∥ ℕ→ℕ₋₂ (n + n)))) ∙
                                                                 funExt⁻ (Lemma296Funs.inv'' {X = Susp A} {A = λ y → north ≡ y} {B = λ _ → Type ℓ}
                                                                                      (merid a) (λ p → ∥ fiber (λ y → σ y {a}) p ∥ ℕ→ℕ₋₂ (n + n))
                                                                                      (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n))
                                                                                      (equivTest' {X = Susp A} (merid a)
                                                                                                  {A = λ q → ∥ fiber (λ y → σ y {a}) q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                                  {B = λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                                        (λ q → ua' (RlFun2 a a n iscon q , RlFunEquiv2 a a n iscon q))))
                                                                                       (transport (λ i → north ≡ merid a i) (σ x1 {a})))
                                                             ∣ x1 , ((λ _ → σ x1 {a})) ∣) ∙
                                           (λ k → transport (funExt-part''' {A = λ p → ∥ fiber (λ y → σ y {a}) p ∥ ℕ→ℕ₋₂ (n + n)}
                                                                          {B =  λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)}
                                                                          (merid a) (merid x1)
                                                                          (λ q → ua' (RlFun2 a a n iscon q , RlFunEquiv2 a a n iscon q)) k)
                                                            ∣ x1 , (((λ _ → σ x1 {a}))) ∣) ∙
                                           (λ k → transpFunct {B = λ x → x}
                                                               (ua' (RlFun2 a a n iscon (merid x1) , RlFunEquiv2 a a n iscon (merid x1)))
                                                               (cong (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)) (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙
                                                                     sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1))))
                                                               ∣ x1 , (((λ _ → σ x1 {a}))) ∣ (~ k)) ∙
                                           (λ k → transport (cong (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)) (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙
                                                                   sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1))))
                                                             (ua'Cancel ((RlFun2 a a n iscon (merid x1) , RlFunEquiv2 a a n iscon (merid x1))) k
                                                             ∣ x1 , (((λ _ → σ x1 {a}))) ∣ )) ∙
                                           (λ k → transport (cong (λ q → ∥ fiber merid q ∥ ℕ→ℕ₋₂ (n + n)) (sym (pairLemma3 (mx1 ∙ sym ma) ma ∙
                                                                   sym (assocJ mx1 (sym ma) ma) ∙ (λ i → mx1 ∙ lCancel ma i) ∙ sym (rUnit mx1))))
                                                             (funPart n a x1 iscon k)) ∙
                                           finalStep n a x1 iscon)

  where
  ma : _≡_ {A = Susp A} north south
  ma = merid a
  mx1 : _≡_ {A = Susp A} north south
  mx1 = merid x1
  
  guyid : (transport (λ i → north ≡ merid a i) (σ x1 {a})) ≡ merid x1
  guyid = pairLemma3 {a1 = north} (σ x1 {a}) (merid a) ∙ sym (assoc (merid x1) (sym (merid a)) (merid a)) ∙
          (λ i → merid x1 ∙ (lCancel (merid a)) i) ∙ sym (rUnit (merid x1))

  

{-
J (λ y p → (q : x ≡ y) {A : x ≡ x → Type ℓ'} {B : x ≡ y → Type ℓ'}  →
                                   (r : ((q : x ≡ y) → A (q ∙ (sym p)) ≡ B q)) →
                                   funExt⁻ (Lemma296Funs.inv'' {X = X} {A = λ y → x ≡ y}  p A B (equivTest' {X = X} p {A = A} {B = B} r))
                                            (transport (λ i → x ≡ p i) (p ∙ sym q))
                                    ≡
                                    (funExt⁻ (Lemma294' {A = λ y → x ≡ y} {B = λ _ → Set ℓ'} p A) (transport (λ i → x ≡ p i) (p ∙ sym q))) ∙
                                    (transportRefl (A (transport (λ i → x ≡ p (~ i)) (transport (λ i → x ≡ p i) (p ∙ sym q)))) ∙
                                    cong (λ x → A x) (pairLemma3 {a1 = x} (transport (λ i → x ≡ p i) (p ∙ sym q)) (sym p))) ∙
                                    r (transport (λ i → x ≡ p i) (p ∙ sym q)))
                                    ?

-}


  wowie : (y : Susp A) (ma mx1 : north ≡ y) → (transportLemma {B = λ y → north ≡ y} (sym ma) (transport (λ i₁ → north ≡ ma i₁) (mx1 ∙ (sym ma))) (mx1 ∙ (sym ma)) (transpRCancel (λ i₁ → north ≡ ma (~ i₁)) (mx1 ∙ (sym ma)))) ≡ refl
  wowie y  = J (λ y ma → (mx1 : north ≡ y) → (transportLemma {B = λ y → north ≡ y} (sym ma) (transport (λ i₁ → north ≡ ma i₁) (mx1 ∙ (sym ma))) (mx1 ∙ (sym ma)) (transpRCancel (λ i₁ → north ≡ ma (~ i₁)) (mx1 ∙ (sym ma)))) ≡ refl)
                 λ p → (λ i → transportLemmaRefl {a = north} {B = λ y → _≡_ {A = Susp A} north y}
                                           (λ _ → north) (λ _ → north) i
                                           (transport (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))
                                           (p ∙ (λ _ → north))
                                           (transpRCancel {A = _≡_ {A = Susp A} north north} {B = _≡_ {A = Susp A} north north} (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))) ∙
                       (λ k → transportRefl (p ∙ (λ _ → north)) ∙
                              sym (transpRCancel {A = _≡_ {A = Susp A} north north} {B = _≡_ {A = Susp A} north north}
                                                 (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north))) ∙
                              transportRefl (transport (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))) ∙
                       (λ k → transportRefl (p ∙ (λ _ → north)) ∙
                              sym (transpRCancelRefl {A = north ≡ north} (p ∙ (λ _ → north)) k) ∙
                              transportRefl (transport (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))) ∙
                       (λ k → transportRefl (p ∙ (λ _ → north)) ∙
                              symDistr (transportRefl (transport refl (p ∙ (λ _ → north)))) (transportRefl (p ∙ (λ _ → north))) k  ∙
                              transportRefl (transport (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))) ∙
                       (λ k → transportRefl (p ∙ (λ _ → north)) ∙
                              assoc (sym (transportRefl (p ∙ (λ _ → north))))
                                    (sym (transportRefl (transport refl (p ∙ (λ _ → north)))))
                                    (transportRefl (transport (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))) (~ k) ) ∙
                       (λ k → transportRefl (p ∙ (λ _ → north)) ∙
                              sym (transportRefl (p ∙ (λ _ → north))) ∙
                              lCancel (transportRefl (transport (λ i₁ → _≡_ {A = Susp A} north north) (p ∙ (λ _ → north)))) k) ∙
                       (λ k →  transportRefl (p ∙ (λ _ → north)) ∙ (rUnit (sym (transportRefl (p ∙ (λ _ → north)))) (~ k))) ∙
                       (rCancel (transportRefl (p ∙ (λ _ → north))) )
