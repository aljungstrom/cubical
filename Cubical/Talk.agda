module Cubical.Talk where

open import Cubical.Foundations.Prelude hiding (Path)
-- open import Cubical.Data.Fin
-- open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Nat using (ℕ ; suc ; zero ; isSetℕ) 

{-
- (Cubical) Agda: Functional programming language + proof assistant.
- Let us define our first type: the booleans
-}

data Bool : Type where -- data type with two constructors
  true : Bool
  false : Bool

-- We can now write our first program/function

not : Bool → Bool -- → is given by \to
not true = false
not false = true

-- Let's prove something about our function
not-invol : (x : Bool) → not (not x) ≡ x -- _≡_ is the type of equalities
not-invol true = refl -- the goal is on the form a = a. We have a primitive proof of this denoted refl.
not-invol false = refl

{-
Let's construct two related types: ⊤ ('true'), ⊥ ('false')
-}

data ⊤ : Type where
  tt : ⊤

data ⊥ : Type where

¬ : Type → Type -- ⊥ allows us to define the 'negation' of a type
¬ A = A → ⊥

BoolToType : Bool → Type
BoolToType true = ⊤
BoolToType false = ⊥

{- This is a dependent type/family of types over Bool. I.e. for every
boolean x, we have a type (BoolToType x) which differs depending on
what the value of x is.

In general, a dependent type (indexed by another type A) is a function
B : A → Type, assigning a type to every point in A.

Here's a pretty trivial fact:
If you have a dependent type B : A → Type and two equal points x, y : A,
then you get a function B x → B y. Why?

A function B x → B y is just a function B x → B x by substituting y
for x (since they're equal!). We always have a function from a type to
itself, namely the identity -}

substitute : {A : Type} {B : A → Type} (x y : A) → x ≡ y → B x → B y
substitute x = J> λ x → x -- don't worry about this

-- Let's prove that true ≠ false
-- Idea: We have an element of (BoolToType true), namely tt : ⊤.
-- If true = false, substitution tells us that we also get an element of (BoolToType false)
-- which we defined to be ⊥.
true≠false : ¬ (true ≡ false)
true≠false p = substitute {B = BoolToType} true false p tt -- given a proof p : true ≡ false, produce an element in ⊥


{-
data ℕ : Type where
  zero : ℕ
  suc  : ℕ → ℕ
-}

-- Delete?
data _⊔_ (A B : Type) : Type where
  inl : A → A ⊔ B
  inr : B → A ⊔ B

infixl 6 _+_
infixr 6 _∷_

{-
- Let's write our first function pred, which returns the predecessor of a natural number n
-}

pred : ℕ → ℕ
pred zero = 0 -- pred 0 will have to be 0
pred (suc x) = x

{-
Let's do something more fun: let's define +
-}

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

{-
Let's check that 5 + 7 = 12

-- We have an identity type _≡_ in agda. It comes with a proof that everything is equal to itself, donted refl.
-}

reflℕ : (n : ℕ) → n ≡ n
reflℕ n = refl

_ : 5 + 7 ≡ 12
_ = refl

{-
- This is an example of a _dependent type_.
- A dependent type a function from a type into the 'type of types'. B : A → Type.
- It assigns to each point a in A, another type B a.
-}

isTrue : Bool → Type
isTrue true = ⊤
isTrue false = ⊥

isZero : ℕ → Type
isZero zero = ⊤
isZero (suc n) = ⊥

{- Let us now prove our first (trivial) theorem. For any natural
number n such that (isZero n) holds, we have that n = 0.
-}

isZeroCheck : (n : ℕ) → isZero n → n ≡ 0
isZeroCheck zero p = refl
isZeroCheck (suc n) ()

{-
- Let's do something more fun now. Let's do lists over a type A.
-}

data List (A : Type) : Type where
  [] : List A
  _∷_ : (a : A) (xs : List A) → List A

one-two-three : List ℕ
one-two-three = 1 ∷ 2 ∷ 3 ∷ []

{-
Let's define the 
-}

tail : {A : Type} → List A → List A
tail [] = []
tail (a ∷ xs) = xs

length : {A : Type} → List A → ℕ
length [] = 0
length (a ∷ x) = 1 + length x

{-
- Let's define the head (first element) of a list
- Problem: what do do with the empty list?
- Need:
-}

data Maybe (A : Type) : Type where
  just : A → Maybe A
  nothing : Maybe A

head : {A : Type} → List A → Maybe A
head [] = nothing
head (a ∷ x) = just a

{-
Last element:
-}

last : {A : Type} → List A → Maybe A
last [] = nothing
last (a ∷ []) = just a
last (a₁ ∷ a₂ ∷ x) = last (a₂ ∷ x)

{-
Let's get fancier. Let's add two lists
-}

_++_ : {A : Type} → List A → List A → List A
[] ++ ys = ys
(a ∷ xs) ++ ys = a ∷ (xs ++ ys)

{-Let's prove something: appending [] does nothing
-}

++[] : {A : Type} → (x : List A) → x ++ [] ≡ x
++[] [] = refl
++[] (a ∷ x) = cong (a ∷_) (++[] x)

-- ++ is associative : ?
++assoc : {A : Type} → (x y z : List A) → (x ++ y) ++ z ≡ x ++ (y ++ z)
++assoc [] y z = refl
++assoc (a ∷ x) y z = cong (a ∷_) (++assoc x y z)

{-
List reversal?
-}

reverse : {A : Type} → List A → List A 
reverse [] = []
reverse (a ∷ x) = reverse x ++ (a ∷ [])

{-
Let's prove something: reverse is an involution
-}

reverseInvolutory : {A : Type} → (x : List A) → reverse (reverse x) ≡ x
reverseInvolutory [] = refl
reverseInvolutory {A = A} (a ∷ x) =
  reverse (reverse x ++ (a ∷ [])) ≡⟨ reverse++ (reverse x) (a ∷ []) ⟩
  a ∷ reverse (reverse x)         ≡⟨ cong (a ∷_) (reverseInvolutory x) ⟩
  a ∷ x ∎
  where
  -- we need a lemma
  reverse++ : (xs ys : List A) → reverse (xs ++ ys) ≡ (reverse ys ++ reverse xs)
  reverse++ [] ys = sym (++[] (reverse ys))
  reverse++ (a ∷ xs) ys =
    (reverse (xs ++ ys) ++ (a ∷ []))         ≡⟨ cong (_++ (a ∷ [])) (reverse++ xs ys) ⟩
    ((reverse ys ++ reverse xs) ++ (a ∷ [])) ≡⟨ ++assoc (reverse ys) (reverse xs) (a ∷ []) ⟩
    (reverse ys ++ (reverse xs ++ (a ∷ []))) ∎


{-
Let's write a verified sorting algorithm. For simplicity, we'll do it for natural numbers only.
-}

∞ : Maybe ℕ
∞ = nothing


minℕ : ℕ → ℕ → ℕ
minℕ zero y = zero
minℕ (suc x) zero = zero
minℕ (suc x) (suc y) = suc (minℕ x y)

MaybeMin : Maybe ℕ → Maybe ℕ → Maybe ℕ
MaybeMin (just x) (just x₁) = just (minℕ x x₁)
MaybeMin (just x) nothing = just x
MaybeMin nothing x = x

minList : List ℕ → Maybe ℕ
minList [] = nothing
minList (a ∷ x) = MaybeMin (just a) (minList x)

_and_ : Bool → Bool → Bool
true and y = y
false and y = false

_×_ : (A B : Type) → Type
A × B = Σ A (λ _ → B)

maxℕ : ℕ → ℕ → ℕ
maxℕ zero y = y
maxℕ (suc x) zero = suc x
maxℕ (suc x) (suc y) = suc (maxℕ x y)


isSorted : List ℕ → Type
isSorted [] = ⊤
isSorted (a ∷ x) = (just a ≡ minList (a ∷ x)) × (isSorted x)

insertSorted : ℕ → List ℕ → List ℕ
insertSorted x [] = x ∷ []
insertSorted x (a ∷ y) = minℕ x a ∷ insertSorted (maxℕ x a) y

insertionSort : List ℕ → List ℕ
insertionSort [] = []
insertionSort (a ∷ x) = insertSorted a x

insertionSortCheck : (x : List ℕ) → isSorted (insertionSort x)
insertionSortCheck [] = tt
insertionSortCheck (a ∷ x) = {!!} -- help a x
  where
  minLemma : (x y : ℕ) → ((minℕ x y ≡ x) × (maxℕ x y ≡ y))
                         ⊔ ((minℕ x y ≡ y) × (maxℕ x y ≡ x)) 
  minLemma zero y = inl (refl , refl)
  minLemma (suc x) zero = inr (refl , refl)
  minLemma (suc x) (suc y) with (minLemma x y)
  ... | inl p = inl ((cong suc (fst p)) , (cong suc (snd p)))
  ... | inr p = inr ((cong suc (fst p)) , (cong suc (snd p)))

  lem1 : (a b : ℕ) (xs : _) → MaybeMin (just (minℕ a b)) (minList (insertSorted (maxℕ a b) xs)) ≡ just (minℕ a b)
  lem1 a b [] = cong just {!!}
  lem1 a b (a₁ ∷ xs) = cong (MaybeMin (just (minℕ a b))) hahaha ∙ lem1 a b xs
    where
    hahaha : (MaybeMin (just (minℕ (maxℕ a b) a₁))
       (minList (insertSorted (maxℕ (maxℕ a b) a₁) xs))) ≡ (minList (insertSorted (maxℕ a b) xs))
    hahaha = {!!}

  help : (a : _) (x : _) → isSorted x → isSorted (insertSorted a x)
  help a [] t = refl , tt
  help a (b ∷ xs) t with (minLemma a b)
  ... | inl x = cong just (fst x)
              ∙ {!!}
              ∙ cong₂ MaybeMin (cong just (sym (fst x))) (cong (λ s → minList (insertSorted s xs)) (sym (snd x)))
              , (help (maxℕ a b) xs (snd t))
  ... | inr x = {!refl!} , (help (maxℕ a b) xs (snd t))



data F₃ : Type where
  one : F₃
  two : F₃
  three : F₃

open import Cubical.Foundations.HLevels
isSetF₃ : isSet F₃
isSetF₃ = isOfHLevelRetract 2 (λ {one → 0 ; two → 1 ; three → 2}) (λ { zero → one ; (suc zero) → two ; (suc (suc zero)) → three ; (suc (suc (suc x))) → one})
  (λ { one → refl ; two → refl ; three → refl})
  isSetℕ


isSet⊤ : isSet ⊤
isSet⊤ =
  isOfHLevelRetract 2 (λ _ → 1) (λ _ → tt) (λ {tt → refl}) isSetℕ


record Graph : Type₁ where
  constructor Gr
  field
    V : Type
    E : V → V → Type
    isSetG : isSet V
    isSetE : (x y : V) → isProp (E x y)

open import Cubical.Data.Sigma

open Graph 
module _ (G : Graph) where
  data Walk : V G → V G → Type where
    ⟨_⟩ : (x : V G) → Walk x x
    _⊙_ : {x y z : V G}  → E G x y → Walk y z → Walk x z

  Neighbours : (v : V G) → Type
  Neighbours v = Σ[ w ∈ V G ] E G v w

  isSetNeighbours : (x : _) → isSet (Neighbours x)
  isSetNeighbours x = isSetΣ (isSetG G) λ _ → isProp→isSet (isSetE G _ _)

composeWalk : {G : Graph} {x y z : V G} → Walk G x y → Walk G y z → Walk G x z 
composeWalk ⟨ _ ⟩ q = q
composeWalk (x ⊙ p) q = x ⊙ (composeWalk p q)

len : {G : Graph} {x y : V G} → Walk G x y → ℕ
len ⟨ _ ⟩ = 0
len (x ⊙ y) = 1 + len y

F₃G : Graph
V F₃G = F₃
E F₃G one y = ⊤
E F₃G two one = ⊥
E F₃G two two = ⊤
E F₃G two three = ⊤
E F₃G three one = ⊤
E F₃G three two = ⊤
E F₃G three three = ⊥
isSetG F₃G = isSetF₃
isSetE F₃G one y = λ {tt tt → refl}
isSetE F₃G two one = λ {()}
isSetE F₃G two two = λ {tt tt → refl}
isSetE F₃G two three = λ {tt tt → refl}
isSetE F₃G three one = λ {tt tt → refl}
isSetE F₃G three two = λ {tt tt → refl}
isSetE F₃G three three = λ {()}

myWalk₁ : Walk F₃G one one 
myWalk₁ = (tt ⊙ step1)
  where
  step3 : Walk F₃G three one
  step3 = tt ⊙ ⟨ one ⟩

  step1 : Walk F₃G two one
  step1 = tt ⊙ step3

myWalk₂ : Walk F₃G one one
myWalk₂ = composeWalk myWalk₁ myWalk₁

myWalk₃ : Walk F₃G two two
myWalk₃ = tt ⊙ ⟨ two ⟩

open import Cubical.Data.Vec renaming (_∷_ to _∷'_)
open import Cubical.Data.FinData

Matrix : (A : Type) (n m : ℕ) → Type
Matrix A n m = Vec (Vec A m) n

AdjMatrix : (n : ℕ) → Type
AdjMatrix n = Matrix Bool n n

data SqMatrix (A : Type) : ℕ → Type where
  [] : SqMatrix A 0
  


mapDep : ∀ {ℓ  ℓ'} {A : Type ℓ} {B : Type ℓ'} {n} → (Fin n → A → B) → Vec A n → Vec B n
mapDep {n = zero} f [] = []
mapDep {n = suc n} f (x ∷' xs) = (f (fromℕ n) x) ∷' mapDep {n = n} (λ x y → f (suc x) y) xs


AdjMatrix↑ : (n : ℕ) → AdjMatrix n → (Vec Bool n) → AdjMatrix (suc n)
AdjMatrix↑ n mat f = (false ∷' f) ∷' mapDep (λ n p → lookup n f ∷' p) mat -- map {!foldr _∷'_ ?!} mat

MyGraph : AdjMatrix 4
MyGraph = AdjMatrix↑ 3 (AdjMatrix↑ 2 (AdjMatrix↑ 1 (AdjMatrix↑ 0 [] [])
  (true ∷' [])) (false ∷' (true ∷' []))) (false ∷' (true ∷' true ∷' []))

BoolT : Bool → Type
BoolT true = ⊤
BoolT false = ⊥

isPropBoolT : (x : Bool) → isProp (BoolT x)
isPropBoolT true tt tt = refl
isPropBoolT false ()

{-
   1   2   3  

1  f
    
2    

3


-}

c : (n : ℕ) → AdjMatrix n → Graph
V (c n mat) = Fin n
E (c n mat) x y = BoolT (lookup x (lookup y mat))
isSetG (c n mat) = isSetFin
isSetE (c n mat) x y = isPropBoolT _

t : Type
t = E (c 4 MyGraph) (suc zero) (suc (suc zero))




_ : len myWalk₁ ≡ 3
_ = refl

_ : len myWalk₂ ≡ 6
_ = refl



-- if_then_else : {A : Type} → Bool → A → A → A
-- if true then y else z = y
-- if false then y else z = z

-- _≤?_ : ℕ → ℕ → Bool
-- zero ≤? y = true
-- suc x ≤? zero = false
-- suc x ≤? suc y = x ≤? y

-- maxℕ : ℕ → ℕ → ℕ
-- maxℕ zero y = y
-- maxℕ (suc x) zero = suc x
-- maxℕ (suc x) (suc y) = suc (maxℕ x y)

-- headℕList : List ℕ → ℕ
-- headℕList [] = 0
-- headℕList (a ∷ x) = a

-- isSorted< : List ℕ → Bool
-- isSorted< [] = true
-- isSorted< (a ∷ x) = (headℕList x ≤? a) and isSorted< x



-- _ : isSorted< (3 ∷ 2 ∷ 1 ∷ []) ≡ true
-- _ = refl -- refl

-- _ : isSorted< (one-two-three ++ one-two-three) ≡ false
-- _ = refl

-- merge : List ℕ → List ℕ → List ℕ
-- merge [] y = y
-- merge (a ∷ x) [] = a ∷ x
-- merge (n ∷ x) (m ∷ ys) =
--   if n ≤? m
--   then
--     (m ∷ merge (n ∷ x) ys)
--   else
--     (n ∷ merge x (m ∷ ys))

-- insertSorted : (x : ℕ) → List ℕ → List ℕ
-- insertSorted x [] = x ∷ []
-- insertSorted x (a ∷ xs) = if a ≤? x then x ∷ a ∷ xs else (a ∷ insertSorted x xs)

-- ins-sort : List ℕ → List ℕ
-- ins-sort [] = []
-- ins-sort (a ∷ x) = insertSorted a (ins-sort x)


-- and₁ : (x y : Bool) → x and y ≡ true → y ≡ true
-- and₁ true y p = p
-- and₁ false true p = refl
-- and₁ false false p = p

-- and₂ : (x y : Bool) → x and y ≡ true → y ≡ true
-- and₂ x true p = refl
-- and₂ true false p = p
-- and₂ false false p = p


-- isSorted-sortL : (x : List ℕ) → isSorted< (ins-sort x) ≡ true
-- isSorted-sortL [] = refl
-- isSorted-sortL (a ∷ xs) = help (ins-sort xs) (isSorted-sortL xs)
--   where
--   help : (xs : List ℕ) → isSorted< xs ≡ true → isSorted< (insertSorted a xs) ≡ true
--   help [] p = refl
--   help (b ∷ xs) p = lem _ refl
--     where
--     lem : (t : Bool) → b ≤? a ≡ t → isSorted<
--        (if b ≤? a then a ∷ b ∷ xs else (b ∷ insertSorted a xs))
--        ≡ true
--     lem true s = (λ i →  isSorted< (if (s i) then a ∷ b ∷ xs else (b ∷ insertSorted a xs)))
--                ∙ cong₂ _and_ s p
--     lem false s = (λ i →  isSorted< (if (s i) then a ∷ b ∷ xs else (b ∷ insertSorted a xs)))
--                 ∙ c
--       where
--       st : headℕList (insertSorted a xs) ≤? b ≡ true
--       st = {!!}

--       c : isSorted< (b ∷ insertSorted a xs) ≡ true
--       c = cong₂ _and_ st (help xs (and₂ _ _ p)) -- cong₂ _and_ {!st!} p
-- --   where
-- --   help : (s : Bool) → b ≤? a ≡ s → {!!}
-- --   help = {!(headℕList x ≤? a) and isSorted< x!}

-- -- mergeIsSorted : (xs ys : List ℕ) → isSorted< xs ≡ true → isSorted< ys ≡ true → isSorted< (merge xs ys) ≡ true
-- -- mergeIsSorted [] ys sorted-xs sorted-ys = sorted-ys
-- -- mergeIsSorted (a ∷ xs) [] sorted-xs sorted-ys = sorted-xs
-- -- mergeIsSorted (a ∷ xs) (b ∷ ys) sorted-xs sorted-ys =
-- --   {!!} -- lem (? ≤? ?) refl
-- --   where
-- --   lem : (p : Bool) → (p ≡ a ≤? b)
-- --     → isSorted< (if a ≤? b then a ∷ merge xs (b ∷ ys) else (b ∷ merge (a ∷ xs) ys))
-- --       ≡ true
-- --   lem true q = isSorted< (if a ≤? b then a ∷ merge xs (b ∷ ys) else (b ∷ merge (a ∷ xs) ys))
-- --              ≡⟨ cong isSorted< (λ i → if (q (~ i)) then a ∷ merge xs (b ∷ ys) else (b ∷ merge (a ∷ xs) ys)) ⟩
-- --              cong₂ _and_ lem₁ lem₂
-- --     where
-- --     lem₁ : headℕList (merge xs (b ∷ ys)) ≤? a ≡ true
-- --     lem₁ = {!sorted-xs!}

-- --     lem₂ : isSorted< (merge xs (b ∷ ys)) ≡ true
-- --     lem₂ = mergeIsSorted xs (b ∷ ys) (and₂ _ _ sorted-xs) sorted-ys

-- --   lem false q = {!!}

-- -- -- mergePairs : List (List ℕ) → List (List ℕ)
-- -- -- mergePairs = {!!}





-- -- -- {-
-- -- -- Introduction to Agda

-- -- -- In this talk I will introduce the Agda, a proof assistant and functional programming language based based on dependent type theory. While I normally use Agda to reason about homotopy theory, my goal in this talk is to show how Agda also may be used for writing certified programs/algorithms. I will focus on constructions (which I perceive to be) of computer scientific interest, such as lists and/or graphs.  -}

