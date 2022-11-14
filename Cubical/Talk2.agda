-- {-# OPTIONS --experimental-lossy-unification #-}

module Cubical.Talk2 where

open import Cubical.Foundations.Prelude hiding (Path)
-- open import Cubical.Data.Fin
-- open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Nat using (ℕ ; suc ; zero ; isSetℕ ; max ; min ; snotz ; _·_ ; maxComm)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

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

-- the empty type has a pretty useful elimination principle
⊥-rec : {A : Type} → ⊥ → A
⊥-rec ()

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

substitute : {A : Type} (B : A → Type) (x y : A) → x ≡ y → B x → B y
substitute B x = J> λ x → x -- don't worry about this

-- Let's prove that true ≠ false
-- Idea: We have an element of (BoolToType true), namely tt : ⊤.
-- If true = false, substitution tells us that we also get an element of (BoolToType false)
-- which we defined to be ⊥.
true≠false : ¬ (true ≡ false)
true≠false p = substitute BoolToType true false p tt -- given a proof p : true ≡ false, produce an element in ⊥

-- on a related note, all functions f : A → B takes equal points to equal points
ap : {A B : Type} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
ap f p i = f (p i)

-- Let's do some more data types
-- Natural numbers:
{-
data ℕ : Type where
  zero : ℕ
  suc  : ℕ → ℕ
-}

infixl 6 _+_
infixr 6 _∷_

pred : ℕ → ℕ -- returns the predecessor of a natural number
pred zero = 0 -- pred 0 will have to be 0
pred (suc x) = x


--Let's do something more fun: let's define +

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

-- sanity check

_ : 5 + 7 ≡ 12
_ = refl

-- we can easily prove _+_ commutative, associative, etc, but let's
-- not do this today.

{-
- Let's do something more fun(?)
-}


data List (A : Type) : Type where       -- lists
  [] : List A                           -- the empty list is a list
  _∷_ : (a : A) (xs : List A) → List A -- adding a point to a list gives you a (longer) list

-- Here's a list
one-two-three : List ℕ
one-two-three = 1 ∷ 2 ∷ 3 ∷ []

-- Let's define some basic operations
tail : {A : Type} → List A → List A
tail [] = []
tail (a ∷ xs) = xs

length : {A : Type} → List A → ℕ
length [] = 0
length (a ∷ x) = 1 + length x

-- sanity check
_ : length one-two-three ≡ 3
_ = refl

{-
- Let's define the head (first element) of a list
- Problem: what do do with the empty list?
- In python and company: crash
- Crashing programs can't be defined in Agda.
-}

-- We need to add an artifial 'crash' element
data Maybe (A : Type) : Type where
  just : A → Maybe A -- points in A
  nothing : Maybe A -- 'crash'

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
++[] (a ∷ x) = ap (a ∷_) (++[] x)

-- ++ is associative
++assoc : {A : Type} → (x y z : List A) → (x ++ y) ++ z ≡ x ++ (y ++ z)
++assoc [] y z = refl
++assoc (a ∷ x) y z = ap (a ∷_) (++assoc x y z)


-- List reversal
reverse : {A : Type} → List A → List A 
reverse [] = []
reverse (a ∷ x) = reverse x ++ (a ∷ [])

-- Let's do a harder proof
reverseInvolutory : {A : Type} → (x : List A) → reverse (reverse x) ≡ x
reverseInvolutory [] = refl
reverseInvolutory {A = A} (a ∷ x) =
  reverse (reverse x ++ (a ∷ [])) ≡⟨ reverse++ (reverse x) (a ∷ []) ⟩
  a ∷ reverse (reverse x)         ≡⟨ ap (a ∷_) (reverseInvolutory x) ⟩
  a ∷ x ∎
  where
  -- we need a lemma
  reverse++ : (xs ys : List A) → reverse (xs ++ ys) ≡ (reverse ys ++ reverse xs)
  reverse++ [] ys = sym (++[] (reverse ys))
  reverse++ (a ∷ xs) ys =
    (reverse (xs ++ ys) ++ (a ∷ []))         ≡⟨ ap (_++ (a ∷ [])) (reverse++ xs ys) ⟩
    ((reverse ys ++ reverse xs) ++ (a ∷ [])) ≡⟨ ++assoc (reverse ys) (reverse xs) (a ∷ []) ⟩
    (reverse ys ++ (reverse xs ++ (a ∷ []))) ∎

-- What about sorting?
-- Let's define what it means for a list to be sorted.
isSorted : List ℕ → Type
isSorted [] = ⊤
isSorted (a ∷ []) = ⊤
isSorted (a ∷ b ∷ x) = (min a b ≡ a) × isSorted (b ∷ x)

insertSorted : ℕ → List ℕ → List ℕ
insertSorted x [] = x ∷ []
insertSorted x (a ∷ y) = min a x ∷ insertSorted (max a x) y

insertion-sort : List ℕ → List ℕ
insertion-sort [] = []
insertion-sort (a ∷ x) = insertSorted a (insertion-sort x)

-- Let's prove the correctness of our sorting algorithm
insertion-sort-ok : (x : List ℕ) → isSorted (insertion-sort x)
insertion-sort-ok [] = tt
insertion-sort-ok (a ∷ xs) =
  insertSorted-presSorted a (insertion-sort xs) (insertion-sort-ok xs)
  where
  postulate -- I am too lazy to prove this right now
    insertSorted-presSorted : (x : ℕ) (ys : List ℕ)
                           → isSorted ys → isSorted (insertSorted x ys)


-- Let's try it
myList : List ℕ
myList = 6 ∷ 53 ∷ 52 ∷ 5 ∷ 23 ∷ 3 ∷ 10  ∷ 4 ∷ []

_ : insertion-sort myList ≡ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 10 ∷ 23 ∷ 52 ∷ 53 ∷ [] 
_ = refl

-- Binary trees
data boringTree (A : Type) : Type where
  final : boringTree A
  node : A → boringTree A → boringTree A → boringTree A

lookupL : {A : Type} → ℕ → List A → Maybe A
lookupL zero l = head l
lookupL (suc n) [] = nothing
lookupL (suc n) (a ∷ l) = lookupL n l

node-ish : {A : Type} → Maybe A → boringTree A → boringTree A → boringTree A
node-ish (just a) x y = node a x y
node-ish nothing x y = final

List→Tree-helper : {A : Type} → List A → (current d : ℕ) → boringTree A -- dummy variable d
List→Tree-helper l current zero = final
List→Tree-helper l current (suc d) =
  node-ish (lookupL current l)
           (List→Tree-helper l (current · 2 + 1) d)
           (List→Tree-helper l (current · 2 + 2) d)

List→Tree : {A : Type} → List A → boringTree A
List→Tree l = List→Tree-helper l 0 (length l)

MyList : List ℕ
MyList = 5 ∷ 9 ∷ 7 ∷ 3 ∷ 6 ∷ 8 ∷ 100 ∷ []

MyTree : boringTree ℕ
MyTree = List→Tree MyList

DFS : boringTree ℕ → List ℕ
DFS final = []
DFS (node x y z) = DFS y ++ ((x ∷ []) ++ DFS z)

_ : length (DFS MyTree) ≡ length MyList
_ = refl

-- Trees with additional information

-- saves height
data hTree' (A : Type) : ℕ → Type where
  emp : hTree' A 0
  cons : {n m : ℕ} → A → hTree' A n → hTree' A m → hTree' A (suc (max n m))

hTree : (A : Type) → Type
hTree A = Σ[ n ∈ ℕ ] hTree' A n

height : {A : Type} → hTree A → ℕ
height = fst

Tree→hTree : {A : Type} → boringTree A → hTree A
Tree→hTree final = 0 , emp
Tree→hTree (node x y z) = suc (max (height l) (height r)) , cons x (snd l) (snd r)
  where
  l = Tree→hTree y
  r = Tree→hTree z

max-ind : {A : ℕ → Type} → A 0 → ((n m : ℕ) → A n → A m → A (suc (max n m))) → ((n m : ℕ) → A (suc (max n m)))
max-ind b ind zero zero = ind 0 0 b b
max-ind b ind zero (suc m) =
  ind zero (suc m) b (max-ind b ind zero m)
max-ind {A = A} b ind (suc n) zero =
  ind (suc n) zero (subst A (cong suc (maxComm n zero)) (max-ind b ind n zero)) b
max-ind {A = A} b ind (suc n) (suc m) =
  subst A refl (ind (suc n) (suc m) (subst A (cong suc (maxComm n zero)) (max-ind {A = A} b ind n zero)) (max-ind b ind zero m))

hTree→Tree-helper : {A : Type} → ℕ → (h : hTree A) → boringTree A -- dummy variable
hTree→Tree-helper n (.0 , emp) = final
hTree→Tree-helper zero (.(suc (max n m)) , cons {n = n} {m = m} x left right) = final
hTree→Tree-helper (suc h) (.(suc (max n m)) , cons {n = n} {m = m} x left right) =
  node x (hTree→Tree-helper h (n , left)) (hTree→Tree-helper h (m , right))

hTree→Tree : {A : Type} → hTree A → boringTree A
hTree→Tree t = hTree→Tree-helper (height t) t

_ : hTree→Tree (Tree→hTree MyTree) ≡ MyTree
_ = refl

_∈[_±1] : ℕ → ℕ → Type
zero ∈[ zero ±1] = ⊤
zero ∈[ suc zero ±1] = ⊤
zero ∈[ suc (suc y) ±1] = ⊥
suc zero ∈[ zero ±1] = ⊤
suc (suc x) ∈[ zero ±1] = ⊥
suc x ∈[ suc y ±1] = x ∈[ y ±1]

data bTree' (A : Type) : ℕ → Type where
  emp : bTree' A 0
  node : (n m : ℕ) → bTree' A n → bTree' A m → n ∈[ m ±1] → bTree' A (suc (max n m))

bTree : Type → Type
bTree A = Σ[ n ∈ ℕ ] (bTree' A n)

height-b : {A : Type} → bTree A → ℕ
height-b = fst

getChildren : {A : Type} → bTree A → bTree A × bTree A
getChildren (.0 , emp) = (0 , emp) , (0 , emp)
getChildren (.(suc (max n m)) , node n m l r x) = (n , l) , (m , r)

isBinary : {A : Type} (x : bTree A) → height-b (fst (getChildren x)) ∈[ height-b (snd (getChildren x)) ±1]
isBinary (.0 , emp) = tt
isBinary (.(suc (max n m)) , node n m l r x) = x

-- TREE : (A : Type) → Type
-- TREE A = Σ[ n ∈ ℕ ] (hTree A n)

-- height : {A : Type} → TREE A → ℕ
-- height = fst

-- lookup-list : {A : Type} → List A → ℕ → Maybe A
-- lookup-list l zero = head l
-- lookup-list [] (suc n) = nothing
-- lookup-list (a ∷ l) (suc n) = lookup-list l n

-- List→Tree-helper : {A : Type} → (len : ℕ) → List A → TREE A
-- List→Tree-helper len n = {!!}

-- -- Let's do trees
-- data Tree (A : Type) : Type where
--   Node : A → Maybe (Tree A) → Maybe (Tree A) → Tree A

-- leaf : {A : Type} → A → Tree A
-- leaf a = Node a nothing nothing

-- TreeOfNats : Tree ℕ
-- TreeOfNats = Node 10 (just (leaf 9)) (just (leaf 9))

-- Maybe→ : {A B : Type} (f : A → B) → Maybe A → Maybe B
-- Maybe→ f (just x) = just (f x)
-- Maybe→ f nothing = nothing

-- Maybe→Bool : {A : Type} → Maybe A → Bool
-- Maybe→Bool (just x) = true
-- Maybe→Bool nothing = false

-- _≟_ : (n m : ℕ) → Maybe (n ≡ m)
-- zero ≟ zero = just refl
-- zero ≟ suc m = nothing
-- suc n ≟ zero = nothing
-- suc n ≟ suc m = Maybe→ (ap suc) (n ≟ m)

-- _or_ : Bool → Bool → Bool
-- true or y = true
-- false or y = y


-- TreeMap : {A B : Type} (l : A → B) (rec : A → B → B → B) (child : A → B → B) → Tree A → B 
-- TreeMap l rec child (Node x (just y) (just z)) =
--   rec x (TreeMap l rec child y) (TreeMap l rec child z)
-- TreeMap l rec child (Node x (just y) nothing) =
--   child x (TreeMap l rec child y)
-- TreeMap l rec child (Node x nothing (just y)) =
--   child x (TreeMap l rec child y)
-- TreeMap l rec child (Node x nothing nothing) = l x

-- search : ℕ → Tree ℕ → Bool
-- search t (Node x y z) with (t ≟ x)
-- ... | just p = true
-- ... | nothing = TreeMap (λ x → Maybe→Bool (t ≟ x))
--                        (λ _ → _or_)
--                        (λ _ x → x)
--                        (Node x y z)

-- test : search 9 TreeOfNats ≡ true
-- test = refl

-- Maybe→List : {A B : Type} (f : A → List B) → Maybe A → List B
-- Maybe→List f (just x) = f x
-- Maybe→List f nothing = []

-- ListONodes : Tree ℕ → List ℕ
-- ListONodes (Node x (just xs) (just ys)) = x ∷ (ListONodes xs ++ ListONodes ys)
-- ListONodes (Node x (just xs) nothing) = x ∷ ListONodes xs
-- ListONodes (Node x nothing (just x₁)) = x ∷ ListONodes x₁
-- ListONodes (Node x nothing nothing) = x ∷ []

-- findMinHelper : ℕ → Tree ℕ → ℕ
-- findMinHelper n =
--   TreeMap (λ m → m)
--           (λ x y z → min x (min y z))
--           min

-- findMin : Tree ℕ → ℕ
-- findMin (Node x (just xs) (just ys)) = min (findMinHelper x xs) (findMinHelper x ys)
-- findMin (Node x (just xs) nothing) = findMinHelper x xs
-- findMin (Node x nothing (just xs)) = findMinHelper x xs
-- findMin (Node x nothing nothing) = x

-- Tree1 : Tree ℕ
-- Tree1 = Node 1 nothing (just (leaf 2))

-- Tree2 : Tree ℕ
-- Tree2 = Node 1 (just (leaf 2)) nothing

-- ValTree : {A : Type} → Tree A → A
-- ValTree (Node x x₁ x₂) = x

-- Maybe→Type : {A : Type} (B : A → Type) → Maybe A → Type
-- Maybe→Type B (just x) = B x
-- Maybe→Type B nothing = ⊥

-- hasLeft-child : {A : Type} → Tree A → Type
-- hasLeft-child (Node x (just x₁) z) = ⊤
-- hasLeft-child (Node x nothing z) = ⊥

-- getLeftChild : {A : Type} → (T : Tree A) → hasLeft-child T → Tree A
-- getLeftChild (Node x (just x₁) x₂) h = x₁

-- hasRight-child : {A : Type} → Tree A → Type
-- hasRight-child (Node x y (just x₁)) = ⊤
-- hasRight-child (Node x y nothing) = ⊥

-- getRightChild : {A : Type} → (T : Tree A) → hasRight-child T → Tree A
-- getRightChild (Node x x₁ (just x₂)) r = x₂

-- Children : {A : Type} → Tree A → Maybe (Tree A) × Maybe (Tree A)
-- Children (Node x y z) = y , z

-- data Tree→Type {A : Type} (T : Tree A) : Type where
--   root : Tree→Type T
--   left : (h : hasLeft-child T) → Tree→Type (getLeftChild T h) → Tree→Type T
--   right : (h : hasRight-child T) → Tree→Type (getRightChild T h) → Tree→Type T
--   pₗ : (h : hasLeft-child T) (s : Tree→Type (getLeftChild T h)) → left h s ≡ root
--   pᵣ : (h : hasRight-child T) (s : Tree→Type (getRightChild T h)) → right h s ≡ root
  
-- isTree : {A : Type} (t : Tree A) → Type
-- isTree t = isContr (Tree→Type t)

-- check : isTree (Node 1 nothing (just (leaf 2)))
-- check = root , λ { root → refl
--                 ; (right h x) → sym (pᵣ h x)
--                 ; (pᵣ h x i) j → pᵣ h x (i ∨ ~ j)}

-- check2 : isTree (Node 1 (just (Node 0 nothing (just (Node 2 nothing nothing))))
--                 (just (Node 3 nothing (just (Node 2 nothing nothing)))))
-- fst check2 = root
-- snd check2 root = refl
-- snd check2 (left h y) = sym (pₗ h y)
-- snd check2 (right h y) = sym (pᵣ h y)
-- snd check2 (pₗ h root i) j =  pₗ h root (~ j ∨ i)
-- snd check2 (pₗ h (right m root) i) j = pₗ h (right m root) (~ j ∨ i)
-- snd check2 (pₗ h (pᵣ m root i) j) k = pₗ h (pᵣ m root i) (~ k ∨ j)
-- snd check2 (pᵣ h root i) j = pᵣ h root (~ j ∨ i)
-- snd check2 (pᵣ h (right h₁ root) i) j = pᵣ h (right h₁ root) (~ j ∨ i)
-- snd check2 (pᵣ h (pᵣ m root i) j) k = pᵣ h (pᵣ m root i) (~ k ∨ j)


-- open import Cubical.Foundations.Equiv
-- GraphHom : {!!}
-- GraphHom = {!!}

-- ∞ : Maybe ℕ
-- ∞ = nothing

-- -- minℕ : ℕ → ℕ → ℕ
-- -- minℕ zero y = zero
-- -- minℕ (suc x) zero = zero
-- -- minℕ (suc x) (suc y) = suc (minℕ x y)

-- -- MaybeMin : Maybe ℕ → Maybe ℕ → Maybe ℕ
-- -- MaybeMin (just x) (just x₁) = just (minℕ x x₁)
-- -- MaybeMin (just x) nothing = just x
-- -- MaybeMin nothing x = x

-- -- minList : List ℕ → Maybe ℕ
-- -- minList [] = nothing
-- -- minList (a ∷ x) = MaybeMin (just a) (minList x)

-- -- _and_ : Bool → Bool → Bool
-- -- true and y = y
-- -- false and y = false

-- -- _×_ : (A B : Type) → Type
-- -- A × B = Σ A (λ _ → B)

-- -- maxℕ : ℕ → ℕ → ℕ
-- -- maxℕ zero y = y
-- -- maxℕ (suc x) zero = suc x
-- -- maxℕ (suc x) (suc y) = suc (maxℕ x y)


-- -- isSorted : List ℕ → Type
-- -- isSorted [] = ⊤
-- -- isSorted (a ∷ x) = (just a ≡ minList (a ∷ x)) × (isSorted x)

-- -- insertSorted : ℕ → List ℕ → List ℕ
-- -- insertSorted x [] = x ∷ []
-- -- insertSorted x (a ∷ y) = minℕ x a ∷ insertSorted (maxℕ x a) y

-- -- insertionSort : List ℕ → List ℕ
-- -- insertionSort [] = []
-- -- insertionSort (a ∷ x) = insertSorted a x

-- -- insertionSortCheck : (x : List ℕ) → isSorted (insertionSort x)
-- -- insertionSortCheck [] = tt
-- -- insertionSortCheck (a ∷ x) = {!!} -- help a x
-- --   where
-- --   minLemma : (x y : ℕ) → ((minℕ x y ≡ x) × (maxℕ x y ≡ y))
-- --                          ⊔ ((minℕ x y ≡ y) × (maxℕ x y ≡ x)) 
-- --   minLemma zero y = inl (refl , refl)
-- --   minLemma (suc x) zero = inr (refl , refl)
-- --   minLemma (suc x) (suc y) with (minLemma x y)
-- --   ... | inl p = inl ((ap suc (fst p)) , (ap suc (snd p)))
-- --   ... | inr p = inr ((ap suc (fst p)) , (ap suc (snd p)))

-- --   lem1 : (a b : ℕ) (xs : _) → MaybeMin (just (minℕ a b)) (minList (insertSorted (maxℕ a b) xs)) ≡ just (minℕ a b)
-- --   lem1 a b [] = ap just {!!}
-- --   lem1 a b (a₁ ∷ xs) = ap (MaybeMin (just (minℕ a b))) hahaha ∙ lem1 a b xs
-- --     where
-- --     hahaha : (MaybeMin (just (minℕ (maxℕ a b) a₁))
-- --        (minList (insertSorted (maxℕ (maxℕ a b) a₁) xs))) ≡ (minList (insertSorted (maxℕ a b) xs))
-- --     hahaha = {!!}

-- --   help : (a : _) (x : _) → isSorted x → isSorted (insertSorted a x)
-- --   help a [] t = refl , tt
-- --   help a (b ∷ xs) t with (minLemma a b)
-- --   ... | inl x = ap just (fst x)
-- --               ∙ {!!}
-- --               ∙ ap₂ MaybeMin (ap just (sym (fst x))) (ap (λ s → minList (insertSorted s xs)) (sym (snd x)))
-- --               , (help (maxℕ a b) xs (snd t))
-- --   ... | inr x = {!refl!} , (help (maxℕ a b) xs (snd t))



-- -- data F₃ : Type where
-- --   one : F₃
-- --   two : F₃
-- --   three : F₃

-- -- open import Cubical.Foundations.HLevels
-- -- isSetF₃ : isSet F₃
-- -- isSetF₃ = isOfHLevelRetract 2 (λ {one → 0 ; two → 1 ; three → 2}) (λ { zero → one ; (suc zero) → two ; (suc (suc zero)) → three ; (suc (suc (suc x))) → one})
-- --   (λ { one → refl ; two → refl ; three → refl})
-- --   isSetℕ


-- -- isSet⊤ : isSet ⊤
-- -- isSet⊤ =
-- --   isOfHLevelRetract 2 (λ _ → 1) (λ _ → tt) (λ {tt → refl}) isSetℕ


-- -- record Graph : Type₁ where
-- --   constructor Gr
-- --   field
-- --     V : Type
-- --     E : V → V → Type
-- --     isSetG : isSet V
-- --     isSetE : (x y : V) → isProp (E x y)

-- -- open import Cubical.Data.Sigma

-- -- open Graph 
-- -- module _ (G : Graph) where
-- --   data Walk : V G → V G → Type where
-- --     ⟨_⟩ : (x : V G) → Walk x x
-- --     _⊙_ : {x y z : V G}  → E G x y → Walk y z → Walk x z

-- --   Neighbours : (v : V G) → Type
-- --   Neighbours v = Σ[ w ∈ V G ] E G v w

-- --   isSetNeighbours : (x : _) → isSet (Neighbours x)
-- --   isSetNeighbours x = isSetΣ (isSetG G) λ _ → isProp→isSet (isSetE G _ _)

-- -- composeWalk : {G : Graph} {x y z : V G} → Walk G x y → Walk G y z → Walk G x z 
-- -- composeWalk ⟨ _ ⟩ q = q
-- -- composeWalk (x ⊙ p) q = x ⊙ (composeWalk p q)

-- -- len : {G : Graph} {x y : V G} → Walk G x y → ℕ
-- -- len ⟨ _ ⟩ = 0
-- -- len (x ⊙ y) = 1 + len y

-- -- F₃G : Graph
-- -- V F₃G = F₃
-- -- E F₃G one y = ⊤
-- -- E F₃G two one = ⊥
-- -- E F₃G two two = ⊤
-- -- E F₃G two three = ⊤
-- -- E F₃G three one = ⊤
-- -- E F₃G three two = ⊤
-- -- E F₃G three three = ⊥
-- -- isSetG F₃G = isSetF₃
-- -- isSetE F₃G one y = λ {tt tt → refl}
-- -- isSetE F₃G two one = λ {()}
-- -- isSetE F₃G two two = λ {tt tt → refl}
-- -- isSetE F₃G two three = λ {tt tt → refl}
-- -- isSetE F₃G three one = λ {tt tt → refl}
-- -- isSetE F₃G three two = λ {tt tt → refl}
-- -- isSetE F₃G three three = λ {()}

-- -- myWalk₁ : Walk F₃G one one 
-- -- myWalk₁ = (tt ⊙ step1)
-- --   where
-- --   step3 : Walk F₃G three one
-- --   step3 = tt ⊙ ⟨ one ⟩

-- --   step1 : Walk F₃G two one
-- --   step1 = tt ⊙ step3

-- -- myWalk₂ : Walk F₃G one one
-- -- myWalk₂ = composeWalk myWalk₁ myWalk₁

-- -- myWalk₃ : Walk F₃G two two
-- -- myWalk₃ = tt ⊙ ⟨ two ⟩

-- -- open import Cubical.Data.Vec renaming (_∷_ to _∷'_)
-- -- open import Cubical.Data.FinData

-- -- Matrix : (A : Type) (n m : ℕ) → Type
-- -- Matrix A n m = Vec (Vec A m) n

-- -- AdjMatrix : (n : ℕ) → Type
-- -- AdjMatrix n = Matrix Bool n n

-- -- data SqMatrix (A : Type) : ℕ → Type where
-- --   [] : SqMatrix A 0
  


-- -- mapDep : ∀ {ℓ  ℓ'} {A : Type ℓ} {B : Type ℓ'} {n} → (Fin n → A → B) → Vec A n → Vec B n
-- -- mapDep {n = zero} f [] = []
-- -- mapDep {n = suc n} f (x ∷' xs) = (f (fromℕ n) x) ∷' mapDep {n = n} (λ x y → f (suc x) y) xs


-- -- AdjMatrix↑ : (n : ℕ) → AdjMatrix n → (Vec Bool n) → AdjMatrix (suc n)
-- -- AdjMatrix↑ n mat f = (false ∷' f) ∷' mapDep (λ n p → lookup n f ∷' p) mat -- map {!foldr _∷'_ ?!} mat

-- -- MyGraph : AdjMatrix 4
-- -- MyGraph = AdjMatrix↑ 3 (AdjMatrix↑ 2 (AdjMatrix↑ 1 (AdjMatrix↑ 0 [] [])
-- --   (true ∷' [])) (false ∷' (true ∷' []))) (false ∷' (true ∷' true ∷' []))

-- -- BoolT : Bool → Type
-- -- BoolT true = ⊤
-- -- BoolT false = ⊥

-- -- isPropBoolT : (x : Bool) → isProp (BoolT x)
-- -- isPropBoolT true tt tt = refl
-- -- isPropBoolT false ()

-- -- {-
-- --    1   2   3  

-- -- 1  f

