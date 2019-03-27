module plfa.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax;proj₁;proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.Induction using (*-distrib-+;*-comm;+-comm;∸-+-assoc)
open import plfa.Isomorphism using (_≃_; _⇔_; extensionality)

data List (A : Set) : Set where
  []   : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []


infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]        ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set}(xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = 
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎    
++-assoc (x ∷ xs) ys zs = 
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (_∷_ x) (++-identityʳ xs)

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys = 
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎  
length-++ (x ∷ xs) ys = 
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

reverse-++-commute : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute [] ys = 
  begin
    reverse ys
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    reverse ys ++ []
  ∎
reverse-++-commute (x ∷ xs) ys = 
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    (reverse (xs ++ ys)) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-commute xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ (reverse xs ++ [ x ])
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎

reverse-involution : ∀ {A : Set} (xs : List A)
  → reverse (reverse xs) ≡ xs
reverse-involution [] = refl
reverse-involution (x ∷ xs) = 
  begin
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-commute (reverse xs) [ x ] ⟩
    x ∷ (reverse (reverse xs))
  ≡⟨ cong (x ∷_) (reverse-involution xs) ⟩
    x ∷ xs
  ∎
   
shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys = 
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
     reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

sucs : List ℕ → List ℕ
sucs = map suc

map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A)
  → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose f g [] = refl
map-compose f g (x ∷ xs) rewrite map-compose f g xs = refl

map-++-commute : ∀ {A B : Set} {f : A → B} (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute [] ys = refl
map-++-commute {A}{B}{f} (x ∷ xs) ys = 
  begin
    f x ∷ map f (xs ++ ys)
  ≡⟨ cong (_ ∷_) (map-++-commute xs ys) ⟩
    f x ∷ map f xs ++ map f ys
  ∎

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set}
  → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node l n r) = node (map-Tree f g l) (g n) (map-Tree f g r)


foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys = 
  begin
     x ⊗ foldr _⊗_ e (xs ++ ys)
  ≡⟨ cong (_ ⊗_) (foldr-++ _⊗_ e xs ys) ⟩
    x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs
  ∎

map-is-foldr′ :  ∀ {A B : Set} {f : A → B} (x : List A) →
  map f x ≡ foldr (λ y → _∷_ (f y)) [] x
map-is-foldr′ [] = refl
map-is-foldr′ {A}{B}{f} (x ∷ xs) = 
  begin
    f x ∷ map f xs
  ≡⟨ cong (_ ∷_) (map-is-foldr′ xs) ⟩
    f x ∷ foldr (λ y → _∷_ (f y)) [] xs
  ∎
  
map-is-foldr : ∀ {A B : Set} {f : A → B} →
  map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr {A}{B}{f} = extensionality map-is-foldr′

fold-Tree : ∀ {A B C : Set}
  → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree fn comb (leaf x) = fn x
fold-Tree fn comb (node l n r) =
  let left-res  = fold-Tree fn comb l
      right-res = fold-Tree fn comb r in
      comb left-res n right-res  

-- map-Tree : ∀ {A B C D : Set}
--  → (A → C) → (B → D) → Tree A B → Tree C D
-- A & C node types
-- B & D leaf types
-- map-Tree f g (leaf x) = leaf (f x)
-- map-Tree f g (node l n r) = node (map-Tree f g l) (g n) (map-Tree f g r) 

map-is-fold-Tree′ : ∀ {A B C D : Set} {f : A → C} {g : B → D} (t : Tree A B) →
      map-Tree f g t ≡ fold-Tree (λ lf → leaf (f lf)) (λ l n r → node l (g n) r) t
map-is-fold-Tree′ (leaf x) = refl
map-is-fold-Tree′ {A}{B}{C}{D}{f}{g} (node l n r) = 
  begin
    node (map-Tree f g l) (g n) (map-Tree f g r)
  ≡⟨ cong (λ t → (node t _ _)) (map-is-fold-Tree′ l) ⟩
    node (fold-Tree (λ lf → leaf (f lf)) (λ l₁ n₁ → node l₁ (g n₁)) l) (g n) (map-Tree f g r)
  ≡⟨ cong (λ t → (node _ _ t)) (map-is-fold-Tree′ r) ⟩
    node (fold-Tree (λ lf → leaf (f lf)) (λ l₁ n₁ → node l₁ (g n₁)) l)
      (g n) (fold-Tree (λ lf → leaf (f lf)) (λ l₁ n₁ → node l₁ (g n₁)) r)
  ∎

map-is-fold-Tree : ∀ {A B C D : Set} (f : A → C) (g : B → D) →
  map-Tree f g ≡ fold-Tree (λ lf → leaf (f lf)) (λ l n r → (node l (g n) r)) 
map-is-fold-Tree f g = extensionality map-is-fold-Tree′


downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n

*-2 : ∀ (n : ℕ) → 2 * n ≡ n + n
*-2 zero = refl
*-2 (suc n) = 
  begin
    suc (n + suc (n + zero))
  ≡⟨ cong (λ x → suc (n + suc x)) (+-comm n zero) ⟩
    suc (n + suc (zero + n))
  ≡⟨⟩
    suc (n + suc n)
  ∎
open import Data.Nat.Properties using (*-distrib-∸;*-identity;+-∸-assoc;+-∸-comm;n∸n≡0;m≤m+n)

sq-gte : ∀ {n : ℕ} → n ≤ n * n
sq-gte {zero} = z≤n
sq-gte {suc n} = s≤s (m≤m+n n (n * suc n))

sum-downFrom : ∀ (n : ℕ)
  → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) = 
  begin
    sum (n ∷ downFrom n) * 2
  ≡⟨⟩
    (n + sum (downFrom n)) * 2
  ≡⟨ *-distrib-+ n (sum (downFrom n)) 2 ⟩
    n * 2 + sum (downFrom n) * 2
  ≡⟨ cong (n * 2 +_) (sum-downFrom n) ⟩
    n * 2 + (n * (n ∸ 1))
  ≡⟨ cong (_+ (n * (n ∸ 1))) (*-comm n 2) ⟩
    2 * n + (n * (n ∸ 1))
  ≡⟨ cong (_+ (n * (n ∸ 1))) (*-2 n) ⟩
    n + n + n * (n ∸ 1)
   ≡⟨ cong (n + n +_) ((proj₁ *-distrib-∸) n n 1) ⟩    
    n + n + (n * n ∸ n * 1)
   ≡⟨ cong (λ x → (n + n + (n * n ∸ x))) ((proj₂  *-identity) n) ⟩
     n + n + (n * n ∸ n)
   ≡⟨ cong (_ +_) (+-comm n (n * n ∸ n)) ⟩
     n + (n * n ∸ n) + n
   ≡⟨ cong (_ +_) (sym (+-∸-comm n sq-gte)) ⟩
     n + (n * n + n) ∸ n
   ≡⟨ cong (_∸ n) (+-comm n (n * n + n)) ⟩
      (n * n + n) + n ∸ n
   ≡⟨ cong (_ +_) (n∸n≡0 n) ⟩
     (n * n + n) + 0
   ≡⟨ +-comm (n * n + n) 0 ⟩
      0 + (n * n + n)
   ≡⟨⟩
     n * n + n
   ≡⟨ +-comm (n * n) n ⟩
     n + n * n
   ∎

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y = 
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y = 
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y    
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

foldl-e-≡ : ∀ {A B : Set} {_⊗_ : A → A → A} {xs : List A} {e x : A} → e ≡ x 
  → foldl _⊗_ e xs ≡ foldl _⊗_ x xs
foldl-e-≡ {A}{B}{_⊗_}{xs} p = cong (λ e≡x → foldl _⊗_ e≡x xs) p  

foldl-⊗ : ∀ {A B : Set} (_⊗_ : A → A → A) (x e : A) (xs : List A) → IsMonoid _⊗_ e
  → x ⊗ (foldl _⊗_ e xs) ≡ foldl _⊗_ (e ⊗ x) xs
foldl-⊗ _⊗_ x e [] ⊗-monoid = 
  begin
    x ⊗ e
  ≡⟨ (identityʳ ⊗-monoid) x ⟩
    x
  ≡⟨ sym ((identityˡ ⊗-monoid) x) ⟩
    e ⊗ x
  ∎
foldl-⊗ _⊗_ x e (x₁ ∷ xs) ⊗-monoid = 
  begin
    x ⊗ (foldl _⊗_ e (x₁ ∷ xs))
  ≡⟨⟩
    x ⊗ (foldl _⊗_ (e ⊗ x₁) xs)
  ≡⟨ cong (x ⊗_) (sym (foldl-⊗ _⊗_ x₁ e xs ⊗-monoid)) ⟩
    x ⊗ (x₁ ⊗ (foldl _⊗_ e xs))
  ≡⟨ sym ((assoc ⊗-monoid) x x₁ (foldl _⊗_ e xs)) ⟩
    (x ⊗ x₁) ⊗ (foldl _⊗_ e xs)
  ≡⟨ foldl-⊗ _⊗_ (x ⊗ x₁) e xs ⊗-monoid ⟩
    foldl _⊗_ (e ⊗ (x ⊗ x₁)) xs
  ≡⟨ foldl-e-≡ (sym ((assoc ⊗-monoid) e x x₁)) ⟩
    foldl _⊗_ ((e ⊗ x) ⊗ x₁) xs
  ∎


foldr-monoid-foldl : ∀ {A B : Set} (_⊗_ : A → A → A) (e : A) (xs : List A) →
  IsMonoid _⊗_ e → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl _⊗_ e [] ⊗-monoid = refl
foldr-monoid-foldl {A}{B} _⊗_ e (x ∷ xs) ⊗-monoid = 
  begin
    foldr _⊗_ e (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ e xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid-foldl {A}{B} _⊗_ e xs ⊗-monoid) ⟩
    x ⊗ (foldl _⊗_ e xs)
  ≡⟨ foldl-⊗ {A}{B} _⊗_ x e xs ⊗-monoid ⟩
    foldl _⊗_ (e ⊗ x) xs
  ∎


data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys =
  record
  { to      = to xs ys
  ; from    = from xs ys
  ; from∘to = λ Px → from∘to Px
  ; to∘from = {!!}
  }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      All P (xs ++ ys) → (All P xs × All P ys)
    to [] ys Pys = ⟨ [] , Pys ⟩
    to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
    ... | ⟨ Pxs , Pys ⟩ = ⟨ (Px ∷ Pxs) , Pys ⟩

    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      All P xs × All P ys → All P (xs ++ ys)
    from [] ys ⟨ [] , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ (from xs ys ⟨ Pxs , Pys ⟩)

    from∘to : ∀ {A : Set} {P : A → Set} {xs ys : List A} →
      (Px : All P (xs ++ ys)) → from xs ys (to xs ys Px) ≡ Px
    from∘to {A} {P} {[]} {ys} Px = refl
    from∘to {A} {P} {x ∷ xs} {ys} Px = 
      begin
        from (x ∷ xs) ys (to (x ∷ xs) ys Px)
      ≡⟨⟩
       {!!}
      
      
Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
  { to = to xs ys
  ; from = from xs ys
  }
  where

    to : ∀ {A : Set} {P : A → Set} (xs ys : List A)
      → Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
    to [] ys Pxs++ys = inj₂ Pxs++ys
    to (x ∷ xs) ys (here Px) = inj₁ (here Px)
    to (x ∷ xs) ys (there Pxs++ys) with to xs ys Pxs++ys
    ...| inj₁ Px = inj₁ (there Px)
    ...| inj₂ Py = inj₂ Py

    from : ∀ {A : Set} {P : A → Set} (xs ys : List A)
      → (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
    from [] ys (inj₁ ())
    from [] ys (inj₂ Py) = Py
    from (x ∷ xs) ys (inj₁ (here Px)) = here Px
    from (x ∷ xs) ys (inj₁ (there Px)) = there (from xs ys (inj₁ Px))
    from (x ∷ xs) ys (inj₂ Py) with from xs ys (inj₂ Py)
    ...| Pxs++ys = there Pxs++ys


_∘′_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘′ f) x  =  g (f x)

¬Any≃All¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
  → (¬_ ∘′ Any P) xs ≃ All (¬_ ∘′ P) xs
¬Any≃All¬ P xs =
  record
    { to      = λ{ NotAnyx → {!!} }
    ; from    = {!!}
    ; from∘to = {!!}
    ; to∘from = {!!}
    }


all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p = foldr _∧_ true ∘ map p

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P = ∀ (x : A) → Dec (P x)

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? [] = yes []
All? P? (x ∷ xs) with P? x | All? P? xs
...                | yes Px | yes Pxs = yes (Px ∷ Pxs)
...                | no ¬Px | _       = no λ{ (Px ∷ Pxs) → ¬Px Px}
...                | _      | no ¬Pxs = no λ{ (Px ∷ Pxs) → ¬Pxs Pxs}

any : ∀ {A : Set} → (A → Bool) → List A → Bool
any p = foldr _∨_ false ∘ map p

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no (λ ())
Any? P? (x ∷ xs) with P? x | Any? P? xs
...                | yes Px | _       = yes (here Px)
...                | no  _  | yes Pxs = yes (there Pxs)
...                | no ¬Px | no ¬Pxs = no λ{ (here x₁) → ¬Px x₁ ; (there x₁) → ¬Pxs x₁} 

filter? : ∀ {A : Set} {P : A → Set}
  → (P? : Decidable P) → List A → ∃[ ys ] (All P ys)
filter? P? [] = ⟨ [] , [] ⟩
filter? P? (x ∷ xs) with P? x | filter? P? xs
...                    | yes Px | ⟨ xs′ , Pxs ⟩ = ⟨ x ∷ xs′ , Px ∷ Pxs ⟩
...                    | no ¬p  | ⟨ xs′ , Pxs ⟩ = ⟨ xs′ , Pxs ⟩
