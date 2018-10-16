module basics.list where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import basics.nat
open import basics.bool
data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [] : 𝕃 A
  _∷_ : (x : A) (xs : 𝕃 A) → 𝕃 A

length : ∀{ℓ}{A : Set ℓ} → 𝕃 A → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

_++_ : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → 𝕃 A → 𝕃 B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

filter : ∀ {ℓ}{A : Set ℓ} → (A → 𝔹) → 𝕃 A → 𝕃 A
filter p [] = []
filter p (x ∷ xs) = let r = filter p xs in
                     if p x then x ∷ r else r

remove : ∀{ℓ}{A : Set ℓ} 
  (eq : A → A → 𝔹)(a : A)(l : 𝕃 A) → 𝕃 A
remove eq a l = filter (λ x → ~ (eq a x)) l

data maybe {ℓ}(A : Set ℓ) : Set ℓ where
  just : A → maybe A
  nothing : maybe A

nth : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → maybe A
nth _ [] = nothing
nth 0 (x ∷ _) = just x
nth (suc n) (x ∷ xs) = nth n xs


reverse-helper : ∀{ℓ}{A : Set ℓ} → (𝕃 A) → (𝕃 A) → 𝕃 A
reverse-helper h []  = h
reverse-helper h (x ∷ xs) = reverse-helper (x ∷ h) xs

reverse : ∀{ℓ}{A : Set ℓ} → (𝕃 A) → (𝕃 A)
reverse l = reverse-helper [] l

length-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → length (l1 ++ l2) ≡ (length l1) + (length l2)
length-++ [] l2 = refl
length-++ (x ∷ l1) l2 rewrite length-++ l1 l2 = refl

++-assoc : ∀ {ℓ}{A : Set ℓ} (l1 l2 l3 : 𝕃 A) → (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++-assoc [] l2 l3 = refl
++-assoc (x ∷ l1) l2 l3 rewrite ++-assoc l1 l2 l3 = refl

length-filter : ∀ {ℓ}{ A : Set ℓ} (p : A → 𝔹)(l : 𝕃 A) → length (filter p l) ≤ length l ≡ tt
length-filter p [] = refl
length-filter p (x ∷ l) with p x
length-filter p (x ∷ l) | tt = length-filter p l
length-filter p (x ∷ l) | ff = {!!}  
