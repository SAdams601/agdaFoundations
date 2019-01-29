module plfa.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
    ----------------------------Given proof that forall all A's f and g are the same
    → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero = m
m +′ suc n = suc (m +′ n)

--Proving + and +′ are actually the same function

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
    --Is this some sort of nifty trick for the termination checker??
    helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
    helper m zero = refl
    helper m (suc n) = cong suc (helper m n)
    
same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

open _≃_
