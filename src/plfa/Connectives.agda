module plfa.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-suc)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)
open plfa.Isomorphism.≃-Reasoning

data _×_ (A : Set) (B : Set) : Set where
   ⟨_,_⟩ :
        A
     → B
     ------
     → A × B

proj₁ : ∀ {A B : Set}
  → A × B
  --------
  → A
proj₁ ⟨ a , b ⟩ = a

proj₂ : ∀ {A B : Set}
  → A × B
  --------
  → B
proj₂ ⟨ a , b ⟩ = b

record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
