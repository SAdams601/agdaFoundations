module plfa.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple using (+-suc)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    ------------------------
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to      = λ f → ⟨ (λ x → proj₁ (f x)) , (λ y → proj₂ (f y)) ⟩
    ; from    = λ{ ⟨ f , g ⟩ a → ⟨ (f a) , (g a) ⟩}
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) x = inj₁ (f x)
⊎∀-implies-∀⊎ (inj₂ g) x = inj₂ (g x)  
