module plfa.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-suc)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality; _⇔_)
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

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_ 

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to      = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from    = λ { ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to = λ { ⟨ x , y ⟩ → refl }
    ; to∘from = λ { ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ →  ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record
    { to      = λ{ A⇔B →  ⟨ _⇔_.to A⇔B , _⇔_.from A⇔B ⟩ }
    ; from    = λ{ AprodB → fns-⇔ (proj₁ AprodB) (proj₂ AprodB) }
    ; from∘to = λ{ A⇔B → refl}
    ; to∘from = λ{ ⟨ A→B , B→A ⟩ → refl }
    }
    where
    fns-⇔ : ∀ {A B : Set} → (A → B) → (B → A) → A ⇔ B
    fns-⇔ t f = 
      record
        { to   = t
        ; from = f
        }


data ⊤ : Set where
  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }


⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
   (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

data _⊎_ : Set → Set → Set where

  inj₁ : ∀ {A B : Set}
    → A
    ----------
    → A ⊎ B

  inj₂ : ∀ {A B : Set}
    → B
    ---------
    → A ⊎ B


case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
  ----------
  → C

case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infix 1 _⊎_

case-cancels : ∀ {A B : Set} (w : A ⊎ B) →
  case-⊎ inj₂ inj₁ (case-⊎ inj₂ inj₁ w) ≡ w
case-cancels (inj₁ x) = refl
case-cancels (inj₂ x) = refl

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to      = case-⊎ inj₂ inj₁
    ; from    = case-⊎ inj₂ inj₁
    ; from∘to = λ A⊎B → case-cancels A⊎B                        
    ; to∘from = λ B⊎A → case-cancels B⊎A
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to      = toFull
    ; from    = fromFull
    ; from∘to = λ{ (inj₁ (inj₁ A)) → refl ;
                   (inj₁ (inj₂ B)) → refl ;
                   (inj₂ C) → refl }                          
    ; to∘from = λ { (inj₁ A) → refl ;
                    (inj₂ (inj₁ B)) → refl ;
                    (inj₂ (inj₂ C)) → refl}
    }
    where
      A-to-case = inj₁
      B-to-case = inj₂ ∘ inj₁
      C-to-case   = inj₂ ∘ inj₂
      A⊎B-to-case = case-⊎ A-to-case B-to-case
      toFull = case-⊎ A⊎B-to-case C-to-case
      A-from-case = inj₁ ∘ inj₁
      B-from-case = inj₁ ∘ inj₂
      C-from-case = inj₂
      B⊎C-from-case = case-⊎ B-from-case C-from-case
      fromFull = case-⊎ A-from-case B⊎C-from-case

data ⊥ : Set where

