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

⊥-elim : ∀ {A : Set}
  → ⊥
    ---
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ = 
  record
    { to      = λ{ (inj₁ ()); (inj₂ a) → a}
    ; from    = inj₂
    ; from∘to = λ{ (inj₁ ()); (inj₂ x) → refl }
    ; to∘from = λ { a → refl}
    }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} = 
  ≃-begin  
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎ 

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    --------
  → B
→-elim L M = L M


η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      = λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    = λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to = λ f → refl
    ; to∘from = λ g → extensionality (λ{⟨ x , y ⟩ → refl})
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩}
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) →  g x ; (inj₂ x) → h x}}
    ; from∘to = λ f → extensionality (λ{ (inj₁ x) → refl ; (inj₂ x) → refl})
    ; to∘from = λ{ ⟨ g , h ⟩ → refl}
    } 

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩}
    ; from    = λ{ ⟨ g , h ⟩ → λ{ x → ⟨ g x , h x ⟩}}
    ; from∘to = λ f → extensionality λ{ x → η-× (f x)}
    ; to∘from = λ{ ⟨ g , h ⟩ → refl}
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → inj₁ ⟨ x , z ⟩ ; ⟨ inj₂ x , z ⟩ → inj₂ ⟨ x , z ⟩}
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩ ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩}
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl ; ⟨ inj₂ x , z ⟩ → refl}
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl ; (inj₂ ⟨ y , z ⟩ ) → refl}
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩ ;
                   (inj₂ x) → ⟨ inj₂ x , inj₂ x ⟩}
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩ ;
                   ⟨ inj₁ x , inj₂ z ⟩ → inj₂ z ;
                   ⟨ inj₂ z , _      ⟩ → inj₂ z }
    ; from∘to = λ{ (inj₁ (⟨ x , y ⟩)) → refl ;
                   (inj₂ x) → refl}
    }


⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , C ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , C ⟩ = inj₂ ⟨ b , C ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

{-
×⊎-implies-⊎× : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
×⊎-implies-⊎× ⟨ inj₁ a , inj₁ b ⟩ = inj₁ ⟨ a , b ⟩
×⊎-implies-⊎× ⟨ inj₁ a , inj₂ d ⟩ = {!!}
×⊎-implies-⊎× ⟨ inj₂ c , inj₁ b ⟩ = {!!}
×⊎-implies-⊎× ⟨ inj₂ c , inj₂ d ⟩ = inj₂ ⟨ c , d ⟩
There is not solution to this because we need either an A and a B
or a C and a D but the middle two cases we don't have both of the types to make one
of the required pairs. Instead we have one type from each of the pairs
-}
