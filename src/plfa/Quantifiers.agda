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

{-
⊎∀-implies-∀⊎′ : ∀ {A : Set} {B C : A → Set}
               → ∀ (x : A) → B x ⊎ C x
                 ------------------------------------------
               → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
⊎∀-implies-∀⊎′ a (inj₁ b) = inj₁ (λ x → {!!})
⊎∀-implies-∀⊎′ a (inj₂ c) = inj₂ {!!}  

This does not work because we already have a specific type of B x or C x and can't extract a way to construct a B or C dependently
-}

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    -------------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
  { to      = λ f → λ{ ⟨ x , y ⟩ → f x y}
  ; from    = λ g → λ x → λ y → g ⟨ x , y ⟩
  ; from∘to = λ x → refl
  ; to∘from = λ{ g → extensionality (λ{ ⟨ x , y ⟩ → refl})}
  }

∃×-implies-×∃ : ∀ {A : Set} { B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ⟨ b , c ⟩ ⟩ = ⟨ ⟨ x , b ⟩ , ⟨ x , c ⟩ ⟩

{-
×∃-implies-∃× : ∀ {A : Set} {B C : A → Set} →
  (∃[ x ] B x) × (∃[ x ] C x) → ∃[ x ] (B x × C x)
×∃-implies-∃× ⟨ ⟨ x₁ , b ⟩ , ⟨ x₂ , c ⟩ ⟩ = ⟨ x , ⟨ b , {!!} ⟩ ⟩  

This (the inverse) does not hold because the existential variable need not
be the same for the respective parts of the conjunction.

In the above case x₁ ≢ x₂
-}


data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃ :  ∀ {n : ℕ} → odd n  → ∃[ m ] (1 + m * 2 ≡ n)  

even-∃ even-zero = ⟨ 0 , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                         | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩


odd-∃ (odd-suc e) with even-∃ e
...                | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → even n → ∃[ m ] (2 * m ≡ n)
∃-odd : ∀ {n : ℕ} → odd n → ∃[ m ] (1 + 2 * m ≡ n)

open import Data.Nat.Properties using (+-comm; +-suc)

lemma : ∀ (m : ℕ) → 2 * suc m ≡ suc (suc (2 * m))
lemma m =
  begin
    2 * suc m
  ≡⟨⟩
    suc m + (suc m + zero)
  ≡⟨ cong suc (+-suc m (m + zero)) ⟩
     suc (suc (m + (m + zero)))
  ≡⟨⟩
    suc (suc (2 * m))
  ∎

∃-even even-zero = ⟨ zero , refl ⟩
∃-even (even-suc o) with ∃-odd o
...                        | ⟨ m , refl ⟩ = ⟨ suc m , lemma m ⟩

∃-odd (odd-suc e) with ∃-even e
...                      | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

import plfa.Relations as Rel
open Rel using (_≤_; z≤n; s≤s)
open Rel.≤-Reasoning

x≤x : ∀ {x : ℕ} → x ≤ x
x≤x {zero} = z≤n
x≤x {suc x} = s≤s x≤x

x≤sucx : ∀ {x : ℕ} → x ≤ suc x
x≤sucx {zero} = z≤n
x≤sucx {suc x} = s≤s x≤sucx

lemma₂ : ∀ {x y : ℕ} → x ≤ y → x ≤ suc y
lemma₂ {zero} p = z≤n
lemma₂ {suc x} {zero} () 
lemma₂ {suc x} {suc y} (s≤s p) = s≤s (lemma₂ p)

≤-rhsSuc : ∀ {x y : ℕ} → y ≤ x + suc y
≤-rhsSuc {zero} = x≤sucx
≤-rhsSuc {suc x} = lemma₂ ≤-rhsSuc

y≤y+ : ∀ {x y : ℕ} → y ≤ x + y
y≤y+ {zero} = x≤x
y≤y+ {suc x} {zero} = z≤n
y≤y+ {suc x} {suc y} = s≤s ≤-rhsSuc


y≤sucx : ∀ {x y : ℕ} → x ≤ y → x ≤ suc y
y≤sucx {zero} {zero} p = z≤n
y≤sucx {zero} {suc y} p = z≤n
y≤sucx {suc x} {zero} ()
y≤sucx {suc x} {suc y} (s≤s p) = s≤s (y≤sucx p)

∃-+-≤ : ∀{x y z : ℕ} → ∃[ x ]( x + y ≡ z) → y ≤ z
∃-+-≤ {y} ⟨ zero , refl ⟩ = x≤x
∃-+-≤ {y} ⟨ suc x , refl ⟩ = y≤sucx y≤y+

--"There does not exist an x such that B x"
-- is isomorphic to
-- "for all x's there does not exist a B x"
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
  { to      = λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩}
  ; from    = λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
  ; from∘to = λ{ ¬∃xy → extensionality (λ{ ⟨ x , y ⟩ → refl})}
  ; to∘from = λ{ y → refl}
  }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    ----------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , y ⟩ = λ z → y (z x)             


{-
¬∀-implies-∃¬ : ∀ {A : Set} {B : A → Set}
  → ¬ (∀ x → B x)
    ----------------
  → ∃[ x ] (¬ B x)
¬∀-implies-∃¬ ¬∀ = ⟨ {!!} , (λ x → ¬∀ {!!}) ⟩

The converse is not true because we have not general way to 
construct a term of type A for which ¬ B x holds
-}
