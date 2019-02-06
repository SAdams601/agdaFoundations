module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong-app)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.Connectives using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; curry′) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)


¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ----
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x = λ ¬x → ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    --------
  → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    --------
  → (¬ B → ¬ A)
contraposition f ¬b a = ¬b (f a)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality λ ()


assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ x → ⊥-elim (¬x x)

open import plfa.Relations using (_<_;s<s;z<s)

<-irreflexive : ∀ {n : ℕ}
  → ¬ (n < n)
<-irreflexive {zero} ()
<-irreflexive {suc n} (s<s n<n) = <-irreflexive n<n

data Trichotomy (m n : ℕ) : Set where
  equals :
         m ≡ n
     → ¬(m < n)
     → ¬(n < m)
     --------
     → Trichotomy m n

  m<n :
        m < n
     → m ≢ n
     → ¬(n < m)
     ----------
     → Trichotomy m n

  n<m :
       n < m 
    → m ≢ n
    → ¬(m < n)
       ---------
    → Trichotomy m n



suc-cong-< : ∀ {m n : ℕ}
  → ¬ (m < n)
    ----------
  → ¬ (suc m < suc n)
suc-cong-< ¬-p (s<s p) = ¬-elim ¬-p p

suc-injective : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

suc-≢ : ∀ {m n : ℕ}
  → m ≢ n
    --------
  → suc m ≢ suc n
suc-≢ {zero} {zero} m≢n suc-m≡n = ¬-elim (λ x → m≢n refl) suc-m≡n
suc-≢ {zero} {suc n} m≢n ()
suc-≢ {suc m} {zero} m≢n ()
suc-≢ {suc m} {suc n} m≢n suc-m≡n = contraposition (λ x → suc-injective x) m≢n suc-m≡n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = equals refl (λ()) (λ ())
<-trichotomy zero (suc n) = m<n z<s (λ ()) (λ ()) 
<-trichotomy (suc m) zero = n<m z<s (λ ()) (λ ())
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...         | equals m≡n m≮n n≮m = equals (cong suc m≡n) (suc-cong-< m≮n) (suc-cong-< n≮m)
...         | m<n    mLTn m≢n n≮m = m<n (s<s mLTn) (suc-≢ m≢n) (suc-cong-< n≮m)
...         | n<m    nLTm m≢n m≮n = n<m (s<s nLTm) (suc-≢ m≢n) (suc-cong-< m≮n)  

open plfa.Isomorphism.≃-Reasoning
open import plfa.Connectives using (→-distrib-⊎)

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× {A}{B} = record
    { to      = λ{ x → ⟨ x ∘ inj₁ , x ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl }}
    ; to∘from = λ{ ⟨ fst , snd ⟩ → refl}
    }

×-dual-⊎ : ∀ {A B : Set} → ¬ (A × B) ≲ (¬ A) ⊎ (¬ B)
×-dual-⊎ =
  record
    { to      = λ ¬x → {!!}
    ; from    = λ{ (inj₁ x) a×b → ¬-elim x (proj₁ a×b) ; (inj₂ y) a×b → ¬-elim y (proj₂ a×b)}
    ; from∘to = λ x → {!!}
    }

{-
The issue is that I can't access A , B inside of the ¬ (A × B) 
-}

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A
  ¬¬-elim : ∀ {A : Set} → ¬ ¬ A → A
  peirce : ∀ {A B : Set} → ((A → B) → A) → A
  →-disjunc : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
  deMorgan : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ (λ x → k (inj₁ x)))





Stable : Set → Set
Stable A = ¬ ¬ A → A

neg-stable : ∀ {A : Set} → Stable (¬ A)
neg-stable k = ¬¬¬-elim k

conj-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
conj-stable aS bS = λ ¬¬x → ⟨ (aS (λ ¬x → ¬¬x (λ a×b → ¬x (proj₁ a×b)))) ,
                              bS (λ ¬b → ¬¬x (λ a×b → ¬b (proj₂ a×b))) ⟩
