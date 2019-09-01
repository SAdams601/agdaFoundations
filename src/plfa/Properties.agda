module plfa.Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plfa.Isomorphism
open import plfa.Lambda

V¬—→ : ∀ {M N}
  → Value M
    -----------
  → ¬ (M —→ N)
V¬—→ V-ƛ    ()
V¬—→ V-zero ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M—→N VM = V¬—→ VM M—→N

infix 4 Canonical_∶_

data Canonical_∶_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
    → ∅ , x ∶ A ⊢ N ∶ B
      ---------------------------
    → Canonical (ƛ x ⇒ N) ∶ (A ⇒ B)

  C-zero :
    ----------------------
     Canonical `zero ∶ `ℕ

  C-suc : ∀ {V}
    → Canonical V ∶ `ℕ
      -----------------------
    → Canonical `suc V ∶ `ℕ

canonical : ∀ {V A}
  → ∅ ⊢ V ∶ A
  → Value V
    ---------------
  → Canonical V ∶ A

canonical (⊢ƛ ⊢N)  V-ƛ = C-ƛ ⊢N
canonical (⊢L · ⊢M) ()
canonical ⊢zero V-zero = C-zero
canonical (⊢suc ⊢V) (V-suc VV) = C-suc (canonical ⊢V VV)
canonical (⊢case ⊢L ⊢M ⊢N) ()
canonical (⊢μ t) ()

value : ∀ {M A}
  → Canonical M ∶ A
    -------------------
  → Value M
value (C-ƛ ⊢N) = V-ƛ
value C-zero = V-zero
value (C-suc ⊢V) = V-suc (value ⊢V)

typed : ∀ {M A}
  → Canonical M ∶ A
    ----------------
  → Value M
typed (C-ƛ ⊢N) = V-ƛ
typed C-zero = V-zero
typed (C-suc ⊢V) = V-suc (typed ⊢V)
