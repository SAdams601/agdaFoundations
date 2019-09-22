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

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
       Value M
    ----------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ∶ A
    -----------
  → Progress M

progress (⊢ƛ ⊢N) = done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L—→L′ = step (ξ-·₁ L—→L′)
... | done VL with progress ⊢M
...    | step M—→M′ = step (ξ-·₂ VL M—→M′)
...    | done VM with canonical ⊢L VL
...       | C-ƛ _ = step (β-ƛ VM)
progress ⊢zero = done V-zero
progress (⊢suc ⊢M) with progress ⊢M
... | step M—→M′ = step (ξ-suc M—→M′)
... | done MV    = done (V-suc MV)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′ = step (ξ-case L—→L′)
... | done VL with canonical ⊢L VL
...    | C-zero = step β-zero
...    | C-suc CL = step (β-suc (value CL))
progress (⊢μ ⊢M) = step β-μ

Progress-≃ : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
Progress-≃ {M} = record {to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from}
  where
    to      = λ{ (step {N} M—→N) → inj₂ ⟨ N , M—→N ⟩  ;
                 (done M) → inj₁ M}
    from    = λ{ (inj₁ VM ) → done VM ;
                 (inj₂ ⟨ N , M—→N ⟩) → step M—→N}
    from∘to = λ{ (step M—→N) → refl ; (done VM) → refl}
    to∘from = λ{ (inj₁ VM) → refl ; (inj₂ ⟨ N , M—→N ⟩) → refl}

progress′ : ∀ M {A} → ∅ ⊢ M ∶ A → Value M ⊎ ∃[ N ](M —→ N)
progress′ _        (⊢ƛ ⊢M)  = inj₁ V-ƛ
progress′ (L · M) (⊢L · ⊢M) with progress′ L ⊢L
progress′ (L · M) (⊢L · ⊢M) | inj₂ ⟨ L′ , L—→L′ ⟩ = inj₂ ⟨ L′ · M , ξ-·₁ L—→L′ ⟩
... | inj₁ VL with progress′ M ⊢M
progress′ (L · M) (⊢L · ⊢M) | inj₁ VL | inj₂ ⟨ M′ , M—→M′ ⟩ = inj₂ ⟨ L · M′ , ξ-·₂ VL M—→M′ ⟩
progress′ ((ƛ x ⇒ y ) · M) (⊢L · ⊢M) | inj₁ V-ƛ | inj₁ VM = inj₂ ⟨ y [ x := M ] , (β-ƛ VM) ⟩
progress′ `zero ⊢zero = inj₁ V-zero
progress′ (`suc M) (⊢suc ⊢M) with progress′ M ⊢M 
... | inj₁ VM = inj₁ (V-suc VM)
... | inj₂ ⟨ M′ , M—→M′ ⟩ = inj₂ ⟨ (`suc M′) , (ξ-suc M—→M′) ⟩
progress′ (case L [zero⇒ M |suc x ⇒ N ]) (⊢case ⊢L ⊢M ⊢N) with progress′ L ⊢L
... | inj₂ ⟨ L′ , L—→L′ ⟩ = inj₂ ⟨ case L′ [zero⇒ M |suc x ⇒ N ] , ξ-case L—→L′ ⟩
progress′ case .`zero [zero⇒ M |suc x ⇒ N ] (⊢case ⊢L ⊢M ⊢N) | inj₁ V-zero = inj₂ ⟨ M , β-zero ⟩
progress′ case (`suc V) [zero⇒ M |suc x ⇒ N ] (⊢case ⊢L ⊢M ⊢N) | inj₁ (V-suc VL) = inj₂ ⟨ (N [ x := V ]) , (β-suc VL) ⟩
progress′ (μ x ⇒ N) (⊢μ ⊢M) = inj₂ ⟨ N [ x := μ x ⇒ N ] , β-μ ⟩

{-
—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
-}

value? : ∀ {A M} → ∅ ⊢ M ∶ A → Dec (Value M)
value? {A} {M} ⊢M with progress ⊢M
... | done VM = yes VM
... | step M—→N = no (—→¬V M—→N)


