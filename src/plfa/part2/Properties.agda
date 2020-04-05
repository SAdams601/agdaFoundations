module plfa.part2.Properties where

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
open import plfa.part2.Lambda


V¬→ : ∀ {M N}
  → Value M
    ---------
  → ¬ (M —→ N)
V¬→ V-ƛ          ()
V¬→ V-zero       ()
V¬→ (V-suc M) (ξ-suc M→N) = V¬→ M M→N

→¬V : ∀ {M N}
  → M —→ N
  ----------
  → ¬ Value M
→¬V M→N VM = V¬→ VM M→N

infix 4 Canonical_∶_

data Canonical_∶_ : Term → Type → Set where
  C-ƛ : ∀ {x A N B}
    → ∅ , x ∶ A ⊢ N ∶ B
      -------------------
    → Canonical (ƛ x ⇒ N) ∶ (A ⇒ B)

  C-zero :
    --------------------
    Canonical ‵zero ∶ ‵ℕ

  C-suc : ∀ {V}
    → Canonical V ∶ ‵ℕ
      ----------------
    → Canonical ‵suc V ∶ ‵ℕ

canonical : ∀ {V A}
  → ∅ ⊢ V ∶ A
  → Value V
    -------------
  → Canonical V ∶ A
canonical (⊢ƛ ⊢N)    V = C-ƛ ⊢N
canonical ⊢zero      V = C-zero
canonical (⊢suc ⊢V) (V-suc V) = C-suc (canonical ⊢V V)

value : ∀ {M A}
  → Canonical M ∶ A
    -----------------
  → Value M
value (C-ƛ N)   = V-ƛ
value C-zero    = V-zero
value (C-suc V) = V-suc (value V)

typed : ∀ {M A}
  → Canonical M ∶ A
    ----------------
  → ∅ ⊢ M ∶ A
typed (C-ƛ x)   = ⊢ƛ x
typed C-zero    = ⊢zero
typed (C-suc CV) = ⊢suc (typed CV)

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      -------
    → Progress M

  done :
      Value M
    ---------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ∶ A
    ----------
  → Progress M
progress (⊢ƛ M)        = done V-ƛ
progress (M · N) with progress M
... | step M→M′        = step (ξ-·₁ M→M′)
... | done VM with progress N
...    | step N→N′     = step (ξ-·₂ N→N′)
...    | done VN with canonical M VM
...       | C-ƛ _      = step (β-ƛ VN)
progress ⊢zero         = done V-zero
progress (⊢suc M) with progress M
... | step M→N         = step (ξ-suc M→N)
... | done VM          = done (V-suc VM)
progress (⊢case L M N) with progress L
... | step L→L′        = step (ξ-case L→L′)
... | done VL with canonical L VL
...    | C-zero        = step β-zero
...    | C-suc CL      = step (β-suc (value CL))
progress (⊢μ M)        = step β-μ


Progress-≃ : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
Progress-≃ {M} = record
  { to      = to
  ; from    = from
  ; from∘to = from∘to
  ; to∘from = to∘from }
  where
    to : Progress M → Value M ⊎ ∃[ N ](M —→ N)
    to (done VM) = inj₁ VM
    to (step {N} M→N) = inj₂ ⟨ N , M→N ⟩
    from : Value M ⊎ ∃[ N ](M —→ N) → Progress M
    from (inj₁ VM) = done VM
    from (inj₂ ⟨ N , M→N ⟩) = step M→N
    from∘to : (x : Progress M) → from (to x) ≡ x
    from∘to (step M→N) = refl
    from∘to (done VM) = refl
    to∘from : (M⊎Step : Value M ⊎ ∃[ N ](M —→ N)) → to (from M⊎Step) ≡ M⊎Step
    to∘from (inj₁ VM) = refl
    to∘from (inj₂ ⟨ N , M→N ⟩) = refl

progress′ : ∀ M {A} → ∅ ⊢ M ∶ A → Value M ⊎ ∃[ N ](M —→ N)
progress′ _ (⊢‵ ())
progress′ (ƛ x ⇒ M) (⊢ƛ ty) = inj₁ V-ƛ
progress′ ‵zero ty = inj₁ V-zero
progress′ (‵suc M) (⊢suc tyM) with progress′ M tyM
... | inj₂ ⟨ M′ , M→M′ ⟩ = inj₂ ⟨ ‵suc M′ , (ξ-suc M→M′) ⟩
... | inj₁ VM    = inj₁ (V-suc VM) 
progress′ case L [zero⇒ M |suc x ⇒ N ] (⊢case tyL tyM tyN) with progress′ L tyL
... | inj₂ ⟨ L′ , L→L′ ⟩ = inj₂ ⟨ case L′ [zero⇒ M |suc x ⇒ N ] , (ξ-case L→L′) ⟩
... | inj₁ VL with canonical tyL VL
...    | C-zero   = inj₂ ⟨ M , β-zero ⟩
progress′ case (‵suc V) [zero⇒ M |suc x ⇒ N ] (⊢case tyL tyM tyN) | inj₁ (V-suc VL) | C-suc CL = inj₂ ⟨ N [ x :=  V ] , β-suc (value CL) ⟩
progress′ (μ x ⇒ M) ty = inj₂ ⟨ (M [ x := μ x ⇒ M ]) , β-μ ⟩
progress′ (M · N) (tyM · tyN) with progress′ M tyM
... | inj₂ ⟨ M′ , M→M′ ⟩ = inj₂ ⟨ M′ · N , (ξ-·₁ M→M′) ⟩
... | inj₁ V-ƛ with progress′ N tyN
... | inj₂ ⟨ N′ , N→N′ ⟩ = inj₂ ⟨ M · N′ , ξ-·₂ N→N′ ⟩
progress′ ((ƛ x ⇒ B) · N) (tyM · tyN) | inj₁ V-ƛ | inj₁ VN = inj₂ ⟨ B [ x := N ] , (β-ƛ VN) ⟩

value? : ∀ {A M} → ∅ ⊢ M ∶ A → Dec (Value M)
value? ⊢M with progress ⊢M
... | done VM   = yes VM
... | step M→M′ = no (→¬V M→M′)
