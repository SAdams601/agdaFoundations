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
...    | step N→N′     = step (ξ-·₂ VM N→N′)
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
... | inj₂ ⟨ N′ , N→N′ ⟩ = inj₂ ⟨ M · N′ , ξ-·₂ V-ƛ N→N′ ⟩
progress′ ((ƛ x ⇒ B) · N) (tyM · tyN) | inj₁ V-ƛ | inj₁ VN = inj₂ ⟨ B [ x := N ] , (β-ƛ VN) ⟩

value? : ∀ {A M} → ∅ ⊢ M ∶ A → Dec (Value M)
value? ⊢M with progress ⊢M
... | done VM   = yes VM
... | step M→M′ = no (→¬V M→M′)

ext : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ∶ A → Δ ∋ x ∶ A)
    ----------------------------------
  → (∀ {x y A B} → Γ , y ∶ B ∋ x ∶ A → Δ , y ∶ B ∋ x ∶ A)
ext p Z = Z
ext p (S x≢y ∋x) = S x≢y (p ∋x)


rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ∶ A → Δ ∋ x ∶ A)
    ---------------------------------
  → (∀ {M A} → Γ ⊢ M ∶ A → Δ ⊢ M ∶ A)
rename p (⊢‵ ∋M)          = ⊢‵ (p ∋M)
rename p (⊢ƛ ⊢M)          = ⊢ƛ (rename (ext p) ⊢M)
rename p (⊢L · ⊢M)        = (rename p ⊢L) · (rename p ⊢M)
rename p ⊢zero            = ⊢zero
rename p (⊢suc ⊢M)        = ⊢suc (rename p ⊢M)
rename p (⊢case ⊢L ⊢M ⊢N) = ⊢case (rename p ⊢L) (rename p ⊢M) (rename (ext p) ⊢N)
rename p (⊢μ ⊢M)          = ⊢μ (rename (ext p) ⊢M)

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ∶ A
    ----------
  → Γ ⊢ M ∶ A
weaken {Γ} ⊢M = rename p ⊢M
  where
    p : ∀ {z C}
      → ∅ ∋ z ∶ C
        ----------
      → Γ ∋ z ∶ C
    p ()

drop : ∀ {Γ x M A B C}
  → Γ , x ∶ A , x ∶ B ⊢ M ∶ C
    --------------------------
  → Γ , x ∶ B ⊢ M ∶ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename p ⊢M
  where
    p : ∀ {z C}
      → Γ , x ∶ A , x ∶ B ∋ z ∶ C
        -------------------------
      → Γ , x ∶ B ∋ z ∶ C
    p Z                 = Z
    p (S x≢x Z)         = ⊥-elim (x≢x refl)
    p (S z≢x (S _ ∋z)) = S z≢x ∋z

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ∶ B , x ∶ A ⊢ M ∶ C
    --------------------------
  → Γ , x ∶ A , y ∶ B ⊢ M ∶ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename p ⊢M
  where
    p : ∀ {z C}
      → Γ , y ∶ B , x ∶ A ∋ z ∶ C
    --------------------------
      → Γ , x ∶ A , y ∶ B ∋ z ∶ C
    p Z                    = S x≢y Z
    p (S y≢x Z)            = Z
    p (S z≢x (S z≢y ∋z))   = S z≢y (S z≢x ∋z)

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ∶ A
  → Γ , x ∶ A ⊢ N ∶ B
    -------------------
  → Γ ⊢ N [ x := V ] ∶ B
subst {x = y} ⊢V (⊢‵ {x = x} Z) with  x ≟ y
... | yes _ = weaken ⊢V
... | no y≢y  = ⊥-elim (y≢y refl)
subst {x = y} ⊢V (⊢‵ (S {x = x} x≢y ∋x)) with x ≟ y
... | yes refl = ⊥-elim (x≢y refl)
... | no  _    = ⊢‵ ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl = ⊢ƛ (drop ⊢N)
... | no x≢y     = ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢M · ⊢N)           = (subst ⊢V ⊢M) · (subst ⊢V ⊢N)
subst ⊢V ⊢zero               = ⊢zero
subst ⊢V (⊢suc ⊢N)           = ⊢suc (subst ⊢V ⊢N)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl = ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no x≢y   = ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N)) 
subst {x = y} ⊢V (⊢μ {x = x} ⊢N) with x ≟ y
... | yes refl = ⊢μ (drop ⊢N)
... | no x≢y   = ⊢μ (subst ⊢V (swap x≢y ⊢N))

subst-bind : ∀ {Γ V A B C N} → (x : Id) → (y : Id) → ∅ ⊢ V ∶ A → Γ , y ∶ A , x ∶ B ⊢ N ∶ C → Γ , x ∶ B ⊢ ([ x ≣ y ] V ↔ N) ∶ C

subst′ : ∀ {Γ x N V A B}
  → ∅ ⊢ V ∶ A
  → Γ , x ∶ A ⊢ N ∶ B
    ------------------
  → Γ ⊢ N [ x := V ]′ ∶ B
subst′ {x = y} ⊢V (⊢‵ {x = x} Z) with x ≟ y
... | yes refl = weaken ⊢V
... | no x≢y   = ⊥-elim (x≢y refl)
subst′ {x = y} ⊢V (⊢‵ {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl = ⊥-elim (x≢y refl)
... | no _   = ⊢‵ ∋x
subst′ ⊢V (⊢M · ⊢N) = subst′ ⊢V ⊢M · subst′ ⊢V ⊢N
subst′ ⊢V ⊢zero     = ⊢zero
subst′ ⊢V (⊢suc ⊢N) = ⊢suc (subst′ ⊢V ⊢N)
subst′ {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) = ⊢case (subst′ ⊢V ⊢L) (subst′ ⊢V ⊢M) (subst-bind x y ⊢V ⊢N)
--Γ , x ∶ ‵ℕ ⊢ [ x ≣ y ] V ↔ N ∶ B
subst′ {x = y} ⊢V (⊢μ {x = x} ⊢N) = ⊢μ (subst-bind x y ⊢V ⊢N)
--Γ , x ∶ B ⊢ [ x ≣ y ] V ↔ M ∶ B
subst′ {x = y} ⊢V (⊢ƛ {x = x} ⊢N) = ⊢ƛ (subst-bind x y ⊢V ⊢N)
--Γ , x ∶ A ⊢ [ x ≣ y ] V ↔ N ∶ B


subst-bind x y ⊢V ⊢N with x ≟ y
... | yes refl = drop ⊢N
... | no  x≢y  = subst′ ⊢V (swap x≢y ⊢N)

preserve : ∀ {M N A}
 → ∅ ⊢ M ∶ A
 → M —→ N
 -------------
 → ∅ ⊢ N ∶ A
preserve (⊢L · ⊢M)        (ξ-·₁ L—→L′) = (preserve ⊢L L—→L′) · ⊢M
preserve (⊢L · ⊢M)        (ξ-·₂ VM M—→M′) = ⊢L · (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) · ⊢V)   (β-ƛ VM) = subst ⊢V ⊢N
preserve (⊢suc ⊢M)        (ξ-suc M—→M′) = ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N) (ξ-case L—→L′) = ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢L ⊢M ⊢N) (β-zero) = ⊢M
preserve (⊢case (⊢suc ⊢L) ⊢M ⊢N) (β-suc VV) = subst ⊢L ⊢N
preserve (⊢μ ⊢M) β-μ = subst (⊢μ ⊢M) ⊢M

record Gas : Set where
  constructor gas
  field
    amount : ℕ


data Finished (ℕ : Term) : Set where

  done :
    Value ℕ
    ---------
    → Finished ℕ

  out-of-gas :
    -------------
    Finished ℕ

data Steps (L : Term) : Set where

  steps : ∀ {N}
    → L —↠ N
    → Finished N
  --------------
    → Steps L

eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ∶ A
  -----------
  → Steps L
eval {L} (gas zero) ⊢L = steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL = steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) (preserve ⊢L L—→M)
...   | steps M—↠N fin = steps ( L —→⟨ L—→M ⟩ M—↠N) fin

⊢sucμ : ∅ ⊢ μ "x" ⇒ ‵suc ‵ "x" ∶ ‵ℕ
⊢sucμ = ⊢μ (⊢suc (⊢‵ ∋x))
  where
    ∋x = Z


Normal : Term → Set
Normal M = ∀ {N} → ¬ (M —→ N)

Stuck : Term → Set
Stuck M = Normal M × ¬ Value M

unstuck : ∀ {M A}
  → ∅ ⊢ M ∶ A
  -----------
  → ¬ (Stuck M)
unstuck ⊢M with progress ⊢M
... | step M—→N = λ (⟨ ¬M—→N , ¬VM ⟩) → ¬M—→N M—→N
... | done VM   = λ (⟨ ¬M—→N , ¬VM ⟩) → ¬VM VM


preserves : ∀ {M N A}
  → ∅ ⊢ M ∶ A
  → M —↠ N
   ----------
  → ∅ ⊢ N ∶ A
preserves ⊢M (_ ∎) = ⊢M
preserves ⊢L (_ —→⟨ L—→M ⟩ M—↠N) = preserves (preserve ⊢L L—→M) M—↠N

wttdgs : ∀ {M N A}
  → ∅ ⊢ M ∶ A
  → M —↠ N
  -----------
  → ¬ (Stuck N)
wttdgs ⊢M M—↠N = unstuck (preserves ⊢M M—↠N)

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl

det : ∀ {M M′ M″}
  → M —→ M′
  → M —→ M″
  ---------
  → M′ ≡ M″
det (ξ-·₁ L—→L′) (ξ-·₁ L—→L″) = cong₂ _·_ (det L—→L′ L—→L″) refl
det (ξ-·₁ M—→M′) (ξ-·₂ VL M—→M″) = ⊥-elim (V¬→ VL M—→M′)
det (ξ-·₂ VL M—→M′) (ξ-·₁ M—→M″) = ⊥-elim (V¬→ VL M—→M″)
det (ξ-·₂ VL M—→M′) (ξ-·₂ x M—→M″) = cong₂ _·_ refl (det M—→M′ M—→M″)
det (ξ-·₂ VL M—→M′) (β-ƛ x) = ⊥-elim (V¬→ x M—→M′)
det (β-ƛ x) (ξ-·₂ x₁ M—→M″) = ⊥-elim (V¬→ x M—→M″)
det (β-ƛ x) (β-ƛ x₁) = refl
det (ξ-suc M—→M′) (ξ-suc M—→M″) = cong ‵suc_ (det M—→M′ M—→M″)
det (ξ-case M—→M′) (ξ-case M—→M″) = cong₄ case_[zero⇒_|suc_⇒_] (det M—→M′ M—→M″) refl refl refl
det (ξ-case M—→M′) (β-suc x) = ⊥-elim (V¬→ (V-suc x) M—→M′)
det β-zero β-zero = refl
det (β-suc x) (ξ-case M—→M″) = ⊥-elim (V¬→ (V-suc x) M—→M″)
det (β-suc x) (β-suc x₁) = refl
det β-μ β-μ = refl
  
