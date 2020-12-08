module plfa.part2.Lambda where

open import Relation.Binary.PropositionalEquality using(_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])

Id : Set
Id = String

infix 5 ƛ_⇒_
infix 5 μ_⇒_
infixl 7 _·_
infix 8 ‵suc_
infix 9 ‵_

data Term : Set where
  ‵_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _·_                  : Term → Term → Term
  ‵zero                : Term
  ‵suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term

two : Term
two = ‵suc ‵suc ‵zero

plus : Term
plus = μ "+" ⇒
    ƛ "m"
  ⇒ ƛ "n"
  ⇒ case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n") ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ‵ "s" · (‵ "s" · ‵ "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ‵ "m" · (‵ "s" · (‵ "n" · (‵ "s" · ‵ "z")))

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ ‵suc (‵ "n")

mul : Term
mul = μ "*" ⇒ (ƛ "m" ⇒ ƛ "n" ⇒
              case ‵ "m" [zero⇒ ‵zero
              |suc "m" ⇒ plus · ‵ "n" · (‵ "*" · ‵ "m" · ‵ "n")])

four : Term
four = mul · (two · two)

ƛ′_⇒_ : Term → Term → Term
ƛ′ (‵ x) ⇒ N = ƛ x ⇒ N
ƛ′ _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (‵ x) ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ] = ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (‵ x) ⇒ N = μ x ⇒ N
μ′ _ ⇒ _     = ⊥-elim impossible
  where postulate impossible : ⊥

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
  case′ m
    [zero⇒ n
    |suc m ⇒ ‵suc (+ · (m · n)) ]
  where
  + = ‵ "+"
  m = ‵ "m"
  n = ‵ "n"

mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
  case′ m
    [zero⇒ ‵zero
    |suc m ⇒  plus′ · ((* · (m · n)) · n) ]
  where
    *  = ‵ "*"
    m  = ‵ "m"
    n  = ‵ "n"

data Value : Term → Set where
  V-ƛ : ∀ {x N}
  --------------
    → Value (ƛ x ⇒ N)

  V-zero :
    ----------
    Value ‵zero

  V-suc : ∀ {V}
    → Value V
    ----------
    → Value (‵suc V)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(‵ x) [ y := V ] with x ≟ y
... | yes _    = V
... | no  _    = ‵ x 
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _    = ƛ x ⇒ N
... | no  _    = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ] = (L [ y := V ]) · (M [ y := V ])
‵zero [ y := V ] = ‵zero
(‵suc M) [ y := V ] = ‵suc (M [ y := V ])
case L [zero⇒ M |suc x ⇒ N ] [ y := V ] with x ≟ y
... | yes _    = case L [ y := V ] [zero⇒  M [ y := V ] |suc x ⇒ N ]
... | no  _    = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _    = μ x ⇒ N
... | no  _    = μ x ⇒ N [ y := V ]

_ : (ƛ "z" ⇒ ‵ "s" · (‵ "s" · ‵ "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ‵ "z")
_ = refl

_ : (ƛ "y" ⇒ ‵ "x" · (ƛ "x" ⇒ ‵ "x")) [ "x" := ‵zero ] ≡ (ƛ "y" ⇒ ‵zero · (ƛ "x" ⇒ ‵ "x"))
_ = refl

[_≣_]_↔_ : Id → Id → Term → Term → Term

_[_:=_]′ : Term → Id → Term → Term
(‵ x) [ y := V ]′ with x ≟ y
... | yes _  = V
... | no  _  = ‵ x
(ƛ x ⇒ M) [ y := V ]′                      = ƛ x ⇒ [ x ≣ y ] V ↔ M
(M · L) [ y := V ]′                        = (M [ y := V ]′) · (L [ y := V ]′)
‵zero [ y := V ]′                          = ‵zero
(‵suc M) [ y := V ]′                       = ‵suc (M [ y := V ]′)
(μ x ⇒ M) [ y := V ]′                      = μ x ⇒ [ x ≣ y ] V ↔ M
case L [zero⇒ M |suc x ⇒ N ] [ y := V ]′   = case (L [ y := V ]′)
                                             [zero⇒ (M [ y := V ]′)
                                             |suc x ⇒ [ x ≣ y ] V ↔ N ]


[ x ≣ y ] V ↔ M  with x ≟ y
... | yes _ = M
... | no  _ = M [ y := V ]′

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
    ---------------
    → L · M —→ L′ · M 

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
    ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
    -------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
    ---------
    → ‵suc M —→ ‵suc M′
  
  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
    ----------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
  -----------------------------------------
    → case ‵zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
    ------------------
    → case ‵suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
    -------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

_ : (ƛ "x" ⇒ ‵ "x") · (ƛ "x" ⇒ ‵ "x") —→ (ƛ "x" ⇒ ‵ "x")
_ = β-ƛ V-ƛ

_ : (ƛ "x" ⇒ ‵ "x") · ((ƛ "x" ⇒ ‵ "x") · (ƛ "x" ⇒ ‵ "x")) —→ (ƛ "x" ⇒ ‵ "x") · (ƛ "x" ⇒ ‵ "x")
_ = ξ-·₂ V-ƛ (β-ƛ V-ƛ)

--(β-ƛ V-ƛ)

_ : (twoᶜ · sucᶜ) · ‵zero —→ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ‵ "z")) · ‵zero
_ = ξ-·₁ (β-ƛ V-ƛ) 

infix 2 _—↠_
infix 1 begin_
infixr 2 _—→⟨_⟩_
infix 3 _∎

data _—↠_ : Term → Term → Set where

  _∎ : ∀ M
  ------------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
    ----------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M–↠N = M–↠N

data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N

open import plfa.Isomorphism using (_≲_;_≃_)

private —↠-trans : ∀ {L M N} → L —↠ M → M —↠ N → L —↠ N
        —↠-trans (_ ∎) L—↠N = L—↠N
        —↠-trans (L —→⟨ L—→M₁ ⟩ L—↠M) M—↠N = L —→⟨ L—→M₁ ⟩ —↠-trans L—↠M M—↠N

—↠≲—↠′ : ∀ {M N} → (M —↠ N) ≲ (M —↠′ N)
—↠≲—↠′ {M} {N} =
  record
  { to      = to′ 
  ; from    = from′
  ; from∘to = from∘to′ 
  }
  where
    to′ : ∀ {M N} → (M —↠ N) → (M —↠′ N)
    to′ (_ ∎) = refl′
    to′ (m —→⟨ x ⟩ M—↠N) = trans′ (step′ x) (to′ M—↠N)
    from′ : ∀ {M N} → (M —↠′ N) → (M —↠ N)
    from′ {M₁} {N₁} (step′ x) = M₁ —→⟨ x ⟩ N₁ ∎
    from′ {M₁} refl′ = M₁ ∎
    from′ (trans′ {L} {M} {N} L—↠′M M—↠′N) = —↠-trans (from′ L—↠′M) (from′ M—↠′N)
    from∘to′ : ∀ {M N} → (M—↠N : M —↠ N) → from′ (to′ (M—↠N)) ≡ M—↠N
    from∘to′ (_ ∎) = refl
    from∘to′ (L —→⟨ L—→M₁ ⟩ M—↠N) rewrite from∘to′ M—↠N = refl

one : Term
one = ‵suc ‵zero

_ : (plus · one) · one —↠ two
_ = begin 
          plus · one · one
    —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒
        ‵suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
            ])))
         · ‵ "m"
         · ‵ "n")
        ])) · one · one
       —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
         (ƛ "n" ⇒
       case one [zero⇒ ‵ "n" |suc "m" ⇒
       ‵suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
           ])))
        · ‵ "m"
        · ‵ "n")
       ])· one
       —→⟨ β-ƛ (V-suc V-zero)⟩
         case ‵suc ‵zero [zero⇒ one |suc "m" ⇒
      ‵suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
          ]))) · ‵ "m" · one)]
      —→⟨ β-suc V-zero ⟩ 
        ‵suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
          ]))) · ‵zero · ‵suc ‵zero)
      —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩ 
      ‵suc
      ((ƛ "m" ⇒
        (ƛ "n" ⇒
         case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒
         ‵suc
         ((μ "+" ⇒
           (ƛ "m" ⇒
            (ƛ "n" ⇒
             case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
             ])))
          · ‵ "m"
          · ‵ "n")])) · ‵zero · ‵suc ‵zero)
      —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩ 
        ‵suc
      ((ƛ "n" ⇒
        case ‵zero [zero⇒ ‵ "n" |suc "m" ⇒
        ‵suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
            ])))
         · ‵ "m"
         · ‵ "n")]) · ‵suc ‵zero)
      —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩ 
        ‵suc
      case ‵zero [zero⇒ ‵suc ‵zero |suc "m" ⇒
      ‵suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
          ]))) · ‵ "m" · ‵suc ‵zero)]
      —→⟨ ξ-suc β-zero ⟩ 
        ‵suc (‵suc ‵zero) ∎

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  ‵ℕ  : Type

infixl 5 _,_∶_

data Context : Set where
  ∅     : Context
  _,_∶_ : Context → Id → Type → Context

open import Data.Product using (_×_;_,_)

Context-≅ : Context ≃ List (Id × Type)
Context-≅ = record
  { to      = to
  ; from    = from
  ; from∘to = from∘to
  ; to∘from = to∘from }
  where
    to : Context → List (Id × Type)
    to ∅ = []
    to (ctx , x ∶ ty) =  (x , ty) ∷ (to ctx)
    from : List (Id × Type) → Context
    from [] = ∅
    from ((x , ty) ∷ lst) = (from lst) , x ∶ ty
    from∘to : (x : Context) → from (to x) ≡ x
    from∘to ∅ = refl
    from∘to (ctx , x ∶ ty) rewrite from∘to ctx = refl
    to∘from : (y : List (Id × Type)) → to (from y) ≡ y
    to∘from [] = refl
    to∘from (x ∷ lst) rewrite to∘from lst = refl

infix 4 _∋_∶_

data _∋_∶_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
    -------------------
    → Γ , x ∶ A ∋ x ∶ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ∶ A
    -------------------
    → Γ , y ∶ B ∋ x ∶ A

infix 4 _⊢_∶_

data _⊢_∶_ : Context → Term → Type → Set where

  -- Axiom
  ⊢‵ : ∀ {Γ x A}
    → Γ ∋ x ∶ A
    -------------
    → Γ ⊢ ‵ x ∶ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ∶ A ⊢ N ∶ B
      ------------------
    → Γ ⊢ ƛ x ⇒ N ∶ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ∶ A ⇒ B
    → Γ ⊢ M ∶ A
    ----------------
    → Γ ⊢ L · M ∶ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
    -------------------
      → Γ ⊢ ‵zero ∶ ‵ℕ

  -- ℕ-I₁
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ∶ ‵ℕ
    -------------
    → Γ ⊢ ‵suc M ∶ ‵ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ∶ ‵ℕ
    → Γ ⊢ M ∶ A
    → Γ , x ∶ ‵ℕ ⊢ N ∶ A
    ---------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ∶ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ∶ A ⊢ M ∶ A
      ------------------
    → Γ ⊢ μ x ⇒ M ∶ A

⊢two : ∀ {Γ} → Γ ⊢ two ∶ ‵ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ∶ ‵ℕ ⇒ ‵ℕ ⇒ ‵ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢‵ ∋m) (⊢‵ ∋n)
        (⊢suc (⊢‵ ∋+ · ⊢‵ ∋m′ · ⊢‵ ∋n′)))))
  where
  ∋+  = (S (λ ()) (S (λ()) (S (λ()) Z)))
  ∋m  = (S (λ ()) Z)
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = (S (λ()) Z)

⊢2+2 : ∅ ⊢ plus · two · two ∶ ‵ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two

∋-injective : ∀ {Γ x A B} → Γ ∋ x ∶ A → Γ ∋ x ∶ B → A ≡ B
∋-injective Z Z = refl
∋-injective Z (S x≢ _) = ⊥-elim (x≢ refl)
∋-injective (S x≢ _) Z = ⊥-elim (x≢ refl)
∋-injective (S _ a) (S _ b) = ∋-injective a b

_ : ∅ , "y" ∶ ‵ℕ ⇒ ‵ℕ , "x" ∶ ‵ℕ ⊢ ‵ "y" · ‵ "x" ∶ ‵ℕ
_ = (⊢‵ (S (λ ()) Z)) · ⊢‵ Z

⊢mul : ∀ {Γ} → Γ ⊢ mul ∶ ‵ℕ ⇒ ‵ℕ ⇒ ‵ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢‵ ∋m) ⊢zero
  ((⊢plus · ⊢‵ ∋n) · (⊢‵ ∋* · ⊢‵ Z · ⊢‵ ∋n′)))))
  where
  ∋m  = S (λ ()) Z
  ∋n  = S (λ ()) Z
  ∋*  = S (λ ()) (S (λ ()) (S (λ ()) Z))
  ∋n′ = S (λ ()) Z  
