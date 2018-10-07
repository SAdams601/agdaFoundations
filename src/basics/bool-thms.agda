module basics.bool-thms where
open import basics.bool

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

~~-elim : ∀ (b : 𝔹) → ~ ~ b ≡ b
~~-elim tt = refl
~~-elim ff = refl

&&-idem : ∀{b} → b && b ≡ b
&&-idem{tt} = refl
&&-idem{ff} = refl

||-idem : ∀{b} → b || b ≡ b
||-idem {tt} = refl
||-idem {ff} = refl

||≡ff₁ : ∀ {b1 b2} → b1 || b2 ≡ ff → b1 ≡ ff
||≡ff₁ {ff} p = refl
||≡ff₁ {tt} ()

||-cong₁ : ∀ {b1 b1' b2} → b1 ≡ b1' → b1 || b2 ≡ b1' || b2
||-cong₁ refl = refl
