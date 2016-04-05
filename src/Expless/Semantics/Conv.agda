module Expless.Semantics.Conv where
open import Relation.Binary.PropositionalEquality

open import Expless.Syntax
open import Expless.Syntax.Ren
open import Expless.Semantics.HSub

----------------------------------------------------------------------

data _!_ {Φ A B} : Clos Φ A B → Wh (Φ , A) B → Set where
  `force : ∀{Γ} {σ : Env Φ Γ} {b : Wh (Γ , A) B} {b' : Wh (Φ , A) B}
    → ↑₁ σ / b ⇓ b'
    → (σ `/ b) ! b'

----------------------------------------------------------------------

infix 1 _≈_
infix 1 _≈ᴺ_

data _≈_ {Γ} : ∀{A} (a a' : Wh Γ A) → Set
data _≈ᴺ_ {Γ} : ∀{A} (a a' : Nu Γ A) → Set

data _≈ᴷ_ {Γ} : ∀{A B} (f f' : Clos Γ A B) → Set where
  `conv-clos-eq : ∀{A B}
    {f g : Clos Γ A B}
    → f ≡ g
    → f ≈ᴷ g

  `conv-clos-kappa : ∀{A B}
    {f g : Clos Γ A B}
    {f' g' : Wh (Γ , A) B}
    → f ≢ g
    → f ! f'
    → g ! g'
    → f' ≈ g'
    → f ≈ᴷ g

data _≈_ {Γ} where
  `conv-zero : `zero ≈ `zero
  `conv-suc :
    {n n' : Wh Γ `ℕ}
    → n ≈ n'
    → `suc n ≈ `suc n'

  `conv-lam : ∀{A B}
    {f g : Clos Γ A B}
    → f ≈ᴷ g
    → `λ f ≈ `λ g

  `conv-neut : ∀{A} {a : Nu Γ A} {a' : Nu Γ A}
    → a ≈ᴺ a'
    → `neut a ≈ `neut a'

data _≈ᴺ_ {Γ} where
  `conv-var : ∀{A}
    (i : Var Γ A)
    → `var i ≈ᴺ `var i

  `conv-rec : ∀{C}
    {n : Nu Γ `ℕ}
    {cz : Wh Γ C}
    {cs : Clos Γ C C}
    {n' : Nu Γ `ℕ}
    {cz' : Wh Γ C}
    {cs' : Clos Γ C C}
    → n ≈ᴺ n'
    → cz ≈ cz'
    → cs ≈ᴷ cs'
    → `rec n `of cz `else cs ≈ᴺ `rec n' `of cz' `else cs'

  `conv-app : ∀{A B}
    {f : Nu Γ (A `→ B)}
    {a : Wh Γ A}
    {f' : Nu Γ (A `→ B)}
    {a' : Wh Γ A}
    → f ≈ᴺ f'
    → a ≈ a'
    → f `∙ a ≈ᴺ f' `∙ a'

----------------------------------------------------------------------


