module Expless.Semantics.HSub where
open import Expless.Syntax

----------------------------------------------------------------------

infix 1 _/_⇓_
infix 1 _/ᴺ_⇓_
infix 1 _∘_⇓_

data _/_⇓_ {Φ Γ} (σ : Env Φ Γ) : ∀{A} → Wh Γ A → Wh Φ A → Set
data _/ᴺ_⇓_ {Φ Γ} (σ : Env Φ Γ) : ∀{A} → Nu Γ A → Wh Φ A → Set

data _∘_⇓_ {Φ Δ} (σ : Env Φ Δ) : ∀{Γ} → Env Δ Γ → Env Φ Γ → Set where
  `comp-emp : σ ∘ ∅ ⇓ ∅

  `comp-ext : ∀{Γ A} {ρ : Env Δ Γ} {a : Wh Δ A} {a' : Wh Φ A} {ρ' : Env Φ Γ}
    → σ ∘ ρ ⇓ ρ'
    → σ / a ⇓ a'
    → σ ∘ ρ , a ⇓ ρ' , a'

data _∙ᴷ_⇓_ {Γ A B} : Clos Γ A B → Wh Γ A → Wh Γ B → Set where
  `app-clos : ∀{Δ}
    {b : Wh (Δ , A) B}
    {σ : Env Γ Δ}
    {a : Wh Γ A}
    {b' : Wh Γ B}
    → σ , a / b ⇓ b'
    → (σ `/ b) ∙ᴷ a ⇓ b'

data _∙_⇓_ {Γ A B} : Wh Γ (A `→ B) → Wh Γ A → Wh Γ B → Set where
  `app-lam :
    {f : Clos Γ A B}
    {a : Wh Γ A}
    {b : Wh Γ B}
    → f ∙ᴷ a ⇓ b
    → `λ f ∙ a ⇓ b

  `app-neut :
    {f : Nu Γ (A `→ B)}
    {a : Wh Γ A}
    → `neut f ∙ a ⇓ `neut (f `∙ a)

data rec_of_else_⇓_ {Γ C} : Wh Γ `ℕ → Wh Γ C → Clos Γ C C → Wh Γ C → Set where
  `rec-zero :
    {cz : Wh Γ C}
    {cs : Clos Γ C C}
    → rec `zero of cz else cs ⇓ cz

  `rec-suc :
    {n : Wh Γ `ℕ}
    {cz : Wh Γ C}
    {cs : Clos Γ C C}
    {c c' : Wh Γ C}
    → rec n of cz else cs ⇓ c
    → cs ∙ᴷ c ⇓ c'
    → rec `suc n of cz else cs ⇓ c'

  `rec-neut :
    {n : Nu Γ `ℕ}
    {cz : Wh Γ C}
    {cs : Clos Γ C C}
    → rec `neut n of cz else cs ⇓ `neut (`rec n `of cz `else cs)

data _/ᴷ_⇓_ {Φ Γ} (σ : Env Φ Γ) : ∀{A B} → Clos Γ A B → Clos Φ A B → Set where
  `sub-clos : ∀{A B Δ}
    {f : Wh (Δ , A) B}
    {ρ : Env Γ Δ}
    {ρ' : Env Φ Δ}
    → σ ∘ ρ ⇓ ρ'
    → σ /ᴷ (ρ `/ f) ⇓ (ρ' `/ f)

----------------------------------------------------------------------

data _/_⇓_ {Φ Γ} σ where
  `sub-zero : σ / `zero ⇓ `zero
  `sub-suc :
    {n : Wh Γ `ℕ}
    {n' : Wh Φ `ℕ}
    → σ / n ⇓ n'
    → σ / `suc n ⇓ `suc n'

  `sub-lam : ∀{A B}
    {f : Clos Γ A B}
    {f' : Clos Φ A B}
    → σ /ᴷ f ⇓ f'
    → σ / `λ f ⇓ `λ f'

  `sub-neut : ∀{B}
    {n : Nu Γ B}
    {n' : Wh Φ B}
    (pn : σ /ᴺ n ⇓ n')
    → σ / `neut n ⇓ n'

----------------------------------------------------------------------

data _/ᴺ_⇓_ {Φ Γ} σ where
  `sub-var : ∀{A}
    (i : Var Γ A)
    → σ /ᴺ `var i ⇓ lookup σ i

  `sub-rec : ∀{C}
    {n : Nu Γ `ℕ}
    {cz : Wh Γ C}
    {cs : Clos Γ C C}
    {n' : Wh Φ `ℕ}
    {cz' : Wh Φ C}
    {cs' : Clos Φ C C}
    {c : Wh Φ C}
    → σ /ᴺ n ⇓ n'
    → σ / cz ⇓ cz'
    → σ /ᴷ cs ⇓ cs'
    → rec n' of cz' else cs'  ⇓ c
    → σ /ᴺ `rec n `of cz `else cs ⇓ c

  `sub-app : ∀{A B}
    {f : Nu Γ (A `→ B)}
    {a : Wh Γ A}
    {f' : Wh Φ (A `→ B)}
    {a' : Wh Φ A}
    {b' : Wh Φ B}
    → σ /ᴺ f ⇓ f'
    → σ / a ⇓ a'
    → f' ∙ a' ⇓ b'
    → σ /ᴺ f `∙ a ⇓ b'

----------------------------------------------------------------------

