module Expless.Model where
open import Expless.Syntax
open import Expless.Syntax.Ren
open import Expless.Syntax.Emb
open import Expless.Semantics.HSub
open import Expless.Semantics.Conv

open import Data.Unit
open import Data.Product

----------------------------------------------------------------------

⟦_⊢_∶ʳ_⟧ : (Γ : Ctx) (A : Type) (a : Wh Γ A) → Set

⟦_⊩_⇒_∶ʳ_⟧ : (Γ : Ctx) (A B : Type) (f : Clos Γ A B) → Set
⟦ Γ ⊩ A ⇒ B ∶ʳ σ `/ b ⟧ = ∀{Δ}
  (Δ≥Γ : Ren Δ Γ)
  (a : Val wh Δ A)
  → ⟦ Δ ⊢ A ∶ʳ a ⟧
  → ∃ λ b'
  → renˢ Δ≥Γ σ , a / b ⇓ b'
  ∧ ⟦ Δ ⊢ B ∶ʳ b' ⟧

⟦ Γ ⊢ `ℕ ∶ʳ `zero ⟧ = ⊤
⟦ Γ ⊢ `ℕ ∶ʳ `suc n ⟧ = ⟦ Γ ⊢ `ℕ ∶ʳ n ⟧
⟦ Γ ⊢ (A `→ B) ∶ʳ `λ f ⟧ = ⟦ Γ ⊩ A ⇒ B ∶ʳ f ⟧
⟦ Γ ⊢ A ∶ʳ `neut a ⟧ = ∃ λ a' → a ≈ᴺ embᴺ a'

Val-Model = ⟦_⊢_∶ʳ_⟧
syntax Val-Model Γ A a = ⟦ Γ ⊢ a ∶ A ⟧

Bind-Model = ⟦_⊩_⇒_∶ʳ_⟧
syntax Bind-Model Γ A B f = ⟦ Γ ⊩ f ∶ A ⇒ B ⟧

----------------------------------------------------------------------

⟦_⊢_∶ʳ_/_∶ʳ_⟧ : (Φ Γ : Ctx) (σ : Env Φ Γ) (A : Type) (a : Wh Γ A) → Set
⟦ Φ ⊢ Γ ∶ʳ σ / A ∶ʳ a ⟧ = ∃ λ a' → σ / a ⇓ a' ∧ ⟦ Φ ⊢ a' ∶ A ⟧

Sub-Model = ⟦_⊢_∶ʳ_/_∶ʳ_⟧
syntax Sub-Model Φ Γ σ A a = ⟦ Φ ⊢ σ ∶ Γ / a ∶ A ⟧

----------------------------------------------------------------------

⟦_⊩_∶ʳ_/_⇒_∶ʳ_⟧ : (Φ Γ : Ctx) (σ : Env Φ Γ) (A B : Type) (a : Bind wh Γ A B) → Set
⟦ Φ ⊩ Γ ∶ʳ σ / A ⇒ B ∶ʳ f ⟧ = ∃ λ f' → σ /ᴷ f ⇓ f' ∧ ⟦ Φ ⊩ f' ∶ A ⇒ B ⟧

BSub-Model = ⟦_⊩_∶ʳ_/_⇒_∶ʳ_⟧
syntax BSub-Model Φ Γ σ A B f = ⟦ Φ ⊩ σ ∶ Γ / f ∶ A ⇒ B ⟧

----------------------------------------------------------------------

data ⟦_⊨_∶ʳ_⟧ (Φ : Ctx) : (Γ : Ctx) (σ : Env Φ Γ) → Set where
  ∅ : ⟦ Φ ⊨ ∅ ∶ʳ ∅ ⟧
  _,_ : ∀{Γ A} {σ : Env Φ Γ} {a : Wh Φ A}
    → ⟦ Φ ⊨ Γ ∶ʳ σ ⟧
    → ⟦ Φ ⊢ a ∶ A ⟧
    → ⟦ Φ ⊨ Γ , A ∶ʳ σ , a ⟧

Env-Model = ⟦_⊨_∶ʳ_⟧
syntax Env-Model Φ Γ σ = ⟦ Φ ⊨ σ ∶ Γ ⟧

----------------------------------------------------------------------
