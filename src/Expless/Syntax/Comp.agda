module Expless.Syntax.Comp where
open import Relation.Binary.PropositionalEquality

open import Expless.Syntax
open import Expless.Syntax.Ren

----------------------------------------------------------------------

comp : ∀{Γ Φ Δ}
  (Δ≥Φ : Ren Δ Φ)
  (Φ≥Γ : Ren Φ Γ)
  → Ren Δ Γ
comp done Φ≥Γ = Φ≥Γ
comp (skip Δ≥Φ) Φ≥Γ = skip (comp Δ≥Φ Φ≥Γ)
comp (keep Δ≥Φ) (skip Φ≥Γ) = skip (comp Δ≥Φ Φ≥Γ)
comp (keep Δ≥Φ) (keep Φ≥Γ) = keep (comp Δ≥Φ Φ≥Γ)

comp-renᴿ : ∀{Γ Φ Δ A}
  (Δ≥Φ : Ren Δ Φ)
  (Φ≥Γ : Ren Φ Γ)
  (i : Var Γ A)
  → renᴿ Δ≥Φ (renᴿ Φ≥Γ i) ≡ renᴿ (comp Δ≥Φ Φ≥Γ) i
comp-renᴿ done done ()
comp-renᴿ (skip Δ≥Φ) Φ≥Γ i = cong there (comp-renᴿ Δ≥Φ Φ≥Γ i)
comp-renᴿ (keep Δ≥Φ) (skip Φ≥Γ) i = comp-renᴿ (skip Δ≥Φ) Φ≥Γ i
comp-renᴿ (keep Δ≥Φ) (keep Φ≥Γ) here = refl
comp-renᴿ (keep Δ≥Φ) (keep Φ≥Γ) (there i) = comp-renᴿ (skip Δ≥Φ) Φ≥Γ i

----------------------------------------------------------------------
