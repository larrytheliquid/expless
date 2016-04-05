module Expless.Syntax.Comp.Props where
open import Relation.Binary.PropositionalEquality

open import Expless.Syntax
open import Expless.Syntax.Ren
open import Expless.Syntax.Comp

----------------------------------------------------------------------

comp-ren : ∀{Γ Φ Δ A}
  (Δ≥Φ : Ren Δ Φ)
  (Φ≥Γ : Ren Φ Γ)
  (a : Wh Γ A)
  → ren Δ≥Φ (ren Φ≥Γ a) ≡ ren (comp Δ≥Φ Φ≥Γ) a

comp-renᴺ : ∀{Γ Φ Δ A}
  (Δ≥Φ : Ren Δ Φ)
  (Φ≥Γ : Ren Φ Γ)
  (a : Nu Γ A)
  → renᴺ Δ≥Φ (renᴺ Φ≥Γ a) ≡ renᴺ (comp Δ≥Φ Φ≥Γ) a

comp-renˢ : ∀{Γ Φ Δ Ω}
  (Ω≥Δ : Ren Ω Δ)
  (Δ≥Φ : Ren Δ Φ)
  (σ : Env Φ Γ)
  → renˢ Ω≥Δ (renˢ Δ≥Φ σ) ≡ renˢ (comp Ω≥Δ Δ≥Φ) σ
comp-renˢ Δ≥Φ Φ≥Γ ∅ = refl
comp-renˢ Δ≥Φ Φ≥Γ (σ , a)
  rewrite comp-renˢ Δ≥Φ Φ≥Γ σ | comp-ren Δ≥Φ Φ≥Γ a = refl

comp-renᴷ : ∀{Γ Φ Δ A B}
  (Δ≥Φ : Ren Δ Φ)
  (Φ≥Γ : Ren Φ Γ)
  (k : Clos Γ A B)
  → renᴮ Δ≥Φ (renᴮ Φ≥Γ k) ≡ renᴮ (comp Δ≥Φ Φ≥Γ) k
comp-renᴷ Δ≥Φ Φ≥Γ (σ `/ b) rewrite comp-renˢ Δ≥Φ Φ≥Γ σ = refl

comp-ren Δ≥Φ Φ≥Γ `zero = refl
comp-ren Δ≥Φ Φ≥Γ (`suc n) rewrite comp-ren Δ≥Φ Φ≥Γ n = refl
comp-ren Δ≥Φ Φ≥Γ (`λ b) rewrite comp-renᴷ Δ≥Φ Φ≥Γ b = refl
comp-ren Δ≥Φ Φ≥Γ (`neut a) rewrite comp-renᴺ Δ≥Φ Φ≥Γ a = refl

comp-renᴺ Δ≥Φ Φ≥Γ (`var i) rewrite comp-renᴿ Δ≥Φ Φ≥Γ i = refl
comp-renᴺ Δ≥Φ Φ≥Γ (f `∙ a)
  rewrite comp-renᴺ Δ≥Φ Φ≥Γ f | comp-ren Δ≥Φ Φ≥Γ a = refl
comp-renᴺ Δ≥Φ Φ≥Γ (`rec n `of cz `else cs)
  rewrite comp-renᴺ Δ≥Φ Φ≥Γ n | comp-ren Δ≥Φ Φ≥Γ cz | comp-renᴷ Δ≥Φ Φ≥Γ cs = refl

----------------------------------------------------------------------

comp-id : ∀{Φ Γ} (Φ≥Γ : Ren Φ Γ)
  → comp idRen Φ≥Γ ≡ comp Φ≥Γ idRen
comp-id done = refl
comp-id (skip x) = cong skip (comp-id x)
comp-id (keep x) = cong keep (comp-id x)

----------------------------------------------------------------------

renˢ-comp : ∀{Δ Φ Γ} B (σ : Env Φ Γ) (Δ≥Φ : Ren Δ Φ)
  → renˢ (skip {A = B} idRen) (renˢ Δ≥Φ σ) ≡ renˢ (keep Δ≥Φ) (renˢ (skip idRen) σ)
renˢ-comp B σ Δ≥Φ
  rewrite comp-renˢ (wknRen₁ {A = B}) Δ≥Φ σ | comp-renˢ (keep Δ≥Φ) (wknRen₁ {A = B}) σ | comp-id Δ≥Φ
  = refl

----------------------------------------------------------------------
