module Expless.Syntax.Ren.Props where
open import Relation.Binary.PropositionalEquality

open import Expless.Syntax
open import Expless.Syntax.Ren

----------------------------------------------------------------------

lookup-renˢ : ∀{Φ Γ Δ A}
  (σ : Env Φ Γ)
  (Δ≥Φ : Ren Δ Φ)
  (i : Var Γ A)
  (a : Wh Φ A)
  → a ≡ lookup σ i
  → ren Δ≥Φ a ≡ lookup (renˢ Δ≥Φ σ) i
lookup-renˢ (σ , a) Δ≥Φ here a' q = cong (ren Δ≥Φ) q
lookup-renˢ (σ , a) Δ≥Φ (there i) a' q = lookup-renˢ σ Δ≥Φ i a' q

----------------------------------------------------------------------

id-renᴿ : ∀{Γ A} (i : Var Γ A) → renᴿ idRen i ≡ i
id-renᴿ here = refl
id-renᴿ (there i) rewrite id-renᴿ i = refl

id-ren : ∀{m Γ A} (a : Val m Γ A) → ren idRen a ≡ a
id-renᴺ : ∀{m Γ A} (a : Neut m Γ A) → renᴺ idRen a ≡ a

id-renˢ : ∀{Φ Γ} (σ : Env Φ Γ) → renˢ idRen σ ≡ σ
id-renˢ ∅ = refl
id-renˢ (σ , a) rewrite id-renˢ σ | id-ren a = refl

id-renᴮ : ∀{m Γ A B} (a : Bind m Γ A B) → renᴮ idRen a ≡ a
id-renᴮ (`val b) rewrite id-ren b = refl
id-renᴮ (σ `/ b) rewrite id-renˢ σ = refl

id-ren `zero = refl
id-ren (`suc n) rewrite id-ren n = refl
id-ren (`λ b) rewrite id-renᴮ b = refl
id-ren (`neut a) rewrite id-renᴺ a = refl

id-renᴺ (`var i) rewrite id-renᴿ i = refl
id-renᴺ (f `∙ a) rewrite id-renᴺ f | id-ren a = refl
id-renᴺ (`rec n `of cz `else cs)
  rewrite id-renᴺ n | id-ren cz | id-renᴮ cs = refl

----------------------------------------------------------------------

id-lookup : ∀{Γ A} (i : Var Γ A) → `neut (`var i) ≡ lookup idEnv i
id-lookup here = refl
id-lookup (there i)
  with lookup-renˢ idEnv wknRen₁ i (`neut (`var i)) (id-lookup i)
... | q rewrite id-renᴿ i = q

----------------------------------------------------------------------
