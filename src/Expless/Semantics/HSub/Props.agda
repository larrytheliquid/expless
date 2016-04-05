module Expless.Semantics.HSub.Props where
open import Relation.Binary.PropositionalEquality

open import Expless.Syntax
open import Expless.Syntax.Ren
open import Expless.Semantics.HSub

open import Expless.Syntax.Ren.Props using ( lookup-renˢ ; id-lookup )

----------------------------------------------------------------------

ren-hsub : ∀{Φ Δ Γ A} {a : Wh Γ A} {a' : Wh Φ A} {σ : Env Φ Γ}
  (Δ≥Φ : Ren Δ Φ) → σ / a ⇓ a' → renˢ Δ≥Φ σ / a ⇓ ren Δ≥Φ a'
renᴺ-hsub : ∀{Φ Δ Γ A} {a : Nu Γ A} {a' : Wh Φ A} {σ : Env Φ Γ}
  (Δ≥Φ : Ren Δ Φ) → σ /ᴺ a ⇓ a' → renˢ Δ≥Φ σ /ᴺ a ⇓ ren Δ≥Φ a'

renˢ-hsub : ∀{Φ Ψ Γ Δ} {ρ : Env Ψ Γ} {ρ' : Env Φ Γ} {σ : Env Φ Ψ}
  (Δ≥Φ : Ren Δ Φ) → σ ∘ ρ ⇓ ρ' → renˢ Δ≥Φ σ ∘ ρ ⇓ renˢ Δ≥Φ ρ'
renˢ-hsub Δ≥Φ `comp-emp = `comp-emp
renˢ-hsub Δ≥Φ (`comp-ext ρ⇓ρ' a⇓a') = `comp-ext (renˢ-hsub Δ≥Φ ρ⇓ρ') (ren-hsub Δ≥Φ a⇓a')

renᴷ-hsub : ∀{Φ Δ Γ A B} {k : Clos Γ A B} {k' : Clos Φ A B} {σ : Env Φ Γ}
  (Δ≥Φ : Ren Δ Φ) → σ /ᴷ k ⇓ k' → renˢ Δ≥Φ σ /ᴷ k ⇓ renᴮ Δ≥Φ k'
renᴷ-hsub Δ≥Φ (`sub-clos ρ⇓ρ') = `sub-clos (renˢ-hsub Δ≥Φ ρ⇓ρ')

ren-appᴷ : ∀{Δ Γ A B} {f : Clos Γ A B} {a : Wh Γ A} {b : Wh Γ B}
  (Δ≥Γ : Ren Δ Γ) → f ∙ᴷ a ⇓ b → renᴮ Δ≥Γ f ∙ᴷ ren Δ≥Γ a ⇓ ren Δ≥Γ b
ren-appᴷ Δ≥Γ (`app-clos b⇓b') = `app-clos (ren-hsub Δ≥Γ b⇓b')

ren-app : ∀{Δ Γ A B} {f : Wh Γ (A `→ B)} {a : Wh Γ A} {b : Wh Γ B}
  (Δ≥Γ : Ren Δ Γ) → f ∙ a ⇓ b → ren Δ≥Γ f ∙ ren Δ≥Γ a ⇓ ren Δ≥Γ b
ren-app Δ≥Γ (`app-lam k⇓k') = `app-lam (ren-appᴷ Δ≥Γ k⇓k')
ren-app Δ≥Γ `app-neut = `app-neut

ren-rec : ∀{Δ Γ C} {n : Wh Γ `ℕ} {cz : Wh Γ C} {cs : Clos Γ C C} {c : Wh Γ C}
  (Δ≥Γ : Ren Δ Γ) → rec n of cz else cs ⇓ c → rec (ren Δ≥Γ n) of (ren Δ≥Γ cz) else (renᴮ Δ≥Γ cs) ⇓ ren Δ≥Γ c
ren-rec Δ≥Γ `rec-zero = `rec-zero
ren-rec Δ≥Γ (`rec-suc c⇓c' cs⇓cs') = `rec-suc (ren-rec Δ≥Γ c⇓c') (ren-appᴷ Δ≥Γ cs⇓cs')
ren-rec Δ≥Γ `rec-neut = `rec-neut

----------------------------------------------------------------------

ren-hsub Δ≥Φ `sub-zero = `sub-zero
ren-hsub Δ≥Φ (`sub-suc n⇓n') = `sub-suc (ren-hsub Δ≥Φ n⇓n')
ren-hsub Δ≥Φ (`sub-lam k⇓k') = `sub-lam (renᴷ-hsub Δ≥Φ k⇓k')
ren-hsub Δ≥Φ (`sub-neut a⇓a') = `sub-neut (renᴺ-hsub Δ≥Φ a⇓a')

renᴺ-hsub {σ = σ} Δ≥Φ (`sub-var i)
  rewrite lookup-renˢ σ Δ≥Φ i (lookup σ i) refl = `sub-var i
renᴺ-hsub Δ≥Φ (`sub-app f⇓f' a⇓a' b⇓b' )
  = `sub-app (renᴺ-hsub Δ≥Φ f⇓f') (ren-hsub Δ≥Φ a⇓a') (ren-app Δ≥Φ b⇓b')
renᴺ-hsub Δ≥Φ (`sub-rec n⇓n' cz⇓cz' cs⇓cs' c⇓c')
  = `sub-rec (renᴺ-hsub Δ≥Φ n⇓n') (ren-hsub Δ≥Φ cz⇓cz') (renᴷ-hsub Δ≥Φ cs⇓cs') (ren-rec Δ≥Φ  c⇓c')

----------------------------------------------------------------------

hsub-id : ∀{Γ A} (a : Wh Γ A) → idEnv / a ⇓ a
hsub-idᴺ : ∀{Γ A} (a : Nu Γ A) → idEnv /ᴺ a ⇓ `neut a

hsub-comp : ∀{Φ Γ} (σ : Env Φ Γ) → idEnv ∘ σ ⇓ σ
hsub-comp ∅ = `comp-emp
hsub-comp (σ , a) = `comp-ext (hsub-comp σ) (hsub-id a)

hsub-idᴷ : ∀{Γ A B} (k : Clos Γ A B) → idEnv /ᴷ k ⇓ k
hsub-idᴷ (σ `/ b) = `sub-clos (hsub-comp σ)

hsub-id `zero = `sub-zero
hsub-id (`suc n) = `sub-suc (hsub-id n)
hsub-id (`λ k) = `sub-lam (hsub-idᴷ k)
hsub-id (`neut a) = `sub-neut (hsub-idᴺ a)

hsub-idᴺ (`var i) rewrite id-lookup i = `sub-var i
hsub-idᴺ (f `∙ a) = `sub-app (hsub-idᴺ f) (hsub-id a) `app-neut
hsub-idᴺ (`rec b `of cz `else cs) = `sub-rec (hsub-idᴺ b) (hsub-id cz) (hsub-idᴷ cs) `rec-neut

----------------------------------------------------------------------

hsub-det : ∀{Φ Γ A}
  {σ : Env Φ Γ}
  {x : Wh Γ A}
  {y z : Wh Φ A}
  → σ / x ⇓ y
  → σ / x ⇓ z
  → y ≡ z

hsub-detᴺ : ∀{Φ Γ A}
  {σ : Env Φ Γ}
  {x : Nu Γ A}
  {y z : Wh Φ A}
  → σ /ᴺ x ⇓ y
  → σ /ᴺ x ⇓ z
  → y ≡ z

comp-det : ∀{Φ Δ Γ}
  {σ : Env Φ Δ}
  {ρ : Env Δ Γ}
  {ρ₁ ρ₂ : Env Φ Γ}
  → σ ∘ ρ ⇓ ρ₁
  → σ ∘ ρ ⇓ ρ₂
  → ρ₁ ≡ ρ₂
comp-det `comp-emp `comp-emp = refl
comp-det (`comp-ext ρ⇓ρ₁ a⇓a₁) (`comp-ext ρ⇓ρ₂ a⇓a₂)
  rewrite comp-det ρ⇓ρ₁ ρ⇓ρ₂ | hsub-det a⇓a₁ a⇓a₂
  = refl

hsub-detᴷ : ∀{Φ Γ A B}
  {σ : Env Φ Γ}
  {x : Clos Γ A B}
  {y z : Clos Φ A B}
  → σ /ᴷ x ⇓ y
  → σ /ᴷ x ⇓ z
  → y ≡ z
hsub-detᴷ (`sub-clos ρ⇓ρ₁) (`sub-clos ρ⇓ρ₂)
  rewrite comp-det ρ⇓ρ₁ ρ⇓ρ₂ = refl

app-detᴷ : ∀{Γ A B}
  {f : Clos Γ A B}
  {a : Wh Γ A}
  {b₁ b₂ : Wh Γ B}
  → f ∙ᴷ a ⇓ b₁
  → f ∙ᴷ a ⇓ b₂
  → b₁ ≡ b₂
app-detᴷ (`app-clos b⇓b₁) (`app-clos b⇓b₂)
  rewrite hsub-det b⇓b₁ b⇓b₂ = refl

app-det : ∀{Γ A B}
  {f : Wh Γ (A `→ B)}
  {a : Wh Γ A}
  {b₁ b₂ : Wh Γ B}
  → f ∙ a ⇓ b₁
  → f ∙ a ⇓ b₂
  → b₁ ≡ b₂
app-det (`app-lam b⇓b₁) (`app-lam b⇓b₂)
  rewrite app-detᴷ b⇓b₁ b⇓b₂ = refl
app-det `app-neut `app-neut = refl

rec-det : ∀{Γ C}
  {n : Wh Γ `ℕ}
  {cz : Wh Γ C}
  {cs : Clos Γ C C}
  {c₁ c₂ : Wh Γ C}
  → rec n of cz else cs ⇓ c₁
  → rec n of cz else cs ⇓ c₂
  → c₁ ≡ c₂
rec-det `rec-zero `rec-zero = refl
rec-det (`rec-suc c⇓c₁ cs⇓cs₁) (`rec-suc c⇓c₂ cs⇓cs₂)
  rewrite rec-det c⇓c₁ c⇓c₂ | app-detᴷ cs⇓cs₁ cs⇓cs₂
  = refl
rec-det `rec-neut `rec-neut = refl


hsub-det `sub-zero `sub-zero = refl
hsub-det (`sub-suc n⇓n₁) (`sub-suc n⇓n₂)
  rewrite hsub-det n⇓n₁ n⇓n₂ = refl
hsub-det (`sub-lam b⇓b₁) (`sub-lam b⇓b₂)
  rewrite hsub-detᴷ b⇓b₁ b⇓b₂ = refl
hsub-det (`sub-neut x⇓y) (`sub-neut x⇓z) = hsub-detᴺ x⇓y x⇓z

hsub-detᴺ (`sub-var i) (`sub-var .i) = refl
hsub-detᴺ (`sub-app f⇓f₁ a⇓a₁ b⇓b₁) (`sub-app f⇓f₂ a⇓a₂ b⇓b₂)
  rewrite hsub-detᴺ f⇓f₁ f⇓f₂ | hsub-det a⇓a₁ a⇓a₂ | app-det b⇓b₁ b⇓b₂
  = refl
hsub-detᴺ (`sub-rec n⇓n₁ cz⇓cz₁ cs⇓cs₁ c⇓c₁) (`sub-rec n⇓n₂ cz⇓cz₂ cs⇓cs₂ c⇓c₂)
  rewrite hsub-detᴺ n⇓n₁ n⇓n₂ | hsub-det cz⇓cz₁ cz⇓cz₂ | hsub-detᴷ cs⇓cs₁ cs⇓cs₂ | rec-det c⇓c₁ c⇓c₂
  = refl

----------------------------------------------------------------------

hsub-id-det : ∀{Γ A} {a a' : Wh Γ A} → idEnv / a ⇓ a' → a ≡ a'
hsub-id-det {a = a} = hsub-det (hsub-id a)

----------------------------------------------------------------------
