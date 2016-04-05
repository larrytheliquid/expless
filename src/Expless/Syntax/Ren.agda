module Expless.Syntax.Ren where
open import Expless.Syntax

----------------------------------------------------------------------

data Ren : Ctx → Ctx → Set where
  done : Ren ∅ ∅
  skip : ∀{Φ Γ A} → Ren Φ Γ → Ren (Φ , A) Γ
  keep :  ∀{Φ Γ A} → Ren Φ Γ → Ren (Φ , A) (Γ , A)

idRen : ∀{Γ} → Ren Γ Γ
idRen {∅} = done
idRen {Γ , A} = keep idRen

----------------------------------------------------------------------

renᴿ : ∀{Γ Φ A} (σ : Ren Φ Γ) → Var Γ A → Var Φ A
renᴿ done ()
renᴿ (skip σ) i = there (renᴿ σ i)
renᴿ (keep σ) here = here
renᴿ (keep σ) (there i) = there (renᴿ σ i)

----------------------------------------------------------------------

ren : ∀{m Φ Γ A} (σ : Ren Φ Γ) → Val m Γ A → Val m Φ A
renᴺ : ∀{m Φ Γ A} (σ : Ren Φ Γ) → Neut m Γ A → Neut m Φ A

renˢ : ∀{Φ Γ Δ} → Ren Δ Φ → Env Φ Γ → Env Δ Γ
renˢ Δ≥Φ ∅ = ∅
renˢ Δ≥Φ (σ , a) = renˢ Δ≥Φ σ , ren Δ≥Φ a

renᴮ : ∀{m Φ Γ A B} (σ : Ren Φ Γ) → Bind m Γ A B → Bind m Φ A B
renᴮ σ (`val a) = `val (ren (keep σ) a)
renᴮ σ (ρ `/ b) = renˢ σ ρ `/ b

ren σ `zero = `zero
ren σ (`suc n) = `suc (ren σ n)
ren σ (`λ b) = `λ (renᴮ σ b)
ren σ (`neut n) = `neut (renᴺ σ n)

renᴺ σ (`var j) = `var (renᴿ σ j)
renᴺ σ (n `∙ a) = renᴺ σ n `∙ ren σ a
renᴺ σ (`rec n `of cz `else cs) = `rec renᴺ σ n `of ren σ cz `else renᴮ σ cs

----------------------------------------------------------------------

liftRen : ∀{Γ Φ} Δ → Ren Φ Γ → Ren (Φ ++ Δ) (Γ ++ Δ)
liftRen ∅ σ = σ
liftRen (Δ , A) σ = keep (liftRen Δ σ)

skipsRen : ∀{Γ Φ} Δ → Ren Φ Γ → Ren (Φ ++ Δ) Γ
skipsRen ∅ σ = σ
skipsRen (Δ , A) σ = skip (skipsRen Δ σ)

wknRen₁ : ∀{Γ A} → Ren (Γ , A) Γ
wknRen₁ = skip idRen

wknRen : ∀{Γ} Δ → Ren (Γ ++ Δ) Γ
wknRen Δ = skipsRen Δ idRen

wkn : ∀{m Γ A} → Val m Γ A → ∀ Δ → Val m (Γ ++ Δ) A
wkn x Δ = ren (wknRen Δ) x

wkn₁ : ∀{m Γ A B} → Val m Γ B → Val m (Γ , A) B
wkn₁ = ren wknRen₁

wknˢ : ∀{Γ Φ} → Env Φ Γ → ∀ Δ → Env (Φ ++ Δ) Γ
wknˢ σ Δ = renˢ (wknRen Δ) σ

wkn₁ˢ : ∀{Γ Φ A} → Env Φ Γ → Env (Φ , A) Γ
wkn₁ˢ = renˢ wknRen₁

↑₁ : ∀{Γ Δ A} → Env Δ Γ → Env (Δ , A) (Γ , A)
↑₁ σ = wkn₁ˢ σ , `x

idEnv : ∀{Γ} → Env Γ Γ
idEnv {∅} = ∅
idEnv {Γ , A} = ↑₁ idEnv

----------------------------------------------------------------------
