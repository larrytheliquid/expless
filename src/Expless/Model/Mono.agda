module Expless.Model.Mono where
open import Data.Product

open import Expless.Syntax
open import Expless.Syntax.Ren
open import Expless.Syntax.Comp
open import Expless.Syntax.Emb
open import Expless.Semantics.Conv
open import Expless.Model

open import Expless.Semantics.Conv.Props using ( `transᴺ ; `symᴺ ; ren-convᴺ ; emb-ren-symᴺ )
open import Expless.Syntax.Comp.Props using ( comp-renˢ )
open import Expless.Model.ReifyReflect using ( reflectᴿ )

----------------------------------------------------------------------

mono : ∀{Γ Δ} (Δ≥Γ : Ren Δ Γ)
  A (a : Wh Γ A)
  (⟦a⟧ : ⟦ Γ ⊢ a ∶ A ⟧)
  → ⟦ Δ ⊢ ren Δ≥Γ a ∶ A ⟧

mono Δ≥Γ `ℕ `zero tt = tt
mono Δ≥Γ `ℕ (`suc n) ⟦n⟧ = mono Δ≥Γ `ℕ n ⟦n⟧
mono Δ≥Γ `ℕ (`neut b) (b' , b≈b')
  = renᴺ Δ≥Γ b' , `transᴺ (ren-convᴺ Δ≥Γ b≈b') (`symᴺ (emb-ren-symᴺ Δ≥Γ b'))
mono Δ≥Γ (A `→ B) (`neut f) (f' , f≈f')
  = renᴺ Δ≥Γ f' , `transᴺ (ren-convᴺ Δ≥Γ f≈f') (`symᴺ (emb-ren-symᴺ Δ≥Γ f'))

mono Δ≥Γ (A `→ B) (`λ (σ `/ f)) ⟦λf⟧ = result where
  result : ⟦ _ ⊢ ren Δ≥Γ (`λ (σ `/ f)) ∶ A `→ B ⟧
  result Ω≥Δ a ⟦a⟧
    rewrite comp-renˢ Ω≥Δ Δ≥Γ σ
    = ⟦λf⟧ (comp Ω≥Δ Δ≥Γ) a ⟦a⟧

----------------------------------------------------------------------

monos : ∀{Φ Γ Δ}
  (Δ≥Φ : Ren Δ Φ)
  {σ : Env Φ Γ}
  (⟦σ⟧ : ⟦ Φ ⊨ σ ∶ Γ ⟧)
  → ⟦ Δ ⊨ renˢ Δ≥Φ σ ∶ Γ ⟧

monos Δ≥Φ ∅ = ∅
monos Δ≥Φ (_,_ {A = A} ⟦σ⟧ ⟦a⟧) = monos Δ≥Φ ⟦σ⟧ , mono Δ≥Φ A _ ⟦a⟧

----------------------------------------------------------------------

⟦idEnv⟧ : ∀{Γ} → ⟦ Γ ⊨ idEnv ∶ Γ ⟧
⟦idEnv⟧ {∅} = ∅
⟦idEnv⟧ {Γ , A}
  with ⟦idEnv⟧ {Γ}
... | ⟦σ⟧
  = monos wknRen₁ ⟦σ⟧ , reflectᴿ A here

----------------------------------------------------------------------
