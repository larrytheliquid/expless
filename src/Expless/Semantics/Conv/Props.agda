module Expless.Semantics.Conv.Props where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Expless.Syntax
open import Expless.Syntax.Ren
open import Expless.Syntax.Emb
open import Expless.Syntax.Comp.Props
open import Expless.Semantics.Conv

open import Expless.Semantics.HSub.Props using ( ren-hsub ; hsub-det ; hsub-id ; hsub-id-det )

----------------------------------------------------------------------

ren-conv : ∀{Δ Γ A} {a a' : Wh Γ A} (Δ≥Γ : Ren Δ Γ) → a ≈ a' → ren Δ≥Γ a ≈ ren Δ≥Γ a'
ren-convᴺ : ∀{Δ Γ A} {a a' : Nu Γ A} (Δ≥Γ : Ren Δ Γ) → a ≈ᴺ a' → renᴺ Δ≥Γ a ≈ᴺ renᴺ Δ≥Γ a'

ren-convᴷ : ∀{Δ Γ A B} {k k' : Clos Γ A B} (Δ≥Γ : Ren Δ Γ) → k ≈ᴷ k' → renᴮ Δ≥Γ k ≈ᴷ renᴮ Δ≥Γ k'
ren-convᴷ Δ≥Γ (`conv-clos-eq {f = σ `/ b} refl) = `conv-clos-eq refl
ren-convᴷ Δ≥Γ (`conv-clos-kappa {A = A} _ (`force {σ = σ} {b = f} f⇓f') (`force {σ = ρ} {b = g} g⇓g') f'≈g')
  with eq-decᴷ (renˢ Δ≥Γ σ `/ f) (renˢ Δ≥Γ ρ `/ g)
... | yes f≡g rewrite f≡g
  = `conv-clos-eq refl
... | no f≢g
  with ren-hsub (keep Δ≥Γ) f⇓f'
... | qf
  with ren-hsub (keep Δ≥Γ) g⇓g'
... | qg
  with ren-conv (keep Δ≥Γ) f'≈g'
... | ih
  rewrite sym (renˢ-comp A σ Δ≥Γ) | sym (renˢ-comp A ρ Δ≥Γ)
  = `conv-clos-kappa f≢g (`force qf) (`force qg) ih

ren-conv Δ≥Γ `conv-zero = `conv-zero
ren-conv Δ≥Γ (`conv-suc n≈n') = `conv-suc (ren-conv Δ≥Γ n≈n')
ren-conv Δ≥Γ (`conv-lam k≈k') = `conv-lam (ren-convᴷ Δ≥Γ k≈k')
ren-conv Δ≥Γ (`conv-neut a≈a') = `conv-neut (ren-convᴺ Δ≥Γ a≈a')

ren-convᴺ Δ≥Γ (`conv-var i) = `conv-var (renᴿ Δ≥Γ i)
ren-convᴺ Δ≥Γ (`conv-rec n≈n' cz≈cz' cs≈cs')
  = `conv-rec (ren-convᴺ Δ≥Γ n≈n') (ren-conv Δ≥Γ cz≈cz') (ren-convᴷ Δ≥Γ cs≈cs')
ren-convᴺ Δ≥Γ (`conv-app f≈f' a≈a')
  = `conv-app (ren-convᴺ Δ≥Γ f≈f') (ren-conv Δ≥Γ a≈a')

----------------------------------------------------------------------

`refl : ∀{Γ A} (x : Wh Γ A) → x ≈ x
`reflᴺ : ∀{Γ A} (x : Nu Γ A) → x ≈ᴺ x

`reflᴷ : ∀{Γ A B} (k : Clos Γ A B) → k ≈ᴷ k
`reflᴷ (σ `/ b) = `conv-clos-eq refl

`refl `zero = `conv-zero
`refl (`suc n) = `conv-suc (`refl n)
`refl (`λ b) = `conv-lam (`reflᴷ b)
`refl (`neut a) = `conv-neut (`reflᴺ a)

`reflᴺ (`var i) = `conv-var i
`reflᴺ (f `∙ a) = `conv-app (`reflᴺ f) (`refl a)
`reflᴺ (`rec n `of cz `else cs) = `conv-rec (`reflᴺ n) (`refl cz) (`reflᴷ cs)

`refl-eq : ∀{Γ A} (x y : Wh Γ A) → x ≡ y → x ≈ y
`refl-eq x .x refl = `refl x

----------------------------------------------------------------------

`sym : ∀{Γ A} {x y : Wh Γ A} → x ≈ y → y ≈ x
`symᴺ : ∀{Γ A} {x y : Nu Γ A} → x ≈ᴺ y → y ≈ᴺ x

`symᴷ : ∀{Γ A B} {j k : Clos Γ A B} → j ≈ᴷ k → k ≈ᴷ j
`symᴷ (`conv-clos-eq refl) = `conv-clos-eq refl
`symᴷ (`conv-clos-kappa f≢g f⇓f' g⇓g' f'≈g') = `conv-clos-kappa (nsym f≢g) g⇓g' f⇓f' (`sym f'≈g')

`sym `conv-zero = `conv-zero
`sym (`conv-suc n) = `conv-suc (`sym n)
`sym (`conv-lam b≈b') = `conv-lam (`symᴷ b≈b')
`sym (`conv-neut x≈y) = `conv-neut (`symᴺ x≈y)

`symᴺ (`conv-var i) = `conv-var i
`symᴺ (`conv-app f≈f' a≈a') = `conv-app (`symᴺ f≈f') (`sym a≈a')
`symᴺ (`conv-rec n≈n' cz≈cz' cs≈cs') = `conv-rec (`symᴺ n≈n') (`sym cz≈cz') (`symᴷ cs≈cs')

----------------------------------------------------------------------

`trans : ∀{Γ A} {x y z : Wh Γ A}
  → x ≈ z
  → z ≈ y
  → x ≈ y
`transᴺ : ∀{Γ A} {x y z : Nu Γ A}
  → x ≈ᴺ z
  → z ≈ᴺ y
  → x ≈ᴺ y

`transᴷ : ∀{Γ A B} {x y z : Clos Γ A B}
  → x ≈ᴷ z
  → z ≈ᴷ y
  → x ≈ᴷ y
`transᴷ (`conv-clos-eq refl) (`conv-clos-eq refl) = `conv-clos-eq refl
`transᴷ (`conv-clos-eq refl) (`conv-clos-kappa h≢g h⇓h g⇓g' h'≈g') = `conv-clos-kappa h≢g h⇓h g⇓g' h'≈g'
`transᴷ (`conv-clos-kappa f≢g f⇓f' h⇓h f'≈h') (`conv-clos-eq refl) = `conv-clos-kappa f≢g f⇓f' h⇓h f'≈h'
`transᴷ (`conv-clos-kappa {f = f} _ f⇓f' (`force h⇓h₁) f'≈h') (`conv-clos-kappa {g = g} _ (`force h⇓h₂) g⇓g' h'≈g')
  with eq-decᴷ f g
... | yes f≡g
  = `conv-clos-eq f≡g
... | no f≢g
  rewrite hsub-det h⇓h₁ h⇓h₂
  = `conv-clos-kappa f≢g f⇓f' g⇓g' (`trans f'≈h' h'≈g')

`trans `conv-zero `conv-zero = `conv-zero
`trans (`conv-suc x≈z) (`conv-suc z≈y) = `conv-suc (`trans x≈z z≈y)
`trans (`conv-lam x≈z) (`conv-lam z≈y) = `conv-lam (`transᴷ x≈z z≈y)
`trans (`conv-neut x≈z) (`conv-neut z≈y) = `conv-neut (`transᴺ x≈z z≈y)

`transᴺ (`conv-var i) y₁ = y₁
`transᴺ (`conv-app x x₁) (`conv-app x₂ x₃) = `conv-app (`transᴺ x x₂) (`trans x₁ x₃)
`transᴺ (`conv-rec x x₁ x₂) (`conv-rec x₃ x₄ x₅) = `conv-rec (`transᴺ x x₃) (`trans x₁ x₄) (`transᴷ x₂ x₅)

----------------------------------------------------------------------

-- commutativity of emb and ren wrt conv
emb-ren-sym : ∀{Γ Δ A} (Δ≥Γ : Ren Δ Γ) (a : Nf Γ A) → emb (ren Δ≥Γ a) ≈ ren Δ≥Γ (emb a)
emb-ren-symᴺ : ∀{Γ Δ A} (Δ≥Γ : Ren Δ Γ) (a : Ne Γ A) → embᴺ (renᴺ Δ≥Γ a) ≈ᴺ renᴺ Δ≥Γ (embᴺ a)

emb-ren-symᴮ : ∀{Γ Δ A B} (Δ≥Γ : Ren Δ Γ) (b : Bind nf Γ A B) → embᴮ (renᴮ Δ≥Γ b) ≈ᴷ renᴮ Δ≥Γ (embᴮ b)
emb-ren-symᴮ {A = A} Δ≥Γ (`val b)
  with eq-decᴷ (idEnv `/ emb (ren (keep Δ≥Γ) b)) (renˢ Δ≥Γ idEnv `/ emb b)
... | yes k≡k'
  = `conv-clos-eq k≡k'
... | no k≢k'
  with ren-hsub (keep Δ≥Γ) (hsub-id (emb b))
... | q
  rewrite sym (renˢ-comp A idEnv Δ≥Γ)
  = `conv-clos-kappa
  k≢k'
  (`force (hsub-id (emb (ren (keep Δ≥Γ) b))))
  (`force q)
  (emb-ren-sym (keep Δ≥Γ) b)

emb-ren-sym Δ≥Γ `zero = `conv-zero
emb-ren-sym Δ≥Γ (`suc n) = `conv-suc (emb-ren-sym Δ≥Γ n)
emb-ren-sym Δ≥Γ (`λ b) = `conv-lam (emb-ren-symᴮ Δ≥Γ b)

emb-ren-sym Δ≥Γ (`neut a) = `conv-neut (emb-ren-symᴺ Δ≥Γ a)

emb-ren-symᴺ Δ≥Γ (`var i) = `conv-var (renᴿ Δ≥Γ i)
emb-ren-symᴺ Δ≥Γ (f `∙ a) = `conv-app (emb-ren-symᴺ Δ≥Γ f) (emb-ren-sym Δ≥Γ a)
emb-ren-symᴺ Δ≥Γ (`rec n `of cz `else cs) = `conv-rec (emb-ren-symᴺ Δ≥Γ n) (emb-ren-sym Δ≥Γ cz) (emb-ren-symᴮ Δ≥Γ cs)

----------------------------------------------------------------------

nf-conv-eq : ∀{Γ A} (x y : Nf Γ A) → emb x ≈ emb y → x ≡ y
nf-conv-eqᴺ : ∀{Γ A} (x y : Ne Γ A) → embᴺ x ≈ᴺ embᴺ y → x ≡ y

nf-conv-eqᴮ : ∀{Γ A B} (x y : Bind nf Γ A B) → embᴮ x ≈ᴷ embᴮ y → x ≡ y
nf-conv-eqᴮ (`val f) (`val g) (`conv-clos-eq f≡g)
  rewrite nf-conv-eq f g (`refl-eq (emb f) (emb g) (inj-clos₃ f≡g))
  = refl
nf-conv-eqᴮ (`val f) (`val g) (`conv-clos-kappa f≢g (`force f⇓f') (`force g⇓g') f'≈g')
  rewrite sym (hsub-id-det f⇓f') | sym (hsub-id-det g⇓g') | nf-conv-eq f g f'≈g'
  = refl

nf-conv-eq `zero `zero x≈y = refl
nf-conv-eq `zero (`suc n) ()
nf-conv-eq `zero (`neut y) ()
nf-conv-eq (`suc n) `zero ()
nf-conv-eq (`suc m) (`suc n) (`conv-suc m≈n)
  rewrite nf-conv-eq m n m≈n
  = refl
nf-conv-eq (`suc n) (`neut y) ()
nf-conv-eq (`λ j) (`λ k) (`conv-lam j≈k)
  rewrite nf-conv-eqᴮ j k j≈k
  = refl
nf-conv-eq (`λ (`val b)) (`neut y) ()
nf-conv-eq (`neut x) `zero ()
nf-conv-eq (`neut x) (`suc n) ()
nf-conv-eq (`neut x) (`λ (`val b)) ()
nf-conv-eq (`neut x) (`neut y) (`conv-neut x≈y)
  rewrite nf-conv-eqᴺ x y x≈y
  = refl
nf-conv-eqᴺ (`var i) (`var .i) (`conv-var .i) = refl
nf-conv-eqᴺ (f₁ `∙ a₁) (f₂ `∙ a₂) (`conv-app f₁≈f₂ a₁≈a₂)
  rewrite nf-conv-eqᴺ f₁ f₂ f₁≈f₂ | nf-conv-eq a₁ a₂ a₁≈a₂
  = refl
nf-conv-eqᴺ (`rec b₁ `of cz₁ `else cs₁) (`rec b₂ `of cz₂ `else cs₂) (`conv-rec b₁≈b₂ cz₁≈cz₂ cs₁≈cs₂)
  rewrite nf-conv-eqᴺ b₁ b₂ b₁≈b₂ | nf-conv-eq cz₁ cz₂ cz₁≈cz₂ | nf-conv-eqᴮ cs₁ cs₂ cs₁≈cs₂
  = refl
nf-conv-eqᴺ (`var i) (y `∙ a) ()
nf-conv-eqᴺ (`var i) (`rec y `of ct `else cf) ()
nf-conv-eqᴺ (x `∙ a) (`var i) ()
nf-conv-eqᴺ (x `∙ a) (`rec y `of ct `else cf) ()
nf-conv-eqᴺ (`rec x `of ct `else cf) (`var i) ()
nf-conv-eqᴺ (`rec x `of ct `else cf) (y `∙ a) ()

----------------------------------------------------------------------
