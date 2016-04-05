module Expless.Syntax.Emb where
open import Expless.Syntax
open import Expless.Syntax.Ren

----------------------------------------------------------------------

emb : ∀{Γ A} → Nf Γ A → Wh Γ A
embᴺ : ∀{Γ A} → Ne Γ A → Nu Γ A

embᴮ : ∀{Γ A B} → Bind nf Γ A B → Clos Γ A B
embᴮ (`val b) = idEnv `/ emb b

emb `zero = `zero
emb (`suc n) = `suc (emb n)
emb (`λ b) = `λ (embᴮ b)
emb (`neut a) = `neut (embᴺ a)

embᴺ (`var i) = `var i
embᴺ (f `∙ a) = embᴺ f `∙ emb a
embᴺ (`rec n `of cz `else cs) = `rec embᴺ n `of emb cz `else embᴮ cs

----------------------------------------------------------------------
