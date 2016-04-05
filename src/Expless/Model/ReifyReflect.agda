module Expless.Model.ReifyReflect where
open import Relation.Nullary
open import Data.Product

open import Expless.Syntax
open import Expless.Syntax.Ren
open import Expless.Syntax.Emb
open import Expless.Semantics.Conv
open import Expless.Model

open import Expless.Semantics.HSub.Props using ( hsub-id )

----------------------------------------------------------------------

reflect : ∀{Γ} A
  {a : Nu Γ A}
  (a' : Ne Γ A)
  (a≈a' : a ≈ᴺ embᴺ a')
  → ⟦ Γ ⊢ `neut a ∶ A ⟧
reflect `ℕ n' n≈n' = n' , n≈n'
reflect (A `→ B) f' f≈f' = f' , f≈f'

reflectᴿ : ∀{Γ} A
  (i : Var Γ A)
  → ⟦ Γ ⊢ `neut (`var i) ∶ A ⟧
reflectᴿ A i = reflect A (`var i) (`conv-var i)

----------------------------------------------------------------------

reify : ∀{Γ} A
  (a : Wh Γ A)
  (⟦a⟧ : ⟦ Γ ⊢ a ∶ A ⟧)
  → ∃ λ a'
  → a ≈ emb a'

reify `ℕ `zero tt = `zero , `conv-zero
reify `ℕ (`suc n) ⟦n⟧
  with reify `ℕ n ⟦n⟧
... | n' , n≈n'
  = `suc n' , `conv-suc n≈n'
reify `ℕ (`neut n) (n' , n≈n') = `neut n' , `conv-neut n≈n'
reify (A `→ B) (`neut f) (f' , f≈f') = `neut f' , `conv-neut f≈f'

reify (A `→ B) (`λ (σ `/ b)) ⟦f⟧
  with ⟦f⟧ (skip idRen) `x (reflect A `xᴺ (`conv-var here))
... | b' , b⇓b' , ⟦b⟧
  with reify B _ ⟦b⟧
... | b'' , b'≈b''
  with eq-decᴷ (σ `/ b) (idEnv `/ emb b'')
... | yes b≡b''
  = `λ (`val b'') , `conv-lam (`conv-clos-eq b≡b'')
... | no b≢b''
  = `λ (`val b'') , `conv-lam (`conv-clos-kappa b≢b'' (`force b⇓b') (`force (hsub-id (emb b''))) b'≈b'')

----------------------------------------------------------------------
