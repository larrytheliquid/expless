module Expless.Syntax where

----------------------------------------------------------------------

infixr 4 _,_
infixr 0 _∧_

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

----------------------------------------------------------------------

open import Function
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

nsym : ∀{ℓ} {A : Set ℓ} {x y : A} → x ≢ y → y ≢ x
nsym f q = f (sym q)

----------------------------------------------------------------------

infixr 3 _`→_

data Type : Set where
  `ℕ : Type
  _`→_ : Type → Type → Type

data Form : Set where wh nf : Form

----------------------------------------------------------------------

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

data Var : Ctx → Type → Set where
  here : ∀{Γ A} → Var (Γ , A) A
  there : ∀{Γ A B} → Var Γ A → Var (Γ , B) A

_++_ : (Γ Δ : Ctx) → Ctx
Γ ++ ∅ = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

----------------------------------------------------------------------

data Exp : Ctx → Type → Set where
  `λ : ∀{Γ A B} (f : Exp (Γ , A) B) → Exp Γ (A `→ B)
  `var : ∀{Γ A} (i : Var Γ A) → Exp Γ A
  _`∙_ : ∀{Γ A B} (f : Exp Γ (A `→ B)) (a : Exp Γ A) → Exp Γ B

----------------------------------------------------------------------

data Val (m : Form) (Γ : Ctx) : Type → Set
data Neut (m : Form) (Γ : Ctx) : Type → Set
data Env (Φ : Ctx) : Ctx → Set
data Bind : Form → Ctx → Type → Type → Set

data Bind where
  `val : ∀{Γ A B} → Val nf (Γ , A) B → Bind nf Γ A B
  _`/_ : ∀{Γ Δ A B} → Env Δ Γ → Val wh (Γ , A) B → Bind wh Δ A B

----------------------------------------------------------------------

data Val m Γ where
  `zero : Val m Γ `ℕ
  `suc : Val m Γ `ℕ → Val m Γ `ℕ
  `λ : ∀{A B} → Bind m Γ A B → Val m Γ (A `→ B)
  `neut : ∀{A} (x : Neut m Γ A) → Val m Γ A

data Neut m Γ where
  `var : ∀{A} (i : Var Γ A) → Neut m Γ A
  _`∙_ : ∀{A B} (f : Neut m Γ (A `→ B)) (a : Val m Γ A) → Neut m Γ B
  `rec_`of_`else_ : ∀{C} (n : Neut m Γ `ℕ) (cz : Val m Γ C) (cs : Bind m Γ C C) → Neut m Γ C

data Env Φ where
  ∅ : Env Φ ∅
  _,_ : ∀{Γ A} → Env Φ Γ → Val wh Φ A → Env Φ (Γ , A)

Wh = Val wh
Nu = Neut wh
Nf = Val nf
Ne = Neut nf
Clos = Bind wh

----------------------------------------------------------------------

postulate
  eq-dec : ∀{m Γ A} (x y : Val m Γ A) → Dec (x ≡ y)
  eq-decᴷ : ∀{Γ A B} (f g : Clos Γ A B) → Dec (f ≡ g)

----------------------------------------------------------------------

inj-exte₁ : ∀{Φ Γ A}
  {σ₁ σ₂ : Env Φ Γ}
  {a₁ a₂ : Val wh Φ A}
  → _≡_ {A = Env Φ (Γ , A)} (σ₁ , a₁) (σ₂ , a₂)
  → σ₁ ≡ σ₂
inj-exte₁ refl = refl

inj-exte₂ : ∀{Φ Γ A}
  {σ₁ σ₂ : Env Φ Γ}
  {a₁ a₂ : Val wh Φ A}
  → _≡_ {A = Env Φ (Γ , A)} (σ₁ , a₁) (σ₂ , a₂)
  → a₁ ≡ a₂
inj-exte₂ refl = refl

inj-val : ∀{Γ A B}
  {b₁ b₂ : Val nf (Γ , A) B}
  → `val b₁ ≡ `val b₂
  → b₁ ≡ b₂
inj-val refl = refl

inj-clos₁ :  ∀{Δ Γ₁ Γ₂ A B}
  {σ₁  : Env Δ Γ₁}
  {b₁ : Val wh (Γ₁ , A) B}
  {σ₂  : Env Δ Γ₂}
  {b₂ : Val wh (Γ₂ , A) B}
  → σ₁ `/ b₁ ≡ σ₂ `/ b₂
  → Γ₁ ≡ Γ₂
inj-clos₁ refl = refl

inj-clos₂ :  ∀{Δ Γ A B}
  {σ₁ σ₂  : Env Δ Γ}
  {b₁ b₂ : Val wh (Γ , A) B}
  → σ₁ `/ b₁ ≡ σ₂ `/ b₂
  → σ₁ ≡ σ₂
inj-clos₂ refl = refl

inj-clos₃ :  ∀{Δ Γ A B}
  {σ₁ σ₂  : Env Δ Γ}
  {b₁ b₂ : Val wh (Γ , A) B}
  → σ₁ `/ b₁ ≡ σ₂ `/ b₂
  → b₁ ≡ b₂
inj-clos₃ refl = refl

----------------------------------------------------------------------

`xᴺ : ∀{m Γ A} → Neut m (Γ , A) A
`xᴺ = `var here

`x : ∀{m Γ A} → Val m (Γ , A) A
`x = `neut `xᴺ

lookup : ∀{Φ Γ A} → Env Φ Γ → Var Γ A → Wh Φ A
lookup (σ , a) here = a
lookup (σ , a) (there i) = lookup σ i

----------------------------------------------------------------------
