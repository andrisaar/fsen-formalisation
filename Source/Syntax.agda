module Source.Syntax where

open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.List
open import Data.Bool hiding (if_then_else_)

-- Variables and functions are just numbers in a finite set.
Var = Fin
Fun = Fin

-- Function context: how many arguments does a function take?
FCtx = Vec ℕ

-- Expressions: local variables and global variables.
-- σ for the number of global variables, τ for the number of local variables.
-- Thankfully, all the variables are integers, so we don't have to worry about types.
data Exp (σ : ℕ) (τ : ℕ) : Set where
 local  : Var τ → Exp σ τ
 global : Var σ → Exp σ τ
 apply  : (ℕ → ℕ → ℕ) → Exp σ τ → Exp σ τ → Exp σ τ
 const  : ℕ → Exp σ τ

-- Variable context, indicating how many local variables we have. It's a vector because
-- of synchronous call; the topmost element indicates the current context.
VarCtx = Vec ℕ

-- Statements. This includes return, thus it's the internal state.
-- γ is the number of functions, Γ is the function contex,
-- σ is tne number of global variables.
-- Two variable contexts: one before and one after the statement is executed (because we
-- may introduce new local variables). Note that this means you can't keep creating new
-- variables in a while loop, but you can't do that with the system in our paper anyway.
data Stmt' {γ} (Γ : FCtx γ) (σ : ℕ) : ∀{v₁ v₂} → VarCtx v₁ → VarCtx v₂ → Set where
  _≔l_   : ∀{n v}{V : VarCtx v} → Var n → Exp σ n → Stmt' Γ σ (n ∷ V) (n ∷ V)
  _≔g_   : ∀{n v}{V : VarCtx v} → Var σ → Exp σ n → Stmt' Γ σ (n ∷ V) (n ∷ V)
  skip   : ∀{v}{V : VarCtx v} → Stmt' Γ σ V V
  if_then_else_ : ∀{n v₁ v₂}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂} → Exp σ n → Stmt' Γ σ (n ∷ V₁) V₂ → Stmt' Γ σ (n ∷ V₁) V₂ → Stmt' Γ σ (n ∷ V₁) V₂
  while_do_ : ∀{n v}{V : VarCtx v} → Exp σ n → Stmt' Γ σ (n ∷ V) (n ∷ V) → Stmt' Γ σ (n ∷ V) (n ∷ V)
  var    : ∀{n v}{V : VarCtx v} → Exp σ n → Stmt' Γ σ (n ∷ V) (suc n ∷ V)
  _,,_   : ∀{v₁ v₂ v₃}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂}{V₃ : VarCtx v₃} → Stmt' Γ σ V₁ V₂ → Stmt' Γ σ V₂ V₃ → Stmt' Γ σ V₁ V₃
  call   : ∀{n v}{V : VarCtx v} → (f : Fun γ) → Vec (Exp σ n) (lookup f Γ) → Stmt' Γ σ (n ∷ V) (n ∷ V)
  spawn  : ∀{n v}{V : VarCtx v} → (f : Fun γ) → Vec (Exp σ n) (lookup f Γ) → Stmt' Γ σ (n ∷ V) (n ∷ V)
  await  : ∀{n v}{V : VarCtx v} → Exp σ n → Stmt' Γ σ V V
  return : ∀{v}{V : VarCtx (suc v)} → Stmt' Γ σ V (tail V)

-- Statements, simplified: without return. This is what the legal programs may use.
-- The variable context is also simplified to just natural numbers, as we don't have to
-- keep track of the size of the stack.
data Stmt {γ} (Γ : FCtx γ) (σ : ℕ) : ℕ → ℕ → Set where
  _≔l_    : ∀{τ} → Var τ → Exp σ τ → Stmt Γ σ τ τ
  _≔g_    : ∀{τ} → Var σ → Exp σ τ → Stmt Γ σ τ τ
  skip    : ∀{τ} → Stmt Γ σ τ τ
  _∷_     : ∀{τ₁ τ₂ τ₃} → Stmt Γ σ τ₁ τ₂ → Stmt Γ σ τ₂ τ₃ → Stmt Γ σ τ₁ τ₃
  if_then_else_ : ∀{τ₁ τ₂} → Exp σ τ₁ → Stmt Γ σ τ₁ τ₂ → Stmt Γ σ τ₁ τ₂ → Stmt Γ σ τ₁ τ₂
  while_do_ : ∀{τ} → Exp σ τ → Stmt Γ σ τ τ → Stmt Γ σ τ τ
  var     : ∀{τ} → Exp σ τ → Stmt Γ σ τ (suc τ)
  call    : ∀{τ} → (f : Fun γ) → Vec (Exp σ τ) (lookup f Γ) → Stmt Γ σ τ τ
  spawn   : ∀{τ} → (f : Fun γ) → Vec (Exp σ τ) (lookup f Γ) → Stmt Γ σ τ τ

-- The stack itself, indexed by the variable context.
data Stack : ∀{v} (V : VarCtx v) → Set where
  ∅ : Stack []
  _∷_ : ∀{n v}{V : VarCtx v} → Vec ℕ n → Stack V →  Stack (n ∷ V)

-- Tasks. We use a separate boolean index to track whether the task is active or not.
data Task {γ} (Γ : FCtx γ) (σ : ℕ) : Bool → Set where
  ⟨_,_,_⟩ : ∀{n v₁ v₂}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂} → Exp σ n → Stmt' Γ σ (n ∷ V₁) V₂ → Stack (n ∷ V₁) → Task Γ σ false
  ⟨_,_⟩ : ∀{n v₁ v₂}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂} → Stmt' Γ σ (n ∷ V₁) V₂ → Stack (n ∷ V₁) → Task Γ σ true
  ⟨_⟩ : ∀{n v}{V : VarCtx v} → Stack (n ∷ V) → Task Γ σ false

-- Configurations. We don't need task indexes in the source language, so we just
-- pick out the "active" task. Other tasks must be not active (that is, either guarded
-- by an expression or terminated).
data Cfg {γ} (Γ : FCtx γ) : ℕ → Set where
  _▹_,_ : ∀{σ} → Vec ℕ σ → Task Γ σ true → List (Task Γ σ false) →  Cfg Γ σ


 
