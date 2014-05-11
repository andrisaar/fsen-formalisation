module Source.Semantics where

open import Source.Syntax
open import Data.Nat
open import Data.Fin hiding (_≤_)
open import Data.Vec hiding (_++_; [_])
open import Data.List hiding (map)
open import Data.Bool hiding (if_then_else_)
open import Data.Maybe hiding (map)

-- Function map: contains the function bodies.
data FunMap' {γ}(Γ : FCtx γ) (σ : ℕ) : ∀{γ'} → FCtx γ' → FCtx γ' → Set where
  [] : FunMap' Γ σ [] []
  _∷_ : ∀{m n}{γ'}{Γ' Δ : FCtx γ'} → Stmt Γ σ m n → FunMap' Γ σ Γ' Δ → FunMap' Γ σ (m ∷ Γ') (n ∷ Δ)

FunMap : ∀{γ} → FCtx γ → ℕ → FCtx γ → Set
FunMap Γ σ Δ = FunMap' Γ σ Γ Δ

lookup-funmap : ∀{σ γ γ'}{Γ : FCtx γ}{Γ' Δ : FCtx γ'} → (f : Fun γ') → FunMap' Γ σ Γ' Δ → Stmt Γ σ (lookup f Γ') (lookup f Δ)
lookup-funmap zero (x ∷ fm) = x
lookup-funmap (suc f) (x ∷ fm) = lookup-funmap f fm

-- Variable evaluation.
⟦_⟧[_,_] : ∀{σ τ} → Exp σ τ → Vec ℕ σ → Vec ℕ τ → ℕ
⟦ local x ⟧[ _ , Π ] = lookup x Π
⟦ global x ⟧[ Σ , _ ] = lookup x Σ
⟦ apply f e₁ e₂ ⟧[ Σ , Π ] = f ⟦ e₁ ⟧[ Σ , Π ] ⟦ e₂ ⟧[ Σ , Π ]
⟦ const x ⟧[ _ , _ ] = x

-- Straightforward translation of statements to their enriched equivalents.
stmt-to-stmt' : ∀{γ}{Γ : FCtx γ}{σ : ℕ}{v : ℕ}{Π : VarCtx v}{ρ ρ' : ℕ} → Stmt {γ} Γ σ ρ ρ' → Stmt' Γ σ (ρ ∷ Π) (ρ' ∷ Π)
stmt-to-stmt' (x ≔l x₁) = x ≔l x₁
stmt-to-stmt' (x ≔g x₁) = x ≔g x₁
stmt-to-stmt' skip = skip
stmt-to-stmt' (stmt ∷ stmt₁) = stmt-to-stmt' stmt ,,  stmt-to-stmt' stmt₁
stmt-to-stmt' (if x then stmt₁ else stmt₂) = if x then stmt-to-stmt' stmt₁ else stmt-to-stmt' stmt₂
stmt-to-stmt' (while x do stmt) = while x do stmt-to-stmt' stmt
stmt-to-stmt' (var x) = var x
stmt-to-stmt' (call f x) = call f x
stmt-to-stmt' (spawn f x) = spawn f x

-- One step with a task.
-- This takes the form
--   Σ ▹ t ⟶t Σ' ▹ newstate , t' ∥ newtask
-- where
--  Σ are the global variables, t is the task currently executing, newstate is the new state of the task (executing or not),
--  t' is the task after taking the step, and newtask may be the new asynchronous task spawned during execution.
data _▹_⟶t_▹_,_∥_ {γ}{Γ : FCtx γ}{σ} (Σ : Vec ℕ σ) : Task Γ σ true → Vec ℕ σ → (t : Bool) → Task Γ σ t → Maybe (Task Γ σ false) → Set where
  S-Skip : ∀{v τ}{V : VarCtx v}{Π : Stack (τ ∷ V)} → 
    Σ ▹ ⟨ skip , Π ⟩ ⟶t Σ ▹ false , ⟨ Π ⟩ ∥ nothing
  S-Return : ∀{v τ τ'}{V : VarCtx v}{ρ : Vec ℕ τ}{Π : Stack (τ' ∷ V)} →
    Σ ▹ ⟨ return , ρ ∷ Π ⟩ ⟶t Σ ▹ false , ⟨ Π ⟩ ∥ nothing
  S-Await : ∀{v τ}{e : Exp σ τ}{V : VarCtx v}{Π : Stack (τ ∷ V)} → 
    Σ ▹ ⟨ await e , Π ⟩ ⟶t Σ ▹ false , ⟨ e , skip , Π ⟩ ∥ nothing
  S-Seq-Fin : ∀{v₁ v₂ v₃ τ₁ τ₂ Σ' Θ}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂}{V₃ : VarCtx v₃}{s₁ : Stmt' Γ σ (τ₁ ∷ V₁) (τ₂ ∷ V₂)}{s₂ : Stmt' Γ σ (τ₂ ∷ V₂) V₃}{Π₁ : Stack (τ₁ ∷ V₁)}{Π₂ : Stack (τ₂ ∷ V₂)} → 
    Σ ▹ ⟨ s₁ , Π₁ ⟩ ⟶t Σ' ▹ false , ⟨ Π₂ ⟩ ∥ Θ →
    Σ ▹ ⟨ s₁ ,, s₂ , Π₁ ⟩ ⟶t Σ' ▹ true , ⟨ s₂ , Π₂ ⟩ ∥ Θ
  S-Seq-Step : ∀{v₁ v₁' v₂ v₃ τ₁ τ₁' τ₂ Σ' Θ}{V₁ : VarCtx v₁}{V₁' : VarCtx v₁'}{V₂ : VarCtx v₂}{V₃ : VarCtx v₃}{s₁ : Stmt' Γ σ (τ₁ ∷ V₁) (τ₂ ∷ V₂)}{s₂ : Stmt' Γ σ (τ₂ ∷ V₂) V₃}{Π₁ : Stack (τ₁ ∷ V₁)}{Π₁' : Stack (τ₁' ∷ V₁')}{s₁' : Stmt' Γ σ (τ₁' ∷ V₁') (τ₂ ∷ V₂)} → 
    Σ ▹ ⟨ s₁ , Π₁ ⟩ ⟶t Σ' ▹ true , ⟨ s₁' , Π₁' ⟩ ∥ Θ →
    Σ ▹ ⟨ s₁ ,, s₂ , Π₁ ⟩ ⟶t Σ' ▹ true , ⟨ s₁' ,, s₂ , Π₁' ⟩ ∥ Θ
  S-Seq-Grd : ∀{v₁ v₁' v₂ v₃ n₁ n₁' n₂ Σ' Θ}{V₁ : VarCtx v₁}{V₁' : VarCtx v₁'}{V₂ : VarCtx v₂}{V₃ : VarCtx v₃}{s₁ : Stmt' Γ σ (n₁ ∷ V₁) (n₂ ∷ V₂)}{s₂ : Stmt' Γ σ (n₂ ∷ V₂) V₃}{Π₁ : Stack (n₁ ∷ V₁)}{Π₁' : Stack (n₁' ∷ V₁')}{s₁' : Stmt' Γ σ (n₁' ∷ V₁') (n₂ ∷ V₂)}{e} →
    Σ ▹ ⟨ s₁ , Π₁ ⟩ ⟶t Σ' ▹ false , ⟨ e , s₁' , Π₁' ⟩ ∥ Θ → 
    Σ ▹ ⟨ s₁ ,, s₂ , Π₁ ⟩ ⟶t Σ' ▹ false , ⟨ e , s₁' ,, s₂ , Π₁' ⟩ ∥ Θ
  S-Assign-Local : ∀{n c}{v : Var n}{ρ : Vec ℕ n}{V : VarCtx c}{Π : Stack V}{e} →
    Σ ▹ ⟨ v ≔l e , ρ ∷ Π ⟩ ⟶t Σ ▹ false , ⟨ (ρ [ v ]≔ ⟦ e ⟧[ Σ , ρ ]) ∷ Π ⟩ ∥ nothing
  S-Var :  ∀{v τ e}{ρ : Vec ℕ τ}{V : VarCtx v}{Π : Stack V} →
    Σ ▹ ⟨ var e , ρ ∷ Π ⟩ ⟶t Σ ▹ false , ⟨ (⟦ e ⟧[ Σ , ρ ] ∷ ρ) ∷ Π ⟩ ∥ nothing
  S-Assign-Global : ∀{n c}{v : Var σ}{ρ : Vec ℕ n}{V : VarCtx c}{Π : Stack V}{e} →
    Σ ▹ ⟨ v ≔g e , ρ ∷ Π ⟩ ⟶t Σ [ v ]≔ ⟦ e ⟧[ Σ , ρ ] ▹ false , ⟨ ρ ∷ Π ⟩ ∥ nothing
  S-Call : ∀{c τ Δ}{ρ : Vec ℕ τ}{V : VarCtx c}{Π : Stack V}{f : Fun γ}{A} → 
    (fm : FunMap Γ σ Δ) → 
    Σ ▹ ⟨ call f A , ρ ∷ Π ⟩ ⟶t Σ ▹ true , ⟨ stmt-to-stmt' (lookup-funmap f fm) ,, return , map (λ e → ⟦ e ⟧[ Σ , ρ ]) A ∷ (ρ ∷ Π) ⟩ ∥ nothing
  S-Spawn : ∀{c τ Δ}{ρ : Vec ℕ τ}{V : VarCtx c}{Π : Stack V}{f : Fun γ}{A} → 
    (fm : FunMap Γ σ Δ) →
    Σ ▹ ⟨ spawn f A , ρ ∷ Π ⟩ ⟶t Σ ▹ false , ⟨ ρ ∷ Π ⟩ ∥ just ⟨ const 1 , stmt-to-stmt' (lookup-funmap f fm) , map (λ e → ⟦ e ⟧[ Σ , ρ ]) A ∷ ∅ ⟩
  S-If-True : ∀{v₁ v₂ τ e}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂}{s₁ s₂ : Stmt' Γ σ (τ ∷ V₁) V₂}{ρ Π} → 
    ⟦ e ⟧[ Σ , ρ ] > 0 → 
    Σ ▹ ⟨ if e then s₁ else s₂ , ρ ∷ Π ⟩ ⟶t Σ ▹ true , ⟨ s₁ , ρ ∷ Π ⟩ ∥ nothing
  S-If-False : ∀{v₁ v₂ τ e}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂}{s₁ s₂ : Stmt' Γ σ (τ ∷ V₁) V₂}{ρ Π} → 
    ⟦ e ⟧[ Σ , ρ ] ≤ 0 → 
    Σ ▹ ⟨ if e then s₁ else s₂ , ρ ∷ Π ⟩ ⟶t Σ ▹ true , ⟨ s₁ , ρ ∷ Π ⟩ ∥ nothing
  S-While-True : ∀{v τ e}{V : VarCtx v}{s : Stmt' Γ σ (τ ∷ V) (τ ∷ V)}{ρ Π} → 
    ⟦ e ⟧[ Σ , ρ ] > 0 → 
    Σ ▹ ⟨ while e do s , ρ ∷ Π ⟩ ⟶t Σ ▹ true , ⟨ s ,, while e do s , ρ ∷ Π ⟩ ∥ nothing
  S-While-False : ∀{v τ e}{V : VarCtx v}{s : Stmt' Γ σ (τ ∷ V) (τ ∷ V)}{ρ Π} → 
    ⟦ e ⟧[ Σ , ρ ] ≤ 0 → 
    Σ ▹ ⟨ while e do s , ρ ∷ Π ⟩ ⟶t Σ ▹ false , ⟨ ρ ∷ Π ⟩ ∥ nothing
   
-- Given a global state and a list of tasks, generate a list of configurations which contains one
-- configuration per every task that could be scheduled from the list of tasks.
generate-active-tasks : ∀{γ σ}{Γ : FCtx γ} → Vec ℕ σ → List (Task Γ σ false) → List (Cfg Γ σ)
generate-active-tasks Σ all = generate-active-tasks' [] all
  where generate-active-tasks' : List (Task _ _ false) → List (Task _ _ false) → List (Cfg _ _)
        generate-active-tasks' l [] = []
        generate-active-tasks' l (⟨ e , s , ρ ∷ Π ⟩ ∷ r) with ⟦ e ⟧[ Σ , ρ ]
        ... | zero = generate-active-tasks' (⟨ e , s , ρ ∷ Π ⟩ ∷ l) r
        ... | suc n = (Σ ▹ ⟨ s , ρ ∷ Π ⟩ , (l ++ r)) ∷ generate-active-tasks' (⟨ e , s , ρ ∷ Π ⟩ ∷ l) r
        generate-active-tasks' l (⟨ Π ⟩ ∷ r) = generate-active-tasks' (⟨ Π ⟩ ∷ l) r

-- Finally, the main relation: starting from a configuration, when we take a step, there may be a number
-- of different configurations we end up with, depending on what the scheduler does. Here we just generate
-- all the possibilities and let someone else make the decision which path to take.
data _⟶_ {γ σ}{Γ : FCtx γ} : Cfg Γ σ → List (Cfg Γ σ) → Set where
  same-task : ∀{Σ Σ' ts t t' Θ} → 
    Σ ▹ t ⟶t Σ' ▹ true , t' ∥ Θ → 
    (Σ ▹ t , ts) ⟶ [ Σ' ▹ t' , maybe (λ x → x ∷ ts) ts Θ ]
  other-task : ∀{Σ Σ' ts t t' Θ} → 
    Σ ▹ t ⟶t Σ' ▹ false , t' ∥ Θ → 
    (Σ ▹ t , ts) ⟶ generate-active-tasks Σ (t' ∷ maybe (λ x → x ∷ ts) ts Θ)
 
