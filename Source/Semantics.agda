module Source.Semantics where

open import Source.Syntax
open import Data.Nat
open import Data.Fin hiding (_≤_)
open import Data.Vec hiding (_++_)
open import Data.List
open import Data.Bool hiding (if_then_else_)
open import Data.Product renaming (_,_ to _,,_)
open import Data.Maybe

-- Function map: contains the function bodies.
data FunMap {γ}(Γ : FCtx γ) (σ : ℕ) : ∀{γ'} → FCtx γ' → FCtx γ' → Set where
  [] : FunMap Γ σ [] []
  _∷_ : ∀{m n}{γ'}{Γ' Δ : FCtx γ'} → Stmt Γ σ m n → FunMap Γ σ Γ' Δ → FunMap Γ σ (m ∷ Γ') (n ∷ Δ)

lookup-funmap : ∀{σ γ γ'}{Γ : FCtx γ}{Γ' Δ : FCtx γ'} → (f : Fun γ') → FunMap Γ σ Γ' Δ → Stmt Γ σ (lookup f Γ') (lookup f Δ)
lookup-funmap zero (x ∷ fm) = x
lookup-funmap (suc f) (x ∷ fm) = lookup-funmap f fm

-- Variable evaluation.
⟦_⟧[_,_] : ∀{ρ σ} → Exp ρ σ → Vec ℕ σ → Vec ℕ ρ → ℕ
⟦ local x ⟧[ Π , _ ] = lookup x Π
⟦ global x ⟧[ _ , Σ ] = lookup x Σ
⟦ apply f e₁ e₂ ⟧[ Π , Σ ] = f ⟦ e₁ ⟧[ Π , Σ ] ⟦ e₂ ⟧[ Π , Σ ]
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
--   Σ ▹ t ⟶t Σ' ▹ newstate ,, t' ∥ newtask
-- where
--  Σ are the global variables, t is the task currently executing, newstate is the new state of the task (executing or not),
--  t' is the task after taking the step, and newtask may be the new asynchronous task spawned during execution.
data _▹_⟶t_▹_∥_ {γ}{Γ : FCtx γ}{σ} (Σ : Vec ℕ σ) : Task Γ σ true → Vec ℕ σ → (∃ λ t → Task Γ σ t) → Maybe (Task Γ σ false) → Set where
  S-Skip : ∀{v n}{V : VarCtx v}{S : Stack (n ∷ V)} → 
    Σ ▹ ⟨ skip , S ⟩ ⟶t Σ ▹ false ,, ⟨ S ⟩ ∥ nothing
  S-Return : ∀{v n}{V : VarCtx v}{S : Stack (n ∷ V)}{n'}{v' : Vec ℕ n'} →
    Σ ▹ ⟨ return , v' ∷ S ⟩ ⟶t Σ ▹ false ,, ⟨ S ⟩ ∥ nothing
  S-Await : ∀{v n}{e : Exp σ n}{V : VarCtx v}{S : Stack (n ∷ V)} → 
    Σ ▹ ⟨ await e , S ⟩ ⟶t Σ ▹ false ,, ⟨ e , skip , S ⟩ ∥ nothing
  S-Seq-Fin : ∀{v₁ v₂ v₃ n₁ n₂}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂}{V₃ : VarCtx v₃}{s₁ : Stmt' Γ σ (n₁ ∷ V₁) (n₂ ∷ V₂)}{s₂ : Stmt' Γ σ (n₂ ∷ V₂) V₃}{S₁ : Stack (n₁ ∷ V₁)}{S₂ : Stack (n₂ ∷ V₂)}{Θ}{Σ' : Vec ℕ σ} → 
    Σ ▹ ⟨ s₁ , S₁ ⟩ ⟶t Σ' ▹ false ,, ⟨ S₂ ⟩ ∥ Θ →
    Σ ▹ ⟨ s₁ ,, s₂ , S₁ ⟩ ⟶t Σ' ▹ true ,, ⟨ s₂ , S₂ ⟩ ∥ Θ
  S-Seq-Step : ∀{v₁ v₁' v₂ v₃ n₁ n₁' n₂}{V₁ : VarCtx v₁}{V₁' : VarCtx v₁'}{V₂ : VarCtx v₂}{V₃ : VarCtx v₃}{s₁ : Stmt' Γ σ (n₁ ∷ V₁) (n₂ ∷ V₂)}{s₂ : Stmt' Γ σ (n₂ ∷ V₂) V₃}{S₁ : Stack (n₁ ∷ V₁)}{S₁' : Stack (n₁' ∷ V₁')}{s₁' : Stmt' Γ σ (n₁' ∷ V₁') (n₂ ∷ V₂)}{Θ}{Σ' : Vec ℕ σ} → 
    Σ ▹ ⟨ s₁ , S₁ ⟩ ⟶t Σ' ▹ true ,, ⟨ s₁' , S₁' ⟩ ∥ Θ →
    Σ ▹ ⟨ s₁ ,, s₂ , S₁ ⟩ ⟶t Σ' ▹ true ,, ⟨ s₁' ,, s₂ , S₁' ⟩ ∥ Θ
  S-Seq-Grd : ∀{v₁ v₁' v₂ v₃ n₁ n₁' n₂}{V₁ : VarCtx v₁}{V₁' : VarCtx v₁'}{V₂ : VarCtx v₂}{V₃ : VarCtx v₃}{s₁ : Stmt' Γ σ (n₁ ∷ V₁) (n₂ ∷ V₂)}{s₂ : Stmt' Γ σ (n₂ ∷ V₂) V₃}{S₁ : Stack (n₁ ∷ V₁)}{S₁' : Stack (n₁' ∷ V₁')}{s₁' : Stmt' Γ σ (n₁' ∷ V₁') (n₂ ∷ V₂)}{e : Exp σ n₁'}{Θ}{Σ' : Vec ℕ σ} →
    Σ ▹ ⟨ s₁ , S₁ ⟩ ⟶t Σ' ▹ false ,, ⟨ e , s₁' , S₁' ⟩ ∥ Θ → 
    Σ ▹ ⟨ s₁ ,, s₂ , S₁ ⟩ ⟶t Σ' ▹ false ,, ⟨ e , s₁' ,, s₂ , S₁' ⟩ ∥ Θ
  S-Assign-Local : ∀{n c}{v : Var n}{ρ : Vec ℕ n}{V : VarCtx c}{Π : Stack V}{e} →
    Σ ▹ ⟨ v ≔l e , ρ ∷ Π ⟩ ⟶t Σ ▹ false ,, ⟨ (ρ [ v ]≔ ⟦ e ⟧[ ρ , Σ ]) ∷ Π ⟩ ∥ nothing
  S-Var :  ∀{n c}{v : Var n}{ρ : Vec ℕ n}{V : VarCtx c}{Π : Stack V}{e} →
    Σ ▹ ⟨ var e , ρ ∷ Π ⟩ ⟶t Σ ▹ false ,, ⟨ (⟦ e ⟧[ ρ , Σ ] ∷ ρ) ∷ Π ⟩ ∥ nothing
  S-Assign-Global : ∀{n c}{v : Var σ}{ρ : Vec ℕ n}{V : VarCtx c}{Π : Stack V}{e} →
    Σ ▹ ⟨ v ≔g e , ρ ∷ Π ⟩ ⟶t Σ [ v ]≔ ⟦ e ⟧[ ρ , Σ ] ▹ false ,, ⟨ ρ ∷ Π ⟩ ∥ nothing
  S-Call : ∀{n c}{ρ : Vec ℕ n}{V : VarCtx  c}{Π : Stack V}{f : Fun γ}{A Δ} → 
    (fm : FunMap Γ σ Γ Δ) → 
    Σ ▹ ⟨ call f A , ρ ∷ Π ⟩ ⟶t Σ ▹ true ,, ⟨ stmt-to-stmt' (lookup-funmap f fm) ,, return , Data.Vec.map (λ e → ⟦ e ⟧[ ρ , Σ ]) A ∷ (ρ ∷ Π) ⟩ ∥ nothing
  S-Spawn : ∀{n c}{ρ : Vec ℕ n}{V : VarCtx  c}{Π : Stack V}{f : Fun γ}{A Δ} → 
    (fm : FunMap Γ σ Γ Δ) →
    Σ ▹ ⟨ spawn f A , ρ ∷ Π ⟩ ⟶t Σ ▹ false ,, ⟨ ρ ∷ Π ⟩ ∥ just ⟨ const 1 , stmt-to-stmt' (lookup-funmap f fm) , Data.Vec.map (λ e → ⟦ e ⟧[ ρ , Σ ]) A ∷ ∅ ⟩
  S-If-True : ∀{n v₁ v₂ e}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂}{s₁ s₂ : Stmt' Γ σ (n ∷ V₁) V₂}{ρ}{Π : Stack V₁} → 
    ⟦ e ⟧[ ρ , Σ ] > 0 → 
    Σ ▹ ⟨ if e then s₁ else s₂ , ρ ∷ Π ⟩ ⟶t Σ ▹ true ,, ⟨ s₁ , ρ ∷ Π ⟩ ∥ nothing
  S-If-False : ∀{n v₁ v₂ e}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂}{s₁ s₂ : Stmt' Γ σ (n ∷ V₁) V₂}{ρ}{Π : Stack V₁} → 
    ⟦ e ⟧[ ρ , Σ ] ≤ 0 → 
    Σ ▹ ⟨ if e then s₁ else s₂ , ρ ∷ Π ⟩ ⟶t Σ ▹ true ,, ⟨ s₁ , ρ ∷ Π ⟩ ∥ nothing
  S-While-True : ∀{n v₁ v₂ e}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂}{s : Stmt' Γ σ (n ∷ V₁) (n ∷ V₁)}{ρ}{Π : Stack V₁} → 
    ⟦ e ⟧[ ρ , Σ ] > 0 → 
    Σ ▹ ⟨ while e do s , ρ ∷ Π ⟩ ⟶t Σ ▹ true ,, ⟨ s ,, while e do s , ρ ∷ Π ⟩ ∥ nothing
  S-While-False : ∀{n v₁ v₂ e}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂}{s : Stmt' Γ σ (n ∷ V₁) (n ∷ V₁)}{ρ}{Π : Stack V₁} → 
    ⟦ e ⟧[ ρ , Σ ] ≤ 0 → 
    Σ ▹ ⟨ while e do s , ρ ∷ Π ⟩ ⟶t Σ ▹ false ,, ⟨ ρ ∷ Π ⟩ ∥ nothing
   
-- Given a global state and a list of tasks, generate a list of configurations which contains one
-- configuration per every task that could be scheduled from the list of tasks.
generate-active-tasks : ∀{γ σ}{Γ : FCtx γ} → Vec ℕ σ → List (Task Γ σ false) → List (Cfg Γ σ)
generate-active-tasks {γ} {σ} {Γ} Σ all = generate-active-tasks' [] all
  where generate-active-tasks' : List (Task Γ σ false) → List (Task Γ σ false) → List (Cfg Γ σ)
        generate-active-tasks' ts [] = []
        generate-active-tasks' ts (⟨ e , s , Π ∷ x₂ ⟩ ∷ ts₂) with ⟦ e ⟧[ Π , Σ ]
        ... | zero = generate-active-tasks' (⟨ e , s , Π ∷ x₂ ⟩ ∷ ts) ts₂
        ... | suc n = (Σ ▹ ⟨ s , Π ∷ x₂ ⟩ , (ts ++ ts₂)) ∷ generate-active-tasks' (⟨ e , s , Π ∷ x₂ ⟩ ∷ ts) ts₂
        generate-active-tasks' ts (⟨ Π ⟩ ∷ ts₂) = generate-active-tasks' (⟨ Π ⟩ ∷ ts) ts₂

-- Finally, the main relation: starting from a configuration, when we take a step, there may be a number
-- of different configurations we end up with, depending on what the scheduler does. Here we just generate
-- all the possibilities and let someone else make the decision which path to take.
data _⟶_ {γ σ}{Γ : FCtx γ} : Cfg Γ σ → List (Cfg Γ σ) → Set where
  same-task : ∀{Σ Σ' : Vec ℕ σ}{n v₁ v₂}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂}{Π : Stack (n ∷ V₁)}{s : Stmt' Γ σ (n ∷ V₁) V₂}{ts : List (Task Γ σ false)}{t : Task Γ σ true}{Θ} → 
    Σ ▹ t ⟶t Σ' ▹ true ,, ⟨ s , Π ⟩ ∥ Θ → 
    (Σ ▹ t , ts) ⟶ ((Σ' ▹ ⟨ s , Π ⟩ , maybe (λ x → x ∷ ts) ts Θ) ∷ []) 
  task-guard : ∀{Σ Σ' : Vec ℕ σ}{n v₁ v₂}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂}{Π : Stack (n ∷ V₁)}{s : Stmt' Γ σ (n ∷ V₁) V₂}{ts : List (Task Γ σ false)}{t : Task Γ σ true}{e}{Θ} → 
    Σ ▹ t ⟶t Σ' ▹ false ,, ⟨ e , s , Π ⟩ ∥ Θ → 
    (Σ ▹ t , ts) ⟶ generate-active-tasks Σ (⟨ e , s , Π ⟩ ∷ maybe (λ x → x ∷ ts) ts Θ)
  task-fin : ∀{Σ Σ' : Vec ℕ σ}{n v₁ v₂}{V₁ : VarCtx v₁}{V₂ : VarCtx v₂}{Π : Stack (n ∷ V₁)}{ts : List (Task Γ σ false)}{t : Task Γ σ true}{Θ} → 
    Σ ▹ t ⟶t Σ' ▹ false ,, ⟨ Π ⟩ ∥ Θ → 
    (Σ ▹ t , ts) ⟶ generate-active-tasks Σ (⟨ Π ⟩ ∷ (maybe (λ x → x ∷ ts) ts Θ))
