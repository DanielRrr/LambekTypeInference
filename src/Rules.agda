module Rules where

open import Types
open import Expression

open import Data.Nat
open import Data.Product
open import Data.Vec  

data TypeSubst : Set where
    typeSubst : ∀ {n} → Vec (TVar × Type) n → TypeSubst

data _::_ : Expr → Type → Set where
    typeRel : (M : Expr) (A : Type) → M :: A

data TypeEnv : Set where
    typeEnv : ∀ {n} → Vec (Name × Type) n → TypeEnv

empty : TypeEnv
empty = typeEnv []


infixl 7 _+++_
_+++_ : TypeEnv → TypeEnv → TypeEnv
typeEnv x +++ typeEnv x₁ = typeEnv (x ++ x₁)

data _⊢_ : {M : Expr} {A : Type} → (Γ : TypeEnv) → M :: A → Set where
    axiom : {x : Name} {A : Type} → (empty +++ typeEnv [ x , A ]) ⊢ typeRel (var x) A  
    abs₁ : {x : Name} {A B : Type} {M : Expr} {Π : TypeEnv}
         → (typeEnv [ x , A ] +++ Π) ⊢ typeRel M B
         → Π ⊢ typeRel (λ₁ x M) (A ⇒ B)
    abs₂ : {x : Name} {A B : Type} {M : Expr} {Π : TypeEnv}
         → (Π +++ typeEnv [ x , A ]) ⊢ typeRel M B
         → Π ⊢ typeRel (λ₂ x M) (B ⇐ A)
    ⊗-intro : {Γ Δ : TypeEnv} {A B : Type} {M N : Expr}
         → Γ ⊢ typeRel M A
         → Δ ⊢ typeRel N B
         → (Γ +++ Δ) ⊢ typeRel (M · N) (A ⊗ B)
    ⊗-elim : {Γ Δ Π : TypeEnv} {A B C : Type} {M N : Expr} {x y : Name}
         → Γ ⊢ typeRel M (A ⊗ B)
         → (Δ +++ typeEnv [ x , A ] +++ typeEnv [ y , B ] +++ Π) ⊢ typeRel N C
         → (Δ +++ Γ +++ Π) ⊢ typeRel (Let M (x , y) N) C
    $ₗ-rule : {Γ Δ : TypeEnv} {A B : Type} {M N : Expr}
         → Γ ⊢ typeRel M A
         → Δ ⊢ typeRel N (A ⇒ B)
         → (Γ +++ Δ) ⊢ typeRel (M $ₗ N) B 
    $ᵣ-rule : {Γ Δ : TypeEnv} {A B : Type} {M N : Expr}
         → Γ ⊢ typeRel M (B ⇐ A)
         → Δ ⊢ typeRel N A
         → (Γ +++ Δ) ⊢ typeRel (M $ᵣ N) B
