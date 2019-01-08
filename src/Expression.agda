module Expression where

open import Data.Bool
open import Data.Product
open import Data.List
open import Data.String hiding (_++_)
open import Data.String.Unsafe

open import Function

Name : Set
Name = String

data Expr : Set where
    var : Name → Expr
    λ₁ : Name → Expr → Expr
    λ₂ : Name → Expr → Expr
    _$ₗ_ : Expr → Expr → Expr
    _$ᵣ_ : Expr → Expr → Expr
    _·_ : Expr → Expr → Expr
    Let : Expr → Name × Name → Expr → Expr

freeVariables :
    Expr → List Name
freeVariables (var x) =
    [ x ]
freeVariables (λ₁ x expr) =
    boolFilter (not ∘ (_==_ x)) (freeVariables expr)
freeVariables (λ₂ x expr) =
    boolFilter (not ∘ (_==_ x)) (freeVariables expr)
freeVariables (expr $ₗ expr₁) =
    (freeVariables expr) ++ (freeVariables expr₁)
freeVariables (expr $ᵣ expr₁) =
    (freeVariables expr) ++ (freeVariables expr₁)
freeVariables (expr · expr₁) =
    (freeVariables expr) ++ (freeVariables expr₁)
freeVariables (Let expr (x , y) expr₁) =
    (freeVariables expr) ++ boolFilter (not ∘ λ x₁ → (x₁ == x) ∧ (x₁ == y)) (freeVariables expr₁)
